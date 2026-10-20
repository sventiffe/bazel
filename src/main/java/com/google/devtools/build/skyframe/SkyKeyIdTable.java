// Copyright 2026 The Bazel Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package com.google.devtools.build.skyframe;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.lang.invoke.VarHandle;
import java.util.Arrays;

/**
 * Bijective, sharded 30-bit integer ID table for {@link SkyKey} instances.
 *
 * <p>Allows {@link GroupedDeps} and {@link ReverseDepsUtility} to store forward and reverse
 * dependency edges as primitive {@code int[]} arrays instead of {@code Object[]} reference arrays,
 * eliminating tens of millions of GC-traced pointers on large Skyframe graphs.
 *
 * <p>Assigned IDs are strictly positive 30-bit integers ({@code 1 <= id <= 0x3FFF_FFFF}), leaving
 * the sign bit (or top 2 bits) free for group-length markers in {@link GroupedDeps} or operation
 * tags in {@link ReverseDepsUtility}.
 */
public final class SkyKeyIdTable {

  private static final int STRIPE_BITS = 8;
  private static final int STRIPE_COUNT = 1 << STRIPE_BITS;
  private static final int STRIPE_MASK = STRIPE_COUNT - 1;

  private static final int PAGE_BITS = 12;
  private static final int PAGE_SIZE = 1 << PAGE_BITS;
  private static final int PAGE_MASK = PAGE_SIZE - 1;

  /** Maximum local index per stripe so that {@code (localIndex << 8) | stripe} fits in 30 bits. */
  private static final int MAX_LOCAL_INDEX = (1 << (30 - STRIPE_BITS)) - 1;

  public static final int KEY_ID_MASK = 0x3FFF_FFFF;

  private static final Stripe[] STRIPES = new Stripe[STRIPE_COUNT];

  static {
    for (int i = 0; i < STRIPE_COUNT; i++) {
      STRIPES[i] = new Stripe(i);
    }
  }

  private SkyKeyIdTable() {}

  private static int smear(int hashCode) {
    int h = hashCode;
    h ^= h >>> 16;
    h *= 0x85ebca6b;
    h ^= h >>> 13;
    h *= 0xc2b2ae35;
    h ^= h >>> 16;
    return h;
  }

  /** Returns the positive 30-bit integer ID for {@code key}, assigning one if not yet present. */
  public static int intern(SkyKey key) {
    checkNotNull(key);
    int rawHash = key.hashCode();
    int h = smear(rawHash);
    int stripeIdx = h & STRIPE_MASK;
    Stripe stripe = STRIPES[stripeIdx];
    int[] table = stripe.table;
    SkyKey[][] pages = stripe.pages;
    int mask = table.length - 1;
    int slot = (h >>> STRIPE_BITS) & mask;
    while (true) {
      int localIndex = table[slot];
      if (localIndex == 0) {
        break;
      }
      int pageIdx = localIndex >>> PAGE_BITS;
      if (pageIdx < pages.length) {
        SkyKey[] page = pages[pageIdx];
        if (page != null) {
          SkyKey existing = page[localIndex & PAGE_MASK];
          if (existing != null
              && (existing == key || (existing.hashCode() == rawHash && existing.equals(key)))) {
            return (localIndex << STRIPE_BITS) | stripeIdx;
          }
        }
      }
      slot = (slot + 1) & mask;
    }
    return stripe.internSlow(key, rawHash, h);
  }

  /** Resolves a positive 30-bit integer ID back to its {@link SkyKey} in lock-free O(1) time. */
  public static SkyKey get(int id) {
    Stripe stripe = STRIPES[id & STRIPE_MASK];
    int localIndex = (id & KEY_ID_MASK) >>> STRIPE_BITS;
    return stripe.pages[localIndex >>> PAGE_BITS][localIndex & PAGE_MASK];
  }

  private static final class Stripe {
    private final int stripeIdx;
    private int count = 0;
    /** Open-addressed hash table storing {@code localIndex > 0} directly (0 = empty). */
    volatile int[] table = new int[256];
    volatile SkyKey[][] pages;

    Stripe(int stripeIdx) {
      this.stripeIdx = stripeIdx;
      SkyKey[][] initPages = new SkyKey[16][];
      initPages[0] = new SkyKey[PAGE_SIZE];
      this.pages = initPages;
    }

    synchronized int internSlow(SkyKey key, int rawHash, int h) {
      int[] t = this.table;
      SkyKey[][] curPages = this.pages;
      int mask = t.length - 1;
      int slot = (h >>> STRIPE_BITS) & mask;
      while (true) {
        int existingIdx = t[slot];
        if (existingIdx == 0) {
          break;
        }
        SkyKey existing = curPages[existingIdx >>> PAGE_BITS][existingIdx & PAGE_MASK];
        if (existing == key || (existing.hashCode() == rawHash && existing.equals(key))) {
          return (existingIdx << STRIPE_BITS) | this.stripeIdx;
        }
        slot = (slot + 1) & mask;
      }

      int localIndex = ++this.count;
      checkState(localIndex <= MAX_LOCAL_INDEX, "SkyKeyIdTable stripe overflow: %s", localIndex);
      int id = (localIndex << STRIPE_BITS) | this.stripeIdx;

      int pageIdx = localIndex >>> PAGE_BITS;
      int pageOffset = localIndex & PAGE_MASK;
      if (pageIdx >= curPages.length) {
        SkyKey[][] newPages = Arrays.copyOf(curPages, curPages.length * 2);
        SkyKey[] newPage = new SkyKey[PAGE_SIZE];
        newPage[pageOffset] = key;
        newPages[pageIdx] = newPage;
        VarHandle.releaseFence();
        this.pages = newPages;
        curPages = newPages;
      } else if (curPages[pageIdx] == null) {
        SkyKey[] newPage = new SkyKey[PAGE_SIZE];
        newPage[pageOffset] = key;
        VarHandle.releaseFence();
        curPages[pageIdx] = newPage;
      } else {
        curPages[pageIdx][pageOffset] = key;
        VarHandle.releaseFence();
      }

      // 75% maximum load factor keeps linear probe chains short while halving table footprint.
      int threshold = (t.length * 3) >>> 2;
      if (localIndex >= threshold) {
        int nextCap = t.length * 2;
        int[] next = new int[nextCap];
        int nextMask = nextCap - 1;
        for (int idx = 1; idx <= localIndex; idx++) {
          SkyKey k = curPages[idx >>> PAGE_BITS][idx & PAGE_MASK];
          int kh = smear(k.hashCode());
          int s = (kh >>> STRIPE_BITS) & nextMask;
          while (next[s] != 0) {
            s = (s + 1) & nextMask;
          }
          next[s] = idx;
        }
        VarHandle.releaseFence();
        this.table = next;
      } else {
        t[slot] = localIndex;
      }
      return id;
    }
  }
}
