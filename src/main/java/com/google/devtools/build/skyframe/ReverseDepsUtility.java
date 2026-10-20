// Copyright 2014 The Bazel Authors. All rights reserved.
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

import com.google.common.base.MoreObjects;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.devtools.build.lib.collect.compacthashset.CompactHashSet;
import com.google.devtools.build.skyframe.KeyToConsolidate.Op;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.RandomAccess;
import java.util.Set;

/**
 * Stores reverse dependencies and delayed reverse-dependency consolidation operations using
 * primitive {@code int[]} arrays backed by {@link SkyKeyIdTable}.
 *
 * <p>Storage schema for reverse dependencies of done node entries:
 *
 * <ul>
 *   <li>0 rdeps: empty {@link ImmutableList}
 *   <li>1 rdep: bare {@link SkyKey}
 *   <li>2-4 rdeps: exact-length {@code int[]} of positive {@link SkyKeyIdTable} IDs ({@code arr[0]
 *       > 0})
 *   <li>5+ rdeps: growable {@code int[]} where {@code arr[0] = -size} and {@code arr[1..size]} are
 *       positive {@link SkyKeyIdTable} IDs (no {@link ArrayList} wrapper object and zero GC-traced
 *       references)
 * </ul>
 *
 * <p>Pending operations in {@code reverseDepsDataToConsolidate} are also stored in a primitive
 * {@code int[]} where {@code arr[0] = count} and {@code arr[1..count]} pack {@code (op.ordinal() <<
 * 30) | keyId}.
 */
abstract class ReverseDepsUtility {

  private static final Op[] OP_VALUES = Op.values();

  static Op getOpToStoreBare(AbstractInMemoryNodeEntry<?> entry) {
    DirtyBuildingState dirtyBuildingState = entry.dirtyBuildingState;
    if (dirtyBuildingState == null) {
      return Op.CHECK;
    }
    return dirtyBuildingState.isIncremental() ? Op.CHECK : Op.ADD;
  }

  private static int encodeOp(SkyKey key, Op op) {
    return (op.ordinal() << 30) | SkyKeyIdTable.intern(key);
  }

  private static Op decodeOp(int encoded) {
    return OP_VALUES[encoded >>> 30];
  }

  private static int decodeKeyId(int encoded) {
    return encoded & SkyKeyIdTable.KEY_ID_MASK;
  }

  static void appendDelayedOp(IncrementalInMemoryNodeEntry entry, SkyKey reverseDep, Op op) {
    int encoded = encodeOp(reverseDep, op);
    int[] consolidations = entry.getReverseDepsDataToConsolidateForReverseDepsUtil();
    if (consolidations == null) {
      consolidations = new int[5];
      consolidations[0] = 1;
      consolidations[1] = encoded;
      entry.setReverseDepsDataToConsolidateForReverseDepsUtil(consolidations);
    } else {
      int newCount = consolidations[0] + 1;
      if (newCount >= consolidations.length) {
        consolidations = Arrays.copyOf(consolidations, consolidations.length * 2 - 1);
        entry.setReverseDepsDataToConsolidateForReverseDepsUtil(consolidations);
      }
      consolidations[newCount] = encoded;
      consolidations[0] = newCount;
    }
  }

  private static void maybeDelayReverseDepOp(
      IncrementalInMemoryNodeEntry entry, SkyKey reverseDep, Op op) {
    int[] consolidations = entry.getReverseDepsDataToConsolidateForReverseDepsUtil();
    int currentReverseDepSize = sizeOf(entry.getReverseDepsRawForReverseDepsUtil());
    if (consolidations == null) {
      int initCap = Math.max(4, currentReverseDepSize);
      consolidations = new int[initCap + 1];
      consolidations[0] = 1;
      consolidations[1] = encodeOp(reverseDep, op);
      entry.setReverseDepsDataToConsolidateForReverseDepsUtil(consolidations);
    } else {
      appendDelayedOp(entry, reverseDep, op);
      consolidations = entry.getReverseDepsDataToConsolidateForReverseDepsUtil();
    }
    if (consolidations[0] >= currentReverseDepSize) {
      consolidateData(entry);
    }
  }

  private static boolean isSingleReverseDep(Object raw) {
    return raw instanceof SkyKey;
  }

  private static final class IntRdepsView extends AbstractList<SkyKey> implements RandomAccess {
    private final int[] arr;
    private final int offset;
    private final int size;

    IntRdepsView(int[] arr, int offset, int size) {
      this.arr = arr;
      this.offset = offset;
      this.size = size;
    }

    @Override
    public SkyKey get(int index) {
      Preconditions.checkElementIndex(index, size);
      return SkyKeyIdTable.get(arr[offset + index]);
    }

    @Override
    public int size() {
      return size;
    }
  }

  @SuppressWarnings("unchecked")
  private static List<SkyKey> multipleAsList(Object raw) {
    if (raw instanceof int[] arr) {
      if (arr.length == 0) {
        return ImmutableList.of();
      }
      if (arr[0] < 0) {
        return new IntRdepsView(arr, 1, -arr[0]);
      }
      return new IntRdepsView(arr, 0, arr.length);
    }
    return (List<SkyKey>) raw;
  }

  private static int sizeOf(Object raw) {
    if (isSingleReverseDep(raw)) {
      return 1;
    }
    if (raw instanceof int[] arr) {
      return arr.length == 0 ? 0 : (arr[0] < 0 ? -arr[0] : arr.length);
    }
    return ((List<?>) raw).size();
  }

  static void addReverseDep(IncrementalInMemoryNodeEntry entry, SkyKey newReverseDep) {
    int[] dataToConsolidate = entry.getReverseDepsDataToConsolidateForReverseDepsUtil();
    if (dataToConsolidate != null) {
      maybeDelayReverseDepOp(entry, newReverseDep, Op.ADD);
      return;
    }
    var raw = entry.getReverseDepsRawForReverseDepsUtil();
    int newSize = sizeOf(raw) + 1;
    if (newSize == 1) {
      entry.setReverseDepsForReverseDepsUtil(newReverseDep);
    } else if (newSize == 2) {
      entry.setReverseDepsForReverseDepsUtil(
          new int[] {SkyKeyIdTable.intern((SkyKey) raw), SkyKeyIdTable.intern(newReverseDep)});
    } else if (newSize <= 4) {
      int[] newArray = Arrays.copyOf((int[]) raw, newSize);
      newArray[newSize - 1] = SkyKeyIdTable.intern(newReverseDep);
      entry.setReverseDepsForReverseDepsUtil(newArray);
    } else if (newSize == 5) {
      int[] oldArr = (int[]) raw;
      int[] newArr = new int[9];
      newArr[0] = -5;
      System.arraycopy(oldArr, 0, newArr, 1, 4);
      newArr[5] = SkyKeyIdTable.intern(newReverseDep);
      entry.setReverseDepsForReverseDepsUtil(newArr);
    } else {
      int[] arr = (int[]) raw;
      if (newSize >= arr.length) {
        arr = Arrays.copyOf(arr, arr.length * 2 - 1);
        entry.setReverseDepsForReverseDepsUtil(arr);
      }
      arr[newSize] = SkyKeyIdTable.intern(newReverseDep);
      arr[0] = -newSize;
    }
  }

  /** See {@link #addReverseDep} method. */
  static void removeReverseDep(IncrementalInMemoryNodeEntry entry, SkyKey reverseDep) {
    maybeDelayReverseDepOp(entry, reverseDep, Op.REMOVE);
  }

  static void removeReverseDepsMatching(
      IncrementalInMemoryNodeEntry entry, Set<SkyKey> deletedKeys) {
    consolidateData(entry);
    ImmutableCollection<SkyKey> currentReverseDeps =
        consolidateAndGetReverseDeps(entry, /* checkConsistency= */ true);
    var remainingReverseDeps = new ArrayList<SkyKey>(currentReverseDeps.size());
    for (SkyKey reverseDep : currentReverseDeps) {
      if (!deletedKeys.contains(reverseDep)) {
        remainingReverseDeps.add(reverseDep);
      }
    }
    writeReverseDeps(entry, remainingReverseDeps);
  }

  static ImmutableCollection<SkyKey> consolidateAndGetReverseDeps(
      IncrementalInMemoryNodeEntry entry, boolean checkConsistency) {
    consolidateData(entry);

    var raw = entry.getReverseDepsRawForReverseDepsUtil();
    if (isSingleReverseDep(raw)) {
      return ImmutableSet.of((SkyKey) raw);
    } else {
      List<SkyKey> reverseDeps = multipleAsList(raw);
      if (!checkConsistency) {
        return ImmutableList.copyOf(reverseDeps);
      }
      ImmutableSet<SkyKey> set = ImmutableSet.copyOf(reverseDeps);
      if (set.size() != reverseDeps.size()) {
        Set<SkyKey> seen = new HashSet<>();
        Set<SkyKey> duplicates = new HashSet<>();
        for (SkyKey key : reverseDeps) {
          if (!seen.add(key)) {
            duplicates.add(key);
          }
        }
        throw new IllegalStateException(
            String.format("In node %s: duplicate reverse deps present: %s", entry, duplicates));
      }
      return set;
    }
  }

  static Set<SkyKey> returnNewElements(IncrementalInMemoryNodeEntry entry) {
    return consolidateDataAndReturnNewElements(entry, /* mutateObject= */ false);
  }

  private static Set<SkyKey> consolidateDataAndReturnNewElements(
      IncrementalInMemoryNodeEntry entry, boolean mutateObject) {
    int[] dataToConsolidate = entry.getReverseDepsDataToConsolidateForReverseDepsUtil();
    if (dataToConsolidate == null) {
      return ImmutableSet.of();
    }
    int dataLen = dataToConsolidate[0];

    Op opToStoreBare = getOpToStoreBare(entry);
    boolean allRdepsAreNew = opToStoreBare == Op.ADD;
    Set<SkyKey> allReverseDeps;
    Set<SkyKey> newReverseDeps;
    var raw = entry.getReverseDepsRawForReverseDepsUtil();
    if (isSingleReverseDep(raw)) {
      Preconditions.checkState(!allRdepsAreNew, entry);
      allReverseDeps = CompactHashSet.create((SkyKey) raw);
      newReverseDeps = CompactHashSet.create();
    } else {
      List<SkyKey> reverseDepsAsList = multipleAsList(raw);
      if (allRdepsAreNew) {
        Preconditions.checkState(reverseDepsAsList.isEmpty(), entry);
        allReverseDeps = null;
        newReverseDeps = CompactHashSet.createWithExpectedSize(dataLen);
      } else {
        allReverseDeps = getReverseDepsSet(entry, reverseDepsAsList);
        newReverseDeps = CompactHashSet.create();
      }
    }

    boolean hadRemoveOnInitial = false;
    for (int i = 1; i <= dataLen; i++) {
      int encoded = dataToConsolidate[i];
      Op op = decodeOp(encoded);
      SkyKey key = SkyKeyIdTable.get(decodeKeyId(encoded));
      switch (op) {
        case CHECK:
          Preconditions.checkState(!allRdepsAreNew, entry);
          Preconditions.checkState(
              allReverseDeps.contains(key),
              "Reverse dep not present: %s %s %s",
              key,
              allReverseDeps,
              entry);
          Preconditions.checkState(
              newReverseDeps.add(key),
              "Duplicate new reverse dep: %s %s %s",
              key,
              allReverseDeps,
              entry);
          break;
        case REMOVE:
          hadRemoveOnInitial = true;
          if (!allRdepsAreNew) {
            Preconditions.checkState(
                allReverseDeps.remove(key),
                "Reverse dep to be removed not present: %s %s %s",
                key,
                allReverseDeps,
                entry);
          }
          Preconditions.checkState(
              newReverseDeps.remove(key) || !allRdepsAreNew,
              "Reverse dep to be removed not present: %s %s %s",
              key,
              newReverseDeps,
              entry);
          break;
        case ADD:
          if (!allRdepsAreNew) {
            Preconditions.checkState(
                allReverseDeps.add(key),
                "Duplicate reverse deps: %s %s %s",
                key,
                raw,
                entry);
          }
          Preconditions.checkState(
              newReverseDeps.add(key),
              "Duplicate new reverse deps: %s %s %s",
              key,
              raw,
              entry);
          break;
      }
    }
    if (mutateObject) {
      entry.setReverseDepsDataToConsolidateForReverseDepsUtil(null);
      if (allRdepsAreNew && !hadRemoveOnInitial) {
        // Fast path for initial build: reuse the already-interned key IDs in dataToConsolidate
        // without re-interning every SkyKey in writeReverseDeps.
        writeReverseDepsFromInitialData(entry, dataToConsolidate, dataLen, newReverseDeps);
      } else {
        writeReverseDeps(entry, allRdepsAreNew ? newReverseDeps : allReverseDeps);
      }
    }
    return newReverseDeps;
  }

  private static void writeReverseDepsFromInitialData(
      IncrementalInMemoryNodeEntry entry,
      int[] dataToConsolidate,
      int count,
      Set<SkyKey> newReverseDeps) {
    if (!entry.keepsEdges() || count == 0) {
      entry.setReverseDepsForReverseDepsUtil(ImmutableList.of());
    } else if (count == 1) {
      entry.setReverseDepsForReverseDepsUtil(Iterables.getOnlyElement(newReverseDeps));
    } else if (count <= 4) {
      int[] arr = new int[count];
      for (int i = 0; i < count; i++) {
        arr[i] = decodeKeyId(dataToConsolidate[i + 1]);
      }
      entry.setReverseDepsForReverseDepsUtil(arr);
    } else {
      int[] arr =
          dataToConsolidate.length == count + 1 ? dataToConsolidate : new int[count + 1];
      arr[0] = -count;
      for (int i = 1; i <= count; i++) {
        arr[i] = dataToConsolidate[i] & SkyKeyIdTable.KEY_ID_MASK;
      }
      entry.setReverseDepsForReverseDepsUtil(arr);
    }
  }

  @CanIgnoreReturnValue
  static Set<SkyKey> consolidateDataAndReturnNewElements(IncrementalInMemoryNodeEntry entry) {
    return consolidateDataAndReturnNewElements(entry, /* mutateObject= */ true);
  }

  static void consolidateData(IncrementalInMemoryNodeEntry entry) {
    int[] dataToConsolidate = entry.getReverseDepsDataToConsolidateForReverseDepsUtil();
    if (dataToConsolidate == null) {
      return;
    }
    entry.setReverseDepsDataToConsolidateForReverseDepsUtil(null);
    int dataLen = dataToConsolidate[0];
    var raw = entry.getReverseDepsRawForReverseDepsUtil();
    if (isSingleReverseDep(raw)) {
      Preconditions.checkState(
          dataLen == 1,
          "dataToConsolidate not size 1 even though only one rdep: %s %s %s",
          dataLen,
          raw,
          entry);
      int encoded = dataToConsolidate[1];
      SkyKey key = SkyKeyIdTable.get(decodeKeyId(encoded));
      Preconditions.checkState(getOpToStoreBare(entry) == Op.CHECK, entry);
      switch (decodeOp(encoded)) {
        case REMOVE:
          entry.setReverseDepsForReverseDepsUtil(ImmutableList.of());
          // Fall through to check.
        case CHECK:
          Preconditions.checkState(key.equals(raw), "%s %s %s", key, raw, entry);
          break;
        case ADD:
          throw new IllegalStateException(
              "Shouldn't delay add if only one element: " + key + ", " + raw + ", " + entry);
      }
      return;
    }
    List<SkyKey> reverseDepsAsList = multipleAsList(raw);
    Set<SkyKey> reverseDepsAsSet = getReverseDepsSet(entry, reverseDepsAsList);

    Preconditions.checkState(getOpToStoreBare(entry) == Op.CHECK, entry);
    for (int i = 1; i <= dataLen; i++) {
      int encoded = dataToConsolidate[i];
      SkyKey key = SkyKeyIdTable.get(decodeKeyId(encoded));
      switch (decodeOp(encoded)) {
        case CHECK:
          Preconditions.checkState(
              reverseDepsAsSet.contains(key), "%s %s %s", key, reverseDepsAsSet, entry);
          break;
        case REMOVE:
          Preconditions.checkState(reverseDepsAsSet.remove(key), "%s %s %s", key, raw, entry);
          break;
        case ADD:
          Preconditions.checkState(reverseDepsAsSet.add(key), "%s %s %s", key, raw, entry);
          break;
      }
    }
    writeReverseDeps(entry, reverseDepsAsSet);
  }

  /** Stores the given reverse deps, which must not contain duplicates. */
  private static void writeReverseDeps(
      IncrementalInMemoryNodeEntry entry, Collection<SkyKey> reverseDeps) {
    if (!entry.keepsEdges() || reverseDeps.isEmpty()) {
      entry.setReverseDepsForReverseDepsUtil(ImmutableList.of());
    } else if (reverseDeps.size() == 1) {
      entry.setReverseDepsForReverseDepsUtil(Iterables.getOnlyElement(reverseDeps));
    } else if (reverseDeps.size() <= 4) {
      int[] arr = new int[reverseDeps.size()];
      int i = 0;
      for (SkyKey k : reverseDeps) {
        arr[i++] = SkyKeyIdTable.intern(k);
      }
      entry.setReverseDepsForReverseDepsUtil(arr);
    } else {
      int n = reverseDeps.size();
      int[] arr = new int[n + 1];
      arr[0] = -n;
      int i = 1;
      for (SkyKey k : reverseDeps) {
        arr[i++] = SkyKeyIdTable.intern(k);
      }
      entry.setReverseDepsForReverseDepsUtil(arr);
    }
  }

  private static Set<SkyKey> getReverseDepsSet(
      IncrementalInMemoryNodeEntry entry, List<SkyKey> reverseDepsAsList) {
    Set<SkyKey> reverseDepsAsSet = CompactHashSet.create(reverseDepsAsList);
    checkForDuplicates(reverseDepsAsSet, reverseDepsAsList, entry);
    return reverseDepsAsSet;
  }

  static void checkForDuplicates(
      Set<SkyKey> reverseDepsAsSet, List<SkyKey> reverseDepsAsList, InMemoryNodeEntry entry) {
    if (reverseDepsAsSet.size() == reverseDepsAsList.size()) {
      return;
    }
    Set<SkyKey> seen = new HashSet<>();
    List<SkyKey> duplicates = new ArrayList<>();
    for (SkyKey key : reverseDepsAsList) {
      if (!seen.add(key)) {
        duplicates.add(key);
      }
    }
    throw new IllegalStateException(
        (reverseDepsAsList.size() - reverseDepsAsSet.size())
            + " duplicate reverse deps: "
            + duplicates
            + " for "
            + entry);
  }

  static String toString(IncrementalInMemoryNodeEntry entry) {
    var raw = entry.getReverseDepsRawForReverseDepsUtil();
    return MoreObjects.toStringHelper("ReverseDeps")
        .add("reverseDeps", isSingleReverseDep(raw) ? raw : multipleAsList(raw))
        .add("singleReverseDep", isSingleReverseDep(raw))
        .add("dataToConsolidate", entry.getReverseDepsDataToConsolidateForReverseDepsUtil())
        .toString();
  }

  private ReverseDepsUtility() {}
}
