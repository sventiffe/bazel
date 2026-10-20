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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.MoreObjects;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.devtools.build.lib.concurrent.ThreadSafety.ThreadHostile;
import com.google.devtools.build.lib.skyframe.serialization.autocodec.SerializationConstant;
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;
import java.util.AbstractCollection;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.RandomAccess;
import java.util.Set;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.LiteralKind;
import org.checkerframework.framework.qual.QualifierForLiterals;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * Encapsulates direct dependency groups Using primitive {@code int[]} {@link SkyKeyIdTable} IDs.
 *
 * <p>Stores both in-flight and compressed dependency groups in primitive {@code int[]} arrays (with
 * positive ints representing {@link SkyKeyIdTable} IDs and negative ints {@code -groupSize}
 * representing multi-element group delimiters), eliminating {@code Object[]} reference scanning by
 * the JVM garbage collector and boxed {@code Integer} allocations.
 */
public class GroupedDeps implements Iterable<List<SkyKey>> {

  @SubtypeOf(DefaultObject.class)
  @Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
  @QualifierForLiterals(LiteralKind.NULL)
  public @interface Compressed {}

  @DefaultQualifierInHierarchy
  @SubtypeOf({})
  @Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
  private @interface DefaultObject {}

  private static final int[] EMPTY_INTS = new int[0];

  /** The total number of deps. */
  private int size;

  /**
   * Primitive int encoding of deps and group delimiters: positive {@code v > 0} is a {@link
   * SkyKeyIdTable} ID; negative {@code v < 0} marks the start of a multi-element group of size
   * {@code -v} (where {@code -v >= 2}). Singleton groups have no preceding size marker.
   */
  private int[] elements;

  private int elementsLen;

  /**
   * Starting indices in {@link #elements} for group {@code i >= 1} at {@code groupIndices[i - 1]}.
   */
  private int[] groupIndices;

  private int groupIndicesLen;

  public GroupedDeps() {
    this(0, EMPTY_INTS, 0, EMPTY_INTS, 0);
  }

  private GroupedDeps(
      int size, int[] elements, int elementsLen, int[] groupIndices, int groupIndicesLen) {
    this.size = size;
    this.elements = elements;
    this.elementsLen = elementsLen;
    this.groupIndices = groupIndices;
    this.groupIndicesLen = groupIndicesLen;
  }

  private void ensureElementsCapacity(int minCapacity) {
    if (elements.length < minCapacity) {
      int newCap = Math.max(4, Math.max(elements.length * 2, minCapacity));
      elements = Arrays.copyOf(elements, newCap);
    }
  }

  private void ensureGroupIndicesCapacity(int minCapacity) {
    if (groupIndices.length < minCapacity) {
      int newCap = Math.max(2, Math.max(groupIndices.length * 2, minCapacity));
      groupIndices = Arrays.copyOf(groupIndices, newCap);
    }
  }

  public void appendSingleton(SkyKey key) {
    markNextGroup();
    ensureElementsCapacity(elementsLen + 1);
    elements[elementsLen++] = SkyKeyIdTable.intern(key);
    size++;
  }

  public void appendGroup(List<SkyKey> group) {
    appendNextGroup(group.iterator(), group.size());
  }

  public void appendGroups(Set<SkyKey> deps, List<Integer> groupSizes) {
    ensureElementsCapacity(elementsLen + deps.size() + groupSizes.size());
    if (isEmpty()) {
      if (groupSizes.size() > 1) {
        ensureGroupIndicesCapacity(groupSizes.size() - 1);
      }
    } else {
      ensureGroupIndicesCapacity(groupIndicesLen + groupSizes.size());
    }
    Iterator<SkyKey> it = deps.iterator();
    for (Integer groupSize : groupSizes) {
      appendNextGroup(it, groupSize);
    }
    checkArgument(
        !it.hasNext(), "size(deps) != sum(groupSizes) (deps=%s, groupSizes=%s)", deps, groupSizes);
  }

  private void appendNextGroup(Iterator<SkyKey> it, int groupSize) {
    if (groupSize == 0) {
      return;
    }
    if (groupSize == 1) {
      appendSingleton(it.next());
      return;
    }
    markNextGroup();
    ensureElementsCapacity(elementsLen + groupSize + 1);
    elements[elementsLen++] = -groupSize;
    for (int i = 0; i < groupSize; i++) {
      elements[elementsLen++] = SkyKeyIdTable.intern(it.next());
    }
    size += groupSize;
  }

  private void markNextGroup() {
    if (!isEmpty()) {
      ensureGroupIndicesCapacity(groupIndicesLen + 1);
      groupIndices[groupIndicesLen++] = elementsLen;
    }
  }

  public void remove(Set<SkyKey> toRemove) {
    if (toRemove.isEmpty()) {
      return;
    }
    GroupedDeps newDeps = new GroupedDeps();
    for (List<SkyKey> group : this) {
      List<SkyKey> newGroup = new ArrayList<>(group.size());
      for (SkyKey key : group) {
        if (!toRemove.contains(key)) {
          newGroup.add(key);
        }
      }
      newDeps.appendGroup(newGroup);
    }

    checkArgument(
        newDeps.size == size - toRemove.size(),
        "Requested removal of absent element(s) (toRemove=%s, elements=%s)",
        toRemove,
        this);

    this.size = newDeps.size;
    this.elements = newDeps.elements;
    this.elementsLen = newDeps.elementsLen;
    this.groupIndices = newDeps.groupIndices;
    this.groupIndicesLen = newDeps.groupIndicesLen;
  }

  private static final class GroupView extends AbstractList<SkyKey> implements RandomAccess {
    private final int[] elements;
    private final int offset;
    private final int length;

    GroupView(int[] elements, int offset, int length) {
      this.elements = elements;
      this.offset = offset;
      this.length = length;
    }

    @Override
    public SkyKey get(int index) {
      checkArgument(index >= 0 && index < length, index);
      return SkyKeyIdTable.get(elements[offset + index]);
    }

    @Override
    public int size() {
      return length;
    }
  }

  public List<SkyKey> getDepGroup(int i) {
    int index = i == 0 ? 0 : groupIndices[i - 1];
    int v = elements[index];
    if (v > 0) {
      return ImmutableList.of(SkyKeyIdTable.get(v));
    }
    int groupSize = -v;
    return new GroupView(elements, index + 1, groupSize);
  }

  public int numGroups() {
    return isEmpty() ? 0 : groupIndicesLen + 1;
  }

  public int numElements() {
    return size;
  }

  public static int numElements(@Compressed Object compressed) {
    switch (compressionCase(compressed)) {
      case EMPTY:
        return 0;
      case SINGLETON:
        return 1;
      case MULTIPLE:
        int[] arr = (int[]) compressed;
        int size = 0;
        int i = 0;
        while (i < arr.length) {
          int v = arr[i++];
          if (v > 0) {
            size++;
          } else {
            int groupSize = -v;
            size += groupSize;
            i += groupSize;
          }
        }
        return size;
    }
    throw new AssertionError(compressed);
  }

  private enum CompressionCase {
    EMPTY,
    SINGLETON,
    MULTIPLE
  }

  private static CompressionCase compressionCase(@Compressed Object compressed) {
    if (compressed == EMPTY_COMPRESSED) {
      return CompressionCase.EMPTY;
    }
    if (compressed instanceof SkyKey) {
      return CompressionCase.SINGLETON;
    }
    checkArgument(compressed instanceof int[], compressed);
    return CompressionCase.MULTIPLE;
  }

  public static Iterable<SkyKey> compressedToIterable(@Compressed Object compressed) {
    switch (compressionCase(compressed)) {
      case EMPTY:
        return ImmutableList.of();
      case SINGLETON:
        return ImmutableList.of((SkyKey) compressed);
      case MULTIPLE:
        int[] arr = (int[]) compressed;
        return () -> new UngroupedIterator(arr, arr.length, null);
    }
    throw new AssertionError(compressed);
  }

  public static @Compressed Object castAsCompressed(Object obj) {
    checkArgument(obj == EMPTY_COMPRESSED || obj instanceof SkyKey || obj instanceof int[]);
    return (@Compressed Object) obj;
  }

  public boolean isEmpty() {
    return elementsLen == 0;
  }

  public static boolean isEmpty(@Compressed Object compressed) {
    return compressed == EMPTY_COMPRESSED;
  }

  public boolean contains(SkyKey key) {
    int targetId = SkyKeyIdTable.intern(key);
    for (int i = 0; i < elementsLen; i++) {
      if (elements[i] == targetId) {
        return true;
      }
    }
    return false;
  }

  @SerializationConstant static final @Compressed Object EMPTY_COMPRESSED = new Object();

  public @Compressed Object compress() {
    switch (numElements()) {
      case 0:
        return EMPTY_COMPRESSED;
      case 1:
        return SkyKeyIdTable.get(elements[0]);
      default:
        return elementsLen == elements.length ? elements : Arrays.copyOf(elements, elementsLen);
    }
  }

  public ImmutableSet<SkyKey> toSet() {
    ImmutableSet.Builder<SkyKey> builder = ImmutableSet.builderWithExpectedSize(size);
    for (int i = 0; i < elementsLen; i++) {
      int v = elements[i];
      if (v > 0) {
        builder.add(SkyKeyIdTable.get(v));
      }
    }
    return builder.build();
  }

  public static GroupedDeps decompress(@Compressed Object compressed) {
    switch (compressionCase(compressed)) {
      case EMPTY:
        return new GroupedDeps();
      case SINGLETON:
        int[] single = new int[] {SkyKeyIdTable.intern((SkyKey) compressed)};
        return new GroupedDeps(1, single, 1, EMPTY_INTS, 0);
      case MULTIPLE:
        int[] arr = (int[]) compressed;
        int size = 0;
        int[] groupIndices = EMPTY_INTS;
        int groupIndicesLen = 0;
        int i = 0;
        while (i < arr.length) {
          if (i > 0) {
            if (groupIndicesLen == groupIndices.length) {
              groupIndices =
                  Arrays.copyOf(groupIndices, Math.max(4, groupIndicesLen * 2));
            }
            groupIndices[groupIndicesLen++] = i;
          }
          int v = arr[i++];
          if (v > 0) {
            size++;
          } else {
            int groupSize = -v;
            size += groupSize;
            i += groupSize;
          }
        }
        return new GroupedDeps(size, arr.clone(), arr.length, groupIndices, groupIndicesLen);
    }
    throw new AssertionError(compressed);
  }

  @Override
  public int hashCode() {
    throw new UnsupportedOperationException("Should not need to get hash for " + this);
  }

  private static boolean checkUnorderedIntSliceEquality(
      int[] a, int aOffset, int[] b, int bOffset, int len) {
    if (Arrays.equals(a, aOffset, aOffset + len, b, bOffset, bOffset + len)) {
      return true;
    }
    int[] aCopy = Arrays.copyOfRange(a, aOffset, aOffset + len);
    int[] bCopy = Arrays.copyOfRange(b, bOffset, bOffset + len);
    Arrays.sort(aCopy);
    Arrays.sort(bCopy);
    return Arrays.equals(aCopy, bCopy);
  }

  private final class CollectionView extends AbstractCollection<SkyKey> {
    private final int expectedElementsLen = elementsLen;

    @Override
    public Iterator<SkyKey> iterator() {
      checkState(
          elementsLen == expectedElementsLen,
          "GroupedDeps mutated during iteration (expected size %s, actual size %s)",
          expectedElementsLen,
          elementsLen);
      return new UngroupedIterator(elements, expectedElementsLen, GroupedDeps.this);
    }

    @Override
    public int size() {
      checkState(
          elementsLen == expectedElementsLen,
          "GroupedDeps mutated during iteration (expected size %s, actual size %s)",
          expectedElementsLen,
          elementsLen);
      return size;
    }
  }

  private static final class UngroupedIterator implements Iterator<SkyKey> {
    private final int[] elements;
    private final int expectedSize;
    private final GroupedDeps owner;
    private int i = 0;

    private UngroupedIterator(int[] elements, int expectedSize, GroupedDeps owner) {
      this.elements = elements;
      this.expectedSize = expectedSize;
      this.owner = owner;
      advanceIfSizeMarker();
    }

    @Override
    public boolean hasNext() {
      boolean hasNext = i < expectedSize;
      if (!hasNext && owner != null) {
        checkState(
            owner.elementsLen == expectedSize,
            "GroupedDeps mutated during iteration (expected size %s, actual size %s)",
            expectedSize,
            owner.elementsLen);
      }
      return hasNext;
    }

    @Override
    public SkyKey next() {
      int id = elements[i++];
      advanceIfSizeMarker();
      return SkyKeyIdTable.get(id);
    }

    private void advanceIfSizeMarker() {
      if (i < expectedSize && elements[i] < 0) {
        i++;
      }
    }
  }

  @ThreadHostile
  public Collection<SkyKey> getAllElementsAsIterable() {
    return new CollectionView();
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (!(other instanceof GroupedDeps that)) {
      return false;
    }
    if (this.size != that.size
        || this.elementsLen != that.elementsLen
        || this.numGroups() != that.numGroups()) {
      return false;
    }
    if (Arrays.equals(this.elements, 0, this.elementsLen, that.elements, 0, that.elementsLen)) {
      return true;
    }
    int numGroups = this.numGroups();
    for (int g = 0; g < numGroups; g++) {
      int idx1 = g == 0 ? 0 : this.groupIndices[g - 1];
      int idx2 = g == 0 ? 0 : that.groupIndices[g - 1];
      int v1 = this.elements[idx1];
      int v2 = that.elements[idx2];
      if (v1 > 0 || v2 > 0) {
        if (v1 != v2) {
          return false;
        }
      } else {
        int groupSize1 = -v1;
        int groupSize2 = -v2;
        if (groupSize1 != groupSize2
            || !checkUnorderedIntSliceEquality(
                this.elements, idx1 + 1, that.elements, idx2 + 1, groupSize1)) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public String toString() {
    return MoreObjects.toStringHelper(this)
        .add("size", size)
        .add("elements", getAllElementsAsIterable())
        .toString();
  }

  private class GroupedIterator implements Iterator<List<SkyKey>> {
    private int i = 0;

    @Override
    public boolean hasNext() {
      return i < numGroups();
    }

    @Override
    public List<SkyKey> next() {
      return getDepGroup(i++);
    }
  }

  @Override
  public Iterator<List<SkyKey>> iterator() {
    return new GroupedIterator();
  }

  public static final class WithHashSet extends GroupedDeps {
    private final HashSet<SkyKey> set = new HashSet<>();

    @Override
    public void appendSingleton(SkyKey key) {
      super.appendSingleton(key);
      set.add(key);
    }

    @Override
    public void appendGroup(List<SkyKey> group) {
      super.appendGroup(group);
      set.addAll(group);
    }

    @Override
    public void appendGroups(Set<SkyKey> deps, List<Integer> groupSizes) {
      super.appendGroups(deps, groupSizes);
      set.addAll(deps);
    }

    @Override
    public void remove(Set<SkyKey> toRemove) {
      super.remove(toRemove);
      set.removeAll(toRemove);
    }

    @Override
    public boolean contains(SkyKey needle) {
      return set.contains(needle);
    }

    @Override
    public ImmutableSet<SkyKey> toSet() {
      return ImmutableSet.copyOf(set);
    }
  }
}
