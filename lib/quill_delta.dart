// Copyright (c) 2018, Anatoly Pulyaevskiy. All rights reserved. Use of this source code
// is governed by a BSD-style license that can be found in the LICENSE file.

/// Implementation of Quill Delta format in Dart.
library quill_delta;

import 'dart:convert' show jsonEncode, jsonDecode;
import 'dart:math' as math;

import 'package:collection/collection.dart';
import 'package:quiver_hashcode/hashcode.dart';

const _attributeEquality = DeepCollectionEquality();

enum OpType { insert, delete, retain }

abstract class Op {
  static final String insertKey = 'insert';
  static final String deleteKey = 'delete';
  static final String retainKey = 'retain';
  static final String attributesKey = 'attributes';

  /// Type of the operation.
  OpType get type;

  bool get isInsert => type == OpType.insert;
  bool get isDelete => type == OpType.delete;
  bool get isRetain => type == OpType.retain;

  int get length;
  bool get isEmpty => length == 0;
  bool get isNotEmpty => !isEmpty;

  /// Attributes applied by this operation, can be `null`.
  Map<String, dynamic> get attributes =>
      _attributes == null ? null : UnmodifiableMapView(_attributes);
  final Map<String, dynamic> _attributes;

  T match<T>(
      {T Function(InsertStringOp) insert,
      T Function(InsertObjectOp) insertObject,
      T Function(DeleteOp) delete,
      T Function(RetainOp) retain});

  // TODO Op.attributes should never be null, instead it should be empty

  Op._(Map<String, dynamic> attributes)
      : _attributes =
            attributes == null ? null : Map<String, dynamic>.of(attributes);

  /// Merge two operations, returns `null` when ops can't be merged.
  factory Op.merge(Op op1, Op op2) {
    if (op1.type != op2.type) return null;

    if (op1 is InsertStringOp &&
        op2 is InsertStringOp &&
        op1.hasSameAttributes(op2)) {
      return InsertOp.string(op1.text + op2.text, op1.attributes);
    } else if (op1 is DeleteOp && op2 is DeleteOp) {
      return DeleteOp(op1.count + op2.count);
    } else if (op1 is RetainOp &&
        op2 is RetainOp &&
        op1.hasSameAttributes(op2)) {
      return RetainOp(op1.count + op2.count, op1.attributes);
    }

    return null;
  }

  /// Creates new [Operation] from JSON payload.
  static Op fromJson(Map<String, dynamic> map) {
    if (map.containsKey(Op.insertKey)) {
      final Object value = map[Op.insertKey];
      if (value is String) {
        return InsertOp.string(value, map[Op.attributesKey]);
      } else if (value is Map<String, dynamic> && value.keys.isNotEmpty) {
        final type = value.keys.first;
        final object = value[type];
        return InsertOp.object(type, object, map[Op.attributesKey]);
      }
    } else if (map.containsKey(Op.deleteKey)) {
      final int length = map[Op.deleteKey];
      return DeleteOp(length);
    } else if (map.containsKey(Op.retainKey)) {
      final int length = map[Op.retainKey];
      return RetainOp(length, map[Op.attributesKey]);
    }
    throw ArgumentError.value(map, 'Invalid Delta operation.');
  }

  // Shortcuts because we often need to operate on text ops.
  T getTextOrElse<T>(T els) =>
      this is InsertStringOp ? (this as InsertStringOp).text : els;
  T mapTextOrElse<T>(T Function(String) map, T els) =>
      this is InsertStringOp ? map((this as InsertStringOp).text) : els;
  int indexOf(String s, [int start = 0]) =>
      mapTextOrElse((t) => t.indexOf(s, start), -1);
  bool startsWith(String s) => mapTextOrElse((t) => t.startsWith(s), false);
  bool endsWith(String s) => mapTextOrElse((t) => t.endsWith(s), false);
  bool contains(String s) => mapTextOrElse((t) => t.contains(s), false);
  List<String> split(String s) =>
      mapTextOrElse((t) => t.split(s), List<String>.empty(growable: false));
  bool isString(String s) => mapTextOrElse((t) => t == s, false);

  /// Returns JSON-serializable representation of this operation.
  Map<String, dynamic> toJson();

  /// Returns `true` if this operation has any attributes.
  bool get hasAttributes => _attributes != null && _attributes.isNotEmpty;

  /// Returns `true` if this operation has attribute specified by [name].
  bool hasAttribute(String name) =>
      _attributes != null && _attributes.containsKey(name);

  /// Returns `true` if [other] operation has the same attributes as this one.
  bool hasSameAttributes(Op other) =>
      _attributeEquality.equals(_attributes, other._attributes);

  /// Return a copy of this [Op] with the given [attributes].
  Op withAttributes(Map<String, dynamic> attributes) => match(
      insert: (op) => InsertOp.string(op.text, attributes),
      insertObject: (op) => InsertOp.object(op.key, op.value, attributes),
      delete: (op) => op,
      retain: (op) => RetainOp(op.count, attributes));
}

abstract class InsertOp extends Op {
  @override
  OpType get type => OpType.insert;

  InsertOp._(Map<String, dynamic> attributes) : super._(attributes);

  static InsertStringOp string(String text,
          [Map<String, dynamic> attributes]) =>
      InsertStringOp._(text, attributes);

  static InsertObjectOp object(String objectType, object,
          [Map<String, dynamic> attributes]) =>
      InsertObjectOp._(objectType, object, attributes);

  /// Get the empty insert operation (a no-op).
  factory InsertOp.empty() => _empty;
  static final InsertOp _empty = InsertStringOp._('');
}

class InsertStringOp extends InsertOp {
  final String text;

  @override
  int get length => text.length;

  InsertStringOp._(this.text, [Map<String, dynamic> attributes])
      : assert(text != null),
        super._(attributes);

  @override
  T match<T>(
          {T Function(InsertStringOp) insert,
          T Function(InsertObjectOp) insertObject,
          T Function(DeleteOp) delete,
          T Function(RetainOp) retain}) =>
      insert?.call(this);

  @override
  Map<String, dynamic> toJson() => {
        Op.insertKey: text,
        if (_attributes != null && _attributes.isNotEmpty)
          Op.attributesKey: attributes
      };

  @override
  String toString() =>
      'insert(${text.replaceAll('\n', '\\n')})${hasAttributes ? ' + $attributes' : ''}';

  @override
  bool operator ==(other) {
    if (identical(this, other)) return true;
    if (other is InsertStringOp) {
      return text == other.text && hasSameAttributes(other);
    }
    return false;
  }

  @override
  int get hashCode => hasAttributes
      ? hash2(_mapHashCode(_attributes), text.hashCode)
      : text.hashCode;
}

class InsertObjectOp extends InsertOp {
  /// Type string of the object. This is the key for the insert object in JSON.
  final String key;

  /// Content of the insertion, might be a Map<String, dynamic> with unparsed
  /// object JSON.
  final dynamic value;

  @override
  int get length => 1;

  InsertObjectOp._(this.key, this.value, [Map<String, dynamic> attributes])
      : assert(key != null),
        super._(attributes);

  @override
  T match<T>(
          {T Function(InsertStringOp) insert,
          T Function(InsertObjectOp) insertObject,
          T Function(DeleteOp) delete,
          T Function(RetainOp) retain}) =>
      insertObject?.call(this);

  @override
  Map<String, dynamic> toJson() => {
        Op.insertKey: {key: jsonEncode(value)},
        if (_attributes != null) Op.attributesKey: attributes
      };

  @override
  String toString() =>
      'insert($key: ${value.toString()})${hasAttributes ? ' + $attributes' : ''}';

  @override
  bool operator ==(other) {
    if (identical(this, other)) return true;
    if (other is InsertObjectOp) {
      return key == other.key &&
          value == other.value &&
          hasSameAttributes(other);
    }
    return false;
  }

  @override
  int get hashCode => hasAttributes
      ? hash3(_mapHashCode(_attributes), key.hashCode, value.hashCode)
      : hash2(key.hashCode, value.hashCode);
}

class DeleteOp extends Op {
  final int count;

  @override
  int get length => count;

  @override
  OpType get type => OpType.delete;

  DeleteOp(this.count)
      : assert(count != null),
        super._(null);

  @override
  T match<T>(
          {T Function(InsertStringOp) insert,
          T Function(InsertObjectOp) insertObject,
          T Function(DeleteOp) delete,
          T Function(RetainOp) retain}) =>
      delete?.call(this);

  @override
  Map<String, dynamic> toJson() => {Op.deleteKey: count};

  @override
  String toString() => 'delete($count)';

  @override
  bool operator ==(other) {
    if (identical(this, other)) return true;
    if (other is DeleteOp) {
      return count == other.count;
    }
    return false;
  }

  @override
  int get hashCode => count;
}

class RetainOp extends Op {
  final int count;

  @override
  int get length => count;

  @override
  OpType get type => OpType.retain;

  RetainOp(this.count, [Map<String, dynamic> attributes])
      : assert(count != null),
        super._(attributes);

  @override
  T match<T>(
          {T Function(InsertStringOp) insert,
          T Function(InsertObjectOp) insertObject,
          T Function(DeleteOp) delete,
          T Function(RetainOp) retain}) =>
      retain?.call(this);

  @override
  Map<String, dynamic> toJson() => {
        Op.retainKey: count,
        if (_attributes != null) Op.attributesKey: attributes
      };

  @override
  String toString() => 'retain($count)${hasAttributes ? ' + $attributes' : ''}';

  @override
  bool operator ==(other) {
    if (identical(this, other)) return true;
    if (other is RetainOp) {
      return count == other.count && hasSameAttributes(other);
    }
    return false;
  }

  @override
  int get hashCode => hasAttributes
      ? hash2(_mapHashCode(_attributes), count.hashCode)
      : count.hashCode;
}

int _mapHashCode(Map<String, dynamic> map) =>
    hashObjects(map.entries.map((e) => hash2(e.key, e.value)));

abstract class Delta {
  /// Transforms two attribute sets.
  static Map<String, dynamic> transformAttributes(
      Map<String, dynamic> a, Map<String, dynamic> b, bool priority) {
    if (a == null) return b;
    if (b == null) return null;

    if (!priority) return b;

    final result = b.keys.fold<Map<String, dynamic>>({}, (attributes, key) {
      if (!a.containsKey(key)) attributes[key] = b[key];
      return attributes;
    });

    return result.isEmpty ? null : result;
  }

  /// Composes two attribute sets.
  static Map<String, dynamic> composeAttributes(
      Map<String, dynamic> a, Map<String, dynamic> b,
      {bool keepNull = false}) {
    a ??= const {};
    b ??= const {};

    final result = Map<String, dynamic>.from(a)..addAll(b);
    final keys = result.keys.toList(growable: false);

    if (!keepNull) {
      for (final key in keys) {
        if (result[key] == null) result.remove(key);
      }
    }

    return result.isEmpty ? null : result;
  }

  ///get anti-attr result base on base
  static Map<String, dynamic> invertAttributes(
      Map<String, dynamic> attr, Map<String, dynamic> base) {
    attr ??= const {};
    base ??= const {};

    var baseInverted = base.keys.fold({}, (memo, key) {
      if (base[key] != attr[key] && attr.containsKey(key)) {
        memo[key] = base[key];
      }
      return memo;
    });

    var inverted =
        Map<String, dynamic>.from(attr.keys.fold(baseInverted, (memo, key) {
      if (base[key] != attr[key] && !base.containsKey(key)) {
        memo[key] = null;
      }
      return memo;
    }));
    return inverted;
  }

  Delta._();

  /// Creates new empty [Delta].
  factory Delta() => DeltaImpl._(<Op>[]);

  /// Creates new [Delta] from [other].
  factory Delta.from(Delta other) =>
      DeltaImpl._(List<Op>.from(other.operations));

  /// Creates [Delta] from JSON list of ops.
  factory Delta.fromJson(List data) => data == null
      ? Delta()
      : DeltaImpl._(data.map((op) => Op.fromJson(op)).toList());

  /// Creates a [Delta] by concatenating two deltas.
  factory Delta.concat(Delta first, Delta second) =>
      Delta.from(first)..concat(second);

  /// Composes this delta with [other] and returns new [Delta].
  ///
  /// It is not required for this and [other] delta to represent a document
  /// delta (consisting only of insert operations).
  Delta compose(Delta other) {
    final result = Delta();
    final thisIter = DeltaIterator(this);
    final otherIter = DeltaIterator(other);

    while (thisIter.hasNext || otherIter.hasNext) {
      final newOp = _composeOp(thisIter, otherIter);
      if (newOp != null) result.push(newOp);
    }
    return result..trim();
  }

  /// Composes next operation from [firstIter] and [secondIter].
  ///
  /// Returns new operation or `null` if operations from [firstIter] and
  /// [secondIter] nullify each other. For instance, for the pair `insert('abc')`
  /// and `delete(3)` composition result would be empty string.
  static Op _composeOp(DeltaIterator firstIter, DeltaIterator secondIter) {
    assert(firstIter.hasNext || secondIter.hasNext);

    if (secondIter.isNextInsert) return secondIter.next();
    if (firstIter.isNextDelete) return firstIter.next();

    final zipped = DeltaIterator.zipNext(firstIter, secondIter);

    final firstOp = zipped.op1;
    final secondOp = zipped.op2;

    if (secondOp is RetainOp) {
      final attributes = composeAttributes(
        firstOp.attributes,
        secondOp.attributes,
        keepNull: firstOp.isRetain,
      );
      if (firstOp is RetainOp) {
        return RetainOp(firstOp.length, attributes);
      } else if (firstOp is InsertStringOp) {
        return InsertOp.string(firstOp.text, attributes);
      } else if (firstOp is InsertObjectOp) {
        return InsertOp.object(firstOp.key, firstOp.value, attributes);
      } else {
        throw StateError('Unreachable');
      }
    } else {
      // otherOp == delete && thisOp in [retain, insert]
      assert(secondOp.isDelete);
      if (firstOp.isRetain) return secondOp;
      assert(firstOp.isInsert);
      // otherOp(delete) + thisOp(insert) => null
    }
    return null;
  }

  /// Transforms [other] delta against operations in this delta.
  Delta transform(Delta other, bool priority) {
    final result = Delta();
    final thisIter = DeltaIterator(this);
    final otherIter = DeltaIterator(other);

    while (thisIter.hasNext || otherIter.hasNext) {
      final newOp = _transformOp(thisIter, otherIter, priority);
      if (newOp != null) result.push(newOp);
    }
    return result..trim();
  }

  /// Transforms next operation from [secondIter] against next operation in
  /// [firstIter].
  ///
  /// Returns `null` if both operations nullify each other.
  static Op _transformOp(
      DeltaIterator firstIter, DeltaIterator secondIter, bool priority) {
    if (firstIter.isNextInsert && (priority || !secondIter.isNextInsert)) {
      return RetainOp(firstIter.next().length);
    } else if (secondIter.isNextInsert) {
      return secondIter.next();
    }

    final zipped = DeltaIterator.zipNext(firstIter, secondIter);
    final firstOp = zipped.op1;
    final secondOp = zipped.op2;
    final length = zipped.length;

    // At this point only delete and retain operations are possible.
    if (firstOp.isDelete) {
      // otherOp is either delete or retain, so they nullify each other.
      return null;
    } else if (secondOp.isDelete) {
      return secondOp;
    } else {
      // Retain otherOp which is either retain or insert.
      return RetainOp(
        length,
        transformAttributes(firstOp.attributes, secondOp.attributes, priority),
      );
    }
  }

  /// Inverts this delta against [base].
  ///
  /// Returns new delta which negates effect of this delta when applied to
  /// [base]. This is an equivalent of "undo" operation on deltas.
  Delta invert(Delta base) {
    final inverted = Delta();
    if (base.isEmpty) return inverted;

    var baseIndex = 0;
    for (final op in operations) {
      if (op is InsertOp) {
        inverted.delete(op.length);
      } else if (op is DeleteOp) {
        final length = op.length;
        final sliceDelta = base.slice(baseIndex, baseIndex + length);
        inverted.concat(sliceDelta);
        baseIndex += length;
      } else if (op is RetainOp) {
        if (!op.hasAttributes) {
          inverted.retain(op.count, null);
          baseIndex += op.count;
        } else {
          final length = op.length;
          final sliceDelta = base.slice(baseIndex, baseIndex + length);
          sliceDelta.operations.forEach((baseOp) {
            var invertAttr = invertAttributes(op.attributes, baseOp.attributes);
            inverted.retain(
                baseOp.length, invertAttr.isEmpty ? null : invertAttr);
          });
          baseIndex += length;
        }
      } else {
        throw StateError('Unreachable');
      }
    }
    inverted.trim();
    return inverted;
  }

  /// Changes every time this delta is modified.
  ///
  /// Used by [DeltaIterator] to check if delta changed
  /// (making the iterator invalid).
  int get state;

  /// Returns list of operations in this delta.
  List<Op> get operations;

  /// Returns JSON-serializable version of this delta.
  List toJson() => operations;

  /// Returns `true` if this delta is empty.
  bool get isEmpty => operations.isEmpty;

  /// Returns `true` if this delta is not empty.
  bool get isNotEmpty => operations.isNotEmpty;

  /// Returns number of operations in this delta.
  int get length => operations.length;

  /// Returns [Op] at specified [index] in this delta.
  Op operator [](int index) => operations[index];

  /// Returns the first [Op] in this delta.
  Op get first => operations.first;

  /// Returns the last [Op] in this delta.
  Op get last => operations.isEmpty
      ? throw StateError('No element')
      : operations[operations.length - 1];

  /// Retain [count] of characters from current position.
  void retain(int count, [Map<String, dynamic> attributes]);

  /// Insert [text] at current position.
  void insert(String text, [Map<String, dynamic> attributes]);

  /// Insert [object] at current position.
  void insertObject(String type, Object object,
      [Map<String, dynamic> attributes]);

  /// Delete [count] characters from current position.
  void delete(int count);

  /// Pushes new operation into this delta.
  ///
  /// Performs compaction by composing [operation] with current tail operation
  /// of this delta, when possible. For instance, if current tail is
  /// `insert('abc')` and pushed operation is `insert('123')` then existing
  /// tail is replaced with `insert('abc123')` - a compound result of the two
  /// operations.
  void push(Op operation, {bool compact = true});

  /// Removes trailing retain operation with empty attributes, if present.
  void trim();

  /// Concatenates [other] to this delta.
  void concat(Delta other);

  /// Returns slice of this delta from [start] index (inclusive) to [end]
  /// (exclusive).
  Delta slice(int start, [int end]) {
    final delta = Delta();
    var opIterator = DeltaIterator(this);

    var op = opIterator.skip(start);

    var index = start;

    while ((end == null || index < end) && opIterator.hasNext) {
      op = opIterator.next(end == null ? null : end - index);
      delta.push(op);
      index += op.length;
    }
    return delta;
  }

  /// Transforms [index] against this delta.
  ///
  /// Any "delete" operation before specified [index] shifts it backward, as
  /// well as any "insert" operation shifts it forward.
  ///
  /// The [force] argument is used to resolve scenarios when there is an
  /// insert operation at the same position as [index]. If [force] is set to
  /// `true` (default) then position is forced to shift forward, otherwise
  /// position stays at the same index. In other words setting [force] to
  /// `false` gives higher priority to the transformed position.
  ///
  /// Useful to adjust caret or selection positions.
  int transformPosition(int index, {bool force = true}) {
    final iter = DeltaIterator(this);
    var offset = 0;
    while (iter.hasNext && offset <= index) {
      final op = iter.next();
      if (op.isDelete) {
        index -= math.min(op.length, index - offset);
        continue;
      } else if (op.isInsert && (offset < index || force)) {
        index += op.length;
      }
      offset += op.length;
    }
    return index;
  }
}

/// Delta represents a document or a modification of a document as a sequence of
/// insert, delete and retain operations.
///
/// Delta consisting of only "insert" operations is usually referred to as
/// "document delta". When delta includes also "retain" or "delete" operations
/// it is a "change delta".
class DeltaImpl extends Delta {
  final List<Op> _operations;

  int _modificationCount = 0;

  DeltaImpl._(List<Op> operations)
      : assert(operations != null),
        _operations = operations,
        _operationsView = UnmodifiableListView(operations),
        super._();

  final UnmodifiableListView<Op> _operationsView;

  @override
  int get state => _modificationCount;

  @override
  List<Op> get operations => _operationsView;

  @override
  bool operator ==(dynamic other) {
    if (identical(this, other)) return true;
    if (other is! DeltaImpl) return false;
    DeltaImpl typedOther = other;
    final comparator = ListEquality<Op>(const DefaultEquality<Op>());
    return comparator.equals(_operations, typedOther._operations);
  }

  @override
  int get hashCode => hashObjects(_operations);

  @override
  void retain(int count, [Map<String, dynamic> attributes]) {
    assert(count >= 0);
    if (count == 0) return; // no-op
    push(RetainOp(count, attributes));
  }

  @override
  void insert(String text, [Map<String, dynamic> attributes]) {
    assert(text != null);
    if (text.isEmpty) return; // no-op
    push(InsertOp.string(text, attributes));
  }

  @override
  void insertObject(String type, Object object,
      [Map<String, dynamic> attributes]) {
    assert(type != null);
    if (type.isEmpty) return; // no-op
    push(InsertOp.object(type, object, attributes));
  }

  /// Delete [count] characters from current position.
  @override
  void delete(int count) {
    assert(count >= 0);
    if (count == 0) return;
    push(DeleteOp(count));
  }

  @override
  void push(Op operation, {bool compact = true}) {
    Op merged;

    if (compact && _operations.isNotEmpty) {
      merged = Op.merge(_operations.last, operation);
    }

    if (merged != null) {
      _operations.last = merged;
    } else {
      if (_operations.isNotEmpty &&
          _operations.last.isDelete &&
          operation.isInsert) {
        // Insertion and deletion at the same index is commutative,
        // so we normalize by always putting insert first.
        _operations.insert(_operations.length - 1, operation);
      } else {
        _operations.add(operation);
      }
      //_operations.add(operation);
      _modificationCount++;
    }
  }

  @override
  void trim() {
    if (isNotEmpty) {
      final last = _operations.last;
      if (last.isRetain && !last.hasAttributes) {
        _operations.removeLast();
        _modificationCount++;
      }
    }
  }

  @override
  void concat(Delta other) {
    if (other.isNotEmpty) {
      // In case first operation of other can be merged with last operation in
      // our list.
      push(other.first);

      for (var op in other.operations.skip(1)) {
        push(op, compact: false);
      }
    }
  }

  @override
  String toString() => _operations.join('\n');
}

class ZippedOp {
  final Op op1;
  final Op op2;
  int get length => op1.length;

  ZippedOp(this.op1, this.op2)
      : assert(op1 != null),
        assert(op2 != null),
        assert(op1.length == op2.length);
}

/// Specialized iterator for [Delta]s.
class DeltaIterator {
  final Delta delta;
  final int _deltaState;
  int _index = 0;

  /// Local offset inside the current operation.
  int _offset = 0;

  DeltaIterator(this.delta) : _deltaState = delta.state;

  bool get isNextInsert => nextOpType == OpType.insert;

  bool get isNextDelete => nextOpType == OpType.delete;

  bool get isNextRetain => nextOpType == OpType.retain;

  bool get hasNext => _index < delta.length;

  OpType get nextOpType {
    if (_index < delta.length) {
      return delta[_index].type;
    } else {
      return null;
    }
  }

  /// Returns length of next operation without consuming it.
  ///
  /// Returns `-1` if there are no more operations left to iterate.
  int peekLength() {
    if (_index < delta.length) {
      final operation = delta.operations[_index];
      return operation.length - _offset;
    }
    return -1;
  }

  /// Consumes and returns next operation or null if we're at the end of the delta.
  ///
  /// Optional [length] specifies maximum length of operation to return. Note
  /// that actual length of returned operation may be less than specified value.
  Op next([int length]) {
    if (length != null && length <= 0) {
      throw ArgumentError.value(
          length, 'length', 'length should be larger than 0.');
    }

    if (_deltaState != delta.state) {
      throw ConcurrentModificationError(delta);
    }

    if (!hasNext) {
      return null;
    }

    var op = delta[_index];
    final readFullOp = length == null || op.length <= _offset + length;
    if (_offset != 0 || !readFullOp) {
      // here we need to cut off part of the operation.
      final opEnd = op.length;
      final start = _offset;
      final end = readFullOp ? opEnd : _offset + length;
      final progress = end - start;

      op = op.match(
          insert: (op) =>
              InsertOp.string(op.text.substring(start, end), op.attributes),
          // Object insertion always has length 1, so we can never get here.
          insertObject: (op) =>
              throw StateError('Object insertion should not be reached here.'),
          delete: (op) => DeleteOp(progress),
          retain: (op) => RetainOp(progress, op.attributes));

      _offset = end;
    }

    if (readFullOp) {
      _offset = 0;
      _index++;
    }

    return op;
  }

  /// Skips [length] characters in source delta.
  ///
  /// Returns last skipped operation, or `null` if there was nothing to skip.
  Op skip(int length) {
    var skipped = 0;
    Op op;
    while (skipped < length && hasNext) {
      final opLength = peekLength();
      final skip = math.min(length - skipped, opLength);
      op = next(skip);
      skipped += op.length;
    }
    return op;
  }

  /// Zip together the next ops of both iterators. Returned ops will have
  /// matching lengths.
  ///
  /// If either iterator has no ops left, the returned op will be a
  /// [RetainOp] with length matching the other op.
  ///
  /// If both iterators have no ops left, an [ArgumentError] will be
  /// thrown.
  static ZippedOp zipNext(DeltaIterator iter1, DeltaIterator iter2) {
    if (!iter1.hasNext && !iter2.hasNext) {
      throw ArgumentError(
          'At least one of iter1 and iter1 must have ops left.');
    }

    Op op1;
    Op op2;
    int length;

    if (!iter1.hasNext) {
      length = iter2.peekLength();
      op1 = RetainOp(length);
      op2 = iter2.next(length);
    } else if (!iter2.hasNext) {
      length = iter1.peekLength();
      op1 = iter1.next(length);
      op2 = RetainOp(length);
    } else {
      length = math.min(iter1.peekLength(), iter2.peekLength());
      op1 = iter1.next(length);
      op2 = iter2.next(length);
    }

    return ZippedOp(op1, op2);
  }
}

/// Wrapper around a class that implements [Delta] that only exposes `Delta`
/// members.
///
/// A simple wrapper that delegates all `Delta` members to the delta provided in
/// the constructor.
///
/// Base for delegating map implementations like [UnmodifiableDeltaView].
class DeltaView implements Delta {
  final Delta _delta;

  const DeltaView(Delta delta) : _delta = delta;

  @override
  Op operator [](int index) => _delta[index];

  @override
  Delta compose(Delta other) => _delta.compose(other);

  @override
  void concat(Delta other) => _delta.concat(other);

  @override
  void delete(int count) => _delta.delete(count);

  @override
  Op get first => _delta.first;

  @override
  void insert(String text, [Map<String, dynamic> attributes]) =>
      _delta.insert(text, attributes);

  @override
  void insertObject(String type, Object object,
          [Map<String, dynamic> attributes]) =>
      _delta.insertObject(type, object, attributes);

  @override
  Delta invert(Delta other) => _delta.invert(other);

  @override
  bool get isEmpty => _delta.isEmpty;

  @override
  bool get isNotEmpty => _delta.isNotEmpty;

  @override
  Op get last => _delta.last;

  @override
  int get length => _delta.length;

  @override
  List<Op> get operations => _delta.operations;

  @override
  void push(Op operation, {bool compact = true}) =>
      _delta.push(operation, compact: compact);

  @override
  void retain(int count, [Map<String, dynamic> attributes]) =>
      _delta.retain(count, attributes);

  @override
  Delta slice(int start, [int end]) => _delta.slice(start, end);

  @override
  int get state => _delta.state;

  @override
  List toJson() => _delta.toJson();

  @override
  Delta transform(Delta other, bool priority) =>
      _delta.transform(other, priority);

  @override
  int transformPosition(int index, {bool force = true}) =>
      _delta.transformPosition(index, force: force);

  @override
  void trim() => _delta.trim();
}

abstract class _UnmodifiableDeltaMixin implements Delta {
  Error error() => UnsupportedError('Cannot modify unmodifiable delta.');

  @override
  void concat(Delta other) => throw error();

  @override
  void delete(int count) => throw error();

  @override
  void insert(String text, [Map<String, dynamic> attributes]) => throw error();

  @override
  void insertObject(String type, Object object,
          [Map<String, dynamic> attributes]) =>
      throw error();

  @override
  void push(Op operation, {bool compact = true}) => throw error();

  @override
  void retain(int count, [Map<String, dynamic> attributes]) => throw error();

  @override
  void trim() => throw error();
}

class UnmodifiableDeltaView extends DeltaView with _UnmodifiableDeltaMixin {
  UnmodifiableDeltaView(Delta delta) : super(delta);
}
