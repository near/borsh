import BorshSpec

/-!
# Sizes, element counts and the schema factor

Small facts used by the cost bound in `Theorems/Resources.lean`:

* `Value.size` is positive, and the three mutual sums are sums over lists;
* the order check costs at most twice the total size of the keys;
* every schema has a positive factor.
-/

namespace BorshSpec

namespace Value

/-- Every value has size at least one. -/
theorem size_pos (v : Value) : 1 ≤ v.size := by
  cases v <;> simp [size] <;> omega

/-- `sizeList` is the sum of the sizes. -/
theorem sizeList_eq_sum : ∀ xs : List Value, sizeList xs = (xs.map size).sum
  | [] => rfl
  | x :: xs => by simp [sizeList, sizeList_eq_sum xs]

/-- `elemsList` is the sum of the element counts. -/
theorem elemsList_eq_sum : ∀ xs : List Value, elemsList xs = (xs.map elems).sum
  | [] => rfl
  | x :: xs => by simp [elemsList, elemsList_eq_sum xs]

/-- `sizePairs` is the sum of the sizes of keys and values. -/
theorem sizePairs_eq_sum : ∀ kvs : List (Value × Value),
    sizePairs kvs = (kvs.map fun p => size p.1 + size p.2).sum
  | [] => rfl
  | (k, v) :: kvs => by simp [sizePairs, sizePairs_eq_sum kvs]

/-- `elemsPairs` is the sum of the element counts of keys and values. -/
theorem elemsPairs_eq_sum : ∀ kvs : List (Value × Value),
    elemsPairs kvs = (kvs.map fun p => elems p.1 + elems p.2).sum
  | [] => rfl
  | (k, v) :: kvs => by simp [elemsPairs, elemsPairs_eq_sum kvs]

/-- The sum of `size` over the keys of a list of entries. -/
theorem sizeList_keys : ∀ kvs : List (Value × Value),
    sizeList (kvs.map Prod.fst) = (kvs.map fun p => size p.1).sum
  | [] => rfl
  | (k, v) :: kvs => by simp [sizeList, sizeList_keys kvs]

/-- The order check costs at most twice the total size of what it checks. -/
theorem strictAscC_snd_le : ∀ xs : List Value, (strictAscC xs).2 ≤ 2 * sizeList xs
  | [] => by simp [strictAscC]
  | [x] => by simp [strictAscC]
  | a :: b :: rest => by
    have ih := strictAscC_snd_le (b :: rest)
    have ha := size_pos a
    have hm : min a.size b.size ≤ a.size := Nat.min_le_left _ _
    simp only [strictAscC, sizeList]
    split
    · simp only [sizeList] at ih
      omega
    · omega

end Value

namespace Schema

/-- Every schema has a positive factor. -/
theorem factor_pos_aux : ∀ s : Schema, 0 < s.factor
  | .uint _ => by simp [factor]
  | .sint _ => by simp [factor]
  | .f32 => by simp [factor]
  | .f64 => by simp [factor]
  | .bool => by simp [factor]
  | .string => by simp [factor]
  | .option s => by simp only [factor]; omega
  | .vec s => by have := factor_pos_aux s; simp [factor]; omega
  | .array n s => by simp only [factor]; split <;> omega
  | .tuple fs => by simp only [factor]; omega
  | .enum vs => by simp only [factor]; omega
  | .map k v => by have := factor_pos_aux k; simp [factor]; omega
  | .set s => by have := factor_pos_aux s; simp [factor]; omega

end Schema

end BorshSpec
