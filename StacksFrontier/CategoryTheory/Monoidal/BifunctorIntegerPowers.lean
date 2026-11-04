module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Int.Basic

/-!
# Integer tensor powers for a tensor bifunctor with chosen duals

Let `T : C ⥤ C ⥤ C` be a bifunctor, thought of as a tensor product, and let `𝟙` be an object of
`C`, thought of as its unit. A finite list `[A₁, …, A_r]` of objects has the tensor product
`A₁ ⊗ (A₂ ⊗ (⋯ ⊗ A_r))`, which is `𝟙` for the empty list. An object `E` together with a chosen
object `E^∨` has *integer tensor powers*: `E^{⊗ n}` is the tensor product of `n` copies of `E` for
`n ≥ 0` and of `-n` copies of `E^∨` for `n < 0`. For families `E_1, …, E_r` and `E_1^∨, …, E_r^∨`
and `n ∈ ℤ^r` this gives the object `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`.

## Main definitions

* `CategoryTheory.Functor.tensorList`: the tensor product of a list of objects.
* `CategoryTheory.Functor.intTensorPow`: the integer tensor power `E^{⊗ n}` of an object with a
  chosen dual.
* `CategoryTheory.Functor.multiTensorPow`: the object `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`.

## Main results

* `CategoryTheory.Functor.intTensorPow_natCast`,
  `CategoryTheory.Functor.intTensorPow_neg_natCast`: the non-negative and the negative powers.
* `CategoryTheory.Functor.tensorList_mem`, `CategoryTheory.Functor.intTensorPow_mem`,
  `CategoryTheory.Functor.multiTensorPow_mem`: a property of objects containing the unit, the
  given objects and their duals and stable under the tensor product holds for all of these
  objects.

## Implementation notes

No monoidal structure on `C` is assumed: the derived categories of sheaves of modules on the large
sites of algebraic geometry carry a derived tensor bifunctor but no monoidal structure in this
library. The products are bracketed to the right.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) (one : C)

/-- The tensor product `A₁ ⊗ (A₂ ⊗ (⋯ ⊗ A_r))` of a list of objects for the bifunctor `T`; the
empty list has tensor product `one`. -/
def tensorList : List C → C
  | [] => one
  | [A] => A
  | A :: A' :: l => (T.obj A).obj (tensorList (A' :: l))

/-- The tensor product of the empty list is `one`. -/
@[simp]
theorem tensorList_nil : T.tensorList one [] = one :=
  rfl

/-- The tensor product of a one-element list `[A]` is `A`. -/
@[simp]
theorem tensorList_singleton (A : C) : T.tensorList one [A] = A :=
  rfl

/-- The tensor product of `A :: A' :: l` is `A` tensored with the tensor product of `A' :: l`. -/
@[simp]
theorem tensorList_cons_cons (A A' : C) (l : List C) :
    T.tensorList one (A :: A' :: l) = (T.obj A).obj (T.tensorList one (A' :: l)) :=
  rfl

/-- A property of objects which holds for `one` and is stable under `T` holds for the tensor
product of a list of objects having it. -/
theorem tensorList_mem (P : C → Prop) (hone : P one)
    (hT : ∀ A A', P A → P A' → P ((T.obj A).obj A')) :
    ∀ l : List C, (∀ A ∈ l, P A) → P (T.tensorList one l)
  | [], _ => hone
  | [A], hl => hl A (List.mem_singleton_self A)
  | A :: A' :: l, hl =>
      hT _ _ (hl A List.mem_cons_self)
        (tensorList_mem P hone hT (A' :: l) fun B hB ↦ hl B (List.mem_cons_of_mem A hB))

/-- The integer tensor power `E^{⊗ n}` of `E` with respect to the chosen dual `E'`: the tensor
product of `n` copies of `E` for `n ≥ 0`, and of `-n` copies of `E'` for `n < 0`. -/
def intTensorPow (E E' : C) : ℤ → C
  | .ofNat n => T.tensorList one (List.replicate n E)
  | .negSucc n => T.tensorList one (List.replicate (n + 1) E')

/-- For `n : ℕ`, the power `E^{⊗ n}` is the tensor product of `n` copies of `E`. -/
@[simp]
theorem intTensorPow_natCast (E E' : C) (n : ℕ) :
    T.intTensorPow one E E' n = T.tensorList one (List.replicate n E) :=
  rfl

/-- For `0 < n`, the power `E^{⊗ -n}` is the tensor product of `n` copies of `E'`. -/
theorem intTensorPow_neg_natCast (E E' : C) {n : ℕ} (hn : 0 < n) :
    T.intTensorPow one E E' (-n) = T.tensorList one (List.replicate n E') := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rfl

/-- The power `E^{⊗ 0}` is `one`. -/
@[simp]
theorem intTensorPow_zero (E E' : C) : T.intTensorPow one E E' 0 = one :=
  rfl

/-- The power `E^{⊗ 1}` is `E`. -/
@[simp]
theorem intTensorPow_one (E E' : C) : T.intTensorPow one E E' 1 = E :=
  rfl

/-- The power `E^{⊗ -1}` is the chosen dual `E'`. -/
@[simp]
theorem intTensorPow_neg_one (E E' : C) : T.intTensorPow one E E' (-1) = E' :=
  rfl

/-- A property of objects which holds for `one`, `E` and `E'` and is stable under `T` holds for
every integer tensor power of `E`. -/
theorem intTensorPow_mem (P : C → Prop) (hone : P one)
    (hT : ∀ A A', P A → P A' → P ((T.obj A).obj A')) {E E' : C} (hE : P E) (hE' : P E') :
    ∀ n : ℤ, P (T.intTensorPow one E E' n)
  | .ofNat _ => T.tensorList_mem one P hone hT _ fun _ hA ↦ (List.eq_of_mem_replicate hA) ▸ hE
  | .negSucc _ => T.tensorList_mem one P hone hT _ fun _ hA ↦ (List.eq_of_mem_replicate hA) ▸ hE'

/-- The object `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` attached to families `E` and `E'` of objects and
chosen duals and to `n ∈ ℤ^r`. -/
def multiTensorPow {r : ℕ} (E E' : Fin r → C) (n : Fin r → ℤ) : C :=
  T.tensorList one (List.ofFn fun j ↦ T.intTensorPow one (E j) (E' j) (n j))

/-- For a single object the multi-index tensor power is the integer tensor power. -/
@[simp]
theorem multiTensorPow_one (E E' : Fin 1 → C) (n : Fin 1 → ℤ) :
    T.multiTensorPow one E E' n = T.intTensorPow one (E 0) (E' 0) (n 0) :=
  rfl

/-- A property of objects which holds for `one`, every `E j` and every `E' j` and is stable under
`T` holds for every object `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`. -/
theorem multiTensorPow_mem (P : C → Prop) (hone : P one)
    (hT : ∀ A A', P A → P A' → P ((T.obj A).obj A')) {r : ℕ} {E E' : Fin r → C}
    (hE : ∀ j, P (E j)) (hE' : ∀ j, P (E' j)) (n : Fin r → ℤ) :
    P (T.multiTensorPow one E E' n) :=
  T.tensorList_mem one P hone hT _ fun A hA ↦ by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hA
    exact T.intTensorPow_mem one P hone hT (hE j) (hE' j) (n j)

end CategoryTheory.Functor

end
