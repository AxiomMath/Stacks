module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# The Čech nerve of an algebra, as iterated tensor products

For an `A'`-algebra `C'` this file sets up the Čech nerve of `A' → C'` in the shape used by the
décalage argument: `cech 0 = C'` and `cech (n + 1) = cech n ⊗[A'] C'`. The new factor on the
right is the vertex `0`, the factors of `cech n` are the vertices `1, …, n + 1`, and the
leftmost factor is the last vertex.

## Main definitions

* `face n i : cech n → cech (n + 1)` is the face skipping the vertex `i`: the face `0` is
  `x ↦ x ⊗ 1`, the faces of positive index act on the left factor.
* `codeg n : cech (n + 1) → cech n` merges the vertices `0` and `1`.
* `v₀ n`, `vₗ n : C' → cech n` are the vertex `0` and the last vertex.
* `κ n : cech 1 → cech (n + 1)` is the inclusion of the last two vertices.

## Main results

* The cosimplicial identities used by the décalage: `face_succ_comp_face_zero`,
  `codeg_comp_face_one`, `codeg_comp_face_succ_succ`, with `face_succ_comp_v₀`.
* `card_cech_lt`: the nerve stays below an uncountable cardinal.
-/

@[expose] public section

open scoped TensorProduct

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

/-- The cardinality of `M ⊗[R] N` is at most `max ℵ₀ #(M × N)`. -/
theorem card_tensorProduct_le (R M N : Type u) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] :
    Cardinal.mk (M ⊗[R] N) ≤ max Cardinal.aleph0 (Cardinal.mk (M × N)) :=
  (Cardinal.mk_le_of_surjective
    (AddCon.mk'_surjective (c := addConGen (TensorProduct.Eqv R M N)))).trans
    (Cardinal.mk_list_le_max _)

variable (A' : Type u) [CommRing A'] (C' : Type u) [CommRing C'] [Algebra A' C']

/-- The Čech nerve of `A' → C'`: `cech 0 = C'`, `cech (n + 1) = cech n ⊗[A'] C'`. -/
abbrev cech : ℕ → CommAlgCat.{u} A'
  | 0 => CommAlgCat.of A' C'
  | n + 1 => CommAlgCat.of A' (cech n ⊗[A'] C')

/-- If `#C' < κ` for an uncountable cardinal `κ`, then every term of the Čech nerve has cardinality
less than `κ`. -/
theorem card_cech_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hC : Cardinal.mk C' < κ) :
    ∀ n, Cardinal.mk (cech A' C' n) < κ
  | 0 => hC
  | n + 1 => by
    refine (card_tensorProduct_le A' (cech A' C' n) C').trans_lt (max_lt hκ ?_)
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hκ.le (card_cech_lt hκ hC n) hC

/-- The vertex `0`, the rightmost factor. -/
def v₀ : ∀ n : ℕ, C' →ₐ[A'] cech A' C' n
  | 0 => AlgHom.id A' C'
  | _ + 1 => Algebra.TensorProduct.includeRight

/-- The last vertex, the leftmost factor. -/
def vₗ : ∀ n : ℕ, C' →ₐ[A'] cech A' C' n
  | 0 => AlgHom.id A' C'
  | n + 1 => (Algebra.TensorProduct.includeLeft (S := A')).comp (vₗ n)

/-- The face maps: `face n i` skips the vertex `i`. -/
def face : ∀ n : ℕ, Fin (n + 2) → (cech A' C' n →ₐ[A'] cech A' C' (n + 1))
  | 0 => Fin.cases (Algebra.TensorProduct.includeLeft (S := A'))
      (fun _ ↦ Algebra.TensorProduct.includeRight)
  | n + 1 => Fin.cases (Algebra.TensorProduct.includeLeft (S := A'))
      (fun i ↦ Algebra.TensorProduct.map (face n i) (AlgHom.id A' C'))

/-- The zeroth codegeneracy, merging the vertices `0` and `1`. -/
def codeg (n : ℕ) : cech A' C' (n + 1) →ₐ[A'] cech A' C' n :=
  Algebra.TensorProduct.lift (AlgHom.id A' _) (v₀ A' C' n) fun _ _ ↦ Commute.all _ _

/-- The last two vertices, `cech 1 → cech (n + 1)`. -/
def κ : ∀ n : ℕ, cech A' C' 1 →ₐ[A'] cech A' C' (n + 1)
  | 0 => AlgHom.id A' _
  | n + 1 => (Algebra.TensorProduct.includeLeft (S := A')).comp (κ n)

variable {A' C'}

/-- The face `0` sends `x` to `x ⊗ 1`. -/
theorem face_zero_apply (n : ℕ) (x : cech A' C' n) :
    face A' C' n 0 x = (x ⊗ₜ[A'] (1 : C') : cech A' C' n ⊗[A'] C') := by
  cases n <;> rfl

/-- The face `i + 1` acts on the left factor of `x ⊗ c`. -/
theorem face_succ_tmul (n : ℕ) (i : Fin (n + 2)) (x : cech A' C' n) (c : C') :
    face A' C' (n + 1) i.succ (x ⊗ₜ[A'] c) = face A' C' n i x ⊗ₜ[A'] c := rfl

/-- The face `1` of `C'` sends `c` to `1 ⊗ c`. -/
theorem face_zero_one_apply (c : C') : face A' C' 0 1 c = ((1 : C') ⊗ₜ[A'] c : C' ⊗[A'] C') := rfl

/-- The vertex `0` of `cech (n + 1)` sends `c` to `1 ⊗ c`. -/
theorem v₀_succ_apply (n : ℕ) (c : C') :
    v₀ A' C' (n + 1) c = ((1 : cech A' C' n) ⊗ₜ[A'] c : cech A' C' n ⊗[A'] C') := rfl

/-- The codegeneracy sends `x ⊗ c` to `x * v₀ n c`. -/
theorem codeg_tmul (n : ℕ) (x : cech A' C' n) (c : C') :
    codeg A' C' n (x ⊗ₜ[A'] c) = x * v₀ A' C' n c := by
  simp [codeg]

/-- The faces of positive index fix the vertex `0`. -/
theorem face_succ_comp_v₀ (n : ℕ) (i : Fin (n + 1)) :
    (face A' C' n i.succ).comp (v₀ A' C' n) = v₀ A' C' (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    ext c
    change face A' C' (n + 1) i.succ ((1 : cech A' C' n) ⊗ₜ[A'] c) = (1 : cech A' C' (n + 1)) ⊗ₜ c
    rw [face_succ_tmul, map_one]

/-- The cosimplicial identity `d_{i+1} d₀ = d₀ d_i`. -/
theorem face_succ_comp_face_zero (n : ℕ) (i : Fin (n + 2)) :
    (face A' C' (n + 1) i.succ).comp (face A' C' n 0) =
      (face A' C' (n + 1) 0).comp (face A' C' n i) := by
  ext x
  change face A' C' (n + 1) i.succ (face A' C' n 0 x) = face A' C' (n + 1) 0 (face A' C' n i x)
  rw [face_zero_apply, face_zero_apply, face_succ_tmul]

/-- The cosimplicial identity `σ₀ d₁ = id`. -/
theorem codeg_comp_face_one (n : ℕ) :
    (codeg A' C' n).comp (face A' C' n 1) = AlgHom.id A' _ := by
  cases n with
  | zero =>
    ext c
    change codeg A' C' 0 ((1 : C') ⊗ₜ[A'] c) = c
    rw [codeg_tmul, one_mul]
    rfl
  | succ n =>
    refine Algebra.TensorProduct.ext' fun x c ↦ ?_
    change codeg A' C' (n + 1) (face A' C' (n + 1) (Fin.succ 0) (x ⊗ₜ[A'] c)) = x ⊗ₜ[A'] c
    rw [face_succ_tmul, codeg_tmul, face_zero_apply, v₀_succ_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The cosimplicial identity `σ₀ d_{i+2} = d_{i+1} σ₀`. -/
theorem codeg_comp_face_succ_succ (n : ℕ) (i : Fin (n + 1)) :
    (codeg A' C' (n + 1)).comp (face A' C' (n + 1) i.succ.succ) =
      (face A' C' n i.succ).comp (codeg A' C' n) := by
  refine Algebra.TensorProduct.ext' fun y c ↦ ?_
  change codeg A' C' (n + 1) (face A' C' (n + 1) i.succ.succ (y ⊗ₜ[A'] c)) =
    face A' C' n i.succ (codeg A' C' n (y ⊗ₜ[A'] c))
  rw [face_succ_tmul, codeg_tmul, codeg_tmul, map_mul]
  congr 1
  exact (DFunLike.congr_fun (face_succ_comp_v₀ n i) c).symm

/-- A face of positive index acts on the left factor, so it carries `includeLeft ∘ φ` to
`includeLeft ∘ ψ` whenever the corresponding face carries `φ` to `ψ`. -/
private theorem face_succ_comp_includeLeft_comp {B : Type u} [CommRing B] [Algebra A' B] (n : ℕ)
    (i : Fin (n + 2)) (φ : B →ₐ[A'] cech A' C' n) (ψ : B →ₐ[A'] cech A' C' (n + 1))
    (h : (face A' C' n i).comp φ = ψ) :
    (face A' C' (n + 1) i.succ).comp ((Algebra.TensorProduct.includeLeft (S := A')).comp φ) =
      (Algebra.TensorProduct.includeLeft (S := A')).comp ψ := by
  subst h
  exact AlgHom.ext fun b ↦ face_succ_tmul n i (φ b) 1

/-- The faces of index at most `n` fix the last vertex. -/
theorem face_comp_vₗ (n : ℕ) (i : Fin (n + 2)) (hi : (i : ℕ) ≤ n) :
    (face A' C' n i).comp (vₗ A' C' n) = vₗ A' C' (n + 1) := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.ext (Nat.le_zero.mp hi)
    rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      ext c
      change face A' C' (n + 1) 0 (vₗ A' C' (n + 1) c) = _
      rw [face_zero_apply]
      rfl
    | succ i => exact face_succ_comp_includeLeft_comp n i _ _ (ih i (by simpa using hi))

/-- The last face sends the last vertex to the second-to-last one. -/
theorem face_last_comp_vₗ (n : ℕ) :
    (face A' C' n (Fin.last (n + 1))).comp (vₗ A' C' n) =
      (κ A' C' n).comp (v₀ A' C' 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact face_succ_comp_includeLeft_comp n (Fin.last (n + 1)) (vₗ A' C' n)
      ((κ A' C' n).comp (v₀ A' C' 1)) ih

/-- The last vertex is the first of the two last ones. -/
theorem κ_comp_vₗ (n : ℕ) : (κ A' C' n).comp (vₗ A' C' 1) = vₗ A' C' (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (Algebra.TensorProduct.includeLeft (S := A')).comp ih

/-- The faces of index at most `n` carry the last two vertices to the last two vertices. -/
theorem face_comp_κ (n : ℕ) (i : Fin (n + 3)) (hi : (i : ℕ) ≤ n) :
    (face A' C' (n + 1) i).comp (κ A' C' n) = κ A' C' (n + 1) := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.ext (Nat.le_zero.mp hi)
    exact Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      refine Algebra.TensorProduct.ext' fun a b ↦ ?_
      change face A' C' (n + 2) 0 (κ A' C' (n + 1) (a ⊗ₜ b)) = _
      rw [face_zero_apply]
      rfl
    | succ i => exact face_succ_comp_includeLeft_comp (n + 1) i _ _ (ih i (by simpa using hi))

/-- The codegeneracy carries the last two vertices to the last two vertices. -/
theorem codeg_comp_κ (n : ℕ) : (codeg A' C' (n + 1)).comp (κ A' C' (n + 1)) = κ A' C' n := by
  refine Algebra.TensorProduct.ext' fun a b ↦ ?_
  change codeg A' C' (n + 1) ((κ A' C' n (a ⊗ₜ b)) ⊗ₜ[A'] (1 : C')) = _
  rw [codeg_tmul, map_one, mul_one]

/-- The codegeneracy fixes the last vertex. -/
theorem codeg_comp_vₗ (n : ℕ) : (codeg A' C' n).comp (vₗ A' C' (n + 1)) = vₗ A' C' n := by
  ext c
  change codeg A' C' n ((vₗ A' C' n c) ⊗ₜ[A'] (1 : C')) = _
  rw [codeg_tmul, map_one, mul_one]

end AlgebraicGeometry.Stack.GroupoidLift

end
