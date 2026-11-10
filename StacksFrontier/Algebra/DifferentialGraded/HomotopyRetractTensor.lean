module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetract
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductInclusion

/-!
# Homotopy retractions are stable under tensoring with a differential graded algebra

Let `ε : A → B` be a homomorphism of differential graded algebras over a commutative ring `R` and
let `C` be a third differential graded algebra. Tensoring with `C` on either side gives
homomorphisms
$$\varepsilon \otimes \mathrm{id} : A \otimes_R C \to B \otimes_R C, \qquad
  \mathrm{id} \otimes \varepsilon : C \otimes_R A \to C \otimes_R B,$$
and a homotopy retraction `(η, H)` of `ε` induces one of each: the section is `η ⊗ id`
respectively `id ⊗ η`, and the homotopy is `H ⊗ id` respectively `(-1)^{\deg} \otimes H`.

The sign is needed on the right and not on the left. On the left the two terms `(-1)^p` and
`(-1)^{p-1}` produced by the differential of the tensor product cancel, because `H` lowers the
degree of the left factor by one; on the right the left factor is untouched by `H`, so the
cancellation has to be produced by the Koszul sign of that factor.

## Main definitions

* `DifferentialGradedAlgebra.tensorHomLeft` and `DifferentialGradedAlgebra.tensorHomRight`: the
  two homomorphisms obtained from `ε` by tensoring with `C`.
* `DifferentialGradedAlgebra.tensorLinearLeft` and
  `DifferentialGradedAlgebra.tensorLinearRight`: an `R`-linear map tensored with the identity of
  `C` on either side.
* `DifferentialGradedAlgebra.tensorLinearRightSigned`: an `R`-linear operator tensored on the
  right with the Koszul sign of the left factor.

## Main results

* `DifferentialGradedAlgebra.HomotopyRetract.tensorLeft` and
  `DifferentialGradedAlgebra.HomotopyRetract.tensorRight`: a homotopy retraction of `ε` induces
  one of `ε ⊗ id` and one of `id ⊗ ε`.

## Implementation notes

The underlying module of the graded tensor product of Tag 065W is the ordinary tensor product, so
an `R`-linear map tensored with the identity is `TensorProduct.map` read through
`GradedTensorProduct.of`. Its compatibility with the total grading is a span induction, that
grading being spanned by the homogeneous pure tensors, and every identity involving the
differential is checked on a pure tensor whose left factor is homogeneous, which is the form in
which the differential of Tag 065W is computed.

The homotopy identity is proved in the form `η ε x = x + (d H x + H d x)`, without a subtraction,
so that the additive induction steps are closed by `abel` after rewriting with the two inductive
hypotheses.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
-/

@[expose] public noncomputable section

universe u

open scoped TensorProduct

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

section Signs

/-- Raising the exponent of `(-1) ^ q` by one flips the sign. -/
theorem negOnePow_add_one (q : ℤ) : (q + 1).negOnePow = -q.negOnePow := by
  rw [Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]

/-- `(-1) ^ q` is its own inverse. -/
theorem negOnePow_mul_self_units (q : ℤ) : q.negOnePow * q.negOnePow = 1 := by
  rw [← Int.negOnePow_add, show q + q = 2 * q from by ring, Int.negOnePow_two_mul]

/-- `negOnePow_add_one` with both sides read as integers rather than as units of `ℤ`. -/
theorem negOnePow_add_one_val (q : ℤ) :
    (((q + 1).negOnePow : ℤ)) = -((q.negOnePow : ℤ)) := by
  rw [negOnePow_add_one, Units.val_neg]

/-- `negOnePow_mul_self_units` with both sides read as integers rather than as units of `ℤ`. -/
theorem negOnePow_mul_self_val (q : ℤ) :
    ((q.negOnePow : ℤ)) * ((q.negOnePow : ℤ)) = 1 := by
  rw [← Units.val_mul, negOnePow_mul_self_units, Units.val_one]

/-- Lowering the exponent of `(-1) ^ q` by one flips the sign, as an identity of integers. This is
the form in which the sign produced by the differential of a graded tensor product is cancelled. -/
theorem negOnePow_val_eq_neg_sub_one (q : ℤ) :
    ((q.negOnePow : ℤ)) = -(((q - 1).negOnePow : ℤ)) := by
  have h1 : (q - 1).negOnePow * (1 : ℤ).negOnePow = q.negOnePow := by
    rw [← Int.negOnePow_add, show q - 1 + 1 = q from by ring]
  rw [← h1, Int.negOnePow_one, mul_neg_one, Units.val_neg]

end Signs

section Homomorphisms

/-- The two homomorphisms `a ↦ ε(a) ⊗ 1` and `c ↦ 1 ⊗ c` into `B ⊗_R C` Koszul-anticommute. -/
theorem anticommutesAlong_tensorHomLeft (ε : A.Hom B) (C : DifferentialGradedAlgebra R) :
    AnticommutesAlong A C (tensorProduct B C) ((tensorInclLeft B C).comp ε)
      (tensorInclRight B C) :=
  fun i j a c =>
    anticommutesAlong_tensorIncl B C i j ⟨ε.toAlgebraHom a, ε.map_grading i a a.2⟩ c

/-- The two homomorphisms `c ↦ c ⊗ 1` and `a ↦ 1 ⊗ ε(a)` into `C ⊗_R B` Koszul-anticommute. -/
theorem anticommutesAlong_tensorHomRight (C : DifferentialGradedAlgebra R) (ε : A.Hom B) :
    AnticommutesAlong C A (tensorProduct C B) (tensorInclLeft C B)
      ((tensorInclRight C B).comp ε) :=
  fun i j c a =>
    anticommutesAlong_tensorIncl C B i j c ⟨ε.toAlgebraHom a, ε.map_grading j a a.2⟩

/-- The homomorphism `ε ⊗ id : A ⊗_R C → B ⊗_R C`. -/
def tensorHomLeft (ε : A.Hom B) (C : DifferentialGradedAlgebra R) :
    (tensorProduct A C).Hom (tensorProduct B C) :=
  tensorLift (anticommutesAlong_tensorHomLeft ε C)

/-- The homomorphism `id ⊗ ε : C ⊗_R A → C ⊗_R B`. -/
def tensorHomRight (C : DifferentialGradedAlgebra R) (ε : A.Hom B) :
    (tensorProduct C A).Hom (tensorProduct C B) :=
  tensorLift (anticommutesAlong_tensorHomRight C ε)

/-- `ε ⊗ id` sends the pure tensor `a ⊗ c` to `ε a ⊗ c`. -/
theorem tensorHomLeft_tmul (ε : A.Hom B) (C : DifferentialGradedAlgebra R)
    (a : A.A) (c : C.A) :
    (tensorHomLeft ε C).toAlgebraHom (a ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) =
      (ε.toAlgebraHom a ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading) := by
  change (tensorInclLeft B C).toAlgebraHom (ε.toAlgebraHom a) *
    (tensorInclRight B C).toAlgebraHom c = _
  exact GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _

/-- `id ⊗ ε` sends the pure tensor `c ⊗ a` to `c ⊗ ε a`. -/
theorem tensorHomRight_tmul (C : DifferentialGradedAlgebra R) (ε : A.Hom B)
    (c : C.A) (a : A.A) :
    (tensorHomRight C ε).toAlgebraHom (c ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading) =
      (c ᵍ⊗ₜ[R] ε.toAlgebraHom a : C.grading ᵍ⊗[R] B.grading) := by
  change (tensorInclLeft C B).toAlgebraHom c *
    (tensorInclRight C B).toAlgebraHom (ε.toAlgebraHom a) = _
  exact GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _

end Homomorphisms

section LinearMaps

/-- An integer multiple can be moved out of the left factor of a pure tensor. -/
theorem zsmul_tmul_left_eq (C D : DifferentialGradedAlgebra R) (m : ℤ) (c : C.A) (x : D.A) :
    ((m • c) ᵍ⊗ₜ[R] x : C.grading ᵍ⊗[R] D.grading) = m • (c ᵍ⊗ₜ[R] x) := by
  change (GradedTensorProduct.of R C.grading D.grading) ((m • c) ⊗ₜ[R] x) =
    m • (GradedTensorProduct.of R C.grading D.grading) (c ⊗ₜ[R] x)
  rw [← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R, ← TensorProduct.smul_tmul',
    LinearEquiv.map_smul]

/-- The Koszul sign preserves the grading. -/
theorem koszulSign_mem (C : DifferentialGradedAlgebra R) (p : ℤ) {c : C.A}
    (hc : c ∈ C.grading p) : koszulSign C c ∈ C.grading p := by
  rw [koszulSign_apply_coe C p ⟨c, hc⟩]
  exact Submodule.smul_of_tower_mem _ _ hc

/-- An `R`-linear map `u : A → B` tensored with the identity of `C` on the right. -/
def tensorLinearLeft (u : A.A →ₗ[R] B.A) (C : DifferentialGradedAlgebra R) :
    (tensorProduct A C).A →ₗ[R] (tensorProduct B C).A :=
  (GradedTensorProduct.of R B.grading C.grading).toLinearMap ∘ₗ
    TensorProduct.map u (LinearMap.id : C.A →ₗ[R] C.A) ∘ₗ
    (GradedTensorProduct.of R A.grading C.grading).symm.toLinearMap

/-- An `R`-linear map `u : A → B` tensored with the identity of `C` on the left. -/
def tensorLinearRight (C : DifferentialGradedAlgebra R) (u : A.A →ₗ[R] B.A) :
    (tensorProduct C A).A →ₗ[R] (tensorProduct C B).A :=
  (GradedTensorProduct.of R C.grading B.grading).toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.id : C.A →ₗ[R] C.A) u ∘ₗ
    (GradedTensorProduct.of R C.grading A.grading).symm.toLinearMap

/-- An `R`-linear operator on `A` tensored on the left with the Koszul sign of `C`. -/
def tensorLinearRightSigned (C : DifferentialGradedAlgebra R) (u : A.A →ₗ[R] A.A) :
    (tensorProduct C A).A →ₗ[R] (tensorProduct C A).A :=
  (GradedTensorProduct.of R C.grading A.grading).toLinearMap ∘ₗ
    TensorProduct.map (koszulSign C) u ∘ₗ
    (GradedTensorProduct.of R C.grading A.grading).symm.toLinearMap

@[simp] theorem tensorLinearLeft_tmul (u : A.A →ₗ[R] B.A) (C : DifferentialGradedAlgebra R)
    (a : A.A) (c : C.A) :
    tensorLinearLeft u C (a ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) =
      (u a ᵍ⊗ₜ[R] c : B.grading ᵍ⊗[R] C.grading) := rfl

@[simp] theorem tensorLinearRight_tmul (C : DifferentialGradedAlgebra R)
    (u : A.A →ₗ[R] B.A) (c : C.A) (a : A.A) :
    tensorLinearRight C u (c ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading) =
      (c ᵍ⊗ₜ[R] u a : C.grading ᵍ⊗[R] B.grading) := rfl

/-- `tensorLinearRightSigned C u` sends the pure tensor `c ⊗ a` to `koszulSign C c ⊗ u a`. -/
theorem tensorLinearRightSigned_tmul (C : DifferentialGradedAlgebra R) (u : A.A →ₗ[R] A.A)
    (c : C.A) (a : A.A) :
    tensorLinearRightSigned C u (c ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading) =
      (koszulSign C c ᵍ⊗ₜ[R] u a : C.grading ᵍ⊗[R] A.grading) := rfl

/-- On a pure tensor whose left factor is homogeneous of degree `q`, the Koszul sign in
`tensorLinearRightSigned C u` becomes the scalar `(-1) ^ q`. -/
theorem tensorLinearRightSigned_tmul_of_mem (C : DifferentialGradedAlgebra R)
    (u : A.A →ₗ[R] A.A) (q : ℤ) {c : C.A} (hc : c ∈ C.grading q) (a : A.A) :
    tensorLinearRightSigned C u (c ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading) =
      ((q.negOnePow : ℤ)) • (c ᵍ⊗ₜ[R] u a : C.grading ᵍ⊗[R] A.grading) := by
  rw [tensorLinearRightSigned_tmul, koszulSign_apply_coe C q ⟨c, hc⟩, zsmul_tmul_left_eq]

/-- A linear map on a graded tensor product raises the total degree by `k` as soon as it does on
pure tensors of homogeneous elements. -/
private theorem map_mem_grading_of_tmul {X Y X' Y' : DifferentialGradedAlgebra R}
    (f : (tensorProduct X Y).A →ₗ[R] (tensorProduct X' Y').A) (k n : ℤ)
    (hf : ∀ (p q : ℤ) (a : X.A) (b : Y.A), a ∈ X.grading p → b ∈ Y.grading q →
      f (a ᵍ⊗ₜ[R] b : X.grading ᵍ⊗[R] Y.grading) ∈ (tensorProduct X' Y').grading (p + q + k))
    {x : (tensorProduct X Y).A} (hx : x ∈ (tensorProduct X Y).grading n) :
    f x ∈ (tensorProduct X' Y').grading (n + k) := by
  have hx' : x ∈ tensorProductGrading X Y n := hx
  clear hx
  rw [tensorProductGrading] at hx'
  induction hx' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨p, q, a, c, ha, hc, hpq, rfl⟩ := hz
      rw [← hpq]
      exact hf p q a c ha hc
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [map_smul]
      exact Submodule.smul_mem _ c hy

/-- If `u` raises degrees by `k`, then so does `u ⊗ id`. -/
theorem tensorLinearLeft_mem_grading (u : A.A →ₗ[R] B.A) (k : ℤ)
    (hu : ∀ (n : ℤ) (a : A.A), a ∈ A.grading n → u a ∈ B.grading (n + k))
    (C : DifferentialGradedAlgebra R) (n : ℤ) {x : (tensorProduct A C).A}
    (hx : x ∈ (tensorProduct A C).grading n) :
    tensorLinearLeft u C x ∈ (tensorProduct B C).grading (n + k) :=
  map_mem_grading_of_tmul _ k n (fun p q a c ha hc => by
    rw [tensorLinearLeft_tmul, add_right_comm]
    exact tmul_mem_grading B C (p + k) q (u a) c (hu p a ha) hc) hx

/-- If `u` raises degrees by `k`, then so does `id ⊗ u`. -/
theorem tensorLinearRight_mem_grading (C : DifferentialGradedAlgebra R) (u : A.A →ₗ[R] B.A)
    (k : ℤ) (hu : ∀ (n : ℤ) (a : A.A), a ∈ A.grading n → u a ∈ B.grading (n + k))
    (n : ℤ) {x : (tensorProduct C A).A} (hx : x ∈ (tensorProduct C A).grading n) :
    tensorLinearRight C u x ∈ (tensorProduct C B).grading (n + k) :=
  map_mem_grading_of_tmul _ k n (fun p q c a hc ha => by
    rw [tensorLinearRight_tmul, add_assoc]
    exact tmul_mem_grading C B p (q + k) c (u a) hc (hu q a ha)) hx

/-- If `u` raises degrees by `k`, then so does `tensorLinearRightSigned C u`: the Koszul sign is
degree-preserving. -/
theorem tensorLinearRightSigned_mem_grading (C : DifferentialGradedAlgebra R)
    (u : A.A →ₗ[R] A.A) (k : ℤ)
    (hu : ∀ (n : ℤ) (a : A.A), a ∈ A.grading n → u a ∈ A.grading (n + k))
    (n : ℤ) {x : (tensorProduct C A).A} (hx : x ∈ (tensorProduct C A).grading n) :
    tensorLinearRightSigned C u x ∈ (tensorProduct C A).grading (n + k) :=
  map_mem_grading_of_tmul _ k n (fun p q c a hc ha => by
    rw [tensorLinearRightSigned_tmul, add_assoc]
    exact tmul_mem_grading C A p (q + k) (koszulSign C c) (u a)
      (koszulSign_mem C p hc) (hu q a ha)) hx

end LinearMaps

section Differential

/-- Induction on an element of a graded tensor product, reducing to pure tensors whose left factor
is homogeneous. -/
private theorem tensorProduct_induction {X Y : DifferentialGradedAlgebra R}
    {P : (tensorProduct X Y).A → Prop} (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (hom : ∀ (p : ℤ) (a : X.grading p) (c : Y.A),
      P (((a : X.A) ᵍ⊗ₜ[R] c : X.grading ᵍ⊗[R] Y.grading)))
    (x : (tensorProduct X Y).A) : P x := by
  obtain ⟨y, rfl⟩ := (GradedTensorProduct.of R X.grading Y.grading).surjective x
  induction y using TensorProduct.inductionOn with
  | add p q hp hq =>
      rw [map_add]
      exact add _ _ hp hq
  | tmul a c =>
      induction a using DirectSum.Decomposition.inductionOn X.grading with
      | zero => simpa using zero
      | add a a' ha ha' =>
          rw [TensorProduct.add_tmul, map_add]
          exact add _ _ ha ha'
      | @homogeneous p a => exact hom p a c

/-- A grading-preserving chain map tensored with the identity of `C` on the right is a chain
map. -/
theorem tensorLinearLeft_map_d (u : A.A →ₗ[R] B.A)
    (hmem : ∀ (n : ℤ) (a : A.A), a ∈ A.grading n → u a ∈ B.grading n)
    (hd : ∀ a, u (A.d a) = B.d (u a)) (C : DifferentialGradedAlgebra R)
    (x : (tensorProduct A C).A) :
    tensorLinearLeft u C ((tensorProduct A C).d x) =
      (tensorProduct B C).d (tensorLinearLeft u C x) := by
  induction x using tensorProduct_induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | hom p a c =>
  rw [tensorProductDifferential_tmul A C p a c, map_add, map_zsmul,
    tensorLinearLeft_tmul, tensorLinearLeft_tmul, tensorLinearLeft_tmul, hd,
    tensorProductDifferential_tmul B C p ⟨u (a : A.A), hmem p (a : A.A) a.2⟩ c]

/-- A chain map tensored with the identity of `C` on the left is a chain map. -/
theorem tensorLinearRight_map_d (C : DifferentialGradedAlgebra R) (u : A.A →ₗ[R] B.A)
    (hd : ∀ a, u (A.d a) = B.d (u a)) (x : (tensorProduct C A).A) :
    tensorLinearRight C u ((tensorProduct C A).d x) =
      (tensorProduct C B).d (tensorLinearRight C u x) := by
  induction x using tensorProduct_induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | hom p c a =>
      rw [tensorProductDifferential_tmul C A p c a, map_add, map_zsmul,
        tensorLinearRight_tmul, tensorLinearRight_tmul, tensorLinearRight_tmul, hd,
        tensorProductDifferential_tmul C B p c (u a)]

end Differential

section Stability

variable {ε : A.Hom B}

/-- The homotopy identity of a retraction, in the form without a subtraction. -/
private theorem sec_apply_eq (ρ : HomotopyRetract ε) (a : A.A) :
    ρ.sec (ε.toAlgebraHom a) = a + (A.d (ρ.htp a) + ρ.htp (A.d a)) := by
  rw [← ρ.htp_eq a]
  abel

/-- The homotopy identity for `ε ⊗ id`, in the form without a subtraction. -/
theorem tensorLinearLeft_sec_eq (ρ : HomotopyRetract ε) (C : DifferentialGradedAlgebra R)
    (x : (tensorProduct A C).A) :
    tensorLinearLeft ρ.sec C ((tensorHomLeft ε C).toAlgebraHom x) =
      x + ((tensorProduct A C).d (tensorLinearLeft ρ.htp C x) +
        tensorLinearLeft ρ.htp C ((tensorProduct A C).d x)) := by
  induction x using tensorProduct_induction with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]
      abel
  | hom p a c =>
      have hL : tensorLinearLeft ρ.sec C ((tensorHomLeft ε C).toAlgebraHom
            ((a : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) =
          ((a : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) +
            ((A.d (ρ.htp (a : A.A)) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) +
              (ρ.htp (A.d (a : A.A)) ᵍ⊗ₜ[R] c :
                A.grading ᵍ⊗[R] C.grading)) := by
        rw [tensorHomLeft_tmul, tensorLinearLeft_tmul, sec_apply_eq, tmul_add_left,
          tmul_add_left]
      have hG1 : (tensorProduct A C).d (tensorLinearLeft ρ.htp C
            ((a : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) =
          (A.d (ρ.htp (a : A.A)) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) +
            (((p - 1).negOnePow : ℤ) •
              (ρ.htp (a : A.A) ᵍ⊗ₜ[R] C.d c :
                A.grading ᵍ⊗[R] C.grading)) := by
        rw [tensorLinearLeft_tmul]
        exact tensorProductDifferential_tmul A C (p - 1)
          ⟨ρ.htp (a : A.A), ρ.htp_mem p (a : A.A) a.2⟩ c
      have hG2 : tensorLinearLeft ρ.htp C ((tensorProduct A C).d
            ((a : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) =
          (ρ.htp (A.d (a : A.A)) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading) +
            ((p.negOnePow : ℤ) •
              (ρ.htp (a : A.A) ᵍ⊗ₜ[R] C.d c :
                A.grading ᵍ⊗[R] C.grading)) := by
        rw [tensorProductDifferential_tmul A C p a c, map_add, map_zsmul,
          tensorLinearLeft_tmul, tensorLinearLeft_tmul]
      rw [hL, hG1, hG2, negOnePow_val_eq_neg_sub_one p, neg_smul]
      abel

/-- **Tensoring with `C` on the right preserves a homotopy retraction.** -/
def HomotopyRetract.tensorLeft (ρ : HomotopyRetract ε) (C : DifferentialGradedAlgebra R) :
    HomotopyRetract (tensorHomLeft ε C) where
  sec := tensorLinearLeft ρ.sec C
  sec_mem n b hb := by
    have h := tensorLinearLeft_mem_grading ρ.sec 0
      (fun m x hx => by rw [add_zero]; exact ρ.sec_mem m x hx) C n hb
    rw [add_zero] at h
    exact h
  sec_d b := tensorLinearLeft_map_d ρ.sec (fun m x hx => ρ.sec_mem m x hx) ρ.sec_d C b
  hom_sec b := by
    obtain ⟨y, rfl⟩ := (GradedTensorProduct.of R B.grading C.grading).surjective b
    induction y using TensorProduct.inductionOn with
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul b c =>
        rw [tensorLinearLeft_tmul, tensorHomLeft_tmul, ρ.hom_sec]
  htp := tensorLinearLeft ρ.htp C
  htp_mem n a ha := by
    have h := tensorLinearLeft_mem_grading ρ.htp (-1)
      (fun m x hx => by
        rw [show m + (-1 : ℤ) = m - 1 from by ring]
        exact ρ.htp_mem m x hx) C n ha
    rw [show n + (-1 : ℤ) = n - 1 from by ring] at h
    exact h
  htp_eq x := by
    rw [tensorLinearLeft_sec_eq ρ C x]
    abel

/-- The homotopy identity for `id ⊗ ε`, in the form without a subtraction. -/
theorem tensorLinearRight_sec_eq (C : DifferentialGradedAlgebra R) (ρ : HomotopyRetract ε)
    (x : (tensorProduct C A).A) :
    tensorLinearRight C ρ.sec ((tensorHomRight C ε).toAlgebraHom x) =
      x + ((tensorProduct C A).d (tensorLinearRightSigned C ρ.htp x) +
        tensorLinearRightSigned C ρ.htp ((tensorProduct C A).d x)) := by
  induction x using tensorProduct_induction with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]
      abel
  | hom q c a =>
      have hL : tensorLinearRight C ρ.sec ((tensorHomRight C ε).toAlgebraHom
            ((c : C.A) ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading)) =
          ((c : C.A) ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading) +
            (((c : C.A) ᵍ⊗ₜ[R] A.d (ρ.htp a) : C.grading ᵍ⊗[R] A.grading) +
              ((c : C.A) ᵍ⊗ₜ[R] ρ.htp (A.d a) :
                C.grading ᵍ⊗[R] A.grading)) := by
        rw [tensorHomRight_tmul, tensorLinearRight_tmul, sec_apply_eq, tmul_add_right,
          tmul_add_right]
      have hG1 : (tensorProduct C A).d (tensorLinearRightSigned C ρ.htp
            ((c : C.A) ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading)) =
          ((q.negOnePow : ℤ)) •
            ((C.d (c : C.A) ᵍ⊗ₜ[R] ρ.htp a : C.grading ᵍ⊗[R] A.grading) +
              ((q.negOnePow : ℤ)) •
                ((c : C.A) ᵍ⊗ₜ[R] A.d (ρ.htp a) :
                  C.grading ᵍ⊗[R] A.grading)) := by
        rw [tensorLinearRightSigned_tmul_of_mem C ρ.htp q c.2 a, map_zsmul,
          tensorProductDifferential_tmul C A q c (ρ.htp a)]
      have hG2 : tensorLinearRightSigned C ρ.htp ((tensorProduct C A).d
            ((c : C.A) ᵍ⊗ₜ[R] a : C.grading ᵍ⊗[R] A.grading)) =
          (((q + 1).negOnePow : ℤ)) •
              (C.d (c : C.A) ᵍ⊗ₜ[R] ρ.htp a : C.grading ᵍ⊗[R] A.grading) +
            ((q.negOnePow : ℤ)) • (((q.negOnePow : ℤ)) •
              ((c : C.A) ᵍ⊗ₜ[R] ρ.htp (A.d a) :
                C.grading ᵍ⊗[R] A.grading)) := by
        rw [tensorProductDifferential_tmul C A q c a, map_add, map_zsmul,
          tensorLinearRightSigned_tmul_of_mem C ρ.htp (q + 1)
            (C.d_mem q (c : C.A) c.2) a,
          tensorLinearRightSigned_tmul_of_mem C ρ.htp q c.2 (A.d a)]
      rw [hL, hG1, hG2]
      simp only [smul_add, smul_smul, negOnePow_mul_self_val, one_smul,
        negOnePow_add_one_val, neg_smul]
      abel

/-- **Tensoring with `C` on the left preserves a homotopy retraction.** The homotopy acquires the
Koszul sign of the left factor. -/
def HomotopyRetract.tensorRight (C : DifferentialGradedAlgebra R) (ρ : HomotopyRetract ε) :
    HomotopyRetract (tensorHomRight C ε) where
  sec := tensorLinearRight C ρ.sec
  sec_mem n b hb := by
    have h := tensorLinearRight_mem_grading C ρ.sec 0
      (fun m x hx => by rw [add_zero]; exact ρ.sec_mem m x hx) n hb
    rw [add_zero] at h
    exact h
  sec_d b := tensorLinearRight_map_d C ρ.sec ρ.sec_d b
  hom_sec b := by
    obtain ⟨y, rfl⟩ := (GradedTensorProduct.of R C.grading B.grading).surjective b
    induction y using TensorProduct.inductionOn with
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul c b =>
        rw [tensorLinearRight_tmul, tensorHomRight_tmul, ρ.hom_sec]
  htp := tensorLinearRightSigned C ρ.htp
  htp_mem n a ha := by
    have h := tensorLinearRightSigned_mem_grading C ρ.htp (-1)
      (fun m x hx => by
        rw [show m + (-1 : ℤ) = m - 1 from by ring]
        exact ρ.htp_mem m x hx) n ha
    rw [show n + (-1 : ℤ) = n - 1 from by ring] at h
    exact h
  htp_eq x := by
    rw [tensorLinearRight_sec_eq C ρ x]
    abel

end Stability

end DifferentialGradedAlgebra
