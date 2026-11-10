module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaFunctorial
public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# The graded pieces of `Ω^•_{B/R}` as tensor products over `A`

Let `R → A → B` be ring maps with `A → B` formally smooth. The graded pieces of the filtration of
`⋀^• Ω_{B/R}` by the forms pulled back from `A` are, by
`KaehlerDifferential.gradedLeftMul_bijective`, tensor products over `B` with `⋀ᵏ_B(B ⊗_A Ω_{A/R})`.
This file rewrites them as tensor products **over `A`** with `⋀ᵏ_A Ω_{A/R}`:

`⋀ᵏ_A Ω_{A/R} ⊗_A (⋀ᵐ Ω_{B/R} / F^1) ≅ F^k ⋀ᵏ⁺ᵐ Ω_{B/R} / F^{k+1}`,  `a ⊗ [η] ↦ [a ∧ η]`,

which is the shape in which [Stacks, Tag 0FUM] uses them: there the coefficient module
`Ω^k_{A/R}` is fixed and `B` runs over the rings of the members of a Čech covering.

## Main definitions

* `exteriorPower.tensorBaseChangeEquiv`: `B ⊗_A ⋀ᵏ_A M ≅ ⋀ᵏ_B (B ⊗_A M)`.
* `KaehlerDifferential.gradedMul`: the map `a ⊗ [η] ↦ [a ∧ η]` above, `A`-linear.

## Main results

* `KaehlerDifferential.gradedMul_bijective`: it is bijective when `A → B` is formally smooth.

## References

* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace exteriorPower

variable (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- The inclusion of `⋀ᵏ M` into the exterior algebra has a retraction, the projection onto the
degree-`k` part of the grading. -/
noncomputable def gradedRetraction (k : ℕ) : ExteriorAlgebra A M →ₗ[A] ⋀[A]^k M :=
  (DFinsupp.lapply k).comp
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[A]^i M)).toLinearMap

/-- `gradedRetraction` restricts to the identity on `⋀ᵏ M`. -/
theorem gradedRetraction_coe (k : ℕ) (x : ⋀[A]^k M) :
    gradedRetraction A M k (x : ExteriorAlgebra A M) = x := by
  simp [gradedRetraction, DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe]

/-- `B ⊗_A ⋀ᵏ_A M ⟶ ⋀ᵏ_B (B ⊗_A M)`, `b ⊗ (m₁ ∧ ⋯ ∧ m_k) ↦ b • ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ m_k))`. -/
noncomputable def tensorBaseChange (k : ℕ) : B ⊗[A] ⋀[A]^k M →ₗ[B] ⋀[B]^k (B ⊗[A] M) :=
  (mapTower k (TensorProduct.mk A B M 1)).liftBaseChange B

/-- `tensorBaseChange` sends `b ⊗ (m₁ ∧ ⋯ ∧ m_k)` to `b • ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ m_k))`. -/
theorem tensorBaseChange_tmul_ιMulti (k : ℕ) (b : B) (m : Fin k → M) :
    tensorBaseChange A B M k (b ⊗ₜ ιMulti A k m) = b • ιMulti B k fun i => (1 : B) ⊗ₜ[A] m i := by
  simp [tensorBaseChange, mapTower_ιMulti]

/-- Induction on `⋀ᵏ M` from the generators `ιMulti A k m`. -/
private theorem induction_ιMulti {k : ℕ} {P : ⋀[A]^k M → Prop} (x : ⋀[A]^k M)
    (mem : ∀ m, P (ιMulti A k m)) (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (c : A) x, P x → P (c • x)) : P x := by
  refine Submodule.span_induction (fun _ ⟨m, h⟩ => h ▸ mem m) zero (fun x y _ _ => add x y)
    (fun c x _ => smul c x) (?_ : x ∈ Submodule.span A (Set.range (ιMulti A k)))
  rw [ιMulti_span]; trivial

/-- The base change of exterior algebras composed with `tensorBaseChange` is the base change of
the inclusion `⋀ᵏ M ⊆ ⋀ M`. -/
theorem exteriorAlgebraBaseChange_tensorBaseChange (k : ℕ) (z : B ⊗[A] ⋀[A]^k M) :
    ProjectiveDeterminant.exteriorAlgebraBaseChange A B M
        (tensorBaseChange A B M k z : ExteriorAlgebra B (B ⊗[A] M)) =
      (⋀[A]^k M).subtype.lTensor B z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | tmul b x =>
    induction x using induction_ιMulti with
    | mem m =>
      rw [tensorBaseChange_tmul_ιMulti, SetLike.val_smul, map_smul, ιMulti_apply_coe,
        ProjectiveDeterminant.exteriorAlgebraBaseChange_ιMulti, LinearMap.lTensor_tmul,
        Submodule.subtype_apply, ιMulti_apply_coe, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Submodule.coe_add, hx, hy]
    | smul c x hx =>
      rw [← TensorProduct.smul_tmul, ← algebraMap_smul B c b, ← TensorProduct.smul_tmul',
        map_smul, SetLike.val_smul, map_smul, hx, LinearMap.lTensor_tmul,
        TensorProduct.smul_tmul', TensorProduct.smul_tmul', LinearMap.lTensor_tmul]

/-- The map `tensorBaseChange : B ⊗_A ⋀ᵏ_A M ⟶ ⋀ᵏ_B (B ⊗_A M)` is injective. -/
theorem tensorBaseChange_injective (k : ℕ) : Function.Injective (tensorBaseChange A B M k) := by
  have hg : Function.Injective ((⋀[A]^k M).subtype.lTensor B) := by
    refine Function.LeftInverse.injective (g := (gradedRetraction A M k).lTensor B) fun z => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : gradedRetraction A M k ∘ₗ (⋀[A]^k M).subtype = LinearMap.id :=
      LinearMap.ext (gradedRetraction_coe A M k)
    rw [this, LinearMap.lTensor_id, LinearMap.id_apply]
  intro z z' h
  apply hg
  rw [← exteriorAlgebraBaseChange_tensorBaseChange, ← exteriorAlgebraBaseChange_tensorBaseChange,
    h]

/-- The map `tensorBaseChange : B ⊗_A ⋀ᵏ_A M ⟶ ⋀ᵏ_B (B ⊗_A M)` is surjective. -/
theorem tensorBaseChange_surjective (k : ℕ) : Function.Surjective (tensorBaseChange A B M k) := by
  intro w
  have hw : ProjectiveDeterminant.exteriorAlgebraBaseChange A B M (w : ExteriorAlgebra B _) ∈
      Submodule.baseChange B (⋀[A]^k M) := by
    rw [← ProjectiveDeterminant.exteriorPower_baseChange_map]
    exact ⟨w, w.2, rfl⟩
  obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective B (⋀[A]^k M) ⟨_, hw⟩
  refine ⟨z, Subtype.ext ((ProjectiveDeterminant.exteriorAlgebraBaseChange A B M).injective ?_)⟩
  rw [exteriorAlgebraBaseChange_tensorBaseChange]
  exact congrArg Subtype.val hz

/-- **The exterior powers commute with base change**: `B ⊗_A ⋀ᵏ_A M ≅ ⋀ᵏ_B (B ⊗_A M)`. -/
noncomputable def tensorBaseChangeEquiv (k : ℕ) : B ⊗[A] ⋀[A]^k M ≃ₗ[B] ⋀[B]^k (B ⊗[A] M) :=
  LinearEquiv.ofBijective (tensorBaseChange A B M k)
    ⟨tensorBaseChange_injective A B M k, tensorBaseChange_surjective A B M k⟩

end exteriorPower

namespace KaehlerDifferential

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- `(⋀ᵏ ι) (1 ⊗ a) = a`, pulled back: the image in `⋀ᵏ_B Ω_{B/R}` of the base change of a form
`a ∈ ⋀ᵏ_A Ω_{A/R}` is its restriction `mapExteriorPower R A B k a`. -/
theorem map_tensorBaseChange_one_tmul (k : ℕ) (a : ⋀[A]^k (Ω[A⁄R])) :
    exteriorPower.map k (mapBaseChange R A B)
        (exteriorPower.tensorBaseChange A B (Ω[A⁄R]) k (1 ⊗ₜ a)) =
      mapExteriorPower R A B k a := by
  induction a using exteriorPower.induction_ιMulti with
  | mem ω =>
    rw [exteriorPower.tensorBaseChange_tmul_ιMulti, one_smul, exteriorPower.map_apply_ιMulti,
      mapExteriorPower_ιMulti]
    congr 1
    funext i
    simp [mapBaseChange_tmul]
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | smul c x hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B c ((1 : B) ⊗ₜ[A] x), map_smul, map_smul, hx,
      map_smul, algebraMap_smul]

/-- The rearrangement `⋀ᵏ_A Ω_{A/R} ⊗_A Q ≅ ⋀ᵏ_B (B ⊗_A Ω_{A/R}) ⊗_B Q` for a `B`-module `Q`. -/
noncomputable def gradedMulAux (k : ℕ) (Q : Type u) [AddCommGroup Q] [Module B Q] [Module A Q]
    [IsScalarTower A B Q] :
    ⋀[A]^k (Ω[A⁄R]) ⊗[A] Q ≃ₗ[A] ⋀[B]^k (B ⊗[A] Ω[A⁄R]) ⊗[B] Q :=
  TensorProduct.comm A _ Q ≪≫ₗ
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B Q
        (⋀[A]^k (Ω[A⁄R]))).symm.restrictScalars A ≪≫ₗ
      ((TensorProduct.comm B Q (B ⊗[A] ⋀[A]^k (Ω[A⁄R]))).restrictScalars A ≪≫ₗ
        (LinearEquiv.rTensor Q
          (exteriorPower.tensorBaseChangeEquiv A B (Ω[A⁄R]) k)).restrictScalars A))

omit [Algebra R B] [IsScalarTower R A B] in
/-- `gradedMulAux` sends `a ⊗ q` to `tensorBaseChange (1 ⊗ a) ⊗ q`. -/
theorem gradedMulAux_tmul (k : ℕ) (Q : Type u) [AddCommGroup Q] [Module B Q] [Module A Q]
    [IsScalarTower A B Q] (a : ⋀[A]^k (Ω[A⁄R])) (q : Q) :
    gradedMulAux R A B k Q (a ⊗ₜ q) =
      exteriorPower.tensorBaseChange A B (Ω[A⁄R]) k (1 ⊗ₜ a) ⊗ₜ q := by
  simp [gradedMulAux, exteriorPower.tensorBaseChangeEquiv]
  rfl

/-- **The graded pieces as tensor products over `A`**: `a ⊗ [η] ↦ [a ∧ η]`,
`⋀ᵏ_A Ω_{A/R} ⊗_A (⋀ᵐ Ω_{B/R} / F^1) ⟶ F^k ⋀ⁿ Ω_{B/R} / F^{k+1}` for `k + m = n`. -/
noncomputable def gradedMul {k m n : ℕ} (h : k + m = n) :
    ⋀[A]^k (Ω[A⁄R]) ⊗[A] exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m →ₗ[A]
      exteriorPower.wedgeGraded (mapBaseChange R A B) k n :=
  ((exteriorPower.gradedLeftMul (mapBaseChange R A B) h).restrictScalars A).comp
    (gradedMulAux R A B k _).toLinearMap

/-- `gradedMul` sends `a ⊗ q` to `gradedLeftMul (tensorBaseChange (1 ⊗ a) ⊗ q)`. -/
theorem gradedMul_tmul {k m n : ℕ} (h : k + m = n) (a : ⋀[A]^k (Ω[A⁄R]))
    (q : exteriorPower.wedgeZeroGraded (mapBaseChange R A B) m) :
    gradedMul R A B h (a ⊗ₜ q) = exteriorPower.gradedLeftMul (mapBaseChange R A B) h
      (exteriorPower.tensorBaseChange A B (Ω[A⁄R]) k (1 ⊗ₜ a) ⊗ₜ q) := by
  rw [gradedMul, LinearMap.comp_apply, LinearEquiv.coe_coe, gradedMulAux_tmul]
  rfl

/-- **`⋀ᵏ_A Ω_{A/R} ⊗_A gr^0 ≅ gr^k`** for `A → B` formally smooth. -/
theorem gradedMul_bijective [Algebra.FormallySmooth A B] {k m n : ℕ} (h : k + m = n) :
    Function.Bijective (gradedMul R A B h) :=
  (gradedLeftMul_bijective R A B h).comp (gradedMulAux R A B k _).bijective

end KaehlerDifferential
