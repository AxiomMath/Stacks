module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine.SurjectiveQuasiIso

/-!
# The canonical element of a determinant line is preserved

The canonical isomorphism of determinant lines attached to a degreewise-surjective
quasi-isomorphism of two-term finite-projective complexes sends `δ` to `δ` when the source and
target have rank zero. The comparison is the naturality of the determinant equivalence of the
short exact sequence formed by the kernel.

## Main results

* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_apply_delta`: the isomorphism carries the
  canonical element to the canonical element.

## References

* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
-/

namespace TwoTermComplex

/-! ### The canonical element is preserved -/

section

universe u v₁ v₀ w₁ w₀

open TwoTermComplex

private theorem kernelDeterminantEquiv_naturality
    {R : Type u} [CommRing R]
    {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : Hom K L)
    (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
    (hM : IsRankZero a.kernelDifferential) (hK : IsRankZero K) (hL : IsRankZero L)
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    kernelDeterminantEquiv a.zero ha.2
        (delta a.kernelDifferential hM x ⊗ₜ[R] delta L hL y) =
      delta K hK (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)) := by
  let eM₁ := determinantAnnihilatorEquiv (R := R) (M := LinearMap.ker a.neg)
  let eM₀ := determinantAnnihilatorEquiv (R := R) (M := LinearMap.ker a.zero)
  let eK₁ := determinantAnnihilatorEquiv (R := R) (M := K₁)
  let eK₀ := determinantAnnihilatorEquiv (R := R) (M := K₀)
  let eL₁ := determinantAnnihilatorEquiv (R := R) (M := L₁)
  let eL₀ := determinantAnnihilatorEquiv (R := R) (M := L₀)
  let γ₁ := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker a.neg).subtype a.neg (LinearMap.ker a.neg).injective_subtype
      a.neg.exact_subtype_ker_map ha.1).val
  let γ₀ := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker a.zero).subtype a.zero (LinearMap.ker a.zero).injective_subtype
      a.zero.exact_subtype_ker_map ha.2).val
  obtain ⟨z, hz⟩ := (ExteriorAlgebra.map_surjective_iff.mpr ha.1) (eL₁ y : ExteriorAlgebra R L₁)
  apply eK₀.injective
  show γ₀ (eM₀ (delta a.kernelDifferential hM x) ⊗ₜ[R] eL₀ (delta L hL y)) =
    eK₀ (delta K hK (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)))
  have hγ₁ := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker a.neg).subtype a.neg (LinearMap.ker a.neg).injective_subtype
      a.neg.exact_subtype_ker_map ha.1).property (eM₁ x) (eL₁ y) z hz
  have hγ₀ := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker a.zero).subtype a.zero (LinearMap.ker a.zero).injective_subtype
      a.zero.exact_subtype_ker_map ha.2).property
      (eM₀ (delta a.kernelDifferential hM x)) (eL₀ (delta L hL y))
      (ExteriorAlgebra.map K z) (by
        show ExteriorAlgebra.map a.zero (ExteriorAlgebra.map K z) =
          ExteriorAlgebra.map L (eL₁ y : ExteriorAlgebra R L₁)
        calc
          _ = ExteriorAlgebra.map (a.zero.comp K) z :=
            congrArg (fun q => q z) (ExteriorAlgebra.map_comp_map K a.zero)
          _ = ExteriorAlgebra.map (L.comp a.neg) z := by rw [a.comm]
          _ = ExteriorAlgebra.map L (ExteriorAlgebra.map a.neg z) :=
            congrArg (fun q => q z) (ExteriorAlgebra.map_comp_map a.neg L).symm
          _ = _ := by rw [hz])
  apply Subtype.ext
  rw [hγ₀]
  show ExteriorAlgebra.map (LinearMap.ker a.zero).subtype
      (ExteriorAlgebra.map a.kernelDifferential (eM₁ x : ExteriorAlgebra R _)) *
      ExteriorAlgebra.map K z =
    ExteriorAlgebra.map K (γ₁ (eM₁ x ⊗ₜ[R] eL₁ y) : ExteriorAlgebra R K₁)
  rw [hγ₁, map_mul]
  congr 1
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rfl

/-- The rank at each stalk is additive along a surjection onto a finite projective module. -/
private theorem rankAtStalk_eq_ker_add
    {R : Type u} [CommRing R] {M : Type v₁} {N : Type v₀}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)] :
    Module.rankAtStalk (R := R) M =
      Module.rankAtStalk (R := R) (LinearMap.ker f) + Module.rankAtStalk (R := R) N := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let e : (LinearMap.ker f × N) ≃ₗ[R] M := LinearEquiv.ofLinear
    { toFun := fun z => z.1.1 + s z.2
      map_add' := by intros; simp; abel
      map_smul' := by intros; simp }
    { toFun := fun z => (⟨z - s (f z), by
          rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hs]; simp⟩, f z)
      map_add' := by intros; ext <;> simp; abel
      map_smul' := by intros; ext <;> simp [smul_sub] }
    (by
      apply LinearMap.ext
      intro x
      show x - s (f x) + s (f x) = x
      abel)
    (by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      apply Prod.ext
      · apply Subtype.ext
        show x.1 + s y - s (f (x.1 + s y)) = x.1
        have hy := LinearMap.congr_fun hs y
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at hy
        simp [hy]
      · show f (x.1 + s y) = y
        have := LinearMap.congr_fun hs y
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        simp [this])
  rw [← Module.rankAtStalk_prod]
  exact (Module.rankAtStalk_eq_of_equiv e).symm

/-- **Stacks 0FJJ.** The canonical determinant equivalence associated to a
degreewise-surjective quasi-isomorphism of two-term finite-projective complexes maps the
canonical determinant element of the source to that of the target. -/
@[stacks 0FJJ]
public theorem determinantEquivOfSurjectiveQuasiIso_apply_delta
    {R : Type u} [CommRing R]
    {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : TwoTermComplex.Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) (hL : TwoTermComplex.IsRankZero L) :
    letI : Module.Finite R (LinearMap.ker a.neg) :=
      TwoTermComplex.kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) :=
      TwoTermComplex.kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) :=
      TwoTermComplex.kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) :=
      TwoTermComplex.kernel_projective a.zero ha.2
    let D := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa
    ∃ hK : TwoTermComplex.IsRankZero K,
      D.equiv (TwoTermComplex.delta K hK) = TwoTermComplex.delta L hL
    := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let D := determinantEquivOfSurjectiveQuasiIso K L a ha hqa
  have hK : IsRankZero K := fun p => by
    have h₁ := congrFun (rankAtStalk_eq_ker_add a.neg ha.1) p
    have h₀ := congrFun (rankAtStalk_eq_ker_add a.zero ha.2) p
    simp only [Pi.add_apply] at h₁ h₀
    have hM := D.kernelRankZero p
    have hLp := hL p
    omega
  refine ⟨hK, ?_⟩
  apply LinearMap.ext
  intro y
  let de : LinearMap.ker a.neg ≃ₗ[R] LinearMap.ker a.zero :=
    LinearEquiv.ofBijective a.kernelDifferential D.kernelAcyclic
  let ddet : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg) ≃ₗ[R]
      ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero) :=
    ProjectiveDeterminant.mapEquiv de
  let : Module.Invertible R
      (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :=
    ProjectiveDeterminant.invertible
  let t : determinantLine L ≃ₗ[R]
      ((TensorProduct R
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
        (ProjectiveDeterminant.module (R := R) (M := L₁))) →ₗ[R]
      (TensorProduct R
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero))
        (ProjectiveDeterminant.module (R := R) (M := L₀)))) :=
    (Module.Invertible.rTensorEquiv
    (ProjectiveDeterminant.module (R := R) (M := L₁))
    (ProjectiveDeterminant.module (R := R) (M := L₀))
    ((TensorProduct.comm R
      (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (Module.Dual R (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)))).trans
      (Module.Invertible.linearEquiv R
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))))).trans
    (LinearEquiv.arrowCongr
      (TensorProduct.comm R
        (ProjectiveDeterminant.module (R := R) (M := L₁))
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)))
      ((TensorProduct.comm R
        (ProjectiveDeterminant.module (R := R) (M := L₀))
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))).trans
        (TensorProduct.congr ddet (LinearEquiv.refl R _))))
  apply LinearMap.congr_fun (t.injective ?_) y
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      show ddet x ⊗ₜ[R] D.equiv (delta K hK) y =
        ddet x ⊗ₜ[R] delta L hL y
      apply (kernelDeterminantEquiv a.zero ha.2).injective
      show kernelDeterminantEquiv a.zero ha.2
          (delta a.kernelDifferential D.kernelRankZero x ⊗ₜ[R]
            D.equiv (delta K hK) y) =
        kernelDeterminantEquiv a.zero ha.2
          (delta a.kernelDifferential D.kernelRankZero x ⊗ₜ[R] delta L hL y)
      rw [D.compatibility]
      exact (kernelDeterminantEquiv_naturality K L a ha D.kernelRankZero hK hL x y).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end

end TwoTermComplex
