module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationDegreeOne
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecTruncation
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecZeroSectionCartesian
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineModelTwistBridge
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Basic

/-!
# The cone `Proj(⨁_d A_{≥ d})` of a graded ring generated in degree one is a blowup

Let `A` be a graded ring, `B = ⨁_{d ≥ 0} A_{≥ d}`, `X = Spec A`, `Z = V(A_+) = Spec A_0`,
`L = Proj B` and `P = Proj A`. If `A` is generated over `A_0` by `f_1, …, f_r ∈ A_1`, then `B` is
the Rees algebra of `A_+ = (f_1, …, f_r)` (`Stacks.Truncation.truncationRingEquivReesAlgebra`), so
that `L → X` is the blowup of `X` along `Z`, and the open `W ⊆ P` on which `𝒪_P(1)` is invertible
and `𝒪_P(m) ≅ 𝒪_P(1)^{⊗ m}` is all of `P`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpecBlowup.projTruncationIsoProjRees`: `Proj B ≅ Proj A[A_+ t]`.
* `Stacks.AlgebraicGeometry.ProjAndSpecBlowup.truncationProjIsoBlowUp`: **`L ≅ Bl_Z X`**.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpecBlowup.ker_zToX`: the ideal sheaf of `Z ⊆ X` is the one
  defined by `A_+`.
* `Stacks.AlgebraicGeometry.ProjAndSpecBlowup.truncationProjIsoBlowUp_hom_blowUpToBase`: the
  isomorphism `L ≅ Bl_Z X` is an isomorphism over `X`.
* `Stacks.AlgebraicGeometry.ProjAndSpecBlowup.whereInvertible_one_eq_top`: `W = P`.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Truncation Stacks.Blowup.AffineModel
open Stacks.AlgebraicGeometry.ProjPolynomialSections Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjAndSpecBlowup

universe u

/-- An equality of ideal sheaves identifies the two blowups over the base. -/
theorem eqToHom_blowUpToBase {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg (blowUp (X := X)) h) ≫ blowUpToBase J = blowUpToBase I := by
  subst h
  simp

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

variable (𝒜) in
/-- **The ideal sheaf of `Z = V(A_+)` in `X = Spec A`** is the quasi-coherent ideal sheaf
defined by the irrelevant ideal `A_+`. -/
theorem ker_zToX :
    (ProjAndSpec.zToX 𝒜).ker = specIdealSheaf (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  have := ProjAndSpec.isClosedImmersion_zToX (𝒜 := 𝒜)
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  refine (Scheme.Hom.ker_apply _ _).trans (Eq.trans ?_ (ideal_specIdealSheaf _).symm)
  change RingHom.ker (Spec.map _).appTop.hom = _
  rw [Stacks.Smooth.ker_specMap_appTop, CommRingCat.hom_ofHom, ProjAndSpec.ker_projZeroRingHom']
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm).symm

variable {r : ℕ} {f : Fin r → A} (hf : ∀ i, f i ∈ 𝒜 1)
  (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)

/-- **`Proj B ≅ Proj A[A_+ t]`**, induced by the graded isomorphism of
`Stacks.Truncation.truncationRingEquivReesAlgebra`, for `A` generated over `A_0` by
`f_1, …, f_r ∈ A_1`. -/
def projTruncationIsoProjRees :
    AlgebraicGeometry.Proj (grading 𝒜) ≅
      AlgebraicGeometry.Proj
        (Stacks.Blowup.reesGrading (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
  projIsoOfGradedSections _ _
    (reesGradedHomInvOfPowEq (irrelevant_pow_eq_truncationIdeal hf hgen))
    (reesGradedHomOfPowEq (irrelevant_pow_eq_truncationIdeal hf hgen))
    (fun _ ↦ by
      rw [reesGradedHomOfPowEq_apply, reesGradedHomInvOfPowEq_apply, RingEquiv.symm_apply_apply])
    (fun _ ↦ by
      rw [reesGradedHomInvOfPowEq_apply, reesGradedHomOfPowEq_apply, RingEquiv.apply_symm_apply])

/-- `Proj B ≅ Proj A[A_+ t]` is an isomorphism over `X = Spec A`: it carries the structure
morphism of the cone `L = Proj B` to that of the affine blowup `Proj A[A_+ t]`. -/
theorem projTruncationIsoProjRees_hom_toSpec :
    (projTruncationIsoProjRees hf hgen).hom ≫
        Stacks.Blowup.toSpec (HomogeneousIdeal.irrelevant 𝒜).toIdeal =
      ProjAndSpec.toSpecA (ProjAndSpecTruncation.truncationConeData 𝒜) := by
  rw [projTruncationIsoProjRees, projIsoOfGradedSections_hom, mapHomOfSection]
  change (mapHomOfTop _ _ _ _ ≫ Proj.toSpecZero _) ≫ Spec.map (CommRingCat.ofHom
    (Stacks.Blowup.reesGradingZeroEquiv (HomogeneousIdeal.irrelevant 𝒜).toIdeal).toRingHom) = _
  rw [mapHomOfTop_toSpecZero, Category.assoc, ← Spec.map_comp, ProjAndSpec.toSpecA]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ Subtype.ext ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    coe_zeroHom_apply]
  change (reesEquivOfPowEq (irrelevant_pow_eq_truncationIdeal hf hgen)).symm
    (algebraMap A (Stacks.Blowup.reesGrading (HomogeneousIdeal.irrelevant 𝒜).toIdeal 0) a) =
      ((sigma 𝒜 a : grading 𝒜 0) : TruncationRing 𝒜)
  rw [RingEquiv.symm_apply_eq, coe_sigma_apply _ a (mem_truncation_zero 𝒜 a), coe_degreeEquiv]
  refine Subtype.ext ?_
  rw [coe_reesEquivOfPowEq_of, Polynomial.monomial_zero_left, SetLike.GradeZero.coe_algebraMap]
  rfl

/-- **`L → X` is the blowup of `X` along `Z`**: for `A` generated over `A_0` by
`f_1, …, f_r ∈ A_1`, the cone `L = Proj(⨁_{d ≥ 0} A_{≥ d})` is the blowup of `X = Spec A` in the
ideal sheaf of the closed subscheme `Z = V(A_+)`. It is an isomorphism over `X` by
`truncationProjIsoBlowUp_hom_blowUpToBase`. -/
@[stacks 0EKF "L → X is the blowup of X along Z when A is generated over A₀ by \
f₁, …, f_r ∈ A₁"]
def truncationProjIsoBlowUp :
    AlgebraicGeometry.Proj (grading 𝒜) ≅ blowUp (ProjAndSpec.zToX 𝒜).ker :=
  projTruncationIsoProjRees hf hgen ≪≫ specProjIso _ ≪≫
    eqToIso (congrArg (blowUp (X := Spec (CommRingCat.of A))) (ker_zToX 𝒜).symm)

/-- **The isomorphism `L ≅ Bl_Z X` is an isomorphism over `X`**: it carries the blowing-up
morphism to the structure morphism `L → X` of the cone. -/
@[stacks 0EKF "the identification of L with the blowup of X along Z is one over X"]
theorem truncationProjIsoBlowUp_hom_blowUpToBase :
    (truncationProjIsoBlowUp hf hgen).hom ≫ blowUpToBase (ProjAndSpec.zToX 𝒜).ker =
      ProjAndSpec.toSpecA (ProjAndSpecTruncation.truncationConeData 𝒜) := by
  rw [truncationProjIsoBlowUp, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Category.assoc, eqToHom_blowUpToBase (ker_zToX 𝒜).symm, specProjIso_hom_blowUpToBase,
    projTruncationIsoProjRees_hom_toSpec]

/-- **`W = P`**: for `A` generated over `A_0` by `f_1, …, f_r ∈ A_1`, the largest open of
`P = Proj A` on which `𝒪_P(1)` is invertible and the multiplication maps
`𝒪_P(n) ⊗ 𝒪_P(m) → 𝒪_P(n + m)` are isomorphisms is all of `P`. -/
@[stacks 0EKF "W = P when A is generated over A₀ by f₁, …, f_r ∈ A₁"]
theorem whereInvertible_one_eq_top {r : ℕ} {f : Fin r → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    ProjInvertibleLocus.whereInvertible 𝒜 1 = ⊤ := by
  rw [GoodOpenClose.whereInvertible_eq_ratioLocus]
  refine top_le_iff.mp fun x _ ↦ ?_
  rw [ProjShared.mem_ratioLocus_iff]
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ x.asHomogeneousIdeal := by
    by_contra! h
    refine x.not_irrelevant_le fun a ha ↦ ?_
    have ha' : a ∈ Ideal.span (Set.range f) := (span_range_eq_irrelevant hf hgen).symm ▸ ha
    exact (Ideal.span_le (I := x.asHomogeneousIdeal.toIdeal)).mpr
      (Set.range_subset_iff.mpr h) ha'
  refine ⟨0, f i, 1, by simpa using hf i, SetLike.one_mem_graded 𝒜, hi, fun h ↦ ?_⟩
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

end Stacks.AlgebraicGeometry.ProjAndSpecBlowup

end
