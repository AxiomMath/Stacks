module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierCriterion
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.Situation
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyOfAProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The global functions on the exceptional curve of the blowup of a surface singularity

Let `(A, 𝔪, κ)` be a rational surface singularity, let `X` be the blowup of `Spec(A)` in `𝔪` and
let `E ⊆ X` be the exceptional divisor. Then `H⁰(E, 𝒪_E) = κ`: the canonical ring homomorphism
from `κ` to the global functions on `E` induced by the structure morphism `E ⟶ Spec(κ)` is an
isomorphism. Consequently `E ⟶ Spec(κ)` is a Cohen–Macaulay curve situation.

## Main definitions

* `AlgebraicGeometry.rationalSingularitySituationBlowUp`: the rational singularity situation with
  the blowup of `Spec(A)` in `𝔪` itself as the normal modification.
* `AlgebraicGeometry.cohenMacaulayCurveSituationExceptionalDivisor`: the Cohen–Macaulay curve
  situation given by the exceptional curve `E ⟶ Spec(κ)`.

## Main results

* `AlgebraicGeometry.surjective_subschemeι_appTop_of_isZero_hgroup_one`: sections of a closed
  subscheme lift to the ambient scheme as soon as the first cohomology of its sheaf of ideals
  vanishes.
* `AlgebraicGeometry.isIso_globalSections_exceptionalDivisorToCentre_residuePoint`:
  `H⁰(E, 𝒪_E) = κ`.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase (moduleGlobalSections)

universe u

namespace AlgebraicGeometry

open Stacks.Blowup

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Lifting sections from a closed subscheme -/

/-- Sections of a closed subscheme `D` of `X` lift to `X` when the first cohomology of the sheaf
of ideals of `D` vanishes. -/
theorem surjective_subschemeι_appTop_of_isZero_hgroup_one {X : Scheme.{u}}
    (D : X.IdealSheafData)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Stacks.Divisors.idealSheafOfModules D)))
    (s : Γ(D.subscheme, ⊤)) :
    ∃ r : Γ(X, ⊤), D.subschemeι.appTop r = s := by
  exact Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one X ⊤
    (Stacks.IdealSheafSequence.divisorIdeal_shortExact D).2 h s

/-! ### The rational singularity situation at the blowup of the maximal ideal -/

variable (S : RationalSingularitySituation.{u})

/-- The rational singularity situation whose normal modification is the blowup of `Spec(A)` in
the maximal ideal. -/
def rationalSingularitySituationBlowUp : RationalSingularitySituation.{u} :=
  have : IsNormal (blowUp (residuePoint S.A).ker) := by
    rw [ker_residuePoint_eq_ofIdealTop_map]
    exact isNormal_blowUp_maximalIdeal_rationalSingularitySituation S
  rationalSingularitySituationOfModification S.A S.nagata S.dimension_two
    S.definesRationalSingularity (blowUpToBase (residuePoint S.A).ker)
    (by rw [ker_residuePoint_eq_ofIdealTop_map]
        exact isModification_blowUpToBase_maximalIdeal S.A S.dimension_two)

/-- The ring of the rational singularity situation at the blowup is the original ring. -/
@[simp]
theorem rationalSingularitySituationBlowUp_A :
    (rationalSingularitySituationBlowUp S).A = S.A := rfl

/-- The source of the rational singularity situation at the blowup is the blowup. -/
@[simp]
theorem rationalSingularitySituationBlowUp_X :
    (rationalSingularitySituationBlowUp S).X = blowUp (residuePoint S.A).ker := rfl

/-- The morphism of the rational singularity situation at the blowup is the blowup morphism. -/
@[simp]
theorem rationalSingularitySituationBlowUp_f :
    (rationalSingularitySituationBlowUp S).f = blowUpToBase (residuePoint S.A).ker := rfl

/-- The special fibre of the rational singularity situation at the blowup is the exceptional
divisor. -/
theorem rationalSingularitySituationBlowUp_exceptionalIdeal :
    (rationalSingularitySituationBlowUp S).exceptionalIdeal =
      exceptionalIdeal (residuePoint S.A).ker := by
  rw [RationalSingularitySituation.exceptionalIdeal_eq_comap,
    RationalSingularitySituation.ker_fromSpecResidueField_closedPoint_eq_ofIdealTop_map,
    ← ker_residuePoint_eq_ofIdealTop_map]
  rfl

/-! ### `H⁰(E, 𝒪_E) = κ` -/

/-- `Γ(X, 𝒪_X) = A` for the blowup `X` of `Spec(A)` in the maximal ideal. -/
theorem isIso_globalFunctions_blowUpToBase_residuePoint :
    IsIso ((Scheme.ΓSpecIso (.of S.A)).inv ≫
      (blowUpToBase (residuePoint S.A).ker).appTop) :=
  (rationalSingularitySituationBlowUp S).isIso_globalFunctions

/-- `H⁰(X, 𝓘) = 𝔪` for the blowup `X` of `Spec(A)` in the maximal ideal, read as the kernel of
restriction to the exceptional divisor. -/
theorem ker_exceptionalIdeal_subschemeι_appTop :
    RingHom.ker ((exceptionalIdeal (residuePoint S.A).ker).subschemeι.appTop).hom =
      Ideal.map ((Scheme.ΓSpecIso (.of S.A)).inv ≫
        (blowUpToBase (residuePoint S.A).ker).appTop).hom (IsLocalRing.maximalIdeal S.A) := by
  have h := (rationalSingularitySituationBlowUp S).idealSheafGlobalSections_exceptionalIdeal
  rw [rationalSingularitySituationBlowUp_exceptionalIdeal] at h
  exact h

/-- `H¹(X, 𝓘) = 0` for the blowup `X` of `Spec(A)` in the maximal ideal, in group-valued
cohomology. -/
theorem isZero_hgroup_one_exceptionalIdeal_residuePoint :
    IsZero (Hgroup (blowUp (residuePoint S.A).ker).ringCatSheaf ⊤ 1
      (Stacks.Divisors.idealSheafOfModules (exceptionalIdeal (residuePoint S.A).ker))) := by
  have h : IsZero (((moduleGlobalSections (rationalSingularitySituationBlowUp S).X
        ).rightDerivedPlus 1).obj (Stacks.Divisors.idealSheafOfModules
        ((rationalSingularitySituationBlowUp S).exceptionalIdeal ^ 1))) :=
    (rationalSingularitySituationBlowUp S).isZero_firstCohomology_exceptionalIdealPow_unconditional
      1
  rw [pow_one, rationalSingularitySituationBlowUp_exceptionalIdeal] at h
  exact (Stacks.Cohomology.ModuleComparison.isZero_hgroup_iff_isZero_rightDerivedPlus_evaluation
    _ ⊤ (m := (1 : ℤ)) (n := 1) (by norm_num) _).2 h

/-- The structure morphism of the exceptional divisor over the residue field, on global
functions, is restriction along the exceptional immersion preceded by `A ≅ Γ(X, 𝒪_X)`. -/
theorem residue_comp_globalSections_exceptionalDivisorToCentre :
    CommRingCat.ofHom (IsLocalRing.residue S.A) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S.A))).inv ≫
          (exceptionalDivisorToCentre (residuePoint S.A)).appTop) =
      ((Scheme.ΓSpecIso (.of S.A)).inv ≫
          (blowUpToBase (residuePoint S.A).ker).appTop) ≫
        (exceptionalIdeal (residuePoint S.A).ker).subschemeι.appTop := by
  have hnat : CommRingCat.ofHom (IsLocalRing.residue S.A) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S.A))).inv =
      (Scheme.ΓSpecIso (.of S.A)).inv ≫ (residuePoint S.A).appTop :=
    Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue S.A))
  rw [← Category.assoc, hnat, Category.assoc, ← Scheme.Hom.comp_appTop,
    exceptionalDivisorToCentre_comp, Scheme.Hom.comp_appTop, Category.assoc]

/-- `H⁰(E, 𝒪_E) = κ`: for a rational surface singularity `(A, 𝔪, κ)`, the canonical homomorphism
from the residue field to the global functions on the exceptional divisor of the blowup of
`Spec(A)` in the maximal ideal is an isomorphism. -/
theorem isIso_globalSections_exceptionalDivisorToCentre_residuePoint :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S.A))).inv ≫
      (exceptionalDivisorToCentre (residuePoint S.A)).appTop) := by
  have hψ := isIso_globalFunctions_blowUpToBase_residuePoint S
  obtain ⟨hinjψ, hsurjψ⟩ := ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of S.A)).inv ≫
    (blowUpToBase (residuePoint S.A).ker).appTop)
  have hpt (a : S.A) :
      ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S.A))).inv ≫
          (exceptionalDivisorToCentre (residuePoint S.A)).appTop).hom
            (IsLocalRing.residue S.A a) =
        ((exceptionalIdeal (residuePoint S.A).ker).subschemeι.appTop).hom
          (((Scheme.ΓSpecIso (.of S.A)).inv ≫
            (blowUpToBase (residuePoint S.A).ker).appTop).hom a) := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using
      congrArg (fun q ↦ CommRingCat.Hom.hom q a)
        (residue_comp_globalSections_exceptionalDivisorToCentre S)
  have hcomap := Ideal.comap_map_of_surjective ((Scheme.ΓSpecIso (.of S.A)).inv ≫
    (blowUpToBase (residuePoint S.A).ker).appTop).hom hsurjψ (IsLocalRing.maximalIdeal S.A)
  have hkerψ : Ideal.comap ((Scheme.ΓSpecIso (.of S.A)).inv ≫
      (blowUpToBase (residuePoint S.A).ker).appTop).hom
      (⊥ : Ideal Γ(blowUp (residuePoint S.A).ker, ⊤)) = ⊥ :=
    (RingHom.ker_eq_comap_bot _).symm.trans ((RingHom.injective_iff_ker_eq_bot _).1 hinjψ)
  rw [hkerψ, sup_bot_eq] at hcomap
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rw [hpt a] at hx
    have hmem : ((Scheme.ΓSpecIso (.of S.A)).inv ≫
        (blowUpToBase (residuePoint S.A).ker).appTop).hom a ∈
        Ideal.map ((Scheme.ΓSpecIso (.of S.A)).inv ≫
          (blowUpToBase (residuePoint S.A).ker).appTop).hom (IsLocalRing.maximalIdeal S.A) := by
      rwa [← ker_exceptionalIdeal_subschemeι_appTop S]
    exact (IsLocalRing.residue_eq_zero_iff a).2 (hcomap ▸ Ideal.mem_comap.2 hmem)
  · obtain ⟨x, hx⟩ := surjective_subschemeι_appTop_of_isZero_hgroup_one
      (exceptionalIdeal (residuePoint S.A).ker)
      (isZero_hgroup_one_exceptionalIdeal_residuePoint S) y
    obtain ⟨a, ha⟩ := hsurjψ x
    exact ⟨IsLocalRing.residue S.A a, by rwa [hpt a, ha]⟩

/-! ### The Cohen–Macaulay curve situation at the exceptional curve -/

/-- The Cohen–Macaulay curve situation given by the exceptional curve of the blowup of a rational
surface singularity at its closed point: a proper scheme of dimension one over the residue field
whose global functions are that field. -/
@[sga "7 X 2.2" "Curvetta clause"]
def cohenMacaulayCurveSituationExceptionalDivisor : CohenMacaulayCurveSituation.{u} where
  k := IsLocalRing.ResidueField S.A
  X := exceptionalDivisor (residuePoint S.A).ker
  f := exceptionalDivisorToCentre (residuePoint S.A)
  proper := isProper_exceptionalDivisorToCentre_residuePoint S.A
  dimension_one := topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two
  isIso_globalSections := isIso_globalSections_exceptionalDivisorToCentre_residuePoint S

/-- The base field of the Cohen–Macaulay curve situation at the exceptional curve is the residue
field. -/
@[simp]
theorem cohenMacaulayCurveSituationExceptionalDivisor_k :
    (cohenMacaulayCurveSituationExceptionalDivisor S).k =
      IsLocalRing.ResidueField S.A := rfl

/-- The curve of the Cohen–Macaulay curve situation at the exceptional curve is the exceptional
divisor. -/
@[simp]
theorem cohenMacaulayCurveSituationExceptionalDivisor_X :
    (cohenMacaulayCurveSituationExceptionalDivisor S).X =
      exceptionalDivisor (residuePoint S.A).ker := rfl

/-- The structure morphism of the Cohen–Macaulay curve situation at the exceptional curve is the
morphism over the centre of the blowup. -/
@[simp]
theorem cohenMacaulayCurveSituationExceptionalDivisor_f :
    (cohenMacaulayCurveSituationExceptionalDivisor S).f =
      exceptionalDivisorToCentre (residuePoint S.A) := rfl

end AlgebraicGeometry

end
