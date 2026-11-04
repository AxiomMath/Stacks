module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingFamily
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# Stable families of curves given by morphisms of schemes

A morphism of schemes `p : X ⟶ S` which is flat, proper, locally of finite presentation and of
relative dimension at most one, with `S` in the chosen big fppf site, is a family of curves in the
sense of Stacks 0D4Z (`AlgebraicGeometry.curveFamilyOfFiberDimensionLE`). This file records when
that family is stable (Stacks 0E75). This is the reading of "a stable family of curves over `R`
with generic fibre `C`" in Stacks 0E8D, 0E97 and 0E98.

## Main definitions

* `AlgebraicGeometry.IsCurveFamilyOfSchemesWith`: a morphism of schemes to a scheme of the site
  is a family of curves with a given property.
* `AlgebraicGeometry.IsStableFamilyOfSchemes` and
  `AlgebraicGeometry.IsStableFamilyOfSchemesOfGenus`: it is a stable family of curves, of genus
  `g`.

## Main results

* `AlgebraicGeometry.IsCurveFamilyOfSchemesWith.isAtWorstNodalOfRelativeDimensionOne`: a
  prestable family of curves given by a morphism of schemes is at-worst-nodal of relative
  dimension one.
* `Stacks.Models.hasSemistableReduction_of_isStableFamilyOfSchemes`: the implication (2) ⟹ (1)
  of Stacks 0E8D. A smooth projective curve over the fraction field of a discrete valuation ring
  `R` which is the generic fibre of a stable family of curves over `R` has semistable reduction.

## Implementation notes

The family of curves is `AlgebraicGeometry.curveFamilyOfFiberDimensionLE`, which bounds the local
dimension of every fibre rather than the dimension of the source
(`AlgebraicGeometry.curveFamilyOfProperFlatMorphism`), so it applies over a discrete valuation
ring. The scheme `X` lies in the site because it is of finite type over `S`.

## References

* [Stacks Project, Tag 0E8D](https://stacks.math.columbia.edu/tag/0E8D)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0CDH](https://stacks.math.columbia.edu/tag/0CDH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A morphism of schemes `p : X ⟶ S`, with `S` in the big fppf site, is a family of curves with
the property `P` when it is flat, proper, locally of finite presentation, with fibres of local
dimension at most one at every point, and the family of curves it defines has `P`. -/
def IsCurveFamilyOfSchemesWith (P : ObjectProperty (CurveFamily B hZ)) {X S : Scheme.{u}}
    (p : X ⟶ S) (hS : B.Contains S) : Prop :=
  ∃ (hflat : Flat p) (hproper : IsProper p) (hlfp : LocallyOfFinitePresentation p)
    (hfib : ∀ x, topologicalKrullDimAt (p.fiber (p x)) (p.asFiber x) ≤ 1),
    P (curveFamilyOfFiberDimensionLE B hZ
      (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS) hS p)
      hflat hproper hlfp hfib)

/-- A stable family of curves given by a morphism of schemes (Stacks 0E75): a morphism of
schemes to a scheme of the big fppf site whose family of curves is stable. -/
abbrev IsStableFamilyOfSchemes {X S : Scheme.{u}} (p : X ⟶ S) (hS : B.Contains S) : Prop :=
  IsCurveFamilyOfSchemesWith B hZ (IsStableCurveFamily B hZ) p hS

/-- A stable family of curves of genus `g` given by a morphism of schemes: a morphism of
schemes to a scheme of the big fppf site whose family of curves `f` is stable with `R¹f_*𝒪_X`
locally free of rank `g`. -/
abbrev IsStableFamilyOfSchemesOfGenus (g : ℕ) {X S : Scheme.{u}} (p : X ⟶ S)
    (hS : B.Contains S) : Prop :=
  IsCurveFamilyOfSchemesWith B hZ (IsStableCurveFamilyOfGenus B hZ g) p hS

variable {B hZ}

/-- A family of curves given by a morphism of schemes is proper. -/
theorem IsCurveFamilyOfSchemesWith.isProper {P : ObjectProperty (CurveFamily B hZ)}
    {X S : Scheme.{u}} {p : X ⟶ S} {hS : B.Contains S}
    (h : IsCurveFamilyOfSchemesWith B hZ P p hS) : IsProper p :=
  h.2.1

/-- A prestable family of curves given by a morphism of schemes is at-worst-nodal of relative
dimension one. -/
theorem IsCurveFamilyOfSchemesWith.isAtWorstNodalOfRelativeDimensionOne
    {P : ObjectProperty (CurveFamily B hZ)} (hP : ∀ F, P F → IsPrestableCurveFamily B hZ F)
    {X S : Scheme.{u}} {p : X ⟶ S} {hS : B.Contains S}
    (h : IsCurveFamilyOfSchemesWith B hZ P p hS) : IsAtWorstNodalOfRelativeDimensionOne p := by
  obtain ⟨_, _, _, _, hst⟩ := h
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget _).1 (hP _ hst).1

/-- A stable family of curves of genus `g` given by a morphism of schemes is a stable family of
curves. -/
theorem IsStableFamilyOfSchemesOfGenus.isStableFamilyOfSchemes {g : ℕ} {X S : Scheme.{u}}
    {p : X ⟶ S} {hS : B.Contains S} (h : IsStableFamilyOfSchemesOfGenus B hZ g p hS) :
    IsStableFamilyOfSchemes B hZ p hS := by
  obtain ⟨h₁, h₂, h₃, h₄, hst⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, hst.1⟩

end AlgebraicGeometry

namespace Stacks.Models

open _root_.AlgebraicGeometry

variable (R : Type u) {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Let `C` be a smooth projective curve over the fraction field `K` of a discrete valuation ring
`R` with `K = H⁰(C, 𝒪_C)`. If `C` is the generic fibre of a model `X ⟶ Spec R` which is a stable
family of curves, then `C` has semistable reduction. -/
theorem hasSemistableReduction_of_isStableFamilyOfSchemes (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (C_to_K : C ⟶ Spec (.of K)) [IsCurve K C_to_K] [Smooth C_to_K] (hC : IsProjective C_to_K)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)]
    (h : ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel C_to_K p e ∧ IsStableFamilyOfSchemes B hZ p hR) :
    HasSemistableReduction R C_to_K hC := by
  obtain ⟨X, p, e, hmod, hst⟩ := h
  exact ⟨X, p, e, hmod, hst.isProper,
    hst.isAtWorstNodalOfRelativeDimensionOne fun _ hF ↦ hF.1⟩

end Stacks.Models

end
