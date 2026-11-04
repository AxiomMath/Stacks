module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction types of a smooth projective curve over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K`. The curve has *semistable reduction* if it admits a proper
model over `R` which is at-worst-nodal of relative dimension one, and *good reduction* if it
admits a proper model over `R` which is smooth.

## Main definitions

* `Stacks.Models.HasSemistableReduction` — the curve has semistable reduction.
* `Stacks.Models.HasGoodReduction` — the curve has good reduction.

## Implementation notes

The source defines semistable reduction by any one of the equivalent conditions of
[Stacks, Tag 0CDG]: a proper at-worst-nodal model exists, a minimal at-worst-nodal model exists,
every minimal model is at-worst-nodal. The definition here is the first of these conditions.
Likewise the source defines good reduction by any one of the equivalent conditions of
[Stacks, Tag 0CDI]: a proper smooth model exists, a minimal model smooth over `R` exists, every
minimal model is smooth over `R`. The definition here is the first of these conditions.

A model is `Stacks.Models.IsModel`: a flat morphism `X ⟶ Spec R`, locally of finite type and
quasi-compact, together with an isomorphism of `C` with the generic fibre over `Spec K`. Being
at-worst-nodal of relative dimension one is
`AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne`.

The standing hypotheses on `C` are: a curve (`AlgebraicGeometry.IsCurve`), smooth over `K`,
projective over `K` in the sense of `AlgebraicGeometry.IsProjective` (a closed immersion into the
projective bundle of a finite-type quasi-coherent module), and the canonical map
`K ⟶ Γ(C, 𝒪_C)` is an isomorphism. They are recorded as hypotheses of the definition, as in the
source, and do not enter the condition. A curve that is H-projective, as in
`Stacks.Models.RegularProperModelSituation`, is projective by
`AlgebraicGeometry.IsProjectiveMorphism.isProjective`.

## References

* [Stacks Project, Tag 0CDH](https://stacks.math.columbia.edu/tag/0CDH)
* [Stacks Project, Tag 0CDG](https://stacks.math.columbia.edu/tag/0CDG)
* [Stacks Project, Tag 0CDJ](https://stacks.math.columbia.edu/tag/0CDJ)
* [Stacks Project, Tag 0CDI](https://stacks.math.columbia.edu/tag/0CDI)
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace Stacks.Models

universe u

variable (R : Type u) {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Stacks Project, Tag 0CDH.** A smooth projective curve `C` over the fraction field `K` of
a discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`, has *semistable reduction* if there is a
proper model `X ⟶ Spec R` of `C` which is at-worst-nodal of relative dimension one. -/
@[stacks 0CDH "existence of a proper model of the curve that is at-worst-nodal of relative \
dimension one"]
def HasSemistableReduction {C : Scheme.{u}} (C_to_K : C ⟶ Spec (.of K))
    [IsCurve K C_to_K] [Smooth C_to_K] (_ : IsProjective C_to_K)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)] : Prop :=
  ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
    IsModel C_to_K p e ∧ IsProper p ∧ IsAtWorstNodalOfRelativeDimensionOne p

/-- **Stacks Project, Tag 0CDJ.** A smooth projective curve `C` over the fraction field `K` of
a discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`, has *good reduction* if there is a
proper model `X ⟶ Spec R` of `C` which is smooth over `R`. -/
@[stacks 0CDJ "existence of a proper smooth model of the curve"]
def HasGoodReduction {C : Scheme.{u}} (C_to_K : C ⟶ Spec (.of K))
    [IsCurve K C_to_K] [Smooth C_to_K] (_ : IsProjective C_to_K)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)] : Prop :=
  ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
    IsModel C_to_K p e ∧ IsProper p ∧ Smooth p

end Stacks.Models

end
