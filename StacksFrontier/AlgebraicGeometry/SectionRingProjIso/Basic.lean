module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# A universally closed scheme with an ample module is its own `Proj`

Let `X` be a scheme and `L` an **ample** invertible `𝒪_X`-module, and let
`S = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` be the graded section ring of Stacks Tag 01CV. Stacks
Tag 01PZ constructs the canonical morphism `r : X ⟶ Proj S`
(`Stacks.SectionRingProjMorphism.projHomOfIsAmple`), and Stacks Tag 01Q1 says it is an open
immersion with dense image. **Stacks Tag 0C6J** says that if moreover the structure morphism of
`X` over the base is universally closed, then `r` is an isomorphism.

## Relation to the relative statement

The source states Tag 0C6J relatively: `f : X ⟶ S` universally closed, `L` an `f`-ample
invertible module, and `r : X ⟶ Proj_S(⨁_{d ≥ 0} f_* L^{⊗ d})` the morphism of Lemma 01VJ. That
statement is `Stacks.RelativeAmple.isIso_relativeAmpleProjHom`, which carries the tag, in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/ProjIso.lean`. This file proves the absolute case,
over a base that is the spectrum of the degree-zero part of the section ring: for
`S = Spec A` the relative `Proj` of `⨁_d f_* L^{⊗ d}` is `Proj Γ_*(X, L)`, `r` is the morphism of
Tag 01PZ, and `f` is the composite of `r` with the structure morphism
`AlgebraicGeometry.Proj.toSpecZero` of `Proj`. The hypotheses here are

* `Stacks.Ample.IsAmple X L`, which over an affine base is `f`-ampleness (Stacks Tag 01VK,
  `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`); the morphism `r` itself —
  `Stacks.SectionRingProjMorphism.projHomOfIsAmple` — takes a proof of it as an argument; and
* universal closedness of `r ≫ Proj.toSpecZero (grading L)`, the morphism
  `X ⟶ Spec (Γ_*(X, L))₀` written as the composite it is.

No hypothesis here says, or implies, that `r` is an isomorphism: universal closedness of
`r ≫ Proj.toSpecZero` is not a consequence of `r` being an isomorphism, since
`Proj.toSpecZero` is universally closed only under a finiteness hypothesis on the graded ring.

## Main results

* `Stacks.SectionRingProjIso.isIso_projHom_of_universallyClosed_comp`: the content, for an
  arbitrary separated morphism `q` out of `Proj Γ_*(X, L)` — if `r ≫ q` is universally closed
  then `r` is an isomorphism.
* `Stacks.SectionRingProjIso.isIso_projHomOfIsAmple`: the affine-base case of Stacks Tag 0C6J,
  the same statement with `q` the structure morphism `Proj.toSpecZero`, whose separatedness is
  Mathlib's `AlgebraicGeometry.Proj.isSeparated`.

## The route

This is the argument of the source. Universal closedness descends along a separated morphism
(`AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated`, Stacks Tag 01W6), so `r` itself is
universally closed, hence a closed map, hence has closed range. Tag 01Q1 makes that range dense,
and a dense closed set is everything, so `r` is a surjective open immersion — an isomorphism by
`AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top`.

## References

* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Ample (IsAmple)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

universe u

namespace Stacks.SectionRingProjIso

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **A universally closed open immersion with dense image is an isomorphism**, for the canonical
morphism `r : X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ: if `r` followed by some separated morphism
`q` is universally closed, then `r` is an isomorphism.

Universal closedness passes from `r ≫ q` to `r` by Stacks Tag 01W6, so the range of `r` is
closed; Stacks Tag 01Q1 makes it dense and makes `r` an open immersion. -/
theorem isIso_projHom_of_universallyClosed_comp {S : Scheme.{u}} (hL : IsAmple X L)
    (q : AlgebraicGeometry.Proj (grading L) ⟶ S) [AlgebraicGeometry.IsSeparated q]
    (hf : UniversallyClosed (projHomOfIsAmple L hL ≫ q)) :
    IsIso (projHomOfIsAmple L hL) := by
  have := hf
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  have : UniversallyClosed (projHomOfIsAmple L hL) :=
    UniversallyClosed.of_comp_of_isSeparated _ q
  have hclosed : IsClosed (Set.range (projHomOfIsAmple L hL).base) :=
    (projHomOfIsAmple L hL).isClosedMap.isClosed_range
  have hdense := Stacks.SectionRingProjImmersion.denseRange_projHomOfIsAmple L hL
  refine AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (TopologicalSpace.Opens.ext ?_)
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, ← hclosed.closure_eq]
  exact hdense.closure_range

/-- **The affine-base case of Stacks Tag 0C6J.** Let `L` be an ample invertible `𝒪_X`-module and
`Γ_*(X, L)` its graded section ring. If the structure morphism of `X` over
`Spec (Γ_*(X, L))₀` — that is, the canonical morphism `r : X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ
followed by `AlgebraicGeometry.Proj.toSpecZero` — is universally closed, then `r` is an
isomorphism.

The tag itself, for a universally closed `f : X ⟶ S` over an arbitrary base and an `f`-ample `L`,
with `r` the morphism into the relative `Proj` of `⨁_{d ≥ 0} f_* L^{⊗ d}` of Lemma 01VJ, is
`Stacks.RelativeAmple.isIso_relativeAmpleProjHom`. -/
theorem isIso_projHomOfIsAmple (hL : IsAmple X L)
    (hf : UniversallyClosed
      (projHomOfIsAmple L hL ≫ AlgebraicGeometry.Proj.toSpecZero (grading L))) :
    IsIso (projHomOfIsAmple L hL) :=
  isIso_projHom_of_universallyClosed_comp L hL _ hf

end Monoidal

end Stacks.SectionRingProjIso

end
