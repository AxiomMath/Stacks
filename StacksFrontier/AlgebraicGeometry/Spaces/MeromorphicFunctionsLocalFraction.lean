module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsChartPullback

/-!
# Meromorphic functions are locally fractions, and regular functions inject into them

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The sheaf
`𝒦_F` of meromorphic functions (Stacks 0EN3) is the sheafification of the presheaf of
sectionwise localizations `U ↦ 𝒮_F(U)⁻¹𝒪_F(U)`, so nothing about a section of `𝒦_F` over a chart
is visible from the construction: it is a section of a sheafification.  This file records the
two facts about that sheafification which a local computation with meromorphic functions needs.

* **A meromorphic function is locally a fraction.**  The morphisms `W ⟶ U` of charts along which
  a section of `𝒦_F` over `U` restricts into the image of `𝒮_F(W)⁻¹𝒪_F(W)` form a covering
  sieve.  This is local surjectivity of the sheafification map.
* **A regular function is not killed by passing to meromorphic functions.**  The map
  `𝒪_F(U) ⟶ 𝒦_F(U)` is injective.  Local injectivity of a sheafification map and injectivity of
  `𝒪_F(U) ⟶ 𝒮_F(U)⁻¹𝒪_F(U)` — the regular sections being nonzerodivisors — make the composite
  locally injective, and `𝒪_F` is a sheaf, hence separated.

Together with the fact that a *regular* section becomes a **unit** in `𝒦_F` (Stacks 0EMC,
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.isUnit_toLocalizationSheaf`) these are
what turn a statement about multiplication on `𝒦_F` into a statement about regular sections of
`𝒪_F`, which is the only form in which Stacks 0EN8's hypothesis on a morphism can be used.

## Main results

* `AlgebraicGeometry.Space.imageSieve_toSheafify_localizationPresheaf_mem`: **a meromorphic
  function over a chart is, on a covering of that chart, a fraction `a/b` with `b` regular.**
* `AlgebraicGeometry.Space.injective_toMeromorphicFunctionSheaf`: **`𝒪_F(U) ⟶ 𝒦_F(U)` is
  injective.**
* `AlgebraicGeometry.Space.isRegularSection_of_injective_mul_toMeromorphicFunctionSheaf`: a
  function whose image in `𝒦_F` multiplies injectively over every chart over `U` is a regular
  section over `U`.
* `AlgebraicGeometry.Space.isUnit_toMeromorphicFunctionSheaf`: a regular section of `𝒪_F` over a
  chart is a unit in `𝒦_F` over that chart.
* `AlgebraicGeometry.Space.isUnit_chartMeromorphicFunctionPullback`: when pullbacks of
  meromorphic functions are defined for `f`, the chartwise pullback carries the image of a
  regular section to a unit.

## Implementation notes

*The universe of the sections is what makes the sheafification lemmas delicate.*  `𝒦_F` is a
sheaf of commutative rings at the universe `u` of the schemes, on a site whose objects live in
`Type (u + 1)` and whose morphisms live in `Type u`.  Mathlib's instances for local injectivity
and local surjectivity of a sheafification map are stated for a concrete category whose carriers
live in `Type (max u_site v_site)`, which here is `Type (u + 1)`, so they do not apply at
`CommRingCat.{u}` and `inferInstance` fails on them.  What does apply is
`CategoryTheory.GrothendieckTopology.W_toSheafify` together with
`AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective`, which holds for concrete
coefficients at the universe of the schemes because the site is essentially small there: a
sheafification map is a local equivalence, and a local equivalence is locally bijective.  Both
facts below are extracted that way rather than by instance search.  The factorization of
`𝒪_F ⟶ 𝒦_F` comes out of Stacks 0EMC with its topology spelled through the projections of the
small étale ringed site, which instance search does not unfold, so the local injectivity of the
sheafification map is supplied again at that spelling — as
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_commRingCat` already does for
sheafification itself.

The separatedness of `𝒪_F` on underlying sets is `CategoryTheory.Presieve.IsSheaf.isSeparated`
of the sheaf of sets underlying it, which needs the sheaf condition to be stable under the
forgetful functor of `CommRingCat`; that instance is available on this site.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN2](https://stacks.math.columbia.edu/tag/0EN2)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The regular sections of `𝒪_F` over an étale chart are nonzerodivisors in the ring of
sections over that chart. -/
theorem regularSections_le_nonZeroDivisors (U : SmallEtale B S hS F) :
    regularSections B S hS F U ≤ ((structurePresheaf B S hS F).obj (op U))⁰ := fun _ hs ↦
  mem_nonZeroDivisors_of_isRegularSectionOn_top
    (smallEtaleScheme B S hS F U).toLocallyRingedSpace _ hs

/-- **A function is not killed by passing to the sectionwise localization.**  The regular
sections over a chart are nonzerodivisors, so `𝒪_F(U) ⟶ 𝒮_F(U)⁻¹𝒪_F(U)` is injective. -/
theorem injective_toLocalizationPresheaf (U : SmallEtale B S hS F) :
    Function.Injective
      (((regularSectionsSubpresheaf B S hS F hF).toLocalizationPresheaf.app (op U)).hom) :=
  IsLocalization.injective (M := regularSections B S hS F U)
    (Localization (regularSections B S hS F U))
    (regularSections_le_nonZeroDivisors B S hS F U)

/-- **The sheafification map of the sectionwise localizations is locally injective.**

This is not found by instance search: Mathlib's instance is stated for a concrete category whose
carriers live in the universe `max u_site v_site`, which is `u + 1` here, while the sections of
`𝒦_F` live in `Type u`.  A sheafification map is in
`CategoryTheory.GrothendieckTopology.W`, and on the small étale site that class is the locally
bijective morphisms for concrete coefficients at the universe of the schemes, the site being
essentially small there. -/
theorem isLocallyInjective_toSheafify_localizationPresheaf :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS F)
      (toSheafify (SmallEtale.topology B S hS F)
        (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf) :=
  ((SmallEtale.topology B S hS F).W_toSheafify _).isLocallyInjective

/-- **The sheafification map of the sectionwise localizations is locally surjective.**  As for
`AlgebraicGeometry.Space.isLocallyInjective_toSheafify_localizationPresheaf`, this is extracted
from `CategoryTheory.GrothendieckTopology.W_toSheafify` rather than by instance search. -/
theorem isLocallySurjective_toSheafify_localizationPresheaf :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F)
      (toSheafify (SmallEtale.topology B S hS F)
        (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf) :=
  ((SmallEtale.topology B S hS F).W_toSheafify _).isLocallySurjective

/-- **A meromorphic function is locally a fraction.**  Let `x` be a section of `𝒦_F` over an
étale scheme chart `U`.  The morphisms of charts `W ⟶ U` along which `x` restricts to the image
of an element of the sectionwise localization `𝒮_F(W)⁻¹𝒪_F(W)` — that is, to a fraction `a/b`
with `a` a function and `b` a regular function on `W` — form a covering sieve of `U`.

This is local surjectivity of the sheafification map whose target is `𝒦_F`, and it is the only
access there is to a section of `𝒦_F`: `𝒦_F` is a sheafification, so a section of it over a
chart is a fraction on a covering of that chart and in general on nothing larger. -/
theorem imageSieve_toSheafify_localizationPresheaf_mem (U : SmallEtale B S hS F)
    (x : (meromorphicFunctionSheaf B S hS F hF).obj.obj (op U)) :
    Presheaf.imageSieve
        (toSheafify (SmallEtale.topology B S hS F)
          (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf) x ∈
      SmallEtale.topology B S hS F U :=
  (isLocallySurjective_toSheafify_localizationPresheaf B S hS F hF).imageSieve_mem x

/-- **The canonical map `𝒪_F ⟶ 𝒦_F` is locally injective.**  It factors as the injection of
`𝒪_F` into the sectionwise localizations followed by a sheafification map, and both are locally
injective. -/
theorem isLocallyInjective_toMeromorphicFunctionSheaf :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS F)
      (toMeromorphicFunctionSheaf B S hS F hF).hom := by
  have : (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective CommRingCat.{u} := by
    change (SmallEtale.topology B S hS F).WEqualsLocallyBijective CommRingCat.{u}
    infer_instance
  have : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS F)
      (toSheafify (smallEtaleRingedSite B S hS F hF).J
        (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf) :=
    ((smallEtaleRingedSite B S hS F hF).J.W_toSheafify _).isLocallyInjective
  exact (Presheaf.isLocallyInjective_iff_of_fac (SmallEtale.topology B S hS F)
    (RingedSite.MultiplicativeSubpresheaf.toLocalizationSheaf_hom
      (regularSectionsSubpresheaf B S hS F hF)).symm).2
    (Presheaf.isLocallyInjective_of_injective _ _ fun V ↦
      injective_toLocalizationPresheaf B S hS F hF V.unop)

/-- **A regular function is not killed by passing to meromorphic functions.**  The map
`𝒪_F(U) ⟶ 𝒦_F(U)` on the sections over an étale scheme chart is injective.

It is locally injective and `𝒪_F` is a sheaf, hence separated on underlying sets, and a locally
injective morphism out of a separated presheaf is injective. -/
theorem injective_toMeromorphicFunctionSheaf (U : SmallEtale B S hS F) :
    Function.Injective (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op U)).hom) := by
  have hsep : Presieve.IsSeparated (SmallEtale.topology B S hS F)
      ((structureSheaf B S hS F hF).obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    ((isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (SmallEtale.topology B S hS F)
        (CategoryTheory.forget CommRingCat.{u})).obj
          (structureSheaf B S hS F hF)).property).isSeparated
  exact (Presheaf.isLocallyInjective_iff_injective_of_separated _ _ hsep).1
    (isLocallyInjective_toMeromorphicFunctionSheaf B S hS F hF) (op U)

/-- **Regularity of a function is detected by multiplication on meromorphic functions.**  If the
image in `𝒦_F` of the restriction of `c` to a chart `V` over `U` multiplies injectively on
`𝒦_F(V)`, for every chart `V` over `U`, then `c` is a regular section over `U`.

Regularity over a chart is regularity on the slice étale site over it
(`AlgebraicGeometry.Space.isRegularSection_iff_isRegularSectionOnSlice`), that is injectivity of
multiplication on `𝒪_F(V)` for every chart `V` over `U`; and `𝒪_F(V) ⟶ 𝒦_F(V)` is injective. -/
theorem isRegularSection_of_injective_mul_toMeromorphicFunctionSheaf (U : SmallEtale B S hS F)
    (c : (structurePresheaf B S hS F).obj (op U))
    (h : ∀ (V : SmallEtale B S hS F) (k : V ⟶ U), Function.Injective
      fun x : (meromorphicFunctionSheaf B S hS F hF).obj.obj (op V) ↦
        x * ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op V)).hom
          ((structurePresheaf B S hS F).map k.op c)) :
    IsRegularSection B S hS F U c := by
  refine isRegularSection_of_isRegularSectionOnSlice B S hS F U c ?_
  apply PresheafOfModules.mono_of_injective
  intro V
  change Function.Injective fun r : (structurePresheaf B S hS F).obj (op V.unop.left) ↦
    r * (structurePresheaf B S hS F).map V.unop.hom.op c
  intro x y hxy
  have hmul : ∀ z : (structurePresheaf B S hS F).obj (op V.unop.left),
      (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op V.unop.left)).hom)
          (z * (structurePresheaf B S hS F).map V.unop.hom.op c) =
        (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op V.unop.left)).hom) z *
          (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op V.unop.left)).hom)
            ((structurePresheaf B S hS F).map V.unop.hom.op c) := fun z ↦ map_mul _ _ _
  refine injective_toMeromorphicFunctionSheaf B S hS F hF V.unop.left
    (h V.unop.left V.unop.hom ?_)
  exact ((hmul x).symm.trans (congrArg
    (fun z ↦ (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op V.unop.left)).hom) z)
      hxy)).trans (hmul y)

/-- **A regular section of `𝒪_F` is a unit in `𝒦_F`.**  This is the inversion clause of
Stacks 0EMC for the multiplicative subpresheaf of regular sections. -/
theorem isUnit_toMeromorphicFunctionSheaf (U : SmallEtale B S hS F)
    (b : (structurePresheaf B S hS F).obj (op U)) (hb : IsRegularSection B S hS F U b) :
    IsUnit (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op U)).hom b) :=
  RingedSite.MultiplicativeSubpresheaf.isUnit_toLocalizationSheaf
    (regularSectionsSubpresheaf B S hS F hF) (op U) ⟨b, hb⟩

/-- **The chartwise pullback of meromorphic functions carries the image of a regular section to
a unit.**  When pullbacks of meromorphic functions are defined for `f` (Stacks 0EN8), a regular
section `b` of `𝒪_Y` over the chart `V` of a diagram of charts pulls back to a regular section
of `𝒪_X` over the chart `U`, which is a unit in `𝒦_X(U)`.

This is the step at which Stacks 0EN8's hypothesis is consumed: it is a statement about regular
sections of the structure sheaves, and this turns it into invertibility in the sheaves of
meromorphic functions. -/
theorem isUnit_chartMeromorphicFunctionPullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (b : (structurePresheaf B S hS Y.1).obj (op d.V))
    (hb : IsRegularSection B S hS Y.1 d.V b) :
    IsUnit (chartMeromorphicFunctionPullback B S hS f hf d
      (((toMeromorphicFunctionSheaf B S hS Y.1 Y.2).hom.app (op d.V)).hom b)) := by
  rw [chartMeromorphicFunctionPullback_toMeromorphicFunctionSheaf]
  exact isUnit_toMeromorphicFunctionSheaf B S hS X.1 X.2 d.U _ (hf d b hb)

end AlgebraicGeometry.Space

end
