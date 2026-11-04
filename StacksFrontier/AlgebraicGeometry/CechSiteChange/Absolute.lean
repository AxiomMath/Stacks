module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Scheme
public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Scheme

/-!
# The absolute Čech complex of [Stacks, Tag 01XL] over the site of open sets

`Stacks.AlgebraicGeometry.Tag01XLDerivedIso.absoluteCechComplexPlus` is built from the Čech
complex `𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 01XL], which is
`CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))` applied to the absolute coefficient
presheaf `A ↦ (A.hom)_* (A.hom)^* ℱ` on the site `Over X`.  This file rewrites it as a Čech
complex over the site `X.Opens` of open sets of `X`, which is the site in which [Stacks, Tag 02FU]
is proved in this repository (`Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso`).

## Main results

* `Stacks.CechSiteChange.absoluteCechOpensPresheaf`: the absolute coefficient presheaf restricted
  to the open sets of `X`, with `absoluteCechOpensPresheaf_obj_obj` evaluating it:
  `V ↦ (V.ι)_* (V.ι)^* ℱ`.
* `Stacks.CechSiteChange.absoluteCechComplexOpensIso`: **the absolute Čech complex of
  [Stacks, Tag 01XL] is the Čech complex, over the site of open sets, of the family of the open
  ranges of an affine open cover, with those coefficients**, naturally in the quasi-coherent
  module.
* `Stacks.CechSiteChange.iSup_affineOpenCover_opensRange`: the open ranges of an affine open cover
  cover `X`, which is the hypothesis `⨆ i, U i = ⊤` of [Stacks, Tag 02FU].

## What remains for the fourth label of [Stacks, Tag 01XL]

Granted this file, the residue is a comparison of *coefficient presheaves on one site*:
`absoluteCechOpensPresheaf X` against
  `Stacks.CechTotalComplex.CoveringResolution.infPushforwardOpens` (for `R = X.ringCatSheaf`,
`U i = (T.f i).opensRange`), whose value at `V` is the direct image of the restriction of `ℱ` to
`V`, with sections `Γ(ℱ, W ⊓ V)` over `W`.  The two Čech complexes are then isomorphic by
functoriality of `CategoryTheory.cechComplexFunctor` in the coefficient presheaf alone — the site
and the family already agree, which is what this file arranges — and
`Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso.exists_coveringResolution` supplies the
quasi-isomorphism.

That the comparison is the *only* thing missing — that there is no site to identify and no
universe to collapse at the level of categories — is a measurement: `X.Opens` is
`TopologicalSpace.Opens X.toTopCat` by `rfl`, `X.ringCatSheaf` is a
`Sheaf (Opens.grothendieckTopology X.toTopCat) RingCat.{u}`, `SheafOfModules.{u} X.ringCatSheaf`
is `X.Modules`, and at the four equal universes `u` the functor
`Stacks.CechTotalComplex.CoveringResolution.cechDiagram X.toTopCat X.ringCatSheaf` applied to a
  module sheaf has type
`(X.Opens)ᵒᵖ ⥤ X.Modules` — the type of `(absoluteCechOpensPresheaf X).obj F`.

The structural reason the presheaves agree, and the route that avoids computing with scalar
actions: both are a `pushforward` of sheaves of modules along the *same* functor of open sets.

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` identifies `(V.ι)^*` with
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`, which is
  `SheafOfModules.pushforward` along `V.ι.opensFunctor`; and
  `AlgebraicGeometry.Scheme.Modules.pushforward V.ι` is `SheafOfModules.pushforward` along
  `Opens.map V.ι.base`.
* The composite functor of open sets is `W ↦ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W ⊓ V`, which is
  `Stacks.CechTotalComplex.CoveringResolution.infFunctor X V`, and the composite ring map is
    `Stacks.CechTotalComplex.CoveringResolution.infRestriction X R V`.
* So the comparison is assembled from `SheafOfModules.pushforwardComp`,
  `SheafOfModules.pushforwardNatIso` and `SheafOfModules.pushforwardCongr` — exactly the three
  steps of Mathlib's own `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` — rather
  than by comparing sections, which is the route that runs into the scalar-action defeq recorded
  for `restrictAppIso`.
* What is still owed on top of that is the `ULift` in
  `Stacks.CechTotalComplex.CoveringResolution.uliftSheaf`, i.e. an isomorphism
  `Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift X R ≅ 𝟭` at the equal universes `u
    = v = w = t` in which this
  application sits.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.CechSiteChange

open Stacks.AlgebraicGeometry.CechPushforwardComplex

variable (X : Scheme.{u})

/-- **The absolute Čech coefficient presheaf of [Stacks, Tag 01XL], on the site of open sets.**
Its value at an open set `V` is `(V.ι)_* (V.ι)^* ℱ`. -/
noncomputable def absoluteCechOpensPresheaf :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      ((X.Opens)ᵒᵖ ⥤ X.Modules) :=
  absoluteCechPresheaf X ⋙
    (Functor.whiskeringLeft (X.Opens)ᵒᵖ (Over X)ᵒᵖ X.Modules).obj (opensOver X).op

/-- The value of `absoluteCechOpensPresheaf` is the direct image of the inverse image along the
inclusion of the open set. -/
theorem absoluteCechOpensPresheaf_obj_obj
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (V : X.Opens) :
    ((absoluteCechOpensPresheaf X).obj F).obj (op V) =
      (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj F.obj) :=
  rfl

/-- **The open ranges of an affine open cover cover `X`** — the hypothesis of
[Stacks, Tag 02FU]. -/
theorem iSup_affineOpenCover_opensRange (T : X.AffineOpenCover.{u, u}) :
    ⨆ i, (T.f i).opensRange = ⊤ :=
  T.openCover.iSup_opensRange

/-- **The absolute Čech complex of [Stacks, Tag 01XL] is a Čech complex over the site of open
sets.**  The family is the family of open ranges of the affine open cover, and the coefficients
are `absoluteCechOpensPresheaf X`; the isomorphism is natural in the quasi-coherent module. -/
noncomputable def absoluteCechComplexOpensIso (T : X.AffineOpenCover.{u, u}) :
    absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) ≅
      absoluteCechOpensPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ (T.f i).opensRange) :=
  Functor.isoWhiskerLeft (absoluteCechPresheaf X)
    (cechComplexFunctorAffineOpenCoverIso (A := X.Modules) X T)

end Stacks.CechSiteChange
