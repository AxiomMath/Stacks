module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections

/-!
# The crossing of the two models of `Rf_*` is natural in the module

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso` of
`BaseChangeMapSections.lean` is the canonical isomorphism

> `Hⁱ(Rf_*(F[0])) ≅ Rⁱ f_* F`

between the unbounded model of the derived direct image, where the base change map `γ` of
[Stacks, Tag 0EX3] lives, and the bounded below model `CategoryTheory.Functor.rightDerivedPlus`,
where conclusions (a) and (b) of that tag, [Stacks, Tag 01XJ] and [Stacks, Tag 01XK] are stated.
It is constructed at a single module `F`, so by itself it crosses the two models only object by
object: nothing says that the crossing commutes with a morphism of modules, which is what any
argument transporting a *map* between the two spellings — rather than one object at a time —
needs.

This file says it, in both directions and with no hypothesis on `f` or on the modules: the
crossing is a natural isomorphism of the two functors `F ↦ Hⁱ(Rf_*(F[0]))` and `F ↦ Rⁱ f_* F`
from modules on `X` to modules on `Y`.

## Main results

* `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_hom_naturality`: **the crossing is
  natural in the module.** For `φ : F ⟶ G`, applying `Hⁱ(Rf_*(-[0]))` to `φ` and then crossing
  is crossing and then `Rⁱ f_*(φ)`.
* `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_inv_naturality`: the same square
  read with the inverses, which is the form a consumer rewriting out of the bounded below model
  uses.

Neither carries a hypothesis: no quasi-coherence, no finiteness, and nothing on `f`.

## Implementation notes

*All the content is one `NatTrans.naturality`.* `homologyFunctorDerivedPushforwardIso` is `Hⁱ`
applied to a component of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso`, which is a
genuine isomorphism of functors `D⁺(𝒪_X) ⥤ D(𝒪_Y)`, so its naturality square at
`(DerivedCategory.Plus.singleFunctor X.Modules 0).map φ` is already the square wanted, before
`Hⁱ` and up to three identifications that hold by `rfl` and so cost nothing in argument
position:

* `DerivedCategory.Plus.ι.map ((Plus.singleFunctor _ 0).map φ)` is
  `(DerivedCategory.singleFunctor _ 0).map φ`, because Mathlib's
  `DerivedCategory.Plus.singleFunctorιIso` is `Iso.refl`;
* `(F.rightDerivedPlus i).map φ` is `Hⁱ` of
  `Plus.ι.map (F.rightDerivedFunctorPlus.map ((Plus.singleFunctor _ 0).map φ))`, because
  `rightDerivedPlus i` is `Plus.singleFunctor _ 0 ⋙ rightDerivedFunctorPlus ⋙
  Plus.homologyFunctor _ i` and `DerivedCategory.Plus.homologyFunctor` is
  `Plus.ι ⋙ DerivedCategory.homologyFunctor`;
* the `inv` of a component `e.app K` of an isomorphism of functors is `e.inv.app K`.

*Why the `Functor.map_comp` step is a separate generic lemma.* Doing the two rewrites
on the goal itself, by `rw [← Functor.map_comp, ← Functor.map_comp]`, fails: the first reports
*did not find an occurrence of the pattern* `?H.map ?f ≫ ?H.map ?g`, together with the note that
the target is not type-correct under the `implicit` transparency level and the mismatch

> `(singleFunctor X.Modules 0).obj F` has type
> `@DerivedCategory X.Modules Scheme.Modules.instCategory …` but is expected to have type
> `@DerivedCategory (SheafOfModules (structureSheafRing X.toSheafedSpace))
> SheafOfModules.instCategory …`

— the two-spellings hazard below, reached by `rw` and by nothing else. It is not a heartbeat
failure: every variant tried compiles the module in a few seconds.
`map_comp_eq_map_comp` performs the same two rewrites at *generic* morphisms of *generic*
categories, where no spelling can intervene, and the two naturality theorems are then
applications of it: each is a single definitional-equality check between the concrete conclusion
and the goal, with no rewriting in the derived category at all.

*The two spellings of the modules on a scheme.* `X.Modules` and
`SheafOfModules.{u} (structureSheafRing _)` are `rfl`-equal types whose `Category` instances are
different terms, and `boundedDerivedPushforwardIso` is stated at the second while these
statements are at the first. As `BaseChangeMapSections.lean` and `DerivedModelCrossing.lean`
record, the crossing is free in argument position and only a `rw` sees it — which is exactly
what the failure quoted above is. Here it happens once, in the single application of
`map_comp_eq_map_comp`, and no transport appears in any statement.

*The `inv` form is proved directly, and that is a choice.* It is the naturality square of the
`hom` of `boundedDerivedPushforwardIso` — read in the other direction, which is the direction in
which that transformation is stated — so it is the same one-line application of
`map_comp_eq_map_comp` and is independent of the `hom` form. Deducing it from the
`hom` form instead, by `rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]`, also works and
costs the same; the direct proof is kept because it leaves the two theorems independent and
subjects no composite of morphisms of the unbounded derived category to a rewrite.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- A functor carries a commuting square to a commuting square. Stated at generic morphisms of
generic categories, which is the only place where the two `Functor.map_comp` rewrites go
through: on the concrete goals below `rw` fails on the two spellings of the modules on a scheme.
See this module's implementation notes. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {A B A' B' : C} {a : A ⟶ B} {b : B ⟶ B'} {c : A ⟶ A'} {d : A' ⟶ B'} (h : a ≫ b = c ≫ d) :
    H.map a ≫ H.map b = H.map c ≫ H.map d := by
  rw [← H.map_comp, ← H.map_comp, h]

variable {X Y : Scheme.{u}}

/-- **The canonical crossing of the two models of the derived direct image is natural in the
module.** For a morphism of schemes `f : X ⟶ Y` and a morphism of modules `φ : F ⟶ G` on `X`,
the degree-`i` cohomology of `Rf_*(φ[0])`, computed in the unbounded derived category, is carried
by `homologyFunctorDerivedPushforwardIso` to `Rⁱ f_* φ`, the morphism of higher direct images in
the bounded below model.

No hypothesis is needed: this is the naturality of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso`, an isomorphism
of functors, read at `(DerivedCategory.Plus.singleFunctor X.Modules 0).map φ` and pushed through
`Hⁱ`. -/
theorem homologyFunctorDerivedPushforwardIso_hom_naturality (f : X ⟶ Y)
    {F G : X.Modules} (φ : F ⟶ G) (i : ℤ) :
    (homologyFunctor Y.Modules i).map
          ((derivedPushforward f.toLRSHom.toShHom).map ((singleFunctor X.Modules 0).map φ)) ≫
        (homologyFunctorDerivedPushforwardIso f G i).hom =
      (homologyFunctorDerivedPushforwardIso f F i).hom ≫
        ((Scheme.Modules.pushforward f).rightDerivedPlus i).map φ :=
  map_comp_eq_map_comp (homologyFunctor Y.Modules i)
    ((boundedDerivedPushforwardIso f.toLRSHom.toShHom).inv.naturality
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ))

/-- **The crossing of the two models of the derived direct image, read with the inverses, is
natural in the module.** The square of
`homologyFunctorDerivedPushforwardIso_hom_naturality` with both instances of the crossing
inverted: `Rⁱ f_* φ` followed by the inverse crossing is the inverse crossing followed by the
degree-`i` cohomology of `Rf_*(φ[0])`.

This is the form in which a consumer holding a morphism between the higher direct images of the
bounded below model rewrites it into the unbounded one. Like the `hom` form it carries no
hypothesis. -/
theorem homologyFunctorDerivedPushforwardIso_inv_naturality (f : X ⟶ Y)
    {F G : X.Modules} (φ : F ⟶ G) (i : ℤ) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus i).map φ ≫
        (homologyFunctorDerivedPushforwardIso f G i).inv =
      (homologyFunctorDerivedPushforwardIso f F i).inv ≫
        (homologyFunctor Y.Modules i).map
          ((derivedPushforward f.toLRSHom.toShHom).map ((singleFunctor X.Modules 0).map φ)) :=
  map_comp_eq_map_comp (homologyFunctor Y.Modules i)
    ((boundedDerivedPushforwardIso f.toLRSHom.toShHom).hom.naturality
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
