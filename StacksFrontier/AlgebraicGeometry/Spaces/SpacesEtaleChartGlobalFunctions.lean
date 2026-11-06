module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections

/-!
# The spaces-étale structure sheaf along the comparison is the small étale one

Let `X` be an algebraic space over a scheme `S`.  The comparison functor of [Stacks, Tag 03G1]
`AlgebraicGeometry.Space.comparisonFunctor` carries an étale scheme chart `W` of `X` to the
algebraic space `yoneda.obj W` étale over `X`, and the structure sheaf of the spaces-étale site
assigns to that object the ring `AlgebraicGeometry.Space.globalFunctions'` of global regular
functions of the *algebraic space* `yoneda.obj W`.  This file identifies that ring with
`Γ(W, 𝒪_W)`, the value of the small étale structure presheaf at `W`, and assembles the
identifications into an isomorphism of presheaves of rings on the small étale site.

The point is that the small étale site of a *representable* algebraic space has a terminal
object — the identity chart `AlgebraicGeometry.Space.idEtaleChart` — so a compatible family of
regular functions on its étale charts is nothing but its value at the identity chart.  Global
regular functions are the sections of the structure presheaf, and sections of a presheaf of
sets on a category with a terminal object are the sections there
(`CategoryTheory.Presheaf.sectionsEquivObjOfIsTerminal`); evaluation at one object of a subring
of a product is a ring homomorphism, so the bijection is a ring isomorphism for free.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv`: the ring isomorphism between the
  global regular functions of the algebraic space represented by an object `U` of the big fppf
  site over `S` and the ring `Γ(U, 𝒪_U)` of global regular functions of `U` itself.
* `AlgebraicGeometry.Space.comparisonGlobalFunctionsRingEquiv`: the same isomorphism read at the
  image of an étale chart `W` of `X` under the comparison functor of [Stacks, Tag 03G1], so with
  `Γ(chartScheme W, ⊤)` on the right.
* `AlgebraicGeometry.Space.comparisonStructureSheafIso`: **the restriction of the spaces-étale
  structure sheaf of `X` along the comparison functor is the universe lift
  `AlgebraicGeometry.Space.liftedStructurePresheaf` of the small étale structure presheaf**, as
  presheaves of commutative rings in the universe `u + 1` of the sections of the spaces-étale
  structure sheaf.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsMap_val_chart`: pullback of global regular functions
  along a morphism of algebraic spaces, evaluated at an étale chart of the source, is pullback
  of global sections of schemes along any morphism of charts lying over it.  This is the
  naturality input, and it holds for an arbitrary pair of charts related by such a morphism.

## Implementation notes

**`AlgebraicGeometry.Space.globalFunctionsMap` is not definitionally precomposition on the
étale charts**, which is why `globalFunctionsMap_val_chart` is proved rather than stated as a
`rfl`-lemma.  Pullback of global functions is defined through
`AlgebraicGeometry.Space.globalFunctionsChartEquiv`, the atlas comparison with compatible
families on *all* scheme charts, where precomposition *is* definitional
(`AlgebraicGeometry.Space.chartFunctionsMap`).  The proof therefore crosses to the all-chart
description, uses the compatibility of the family there with the morphism of scheme charts
underlying the given morphism of étale charts, and crosses back; both crossings are the
defining property of `globalFunctionsChartEquiv`.  Stating the lemma for two *unrelated* charts
joined by a morphism over the given morphism of spaces — rather than for a chart and its image
— is what makes it applicable to the identity charts of two different representable spaces,
which is the only case used here.

**The right-hand side of the presheaf isomorphism is
`AlgebraicGeometry.Space.liftedStructurePresheaf`, not a composite with a universe-lift functor
on `CommRingCat`.**  `Mathlib` has `GrpCat.uliftFunctor`, `CommGrpCat.uliftFunctor`,
`ModuleCat.uliftFunctor` and `CommAlgCat.uliftFunctor` but no `CommRingCat.uliftFunctor`, and
this development already carries the object-wise lift of the small étale structure presheaf
under the name `liftedStructurePresheaf`, introduced for the étale local rings of
[Stacks, Tag 04KG]; the comparison is stated against it so that it composes with what is
already there instead of introducing a second spelling of the same presheaf.

**The pointwise isomorphism is stated onto `Γ(chartScheme W, ⊤)` itself, not onto a `ULift` of
it.**  A `RingEquiv` is universe-polymorphic, so an isomorphism between the `Type (u + 1)` of
compatible families and the `Type u` of global sections of a scheme is a legal and strictly
more informative statement; the `ULift` appears only in the presheaf-level isomorphism, where
both sides must live in one category.

No `@[stacks]` attribute is claimed.  [Stacks, Tag 03G1] is registered on
`AlgebraicGeometry.Space.comparisonFunctor` and its companions, and the content here is the
comparison of the two structure sheaves across it, which the source does not separate out.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Pullback of global functions, read at an étale chart -/

/-- Pullback of global regular functions along a morphism `f : V ⟶ U` of algebraic spaces,
evaluated at an étale chart `WV` of `V`, is pullback of global sections of schemes along any
morphism `ψ` of the underlying objects of the big fppf site which lies over `f` as a morphism
from `WV` to an étale chart `WU` of `U`.

The hypothesis `hψ` is exactly the statement that `ψ` is a morphism of scheme charts from the
chart `WV` of `V` pushed forward along `f` to the chart `WU` of `U`. -/
theorem globalFunctionsMap_val_chart {U V : AlgebraicSpaces B S hS} (f : V ⟶ U)
    (WU : SmallEtale B S hS U.obj) (WV : SmallEtale B S hS V.obj)
    (ψ : (SmallEtale.toOver B S hS V.obj).obj WV ⟶ (SmallEtale.toOver B S hS U.obj).obj WU)
    (hψ : yoneda.map ψ ≫ ((SmallEtale.inclusion B S hS U.obj).obj WU).hom =
      ((SmallEtale.inclusion B S hS V.obj).obj WV).hom ≫ f.hom)
    (s : globalFunctions' B S hS U.obj) :
    (globalFunctionsMap B S hS f s).val (op WV) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom (s.val (op WU)) := by
  have key : ∀ (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.obj)
      (t : globalFunctions' B S hS Y.obj),
      ((globalFunctionsChartEquiv B S hS Y).val t).val
        (op ((SmallEtale.inclusion B S hS Y.obj).obj W)) = t.val (op W) :=
    fun Y W t => congrFun (congrArg Subtype.val ((globalFunctionsChartEquiv B S hS Y).2 t)) (op W)
  let h : (CostructuredArrow.map f.hom).obj ((SmallEtale.inclusion B S hS V.obj).obj WV) ⟶
      (SmallEtale.inclusion B S hS U.obj).obj WU := CostructuredArrow.homMk ψ hψ
  have hcompat : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom
        (((globalFunctionsChartEquiv B S hS U).val s).val
          (op ((SmallEtale.inclusion B S hS U.obj).obj WU))) =
      ((globalFunctionsChartEquiv B S hS U).val s).val
        (op ((CostructuredArrow.map f.hom).obj
          ((SmallEtale.inclusion B S hS V.obj).obj WV))) :=
    ((globalFunctionsChartEquiv B S hS U).val s).property h.op
  rw [← key V WV, globalFunctionsMap_chart]
  show ((globalFunctionsChartEquiv B S hS U).val s).val
    (op ((CostructuredArrow.map f.hom).obj
      ((SmallEtale.inclusion B S hS V.obj).obj WV))) = _
  rw [← hcompat, key U WU s]

/-! ### Global functions on a representable algebraic space -/

/-- **Global regular functions on the algebraic space represented by an object `U` of the big
fppf site over `S` are the global regular functions of `U` itself.**

The small étale site of `yoneda.obj U` has the identity chart as a terminal object
(`AlgebraicGeometry.Space.isTerminalIdEtaleChart`), so a compatible family of regular functions
on its étale charts is determined by, and determines, its value at the identity chart; and
the ring structure on global functions is that of a subring of a product, so evaluation at one
chart is a ring homomorphism. -/
def globalFunctionsYonedaRingEquiv (U : BigFppfOver B S hS) :
    globalFunctions' B S hS (yoneda.obj U) ≃+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  { CategoryTheory.Presheaf.sectionsEquivObjOfIsTerminal (isTerminalIdEtaleChart B S hS U)
      (structurePresheaf B S hS (yoneda.obj U) ⋙ forget CommRingCat.{u}) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- The isomorphism of `AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv` is evaluation
at the identity chart. -/
theorem globalFunctionsYonedaRingEquiv_apply (U : BigFppfOver B S hS)
    (s : globalFunctions' B S hS (yoneda.obj U)) :
    globalFunctionsYonedaRingEquiv B S hS U s = s.val (op (idEtaleChart B S hS U)) := rfl

variable (X : AlgebraicSpaces B S hS)

/-- **The global regular functions of the algebraic space attached to an étale chart `W` of `X`
by the comparison functor of [Stacks, Tag 03G1] are the global regular functions of the scheme
underlying `W`.**

This is `AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv` at the object of the big fppf
site underlying `W`: the algebraic space underlying `(comparisonFunctor B S hS X).obj W` is the
presheaf represented by that object. -/
def comparisonGlobalFunctionsRingEquiv (W : SmallEtale B S hS X.obj) :
    globalFunctions' B S hS
        ((SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj W)).obj ≃+*
      Γ(chartScheme W, ⊤) :=
  globalFunctionsYonedaRingEquiv B S hS ((SmallEtale.toOver B S hS X.obj).obj W)

/-! ### The comparison of structure sheaves -/

/-- **Along the comparison functor of [Stacks, Tag 03G1] the structure sheaf of the
spaces-étale site of `X` is the universe lift of the structure presheaf of the small étale site
of `X`.**

At an étale chart `W` the component is
`AlgebraicGeometry.Space.comparisonGlobalFunctionsRingEquiv` followed by the universe lift, and
the naturality square is `AlgebraicGeometry.Space.globalFunctionsMap_val_chart` applied to the
identity charts of the two representable algebraic spaces involved, the connecting morphism of
charts being the one `W` is mapped along. -/
def comparisonStructureSheafIso :
    (comparisonFunctor B S hS X).op ⋙ (SpacesEtale.structureSheaf B S hS X).obj ≅
      liftedStructurePresheaf B S hS X.obj :=
  NatIso.ofComponents
    (fun W => ((comparisonGlobalFunctionsRingEquiv B S hS X W.unop).trans
      ULift.ringEquiv.symm).toCommRingCatIso)
    (fun {W W'} g => by
      refine CommRingCat.hom_ext (RingHom.ext fun s => ULift.ext ?_)
      refine globalFunctionsMap_val_chart B S hS
        ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map g.unop))
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.obj).obj W.unop))
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.obj).obj W'.unop))
        ((SmallEtale.toOver B S hS X.obj).map g.unop) ?_ s
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end AlgebraicGeometry.Space

end
