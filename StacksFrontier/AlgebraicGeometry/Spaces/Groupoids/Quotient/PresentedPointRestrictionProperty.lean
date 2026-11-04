module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentedChartFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasArrowSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackPresentedSaturation
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange

/-!
# From a presented point of a quotient stack to the source of the restriction

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site and let `g : U' ⟶ U` be a morphism out of the algebraic space a
scheme `V` of the site represents. The converse half of **Stacks 06PJ** has to turn a relative
property of the 1-morphism `𝒮_V ⟶ [U/R]` that `g` presents into the same property of the source
`R' ⟶ U'` of the restriction of `(U, R, s, t, c)` along `g`.

This file performs that passage, in two independent halves.

The first produces the relative property of the presented 1-morphism from a chart: a chart
`f : 𝒮_W ⟶ [U/R]` refined along a surjective, flat, locally finitely presented `b : V ⟶ W`
is 2-isomorphic to the 1-morphism presented by a point of the object space, so the relative
property of **Stacks 045B** for the refinement transfers to it.

The second runs the source's own argument for the restriction: the restricted groupoid has `U'`
as its object space, so the 1-morphism it presents is the canonical projection of its *own*
quotient stack up to equivalence; **Stacks 046T** identifies that quotient stack with `[U/R]`, and
**Stacks 04M9** followed by **Stacks 045C** reads the property off the source map of the restricted
groupoid, which is the one wanted.

## Main definitions

* `AlgebraicGeometry.Stack.liftedChartCoverIso` and
  `AlgebraicGeometry.Stack.presentedSchemeMapIsoSchemePresentationHom`: the two bookkeeping
  2-isomorphisms that identify a refined chart, read down the universe lift, with the composite of
  the refinement and the chart, and the 1-morphism presented by a point of the object space with
  the presentation 1-morphism of Stacks 026O at that point. Both hold because the two sides agree
  at the identity point of the slice, which by **Stacks 04SS** is all a 1-morphism out of a slice
  depends on.
* `AlgebraicGeometry.Stack.presentedSchemeMapQuotientStackMapIso` and
  `AlgebraicGeometry.Stack.schemePresentationHomQuotientStackMapIso`: the compatibility of the
  presented 1-morphism with the 1-morphism of quotient stacks of **Stacks 046Q** induced by a
  morphism of groupoids.

## Main results

* `AlgebraicGeometry.Stack.chartRelativeProperty_schemePresentationHom`: the first half. A chart
  refined by a cover, identified with a presented point, hands its relative property to the
  presentation 1-morphism at that point.
* `AlgebraicGeometry.Stack.relativeProperty_quotientStackProjectionHom_of_schemePresentationHom`:
  if the object space of the groupoid *is* the algebraic space of `V`, the 1-morphism presented by
  the corresponding point is the canonical projection of Stacks 044R up to equivalence, so the
  relative property passes to the projection.
* `AlgebraicGeometry.Stack.prop_source_of_relativeProperty_quotientStackProjectionHom`:
  **Stacks 04M9 against Stacks 045C.** Every relative property of the canonical projection
  `π : S_U ⟶ [U/R]` is a property of the source map `s`, with nothing carried: the arrow space is
  a 2-fibre product of `π` with itself with first leg `s`, and the projection is representable by
  algebraic spaces unconditionally.

## Implementation notes

`AlgebraicGeometry.Stack.associatedMap_id`, `liftedSpaceStackMap_comp` and
`liftedSpaceStackMap_id` are recorded here because the second half needs them and nothing else
does: the library had only `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_id`, a
2-isomorphism, whereas identifying the presented 1-morphism of a restriction with the projection
of its quotient stack needs the strict equality — the comparison 1-morphism is the one of
`AlgebraicGeometry.Stack.liftedSpaceStackMap` at an `eqToHom`, and it has to be *inverted*, which
is a composition of two of those and an identity.

`AlgebraicGeometry.Stack.ChartRelativeProperty` is the condition of Stacks 03YK written out for a
1-morphism whose source is a slice of the site — morphisms in `u` — and whose target is a quotient
stack — morphisms in `u + 1`. Every transport of it here is an instance of **Stacks 0457** in the
form `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, which states that theorem with the
four categories of the square in independent universes; no representability witness is consumed
anywhere, because that form of Stacks 0457 needs none.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04SS](https://stacks.math.columbia.edu/tag/04SS)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u t

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-! ### Functoriality of the 1-morphism attached to a map of presheaves -/

section Functoriality

attribute [local implicit_reducible] CategoryTheory.BasedFunctor.comp

/-- **Stacks 0458 at an identity.** The 1-morphism attached to the identity of a presheaf on the
big fppf site of `S` *is* the identity: it leaves the base object of a point alone and acts on the
fibre by the identity, and a 1-morphism into the category attached to a presheaf is determined by
its action on objects.

This strengthens `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_id` from a
2-isomorphism to an equality, which is what the inverse of an `eqToHom` comparison needs. -/
theorem associatedMap_id (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    (associatedMap C S hS (𝟙 F)).1 = 𝟙 (fibredCategory C S hS F) := by
  refine hom_ext_of_obj C S hS fun x => ?_
  rw [associatedMap_obj]
  rfl

/-- **Stacks 0458 at the universe-raised categories of elements, functorially.** The 1-morphism of
universe lifts attached to a composite of maps of algebraic spaces over `S` is the composite of the
two attached 1-morphisms.

Nothing is carried beyond `AlgebraicGeometry.Stack.associatedMap_comp`: the universe lift up
followed by the universe lift down is the identity functor on the nose, so the inner pair of lifts
of the composite cancels definitionally. -/
theorem liftedSpaceStackMap_comp {X Y Z : AlgebraicSpaces C S hS}
    (a : X.obj ⟶ Y.obj) (b : Y.obj ⟶ Z.obj) :
    liftedSpaceStackMap (X := X) (Y := Y) a ≫ liftedSpaceStackMap (X := Y) (Y := Z) b
      = liftedSpaceStackMap (X := X) (Y := Z) (a ≫ b) := by
  unfold liftedSpaceStackMap
  rw [associatedMap_comp]
  rfl

/-- **Stacks 0458 at the universe-raised categories of elements, at an identity.** -/
theorem liftedSpaceStackMap_id (X : AlgebraicSpaces C S hS) :
    liftedSpaceStackMap (X := X) (Y := X) (𝟙 X.obj) = 𝟙 (liftedSpaceStack X) := by
  unfold liftedSpaceStackMap
  rw [associatedMap_id]
  rfl

end Functoriality

/-- The 1-morphism of universe lifts attached to an identification of two algebraic spaces over `S`
is an equivalence of the underlying categories: at a reflexivity proof it is the identity by
`AlgebraicGeometry.Stack.liftedSpaceStackMap_id`. -/
theorem isEquivalence_liftedSpaceStackMap_eqToHom
    (X Y : AlgebraicSpaces C S hS) (e : X = Y) :
    Functor.IsEquivalence
      (liftedSpaceStackMap (X := X) (Y := Y) (eqToHom e).hom).hom.toFunctor := by
  subst e
  have h : (liftedSpaceStackMap (X := X) (Y := X) (eqToHom (rfl : X = X)).hom).hom.toFunctor
      = 𝟭 (liftedSpaceStack X).val.obj :=
    congrArg (fun k : liftedSpaceStack X ⟶ liftedSpaceStack X => k.hom.toFunctor)
      (liftedSpaceStackMap_id X)
  exact Functor.isEquivalence_of_iso (eqToIso h).symm

/-! ### Two bookkeeping 2-isomorphisms -/

/-- **A chart refined by a cover, read down the universe lift, is the composite.** The composite
`S_V ⟶ S_W ⟶ [U/R]` of universe-raised categories of elements, precomposed with the equivalence
`AlgebraicGeometry.Stack.schemeStackLift` from the slice of the site over `V`, is 2-isomorphic to
the chart precomposed with the refinement.

Both sides send the identity point of the slice over `V` to the object the chart names at `b`, so
this is **Stacks 04SS** in the form
`AlgebraicGeometry.Stack.schemePointIsoOfFiberIso` at the identity comparison. -/
noncomputable def liftedChartCoverIso {G : GroupoidInAlgebraicSpaces C S hS A}
    {V W : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G) (b : V ⟶ W) :
    BasedFunctor.comp (schemeStackLift C S hS V)
        (liftedSpaceStackMap
          (X := Space.representedAlgebraicSpace C S hS V)
          (Y := Space.representedAlgebraicSpace C S hS W) (yoneda.map b) ≫
          liftedChart f).hom ≅
      BasedFunctor.comp (⟨Over.map b, rfl⟩ :
        (schemeFibredCategory C S hS V).val ⥤ᵇ (schemeFibredCategory C S hS W).val) f :=
  schemePointIsoOfFiberIso (isFiberedInGroupoids_quotientStack G) _ _ (Iso.refl _)

/-- **The 1-morphism presented by a point of the object space is the presentation 1-morphism of
Stacks 026O at that point.** Both name the object of `[U/R]` that the point names at the identity,
so this is **Stacks 04SS** at the identity comparison. -/
noncomputable def presentedSchemeMapIsoSchemePresentationHom
    {G : GroupoidInAlgebraicSpaces C S hS A} {V : BigFppfOver C S hS}
    (α : yoneda.obj V ⟶ G.objects.obj) :
    presentedSchemeMap G α ≅ schemePresentationHom α :=
  schemePointIsoOfFiberIso (isFiberedInGroupoids_quotientStack G) _ _ (Iso.refl _)

/-! ### Transports of the chart condition of Stacks 03YK -/

/-- **Stacks 0457 for the chart condition, along a 2-isomorphism.** Two 2-isomorphic 1-morphisms
from the slice of the site over `V` into a quotient stack satisfy the condition of Stacks 03YK at
`P` together. -/
theorem chartRelativeProperty_congr_twoIso
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    {G : GroupoidInAlgebraicSpaces C S hS A} {V : BigFppfOver C S hS}
    {f f' : (schemeFibredCategory C S hS V).val ⥤ᵇ quotientStack G} (e : f ≅ f')
    (h : ChartRelativeProperty C S hS P f) :
    ChartRelativeProperty C S hS P f' := by
  exact @relativeProperty_of_equivalences C S hS
    (schemeFibredCategory C S hS V) (schemeFibredCategory C S hS V)
    (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    P f' f (BasedFunctor.id (schemeFibredCategory C S hS V).val)
    (BasedFunctor.id (quotientStack G)) e inferInstance inferInstance h

/-- **Stacks 0457 for the chart condition, across an equivalence of the target.** If the composite
of a 1-morphism `𝒮_V ⟶ [U'/R']` with an equivalence `[U'/R'] ⟶ [U/R]` satisfies the condition of
Stacks 03YK at `P`, then so does the 1-morphism itself. -/
theorem chartRelativeProperty_of_comp_equivalence
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    {H G : GroupoidInAlgebraicSpaces C S hS A} {V : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS V).val ⥤ᵇ quotientStack H)
    (k : BasedFunctor (quotientStack H) (quotientStack G))
    (hk : Functor.IsEquivalence k.toFunctor)
    (h : ChartRelativeProperty C S hS P (BasedFunctor.comp f k)) :
    ChartRelativeProperty C S hS P f := by
  exact @relativeProperty_of_equivalences C S hS
    (schemeFibredCategory C S hS V) (schemeFibredCategory C S hS V)
    (CatFiberedInGroupoids.mk (quotientStack H) (isFiberedInGroupoids_quotientStack H))
    (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    P f (BasedFunctor.comp f k) (BasedFunctor.id (schemeFibredCategory C S hS V).val) k
    (Iso.refl _) inferInstance hk h

/-! ### The first half: the relative property of a presented point -/

/-- **Stacks 045B for a chart refined by a cover, read at the presented point.** Let `P` be a
property of morphisms of algebraic spaces over `S` stable under base change, local on the target
for the fppf precoverage and stable under composition. Let `f : 𝒮_W ⟶ [U/R]` be a chart
representable by algebraic spaces satisfying the condition of Stacks 03YK at `P`, let
`b : V ⟶ W` be a morphism of the site whose morphism of represented algebraic spaces has `P`, and
suppose the 1-morphism presented by a point `α : h_V ⟶ U` of the object space is 2-isomorphic to
the refined chart. Then the presentation 1-morphism of Stacks 026O at `α` satisfies the condition
of Stacks 03YK at `P`.

The relative property of the refinement is
`AlgebraicGeometry.Stack.hasRelativeProperty_liftedChart_comp_cover` at the morphism universe of
the quotient stack, and **Stacks 0457** brings it down to the slice along
`AlgebraicGeometry.Stack.schemeStackLift`; the 2-isomorphism of the hypothesis is what makes the
two sides of that crossing meet. -/
theorem chartRelativeProperty_schemePresentationHom
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    [P.IsStableUnderComposition]
    {G : GroupoidInAlgebraicSpaces C S hS A} {V W : BigFppfOver C S hS}
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS f)
    (hP : ChartRelativeProperty C S hS P f)
    (b : V ⟶ W)
    (hb : P (ObjectProperty.homMk (yoneda.map b) :
      Space.representedAlgebraicSpace C S hS V ⟶
        Space.representedAlgebraicSpace C S hS W))
    (α : yoneda.obj V ⟶ G.objects.obj)
    (e : presentedSchemeMap G α ≅ BasedFunctor.comp (⟨Over.map b, rfl⟩ :
        (schemeFibredCategory C S hS V).val ⥤ᵇ (schemeFibredCategory C S hS W).val) f) :
    ChartRelativeProperty C S hS P (schemePresentationHom α) :=
  relativeProperty_of_equivalences C S hS P
    (𝒳' := schemeFibredCategory C S hS V)
    (𝒳 := liftedSpaceStack (Space.representedAlgebraicSpace C S hS V))
    (𝒴' := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (𝒴 := CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (schemePresentationHom α)
    (liftedSpaceStackMap
      (X := Space.representedAlgebraicSpace C S hS V)
      (Y := Space.representedAlgebraicSpace C S hS W) (yoneda.map b) ≫ liftedChart f).hom
    (schemeStackLift C S hS V) (BasedFunctor.id (quotientStack G))
    (liftedChartCoverIso f b ≪≫ e.symm ≪≫ presentedSchemeMapIsoSchemePresentationHom α)
    (hasRelativeProperty_liftedChart_comp_cover.{u, t} P f hf hP b hb)

/-! ### The second half: from a presented point to the source of the groupoid -/

/-- **The presented 1-morphism of a groupoid whose object space is represented is its canonical
projection.** If the object space of `(U, R, s, t, c)` is the algebraic space of a scheme `V` of
the site, and the presentation 1-morphism of Stacks 026O at the corresponding point of the object
space satisfies the condition of Stacks 03YK at `P`, then so does the canonical projection
`π : S_U ⟶ [U/R]` of **Stacks 044R**.

The crossing from the slice up to the morphism universe of the quotient stack is
`AlgebraicGeometry.Stack.relativeProperty_liftedChart`, after which the two 1-morphisms differ by
the 1-morphism of universe lifts attached to the identification of the object space with the
algebraic space of `V`, which is an equivalence with a strict inverse by
`AlgebraicGeometry.Stack.liftedSpaceStackMap_comp` and `liftedSpaceStackMap_id`. -/
theorem relativeProperty_quotientStackProjectionHom_of_schemePresentationHom
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    {H : GroupoidInAlgebraicSpaces C S hS A} {V : BigFppfOver C S hS}
    (e : H.objects = Space.representedAlgebraicSpace C S hS V)
    (h : ChartRelativeProperty C S hS P
      (schemePresentationHom (G := H) (eqToHom e.symm).hom)) :
    RelativeProperty.{u, u + 1, u + 1} C S hS P (quotientStackProjectionHom H) := by
  have hA := isEquivalence_liftedSpaceStackMap_eqToHom H.objects
    (Space.representedAlgebraicSpace C S hS V) e
  have h1 : RelativeProperty.{u, u + 1, u + 1} C S hS P
      (liftedSpaceStackMap (X := Space.representedAlgebraicSpace C S hS V) (Y := H.objects)
        (eqToHom e.symm).hom ≫ quotientStackProjectionHom H) :=
    relativeProperty_liftedChart P (schemePresentationHom (eqToHom e.symm).hom) h
  have hid : (eqToHom e).hom ≫ (eqToHom e.symm).hom = 𝟙 H.objects.obj := by
    have h0 : (eqToHom e : H.objects ⟶ Space.representedAlgebraicSpace C S hS V) ≫
        eqToHom e.symm = 𝟙 H.objects := by
      rw [eqToHom_trans, eqToHom_refl]
    exact congrArg (fun k : H.objects ⟶ H.objects => k.hom) h0
  have hkey : liftedSpaceStackMap (X := H.objects)
        (Y := Space.representedAlgebraicSpace C S hS V) (eqToHom e).hom ≫
      liftedSpaceStackMap (X := Space.representedAlgebraicSpace C S hS V) (Y := H.objects)
        (eqToHom e.symm).hom = 𝟙 (liftedSpaceStack H.objects) := by
    rw [liftedSpaceStackMap_comp, hid, liftedSpaceStackMap_id]
  have hsq : liftedSpaceStackMap (X := H.objects)
        (Y := Space.representedAlgebraicSpace C S hS V) (eqToHom e).hom ≫
      (liftedSpaceStackMap (X := Space.representedAlgebraicSpace C S hS V) (Y := H.objects)
        (eqToHom e.symm).hom ≫ quotientStackProjectionHom H)
      = quotientStackProjectionHom H :=
    (Category.assoc
      (liftedSpaceStackMap (X := H.objects)
        (Y := Space.representedAlgebraicSpace C S hS V) (eqToHom e).hom)
      (liftedSpaceStackMap (X := Space.representedAlgebraicSpace C S hS V) (Y := H.objects)
        (eqToHom e.symm).hom) (quotientStackProjectionHom H)).symm.trans
      ((congrArg (fun k : liftedSpaceStack H.objects ⟶ liftedObjectSpace H =>
          k ≫ quotientStackProjectionHom H) hkey).trans
        (Category.id_comp (quotientStackProjectionHom H)))
  exact @relativeProperty_of_equivalences C S hS
    (liftedObjectSpace H) (liftedSpaceStack (Space.representedAlgebraicSpace C S hS V))
    (CatFiberedInGroupoids.mk (quotientStack H) (isFiberedInGroupoids_quotientStack H))
    (CatFiberedInGroupoids.mk (quotientStack H) (isFiberedInGroupoids_quotientStack H))
    P (quotientStackProjectionHom H).hom
    (liftedSpaceStackMap (X := Space.representedAlgebraicSpace C S hS V) (Y := H.objects)
      (eqToHom e.symm).hom ≫ quotientStackProjectionHom H).hom
    (liftedSpaceStackMap (X := H.objects)
      (Y := Space.representedAlgebraicSpace C S hS V) (eqToHom e).hom).hom
    (BasedFunctor.id (quotientStack H))
    (eqToIso (congrArg (fun k : liftedObjectSpace H ⟶ CatFiberedInGroupoids.mk
        (quotientStack H) (isFiberedInGroupoids_quotientStack H) => k.hom) hsq))
    hA inferInstance h1

/-- **Stacks 04M9 against Stacks 045C.** Let `P` be a property of morphisms of algebraic spaces
over `S` stable under base change and local on the target for the fppf precoverage. If the
canonical projection `π : S_U ⟶ [U/R]` of **Stacks 044R** satisfies the condition of Stacks 03YK
at `P`, then the source map `s : R ⟶ U` of the groupoid has `P`.

Nothing is carried. The 2-fibre product of `π` with itself is the arrow space, with first leg `s`,
by `AlgebraicGeometry.Stack.QuotientAtlas.isTwoFibreProduct_arrowSelfSquare`; the representability
of `π` that **Stacks 045C** consumes is
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom`; and the passage
from the relative condition on the lifted `s` to `P` of `s` itself is **Stacks 0457** down the
universe lift followed by the Stacks 04XB bridge
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, whose morphism of
representing presheaves is `s` by `AlgebraicGeometry.Stack.representingMap_associatedMap`.

This is the converse of `AlgebraicGeometry.Stack.QuotientAtlas.relativeProperty_of_prop_source`,
which passes a property of `s` to the projection. -/
theorem prop_source_of_relativeProperty_quotientStackProjectionHom
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (H : GroupoidInAlgebraicSpaces C S hS A)
    (h : RelativeProperty.{u, u + 1, u + 1} C S hS P (quotientStackProjectionHom H)) :
    P H.source := by
  have hbase : RelativeProperty.{u, u + 1, u + 1} C S hS P
      (QuotientAtlas.arrowSelfSquare H).fst :=
    hasRelativeProperty_baseChange.{u, u + 1, u} C S hS P _ _ _
      (quotientStackProjectionHom H) (quotientStackProjectionHom H)
      (QuotientAtlas.arrowSelfSquare H) (QuotientAtlas.isTwoFibreProduct_arrowSelfSquare H)
      (representable_quotientStackProjectionHom H) h
  have h1 : Functor.IsEquivalence (liftedFibredCategoryUp H.arrows).toFunctor :=
    isEquivalence_liftedFibredCategoryUp H.arrows
  have h2 : Functor.IsEquivalence (liftedFibredCategoryUp H.objects).toFunctor :=
    isEquivalence_liftedFibredCategoryUp H.objects
  have hdown : RelativeProperty.{u, u, u + 1} C S hS P
      (associatedMap C S hS H.source.hom).1 :=
    @relativeProperty_of_equivalences C S hS
      (fibredCategory C S hS H.arrows.obj) (QuotientAtlas.liftedArrowSpace H)
      (fibredCategory C S hS H.objects.obj) (liftedObjectSpace H) P
      (associatedMap C S hS H.source.hom).1.hom
      (QuotientAtlas.arrowSelfSquare H).fst.hom
      (liftedFibredCategoryUp H.arrows) (liftedFibredCategoryUp H.objects)
      (Iso.refl _) h1 h2 hbase
  have hprop := (hasRelativeProperty_iff_prop_representingMap.{u, max u t} C S hS P
      (associatedMap C S hS H.source.hom).1
      (isRepresentableByAlgebraicSpaces_associatedMap H.source.hom)
      H.arrows.obj H.objects.obj H.arrows.property H.objects.property
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hdown
  rwa [representingMap_associatedMap] at hprop

/-! ### Compatibility with the 1-morphism of quotient stacks of Stacks 046Q -/

/-- **Stacks 046Q at a presented point.** A morphism `r : (U', R', s', t', c') ⟶ (U, R, s, t, c)`
of groupoids in algebraic spaces carries the 1-morphism presented by a point `a : h_V ⟶ U'` of the
object space of its source to the 1-morphism presented by the transported point
`a ≫ r_U : h_V ⟶ U`.

The 2-isomorphism is `AlgebraicGeometry.Stack.quotientStackMap_commutes` evaluated at the point of
the pointwise groupoid fibration that `a` names, read through **Stacks 04SS** in the form
`AlgebraicGeometry.Stack.schemePointIsoOfFiberIso`: both sides name objects of the fibre of `[U/R]`
over `V`, and the two `eqToIso`s identify those objects with the two ends of that 2-cell. -/
noncomputable def presentedSchemeMapQuotientStackMapIso
    {H G : GroupoidInAlgebraicSpaces C S hS A}
    (r : GroupoidInAlgebraicSpaces.Hom H G)
    {V : BigFppfOver C S hS} (a : yoneda.obj V ⟶ H.objects.obj) :
    presentedSchemeMap G (a ≫ r.toGroupoidHom.mapObjects) ≅
      BasedFunctor.comp (presentedSchemeMap H a) (quotientStackMap r) := by
  let t : (pointwisePresentation H).obj := ⟨V, a.app (op V) (𝟙 V)⟩
  let α := quotientStackMap_commutes r
  let p := (quotientStack G).p
  let x : p.Fiber V := ⟨(BasedFunctor.comp (quotientPointwiseMap r)
      (pointwiseToQuotientStackBased G)).obj t,
    (BasedFunctor.comp (quotientPointwiseMap r)
      (pointwiseToQuotientStackBased G)).w_obj t⟩
  let y : p.Fiber V := ⟨(BasedFunctor.comp (pointwiseToQuotientStackBased H)
      (quotientStackMap r)).obj t,
    (BasedFunctor.comp (pointwiseToQuotientStackBased H)
      (quotientStackMap r)).w_obj t⟩
  haveI hv : p.IsHomLift (𝟙 V) (α.hom.app t) := α.hom.isHomLift' t
  haveI hi : p.IsHomLift (𝟙 V) (α.inv.app t) := α.inv.isHomLift' t
  let ex : x ≅ y := {
    hom := Functor.Fiber.homMk p V (α.hom.app t)
    inv := Functor.Fiber.homMk p V (α.inv.app t)
    hom_inv_id := Functor.Fiber.hom_ext (congrArg (fun η => η.app t) α.hom_inv_id)
    inv_hom_id := Functor.Fiber.hom_ext (congrArg (fun η => η.app t) α.inv_hom_id) }
  apply schemePointIsoOfFiberIso (isFiberedInGroupoids_quotientStack G)
  refine eqToIso ?_ ≪≫ ex ≪≫ eqToIso ?_
  · apply Subtype.ext
    change (quotientStackProjection G).obj
        ⟨V, Discrete.mk ((a ≫ r.toGroupoidHom.mapObjects).app (op V) (𝟙 V))⟩ =
      (pointwiseToQuotientStack G).obj ((quotientPointwiseMap r).obj t)
    exact (quotientStackProjection_obj G
      ⟨V, Discrete.mk ((a ≫ r.toGroupoidHom.mapObjects).app (op V) (𝟙 V))⟩).trans
      (congrArg (pointwiseToQuotientStack G).obj (quotientPointwiseMap_obj r t).symm)
  · apply Subtype.ext
    change (quotientStackMap r).obj ((pointwiseToQuotientStack H).obj t) =
      (quotientStackMap r).obj ((quotientStackProjection H).obj
        ⟨V, Discrete.mk (a.app (op V) (𝟙 V))⟩)
    exact congrArg (quotientStackMap r).obj
      (quotientStackProjection_obj H ⟨V, Discrete.mk (a.app (op V) (𝟙 V))⟩).symm

/-- `AlgebraicGeometry.Stack.presentedSchemeMapQuotientStackMapIso` read at the presentation
1-morphism of Stacks 026O on both sides, through
`AlgebraicGeometry.Stack.presentedSchemeMapIsoSchemePresentationHom`. -/
noncomputable def schemePresentationHomQuotientStackMapIso
    {H G : GroupoidInAlgebraicSpaces C S hS A}
    (r : GroupoidInAlgebraicSpaces.Hom H G)
    {V : BigFppfOver C S hS} (a : yoneda.obj V ⟶ H.objects.obj) :
    schemePresentationHom (G := G) (a ≫ r.toGroupoidHom.mapObjects) ≅
      BasedFunctor.comp (schemePresentationHom (G := H) a) (quotientStackMap r) :=
  (presentedSchemeMapIsoSchemePresentationHom (a ≫ r.toGroupoidHom.mapObjects)).symm ≪≫
    presentedSchemeMapQuotientStackMapIso r a ≪≫
    schemePointIsoOfFiberIso (isFiberedInGroupoids_quotientStack G) _ _ (Iso.refl _)

end AlgebraicGeometry.Stack

end
