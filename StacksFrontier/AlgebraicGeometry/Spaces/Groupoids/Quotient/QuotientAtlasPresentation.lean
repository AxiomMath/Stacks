module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackCell
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Stacks 04M9 in the 2-category of categories fibred in groupoids

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : 𝒮_U ⟶ [U/R]` be the canonical projection of
Stacks 044R. **Stacks 04M9** is formalized in this library as
`AlgebraicGeometry.Stack.quotientStack_twoFibreProduct`, as terminality of the source-target
square in the 2-category of *stacks* in groupoids. Every consumer of it —
`AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty` and through it Stacks 04X0, 06FH and
04TK — asks instead for `AlgebraicGeometry.Stack.QuotientAtlas.Presentation`, which is phrased in
the 2-category of *categories* fibred in groupoids, and so carries that structure as a hypothesis.

This file builds the structure, so that the hypothesis is discharged.

## Main definitions

* `AlgebraicGeometry.Stack.QuotientAtlas.presentation`: the Stacks 04M9 data for a groupoid in
  algebraic spaces, in the form its consumers take.

## Main results

* `CategoryTheory.StackInGroupoids.isEquivalence_of_isTwoFibreProduct`: a comparison 1-morphism
  between two 2-fibre products of one cospan of stacks in groupoids is an equivalence of the
  underlying categories.
* `AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty_of_representable`: **Stacks 06FH**
  and **Stacks 04X0** reduced to the representability of `π` alone — every property of morphisms
  of algebraic spaces stable under base change and local at the target for the fppf topology
  passes from the source map of the groupoid to the projection.

## Implementation notes

**Terminality is not transported; it is not needed.** The obstruction recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/QuotientAtlasFlat.lean` is that
`CategoryTheory.Bicategory.isTwoFibreProduct_underlying` needs a 2-fibre product of the cospan in
the *ambient* 2-category of categories over the site, which does not exist. It is sidestepped
here: the square the `Presentation` carries is the **canonical** 2-fibre product
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` of `π` with itself, whose universal
property in the 2-category of categories fibred in groupoids is
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare` and needs no
input at all.

What Stacks 04M9 is then used for is the remaining content of the structure: the identification
of the apex of that canonical square with `𝒮_R` carrying its first leg to the source map `s`.
That identification is obtained from terminality *inside* the 2-category of stacks in groupoids,
where both squares are available: the canonical square has a stack in groupoids as its apex, by
`AlgebraicGeometry.Stack.relativeProjection_isStackInGroupoids`, so it is a 2-fibre product
there as well by `AlgebraicGeometry.Stack.relativeProductIsTerminal`, and Stacks 04M9 says the
source-target square is one too. Two terminal objects of the category of 2-commutative squares
receive mutually inverse comparison morphisms, so the comparison 1-morphism of apexes is an
equivalence of the underlying categories and its `isoFst` is exactly the compatibility the
`comm` field asks for. The apex and the first leg of the canonical square are literally the
same data read in the two 2-categories, which is why no transport intervenes.

**The two represented stacks are the unraised ones.** `arrowStack` and `objectStack` are objects
of `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, so they are
`AlgebraicGeometry.Stack.fibredCategory` at the arrow and object presheaves, with the identity
comparisons as their `arrowsEquivalence` and `objectsEquivalence`; the universe lift that the
quotient stack forces is absorbed into `toArrowStack` and `toObjectStack` through
`AlgebraicGeometry.Stack.liftedFibredCategoryDown`. With that choice `leg` is the 1-morphism of
Stacks 0458 attached to `s`, and the `leg_eq` field is
`AlgebraicGeometry.Stack.representingMap_associatedMap`.

**Representability of `π` stays a hypothesis.** It is the one field of `Presentation` that
Stacks 04M9 does not provide; the source takes it from Stacks 04WZ, which in this library is
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom` on the bootstrap theorem
Stacks 04S6 part (3). It is taken here as the argument `hπ`, so that nothing beyond the
bootstrap theorem is assumed.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.StackInGroupoids

universe w v₁ v₂ u₁ u₂

variable {𝒟 : Type u₁} [Category.{v₁} 𝒟] {J : GrothendieckTopology 𝒟}

/-- The natural isomorphism of the underlying functors of a 2-isomorphism of stacks in
groupoids. The 2-category of stacks in groupoids is a full sub-2-category of the categories over
the site, so a 2-morphism of it is a natural transformation over the site. -/
def underlyingIso {𝒳 𝒴 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒟 J} {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) :
    f.hom.toFunctor ≅ g.hom.toFunctor where
  hom := e.hom.hom.toNatTrans
  inv := e.inv.hom.toNatTrans
  hom_inv_id := congrArg (fun a => a.hom.toNatTrans) e.hom_inv_id
  inv_hom_id := congrArg (fun a => a.hom.toNatTrans) e.inv_hom_id

variable {𝒳 𝒴 𝒵 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒟 J} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}

/-- **The comparison 1-morphism between two 2-fibre products of one cospan of stacks in
groupoids is an equivalence of the underlying categories** (Stacks 003Q). This is
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` read in the 2-category of stacks
in groupoids rather than in that of categories fibred in groupoids; the proof is the same, since
both are full sub-2-categories of the categories over the site. -/
theorem isEquivalence_of_isTwoFibreProduct {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (a : Bicategory.TwoCommSq.PreHom P Q) : a.hom.hom.toFunctor.IsEquivalence := by
  let b := _root_.Quotient.out (hP.from Q)
  obtain ⟨e₁, -, -⟩ :=
    _root_.Quotient.exact (hP.hom_ext (_root_.Quotient.mk _ (a.comp b)) (𝟙 P))
  obtain ⟨e₂, -, -⟩ :=
    _root_.Quotient.exact (hQ.hom_ext (_root_.Quotient.mk _ (b.comp a)) (𝟙 Q))
  exact (CategoryTheory.Equivalence.mk a.hom.hom.toFunctor b.hom.hom.toFunctor
    (underlyingIso e₁).symm (underlyingIso e₂)).isEquivalence_functor

end CategoryTheory.StackInGroupoids

namespace CategoryTheory.BasedCategory

universe v₁ t₁ v₂ t₂ v₃ t₃ v₀ u₀

variable {𝒮 : Type u₀} [Category.{v₀} 𝒮]

-- NO `whiskerRightIso` HERE. Right-whiskering an isomorphism of based functors is
-- `CategoryTheory.BasedCategory.whiskerRightIso` of
-- `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityQuotientStackCell.lean:104`,
-- which already carries the three based categories at independent universes -- the generality
-- this module needs. A second copy under the same namespace makes the two mutually
-- unimportable.

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The canonical 1-morphism down from the universe lift is an equivalence of the underlying
categories: it is `CategoryTheory.ULiftHom.down`. -/
instance isEquivalence_liftedFibredCategoryDown (X : AlgebraicSpaces C S hS) :
    Functor.IsEquivalence (liftedFibredCategoryDown X).toFunctor :=
  (ULiftHom.equiv : (fibredCategory C S hS X.obj).val.obj ≌
    ULiftHom.{u + 1} (fibredCategory C S hS X.obj).val.obj).isEquivalence_inverse

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.QuotientAtlas

universe u t

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

attribute [local implicit_reducible] StackInGroupoids.bicategory
  Bicategory.InducedBicategory Bicategory.InducedBicategory.bicategory
  Bicategory.InducedBicategory.forget BasedNatTrans.forgetful

/-- **Stacks 04M9 in the form its consumers take.** The identification of the canonical 2-fibre
product of the projection `π : 𝒮_U ⟶ [U/R]` of Stacks 044R with itself as the arrow space of the
groupoid, with first leg the source map, in the 2-category of categories fibred in groupoids.

The only input is the representability of `π`, which Stacks 04M9 does not supply; everything
else is discharged. See the implementation notes. -/
noncomputable def presentation (G : GroupoidInAlgebraicSpaces C S hS B)
    (hπ : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom) :
    Presentation G := by
  classical
  let J := BigFppfOver.topology C S hS
  let U : StackInGroupoids.{u, u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) J :=
    ⟨liftedFibredCategory G.objects, isStackInGroupoids_liftedFibredCategory.{u, u} G.objects⟩
  let Q : StackInGroupoids.{u, u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) J :=
    ⟨quotientStack G, isStackInGroupoids_quotientStack.{u, u} G⟩
  let π : U ⟶ Q := Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G)
  have hprod : (relativeProjection G).IsStackInGroupoids.{u} J :=
    relativeProjection_isStackInGroupoids.{u, u} G
  have hR : Bicategory.IsTwoFibreProduct (relativeProductSquare π π hprod) :=
    relativeProductIsTerminal π π hprod
  have hP : Bicategory.IsTwoFibreProduct (quotientStackSquare G) :=
    quotientStack_twoFibreProduct.{u, u} G
  let a : Bicategory.TwoCommSq.PreHom (relativeProductSquare π π hprod) (quotientStackSquare G) :=
    _root_.Quotient.out (hP.from (relativeProductSquare π π hprod))
  have hae : a.hom.hom.toFunctor.IsEquivalence :=
    StackInGroupoids.isEquivalence_of_isTwoFibreProduct hR hP a
  have hdown : Functor.IsEquivalence (liftedFibredCategoryDown G.arrows).toFunctor :=
    isEquivalence_liftedFibredCategoryDown G.arrows
  exact
    { representable := hπ
      square := quotientStackSelfSquare G
      isTwoFibreProduct := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare
        (quotientStackProjectionHom G) (quotientStackProjectionHom G)
      fstRepresentable := isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS
        _ _ _ (quotientStackProjectionHom G) (quotientStackProjectionHom G)
        (quotientStackSelfSquare G)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare
          (quotientStackProjectionHom G) (quotientStackProjectionHom G)) hπ
      arrowStack := fibredCategory C S hS G.arrows.obj
      objectStack := fibredCategory C S hS G.objects.obj
      leg := (associatedMap C S hS G.source.hom).1
      legRepresentable :=
        -- Stacks 02ZZ against Stacks 04SV, as in
        -- `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_associatedMap`
        isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace C S hS
          (associatedMap C S hS G.source.hom).1
          (isRepresentableByAlgebraicSpace_fibredCategory C S hS G.arrows.obj G.arrows.property)
          (isRepresentableByAlgebraicSpace_fibredCategory C S hS G.objects.obj
            G.objects.property)
      toArrowStack := BasedFunctor.comp a.hom.hom (liftedFibredCategoryDown G.arrows)
      toObjectStack := liftedFibredCategoryDown G.objects
      isEquivalence_toArrowStack :=
        @Functor.isEquivalence_trans _ _ _ _ _ _ a.hom.hom.toFunctor
          (liftedFibredCategoryDown G.arrows).toFunctor hae hdown
      isEquivalence_toObjectStack := isEquivalence_liftedFibredCategoryDown G.objects
      comm := (BasedCategory.whiskerRightIso
        (Bicategory.InducedBicategory.isoHom
          (f := (relativeProductSquare π π hprod).fst) (g := a.hom ≫ (quotientStackSquare G).fst)
          a.isoFst)
        (liftedFibredCategoryDown G.objects)).symm
      arrowsEquivalence := StacksRepresentableCFG.EquivalenceOver.refl _
      objectsEquivalence := StacksRepresentableCFG.EquivalenceOver.refl _
      leg_eq := by
        rw [representingMap_associatedMap]
        rfl }

/-- **Stacks 06FH and Stacks 04X0 with the Stacks 04M9 hypothesis discharged.** Let
`G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `S` whose quotient-stack projection
`π : 𝒮_U ⟶ [U/R]` is representable by algebraic spaces, and let `P` be a property of morphisms
of algebraic spaces over `S` which is stable under base change and local at the target for the
fppf topology. If the source map `s` has `P`, then `π` has `P` in the relative sense of
Stacks 03YK.

This is `AlgebraicGeometry.Stack.QuotientAtlas.hasRelativeProperty` on the presentation built
above, so that only the representability of `π` — which Stacks 04M9 does not supply — is left to
the caller. -/
theorem hasRelativeProperty_of_representable {G : GroupoidInAlgebraicSpaces C S hS B}
    (hπ : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hP : P G.source) :
    HasRelativeProperty C S hS P (quotientStackProjectionHom G) hπ :=
  hasRelativeProperty.{u, t} (presentation G hπ) P hP

end AlgebraicGeometry.Stack.QuotientAtlas

end
