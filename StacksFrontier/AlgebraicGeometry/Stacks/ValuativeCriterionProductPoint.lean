module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionSchemePoint
public import StacksFrontier.CategoryTheory.TwoFibreProduct.ElementsSpan

/-!
# Points of the base change of a valuative square, and their links

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site and let
`q` be a valuative square for `f` (Stacks 0CLK). The special point of `q` is a scheme-valued point
of `𝒴` over the site object `R` attached to the spectrum of the valuation ring, so it has a base
change: the 2-fibre product `R ×_𝒴 𝒳` over the big fppf site of that spectrum, which is
`AlgebraicGeometry.Stack.valuativeBaseChange` below. When `f` is representable by algebraic spaces
(Stacks 02ZW) this 2-fibre product is an algebraic space over `R`, and the existence part of the
valuative criterion for `f` is to be compared with the existence part for that algebraic space.

An object of the base change carries a *link*, exactly as a valuative square does
(`AlgebraicGeometry.Stack.pointLink`): the morphism of `𝒴` from the image under `f` of its
`𝒳`-component to the value of the special point at the unit object. The link is functorial in the
object (`AlgebraicGeometry.Stack.productPointLink_map`), lies over the structure morphism of the
`𝒳`-component read in the site of `S` (`AlgebraicGeometry.Stack.productPointLink_lift`), and at
the object cut out by the generic point of `q` it is the link of `q` itself
(`AlgebraicGeometry.Stack.genericProductPoint_link`). These three facts are the whole interface
through which a dotted arrow of `q` and a section of the base change see each other.

## Main definitions

* `AlgebraicGeometry.Stack.valuativeBaseChange`: the base change of `f` along the special point.
* `AlgebraicGeometry.Stack.productPointLink`: the link of an object of the base change.
* `AlgebraicGeometry.Stack.genericProductPoint`: the object of the base change cut out by the
  generic point of the square.

## Main results

* `AlgebraicGeometry.Stack.productPointLink_map`: the link is functorial.
* `AlgebraicGeometry.Stack.productPointLink_lift`: the link lies over the structure morphism of
  the `𝒳`-component.
* `AlgebraicGeometry.Stack.genericProductPoint_link`: the link of the generic object is the link
  of the square.

## Implementation notes

`genericProductPoint` has to compare two spellings of the spectrum of the fraction field: as an
object `V₀` of the site of the spectrum of the valuation ring, and as the source of the left edge
`j` of the square, an object of the site of `S`. The two are identified by
`CategoryTheory.Over.iteratedSliceBackward` together with `q.genericMap_left` and
`q.j_canonical`, and the comparison isomorphism of the resulting object of the 2-fibre product is
the image of that identification under the special point, followed by the filling 2-morphism of
the square — invertible because the fibres of `𝒴` are groupoids and it lies over an identity.

## References

* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.TwoFibreProductOver.fst AlgebraicGeometry.Stack.sitePointOfSchemePoint

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}

/-- **The base change of `f` along the special point of a valuative square.** The 2-fibre product
`R ×_𝒴 𝒳` taken over the big fppf site of the spectrum `R` of the valuation ring, where the
scheme-valued point of `𝒴` is the special point of the square read on that site by
`AlgebraicGeometry.Stack.sitePointOfSchemePoint`. -/
abbrev valuativeBaseChange (q : ValuativeSquare B S hS f) :=
  TwoFibreProductOver (Over.map (siteObject B S hS q.ring_mem q.base).hom)
    𝒳.val.val.p 𝒴.val.val.p
    (sitePointOfSchemePoint B (siteObject B S hS q.ring_mem q.base) q.y)
    f.hom.hom.toFunctor

/-- **The link of a point of the base change.** For an object `A` of the base change of `f` along
the special point of a valuative square, the morphism of `𝒴` from the image under `f` of the
`𝒳`-component of `A` to the value of the special point at the unit object: the inverse of the
comparison isomorphism of `A`, followed by the image under the special point of the canonical
arrow of the slice at the `𝒳`-component. -/
noncomputable def productPointLink (q : ValuativeSquare B S hS f)
    (A : valuativeBaseChange B q) :
    f.hom.hom.obj A.y ⟶ q.y.hom.obj (Over.mk (𝟙 _)) :=
  A.iso.inv ≫ q.y.hom.map (Over.mkIdTerminal.from
    ((Over.iteratedSliceBackward (siteObject B S hS q.ring_mem q.base)).obj A.x))

/-- Precomposing the canonical arrow to the terminal object of a slice with any arrow does not
change its image under a functor. -/
private theorem map_comp_mkIdTerminal_from {C D : Type*} [Category C] [Category D] {X : C}
    (F : Over X ⥤ D) {A A' : Over X} (g : A ⟶ A') :
    F.map (g ≫ Over.mkIdTerminal.from A') = F.map (Over.mkIdTerminal.from A) :=
  congrArg F.map (Over.mkIdTerminal.hom_ext _ _)

/-- The link is functorial: the image under `f` of the `𝒳`-component of a morphism of the base
change, followed by the link of its target, is the link of its source. -/
theorem productPointLink_map (q : ValuativeSquare B S hS f)
    {A A' : valuativeBaseChange B q} (m : A ⟶ A') :
    f.hom.hom.map m.b ≫ productPointLink B q A' = productPointLink B q A := by
  apply (cancel_epi A.iso.hom).mp
  dsimp only [productPointLink]
  rw [← Category.assoc A.iso.hom, ← m.w]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change q.y.hom.map _ ≫ q.y.hom.map _ = q.y.hom.map _
  rw [← q.y.hom.toFunctor.map_comp]
  exact map_comp_mkIdTerminal_from _ _

/-- The link of an object of the base change lies over the structure morphism of its
`𝒳`-component, read as an object of the slice of the site of `S` at the spectrum of the valuation
ring. -/
theorem productPointLink_lift (q : ValuativeSquare B S hS f) (A : valuativeBaseChange B q) :
    𝒴.val.val.p.IsHomLift
      ((Over.iteratedSliceBackward
        (siteObject B S hS q.ring_mem q.base)).obj A.x).hom
      (productPointLink B q A) := by
  have : 𝒴.val.val.p.IsHomLift (𝟙 A.base) A.iso.hom := A.vertical
  have hinv := IsHomLift.lift_id_inv_isIso 𝒴.val.val.p A.base A.iso.hom
  rw [← A.hx, IsIso.Iso.inv_hom] at hinv
  have hterm := Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal 𝒴.val.val.p
    (siteObject B S hS q.ring_mem q.base) q.y.hom
    ((Over.iteratedSliceBackward (siteObject B S hS q.ring_mem q.base)).obj A.x)
  exact @IsHomLift.comp_lift_id_left _ _ _ _ 𝒴.val.val.p _ _ _ _ _ _ _ hterm _ hinv

/-- **The object of the base change cut out by the generic point of a valuative square.** Its
`𝒳`-component is the value of the generic point at the unit object, its site component is the
spectrum of the fraction field read in the site of the spectrum of the valuation ring, and its
comparison isomorphism is the identification of the two spellings of that spectrum followed by the
filling 2-morphism of the square. -/
noncomputable def genericProductPoint (q : ValuativeSquare B S hS f) :
    valuativeBaseChange B q := by
  let U : BigFppfOver B S hS := siteObject B S hS q.ring_mem q.base
  let y : siteOver B U ⥤ 𝒴.val.val.obj := sitePointOfSchemePoint B U q.y
  let V₀ : siteOver B U := siteObject B U.left.1 U.left.2 q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))
  let V := (Over.map U.hom).obj V₀
  let zK : Over V := Over.mk (𝟙 V)
  have hbaseMap : V₀.hom = q.genericMap.left := by
    apply B.inclusion.map_injective
    rw [q.genericMap_left]
    rfl
  let gm : V ⟶ U := Over.homMk V₀.hom (by
    apply ObjectProperty.hom_ext
    rfl)
  have hgm : gm = q.genericMap := Over.OverMorphism.ext hbaseMap
  have hobj : (Over.iteratedSliceBackward U).obj V₀ = (Over.map q.genericMap).obj zK := by
    change Over.mk gm = Over.mk (𝟙 V ≫ q.genericMap)
    rw [hgm, Category.id_comp]
  have hobj' : (Over.iteratedSliceBackward U).obj V₀ = q.j.hom.toFunctor.obj zK := by
    rwa [q.j_canonical]
  let isoY : y.obj V₀ ≅ (q.j.hom.toFunctor ⋙ q.y.hom.toFunctor).obj zK :=
    q.y.hom.toFunctor.mapIso (eqToIso hobj')
  have hγLift : 𝒴.val.val.p.IsHomLift (𝟙 V) (q.γ.hom.app zK) := q.γ.hom.isHomLift' zK
  have hγIso : IsIso (q.γ.hom.app zK) :=
    Functor.isIso_of_fiber_isGroupoid
      (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid V) _ hγLift
  let iso₀ : (q.j.hom.toFunctor ⋙ q.y.hom.toFunctor).obj zK ≅
      f.hom.hom.toFunctor.obj (q.x.hom.toFunctor.obj zK) :=
    @asIso _ _ _ _ (q.γ.hom.app zK) hγIso
  have hIsoY : 𝒴.val.val.p.IsHomLift (𝟙 V) isoY.hom := by
    have hsource : (Over.forget U).obj ((Over.iteratedSliceBackward U).obj V₀) = V := rfl
    have hs : (schemeFibredCategory B S hS U).val.p.IsHomLift (𝟙 V) (eqToIso hobj').hom :=
      IsHomLift.eqToHom_domain_lift_id hobj' hsource
    exact q.y.hom.preserves_isHomLift _ _
  have hIso₀ : 𝒴.val.val.p.IsHomLift (𝟙 V) iso₀.hom := hγLift
  exact
    { base := V
      x := V₀
      y := q.x.hom.toFunctor.obj zK
      hx := rfl
      hy := Functor.congr_obj q.x.hom.w zK
      iso := isoY ≪≫ iso₀
      vertical := by
        have := hIso₀
        have h := IsHomLift.comp (p := 𝒴.val.val.p) (f := 𝟙 V) (g := 𝟙 V) isoY.hom iso₀.hom
        simpa [CategoryTheory.Iso.trans_hom] using h }

/-- The link of the object cut out by the generic point is the link of the square itself. Both are
the inverse of the filling 2-morphism at the unit object followed by the image under the special
point of the canonical arrow, and the two canonical arrows agree because the unit object is
terminal in its slice. -/
theorem genericProductPoint_link (q : ValuativeSquare B S hS f) :
    productPointLink B q (genericProductPoint B q) = pointLink B q := by
  dsimp only [productPointLink, genericProductPoint, pointLink,
    Iso.trans_inv, Functor.mapIso_inv, eqToIso, asIso_inv]
  rw [Category.assoc, ← q.y.hom.toFunctor.map_comp]
  congr 1
  exact map_comp_mkIdTerminal_from _ _

end AlgebraicGeometry.Stack

end
