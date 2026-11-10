module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The smooth-diagram criterion for a representable morphism (Stacks 06FM)

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target in the sense of **Stacks 06F8**, and which is moreover stable under base change
and local at the target for the fppf precoverage as a property of morphisms of algebraic spaces.
Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is representable by algebraic
spaces. The last assertion of Stacks 06FM says that `f` passes the existential smooth-diagram
test of condition (2) exactly when it has the relative property `P` in the sense of Stacks 03YK,
i.e. of Properties of Stacks, Section 04XB.

This module proves both implications.

## Main definitions

* `AlgebraicGeometry.Stack.twoFibreProductSwapMap`: the 1-morphism exchanging the two factors of
  a 2-fibre product of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty`: a
  representable 1-morphism with the relative property of Stacks 03YK passes the existential
  smooth-diagram test.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_schemePointBaseChange`: the
  smooth-diagram test is inherited by the base change along a scheme-valued point of the target.
* `AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram`: the converse
  of the first.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_relative`: **Stacks 06FM**, the
  assertion for a representable morphism.

## Implementation notes

### From the relative property to a diagram

The diagram is the source's own: a presentation of `𝒴` by a scheme `W`, and the base change of
`f` along it.

Writing `p : (Sch/W)_fppf ⟶ 𝒴` for the presentation supplied by the third clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`, the apex of the diagram is the 2-fibre product
`(Sch/W)_fppf ×_𝒴 𝒳`. It is representable by an algebraic space by **Stacks 0300**, since the
slice is representable by `yoneda.obj W` (**Stacks 025Z**) and `f` is representable by algebraic
spaces. Its two projections are the two legs of the diagram:

* the projection to the slice is the base change of `f`, so it has the relative property `P` by
  **Stacks 045C**, and the bridge of §04XB
  (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`) turns that into `P` of
  the induced morphism of representing presheaves — which is the top horizontal morphism of the
  diagram;
* the projection to `𝒳` is the base change of `p`, so it is smooth and surjective on objects.

The second of those needs a turn, because **Stacks 045C is stated for the *first* projection
only**, and the projection wanted here is the second. The two orders of the 2-fibre product are
exchanged by `CategoryTheory.TwoFibreProductOver.swap`, which is an equivalence strictly over the
site, so `AlgebraicGeometry.Stack.twoFibreProductSwapMap` composed with the first projection of
the square taken in the other order *is* the second projection, on the nose. The relative
property and the representability are then carried across by
`AlgebraicGeometry.Stack.relativeProperty_of_forall_nonempty_equivalenceOver_fst` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst`,
which is what those two transports are for. Surjectivity on objects is read off the
relative property for surjectivity by **Stacks 06D7**.

The vertical 1-morphisms of the diagram have to start at the categories of elements of the two
algebraic spaces rather than at the 2-fibre product and the slice, so each is precomposed with
`AlgebraicGeometry.Stack.equivalenceOverInvMap`, which is smooth and surjective on objects; the
composites are smooth by **Stacks 045B** and surjective on objects by **Stacks 06D6**.

The invertible 2-cell of the diagram comes from the uniqueness half of **Stacks 04SW**: the two
1-morphisms from the category of elements of the apex's representing space to the slice induce
the same morphism of representing presheaves — one by
`AlgebraicGeometry.Stack.representingMap_associatedMap`, the other by
`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap` — so they are 2-isomorphic, and
whiskering that 2-cell with the presentation and the square's own 2-cell gives the one the
diagram wants.

### From a diagram to the relative property

For each scheme-valued point `z` of `𝒴`, the base change of `f` along it is representable by an
algebraic space and the slice is represented by `h_Z`, and
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre` identifies the induced morphism of
representing presheaves with the structural morphism of the lower-shriek extension that the
relative property tests. So it is enough to base change the *diagram*, and then theorem 2's
forward half applies.

Base-changing the diagram is the last paragraph of the Stacks proof, and it is where the two
legs would sit over different apexes: `((Sch/Z) ×_𝒴 𝒳) ×_𝒳 S_U ⟶ (Sch/Z) ×_𝒴 𝒳` is the base
change of the left vertical 1-morphism, hence smooth and surjective on objects, while
`((Sch/Z) ×_𝒴 S_V) ×_{S_V} S_U ⟶ (Sch/Z) ×_𝒴 S_V` is the base change of the 1-morphism attached
to the top horizontal morphism, hence has `P`. The two apexes are identified by
`CategoryTheory.TwoFibreProductOver.cancelSnd`, the over-a-base form of **Stacks 02XD**, applied
twice into the one target `(Sch/Z) ×_𝒴 S_U`: with the identity reindexing on the first and with
`CategoryTheory.CatFiberedInGroupoids.underlyingIso` of the diagram's own 2-cell on the second,
which is what that lemma's reindexing argument exists for.

Two things about the comparison are load-bearing and worth keeping. It is used through
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over` applied to `cancelSnd` directly
rather than through
`CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_cancelSnd`: the quasi-inverse is a
choice, but the forward functor has to stay `cancelSnd`, because the 2-cell of the new diagram is
the counit of that equivalence whiskered on both sides and the whiskering only typechecks against
`CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst`, which holds by `rfl`. And the comparison
natural isomorphism is built by hand from `CategoryTheory.Functor.whiskerLeft` and
`CategoryTheory.Functor.whiskerRight` rather than from the bundled `isoWhiskerLeft`/
`isoWhiskerRight`, and introduced with `let` rather than `have`, because its components have to be
definitionally `fstT.map (ε.inv.app _)` for the verticality argument — a `have` forgets the body
and the verticality step then fails on a type mismatch that reads as a wrong lemma.

### Two elaboration pitfalls in this file

Both are instances of the known `abbrev` unification pitfall. `rw` and `refine` through
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_relocalize` each exceed 200,000 heartbeats with
`timeout at whnf`, reported at the statement's `:= by` so that it reads as a defective statement;
the fix is to `intro` straight onto the `abbrev` goal and use
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` pointwise instead of the iff. And
`AlgebraicGeometry.Stack.prop_representingMap_of_hasPropertyOnSomeSmoothDiagram` must be given
its two category arguments **by name**; leaving them to unification reproduces the same timeout.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Exchanging the two factors of a 2-fibre product of categories fibred in groupoids**, as a
1-morphism of the 2-category: the apex of the canonical square over the cospan `(g, f)` maps to
the apex of the canonical square over `(f, g)` by
`CategoryTheory.TwoFibreProductOver.swap`, which is strictly over the site.

Composed with the first projection of the target square it is the second projection of the source
square, on the nose, which is what lets a statement about first projections — Stacks 045C, say —
be read as a statement about second projections. -/
def twoFibreProductSwapMap
    {𝒳 𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴) :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt :=
  Bicategory.InducedBicategory.mkHom
    ⟨TwoFibreProductOver.swap 𝒲.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor g) (CatFiberedInGroupoids.homFunctor f),
     TwoFibreProductOver.swap_comp_structureFunctor _ _ _ _ _⟩

/-- Base change along `g` of a representable morphism `f` with the relative property `Q`: the
projection to the source of `g` is representable and has `Q` too (Stacks 045C). -/
private theorem exists_hasRelativeProperty_fst_of_baseChange
    (Q : MorphismProperty (AlgebraicSpaces B S hS))
    [Q.IsStableUnderBaseChange] [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴} (R : Bicategory.TwoCommSq g f)
    (hR : Bicategory.IsTwoFibreProduct R) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hrel : HasRelativeProperty.{u, u, u + 1, v} B S hS Q f hf) :
    ∃ h : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom,
      HasRelativeProperty.{u, u, u + 1, v} B S hS Q R.fst h :=
  ⟨_, hasRelativeProperty_baseChange.{u, u, u + 1, v} B S hS Q 𝒳 𝒴 𝒵 f g R hR hf hrel⟩

/-- Precomposing a representable morphism that is smooth and surjective on objects with an
equivalence keeps it so. -/
private theorem exists_smooth_surjective_of_comp_isEquivalence
    {𝒳' 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒳' ⟶ 𝒳) [Functor.IsEquivalence a.hom.toFunctor] (f : 𝒳 ⟶ 𝒴) (f' : 𝒳' ⟶ 𝒴)
    (h : a ≫ f = f') (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsm : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) f hf)
    (hsu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) f hf) :
    ∃ hf' : IsRepresentableByAlgebraicSpaces B S hS f'.hom,
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) f' hf' ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) f' hf' := by
  subst h
  have e : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj), y ⋙ 𝒴.val.p = Over.map V.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳'.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor (a ≫ f)))
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))) :=
    fun V y hy => nonempty_equivalenceOver_fst_of_equivalence_source B S hS a.hom f.hom V y hy
  exact ⟨isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst e hf,
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS _ f (a ≫ f) e hsm,
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS _ f (a ≫ f) e hsu⟩

/-- Two 1-morphisms inducing the same morphism of representing presheaves are 2-isomorphic
(the uniqueness half of Stacks 04SW). -/
private theorem nonempty_iso_of_representingMap_eq
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    {a a' : 𝒜 ⟶ 𝒞}
    (h : representingMap B S hS 𝒜 𝒞 F G eF eG a = representingMap B S hS 𝒜 𝒞 F G eF eG a') :
    Nonempty (a ≅ a') := by
  obtain ⟨e, hee⟩ := Quotient.exact ((morphismSpaceEquiv B S hS 𝒜 𝒞 F G eF eG).injective h)
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)⟩

/-- Precomposing with the backward 1-morphism of a representing equivalence does not change the
induced morphism of representing presheaves. -/
private theorem representingMap_equivalenceOverInvMap_comp
    {𝒳 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) (g : 𝒳 ⟶ 𝒞) :
    representingMap B S hS (fibredCategory B S hS F) 𝒞 F G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eG
        (equivalenceOverInvMap B S hS F eF ≫ g) = representingMap B S hS 𝒳 𝒞 F G eF eG g := by
  rw [representingMap_comp (𝒜 := fibredCategory B S hS F) (ℬ := 𝒳) (𝒞 := 𝒞) B S hS F F G
    (StacksRepresentableCFG.EquivalenceOver.refl _) eF eG _ g,
    representingMap_equivalenceOverInvMap, Category.id_comp]

/-- **The relative property implies the existential smooth-diagram test, Stacks 06FM.** Let `P`
be a property of morphisms of algebraic spaces over `S` stable under base change and local at the
target for the fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism representable by algebraic
spaces whose target is an algebraic stack. If `f` has the relative property `P` of Stacks 03YK,
then there is a smooth diagram over `f`, with left vertical 1-morphism surjective on objects,
whose top horizontal morphism of algebraic spaces has `P`.

The diagram is built from a presentation of `𝒴` by a scheme and the base change of `f` along it;
see the implementation notes of this module. Neither smooth locality of `P` nor any hypothesis on
`𝒳` is used in this direction. -/
theorem hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hrel : HasRelativeProperty.{u, u, u + 1, v} B S hS (spaceProperty B S hS P) f hf) :
    HasPropertyOnSomeSmoothDiagram B S hS P f := by
  obtain ⟨hfib, hrest⟩ := h𝒴
  obtain ⟨W, k, hk, hkprop⟩ := hrest.2.2
  -- the presentation of `𝒴`, read as a 1-morphism of the 2-category
  let pMor : schemeFibredCategory B S hS W ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom k
  have hp : IsRepresentableByAlgebraicSpaces B S hS pMor.hom := hk
  have hpsm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) pMor hp :=
    fun V y hy G hG he => (hkprop V y hy G hG he).2
  have hpsu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) pMor hp :=
    fun V y hy G hG he => (hkprop V y hy G hG he).1
  -- the canonical 2-fibre product square, in both orders of its two factors
  set R : Bicategory.TwoCommSq pMor f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} pMor f
  set R' : Bicategory.TwoCommSq f pMor :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f pMor
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} pMor f
  have hR' : Bicategory.IsTwoFibreProduct R' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f pMor
  -- the projection to the slice is the base change of `f`, so it has the relative property
  obtain ⟨hreprfst, hrelfst⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (spaceProperty B S hS P) R hR hf hrel
  -- the projection to `𝒳` is the base change of the presentation: first in the other order
  obtain ⟨hreprfst', hsmfst'⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (Space.smoothMorphismProperty B S hS) R' hR' hp hpsm
  obtain ⟨_, hsufst'⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (Space.surjectiveMorphismProperty B S hS) R' hR' hp hpsu
  -- and then across the exchange of the two factors
  have hswEquiv : Functor.IsEquivalence (twoFibreProductSwapMap B S hS f pMor).hom.toFunctor := by
    change Functor.IsEquivalence (TwoFibreProductOver.swap _ _ _ _ _)
    infer_instance
  obtain ⟨hreprsnd, hsmsnd, hsusnd⟩ := exists_smooth_surjective_of_comp_isEquivalence B S hS
    (twoFibreProductSwapMap B S hS f pMor) R'.fst R.snd rfl hreprfst' hsmfst' hsufst'
  -- the apex of the square is representable by an algebraic space, by Stacks 0300
  obtain ⟨U, hU, ⟨eU₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴
    (schemeFibredCategory B S hS W) 𝒳 pMor.hom f.hom hf
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  -- read the comparison against the apex of the canonical square, not against `twoFibreProduct`
  let eU : StacksRepresentableCFG.EquivalenceOver R.pt.val.p
    (presheafOfCategories (U ⋙ typeToCat)).p := eU₀
  -- the top horizontal morphism of the diagram, and its property
  set hTop := representingMap B S hS R.pt (schemeFibredCategory B S hS W) U (yoneda.obj W)
    eU (PresheafOfCategories.sliceElementsEquivalenceOver W) R.fst
  have hPh : P hTop :=
    (hasRelativeProperty_iff_prop_representingMap.{u, v} B S hS (spaceProperty B S hS P)
      R.fst hreprfst U (yoneda.obj W) hU (isAlgebraicSpace_yoneda B S hS W) eU
      (PresheafOfCategories.sliceElementsEquivalenceOver W)).1 hrelfst
  refine ⟨U, yoneda.obj W, hU, isAlgebraicSpace_yoneda B S hS W,
    equivalenceOverInvMap B S hS U eU ≫ R.snd,
    equivalenceOverInvMap B S hS (yoneda.obj W)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) ≫ pMor,
    hTop, ?_, ?_, ?_, ?_, hPh⟩
  · -- the invertible 2-cell, from the uniqueness half of Stacks 04SW
    have hleft : representingMap B S hS (fibredCategory B S hS U)
        (schemeFibredCategory B S hS W) U (yoneda.obj W)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (PresheafOfCategories.sliceElementsEquivalenceOver W)
        ((associatedMap B S hS hTop).1 ≫ equivalenceOverInvMap B S hS (yoneda.obj W)
          (PresheafOfCategories.sliceElementsEquivalenceOver W)) = hTop := by
      rw [representingMap_comp (𝒜 := fibredCategory B S hS U)
        (ℬ := fibredCategory B S hS (yoneda.obj W))
        (𝒞 := schemeFibredCategory B S hS W) B S hS U (yoneda.obj W) (yoneda.obj W)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (PresheafOfCategories.sliceElementsEquivalenceOver W),
        representingMap_associatedMap]
      rw [representingMap_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS W) B S hS
        (yoneda.obj W) (PresheafOfCategories.sliceElementsEquivalenceOver W), Category.comp_id]
    have hright : representingMap B S hS (fibredCategory B S hS U)
        (schemeFibredCategory B S hS W) U (yoneda.obj W)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (PresheafOfCategories.sliceElementsEquivalenceOver W)
        (equivalenceOverInvMap B S hS U eU ≫ R.fst) = hTop :=
      representingMap_equivalenceOverInvMap_comp B S hS U _ eU _ R.fst
    obtain ⟨e⟩ := nonempty_iso_of_representingMap_eq (𝒜 := fibredCategory B S hS U)
      (𝒞 := schemeFibredCategory B S hS W) B S hS U (yoneda.obj W)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) (hleft.trans hright.symm)
    exact ⟨Bicategory.whiskerRightIso e pMor ≪≫
      Bicategory.whiskerLeftIso (equivalenceOverInvMap B S hS U eU) R.iso⟩
  · exact isRelativelySmooth_comp B S hS (equivalenceOverInvMap B S hS U eU) R.snd
      (isRelativelySmooth_equivalenceOverInvMap B S hS U hU eU) ⟨hreprsnd, hsmsnd⟩
  · exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p R.pt.val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS U eU))
      (CatFiberedInGroupoids.homFunctor R.snd)
      (CatFiberedInGroupoids.homFunctor_comp_p R.snd)
      (isSurjectiveOnObjects_equivalenceOverInvMap B S hS U eU)
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS R.snd
        hreprsnd).2 hsusnd)
  · exact isRelativelySmooth_comp B S hS
      (equivalenceOverInvMap B S hS (yoneda.obj W)
        (PresheafOfCategories.sliceElementsEquivalenceOver W)) pMor
      (isRelativelySmooth_equivalenceOverInvMap
        (𝒳 := schemeFibredCategory B S hS W) B S hS (yoneda.obj W)
        (isAlgebraicSpace_yoneda B S hS W)
        (PresheafOfCategories.sliceElementsEquivalenceOver W)) ⟨hp, hpsm⟩

/-- **Condition (2) of Stacks 06FM base-changes along a scheme-valued point.** Given a smooth
diagram over `f : 𝒳 ⟶ 𝒴` whose left vertical 1-morphism is surjective on objects and whose top
horizontal morphism has `P`, the base change of `f` along a scheme-valued point `z` of `𝒴`
carries one too.

This is the last paragraph of the proof of Stacks 06FM.  The new diagram's apex is
`((Sch/Z)_fppf ×_𝒴 S_V) ×_{S_V} S_U`: its projection to `(Sch/Z)_fppf ×_𝒴 S_V` is the base
change of the 1-morphism attached to the top horizontal morphism, hence has `P` by Stacks 045C;
and the apex maps to `(Sch/Z)_fppf ×_𝒴 𝒳` through the cancellation
`CategoryTheory.TwoFibreProductOver.cancelSnd`, which identifies it with
`((Sch/Z)_fppf ×_𝒴 𝒳) ×_𝒳 S_U`, where the projection is the base change of the left vertical
1-morphism and so is smooth and surjective on objects. -/
theorem hasPropertyOnSomeSmoothDiagram_schemePointBaseChange
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (Z : BigFppfOver B S hS)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒴.val.obj)
    (hz : z ⋙ 𝒴.val.p = Over.map Z.hom)
    (hsome : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasPropertyOnSomeSmoothDiagram B S hS P
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) f).fst := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hsurj, hb, hPh⟩ := hsome
  -- the 1-morphism attached to `h`, and its relative property
  have hMorRep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS h).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS h).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  have hMorRel : HasRelativeProperty.{u, u, u + 1, v} B S hS (spaceProperty B S hS P)
      (associatedMap B S hS h).1 hMorRep := by
    refine (hasRelativeProperty_iff_prop_representingMap.{u, v} B S hS
      (spaceProperty B S hS P) (associatedMap B S hS h).1 hMorRep U V hU hV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_
    rwa [representingMap_associatedMap]
  -- the base change of the right-hand leg along the point
  set E : Bicategory.TwoCommSq (schemeSliceMap B S hS Z z hz) b :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS Z z hz) b
  have hE : Bicategory.IsTwoFibreProduct E :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS Z z hz) b
  obtain ⟨hEfstRep, hEfstSm⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (Space.smoothMorphismProperty B S hS) E hE hb.1 hb.2
  obtain ⟨V₁, hV₁, ⟨eE₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴
    (schemeSlice B S hS Z) (fibredCategory B S hS V)
    (schemeSliceMap B S hS Z z hz).hom b.hom hb.1
    (isRepresentableByAlgebraicSpace_schemeSlice B S hS Z)
  let eE : StacksRepresentableCFG.EquivalenceOver E.pt.val.p
    (presheafOfCategories (V₁ ⋙ typeToCat)).p := eE₀
  -- the base change of `h` along the right-hand leg
  set F' : Bicategory.TwoCommSq E.snd (associatedMap B S hS h).1 :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} E.snd
      (associatedMap B S hS h).1
  have hF' : Bicategory.IsTwoFibreProduct F' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} E.snd
      (associatedMap B S hS h).1
  obtain ⟨hF'fstRep, hF'fstRel⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (spaceProperty B S hS P) F' hF' hMorRep hMorRel
  obtain ⟨A, hA, ⟨eA₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) E.pt (fibredCategory B S hS U) E.snd.hom
    (associatedMap B S hS h).1.hom hMorRep ⟨V₁, hV₁, ⟨eE⟩⟩
  let eA : StacksRepresentableCFG.EquivalenceOver F'.pt.val.p
    (presheafOfCategories (A ⋙ typeToCat)).p := eA₀
  set hTop := representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst with hTopDef
  have hPTop : P hTop :=
    (hasRelativeProperty_iff_prop_representingMap.{u, v} B S hS (spaceProperty B S hS P)
      F'.fst hF'fstRep A V₁ hA hV₁ eA eE).1 hF'fstRel
  -- the base change of the left-hand leg along the point
  set K : Bicategory.TwoCommSq (schemeSliceMap B S hS Z z hz) f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS Z z hz) f
  set D : Bicategory.TwoCommSq K.snd a :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} K.snd a
  have hD : Bicategory.IsTwoFibreProduct D :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} K.snd a
  have haSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a ha.1 :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS a ha.1).1 hsurj
  obtain ⟨hDfstRep, hDfstSm⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (Space.smoothMorphismProperty B S hS) D hD ha.1 ha.2
  obtain ⟨_, hDfstSu⟩ := exists_hasRelativeProperty_fst_of_baseChange B S hS
    (Space.surjectiveMorphismProperty B S hS) D hD ha.1 haSu
  -- the cancellation, into the common target `(Sch/Z) ×_𝒴 S_U`
  have hcf : (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f) ⋙
      𝒴.val.p = (fibredCategory B S hS U).val.p := by
    rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p f,
      CatFiberedInGroupoids.homFunctor_comp_p a]
  have htarget : (TwoFibreProductOver.structureFunctor (Over.map Z.hom)
      (fibredCategory B S hS U).val.p 𝒴.val.p z
      (CatFiberedInGroupoids.homFunctor a ⋙
        CatFiberedInGroupoids.homFunctor f)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (Over.map Z.hom)
      (fibredCategory B S hS U).val.p 𝒴.val.p z
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (Functor.IsFiberedInGroupoids.over_map Z.hom)
      (fibredCategory B S hS U).isFiberedInGroupoids 𝒴.isFiberedInGroupoids hz hcf
  have hθrefl : ∀ uu : (fibredCategory B S hS U).val.obj,
      𝒴.val.p.IsHomLift (𝟙 ((fibredCategory B S hS U).val.p.obj uu))
        ((Iso.refl (CatFiberedInGroupoids.homFunctor a ⋙
          CatFiberedInGroupoids.homFunctor f)).hom.app uu) := by
    intro uu
    have hbb : (fibredCategory B S hS U).val.p.obj uu =
        𝒴.val.p.obj ((CatFiberedInGroupoids.homFunctor a ⋙
          CatFiberedInGroupoids.homFunctor f).obj uu) :=
      (Functor.congr_obj hcf uu).symm
    rw [hbb]
    change 𝒴.val.p.IsHomLift _ (𝟙 ((CatFiberedInGroupoids.homFunctor a ⋙
      CatFiberedInGroupoids.homFunctor f).obj uu))
    infer_instance
  set targetP := TwoFibreProductOver.structureFunctor (Over.map Z.hom)
    (fibredCategory B S hS U).val.p 𝒴.val.p z
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
  set cancD := TwoFibreProductOver.cancelSnd (Over.map Z.hom) 𝒳.val.p 𝒴.val.p
    (fibredCategory B S hS U).val.p z (CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor a)
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p f) (Iso.refl _) hθrefl
  set cancF := TwoFibreProductOver.cancelSnd (Over.map Z.hom)
    (fibredCategory B S hS V).val.p 𝒴.val.p (fibredCategory B S hS U).val.p z
    (CatFiberedInGroupoids.homFunctor b)
    (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1)
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p b)
    (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x)
  have hcancDstr : cancD ⋙ targetP = D.pt.val.p :=
    TwoFibreProductOver.cancelSnd_comp_structureFunctor (Over.map Z.hom) 𝒳.val.p 𝒴.val.p
      (fibredCategory B S hS U).val.p z (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor a)
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) (Iso.refl _) hθrefl
  have hcancFstr : cancF ⋙ targetP = F'.pt.val.p :=
    TwoFibreProductOver.cancelSnd_comp_structureFunctor (Over.map Z.hom)
      (fibredCategory B S hS V).val.p 𝒴.val.p (fibredCategory B S hS U).val.p z
      (CatFiberedInGroupoids.homFunctor b)
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1)
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p b)
      (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x)
  obtain ⟨FD, hFD, ηD, εD, hηD, hεD⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over D.pt.val.p targetP
      D.pt.isFiberedInGroupoids htarget cancD hcancDstr
      (TwoFibreProductOver.isEquivalence_cancelSnd (Over.map Z.hom) 𝒳.val.p 𝒴.val.p
        (fibredCategory B S hS U).val.p z (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor a)
        (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        (CatFiberedInGroupoids.homFunctor_comp_p a) (Iso.refl _) hθrefl)
  have hwc : (cancF ⋙ FD) ⋙ D.pt.val.p = F'.pt.val.p :=
    (congrArg (fun k : _ ⥤ BigFppfOver B S hS => cancF ⋙ k) hFD).trans hcancFstr
  set cMor : F'.pt ⟶ D.pt := Bicategory.InducedBicategory.mkHom ⟨cancF ⋙ FD, hwc⟩
  have hFDequiv : Functor.IsEquivalence FD :=
    (CategoryTheory.Equivalence.mk cancD FD ηD.symm εD).symm.isEquivalence_functor
  have hcEquiv : Functor.IsEquivalence cMor.hom.toFunctor := by
    change Functor.IsEquivalence (cancF ⋙ FD)
    have h1 := TwoFibreProductOver.isEquivalence_cancelSnd (Over.map Z.hom)
      (fibredCategory B S hS V).val.p 𝒴.val.p (fibredCategory B S hS U).val.p z
      (CatFiberedInGroupoids.homFunctor b)
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1)
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p b)
      (CatFiberedInGroupoids.homFunctor_comp_p (associatedMap B S hS h).1)
      (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x)
    infer_instance
  obtain ⟨hαRep, hαSm, hαSu⟩ := exists_smooth_surjective_of_comp_isEquivalence B S hS cMor D.fst
    (cMor ≫ D.fst) rfl hDfstRep hDfstSm hDfstSu
  refine ⟨A, V₁, hA, hV₁,
    equivalenceOverInvMap B S hS A eA ≫ (cMor ≫ D.fst),
    equivalenceOverInvMap B S hS V₁ eE ≫ E.fst,
    hTop, ?_, ?_, ?_, ?_, hPTop⟩
  · -- the comparison 2-cell between the two iterated products, over the slice
    set fstT := TwoFibreProductOver.fst (Over.map Z.hom) (fibredCategory B S hS U).val.p
      𝒴.val.p z (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
    let ι : CatFiberedInGroupoids.homFunctor (F'.fst ≫ E.fst) ≅
        CatFiberedInGroupoids.homFunctor (cMor ≫ (D.fst ≫ K.fst)) :=
      { hom := Functor.whiskerLeft cancF (Functor.whiskerRight εD.inv fstT)
        inv := Functor.whiskerLeft cancF (Functor.whiskerRight εD.hom fstT)
        hom_inv_id := by
          ext x
          change fstT.map (εD.inv.app (cancF.obj x)) ≫
            fstT.map (εD.hom.app (cancF.obj x)) = _
          rw [← Functor.map_comp, Iso.inv_hom_id_app]
          exact fstT.map_id _
        inv_hom_id := by
          ext x
          change fstT.map (εD.hom.app (cancF.obj x)) ≫
            fstT.map (εD.inv.app (cancF.obj x)) = _
          rw [← Functor.map_comp, Iso.hom_inv_id_app]
          exact fstT.map_id _ }
    have hvert : ∀ x : F'.pt.val.obj,
        (schemeSlice B S hS Z).val.p.IsHomLift (𝟙 (F'.pt.val.p.obj x)) (ι.hom.app x) := by
      intro x
      have h1 : targetP.IsHomLift (𝟙 (targetP.obj (cancF.obj x)))
          (εD.inv.app (cancF.obj x)) :=
        @IsHomLift.lift_id_inv _ _ _ _ targetP (targetP.obj (cancF.obj x)) _ _
          (εD.app (cancF.obj x)) (hεD (cancF.obj x))
      have h2 : (Over.map Z.hom).IsHomLift (𝟙 (targetP.obj (cancF.obj x)))
          (fstT.map (εD.inv.app (cancF.obj x))) :=
        Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq
          (𝟙 (targetP.obj (cancF.obj x))) (εD.inv.app (cancF.obj x))
      have hb2 : targetP.obj (cancF.obj x) = F'.pt.val.p.obj x :=
        Functor.congr_obj hcancFstr x
      rwa [hb2] at h2
    have hcongr := representingMap_congr_twoIso (𝒜 := F'.pt)
      (𝒞 := schemeSlice B S hS Z) B S hS A (yoneda.obj Z) eA
      (schemeSliceEquivalenceOver B S hS Z)
      (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso ι hvert) :
        F'.fst ≫ E.fst ≅ cMor ≫ (D.fst ≫ K.fst))
    have hleft : representingMap B S hS (fibredCategory B S hS A) (schemeSlice B S hS Z) A
        (yoneda.obj Z) (StacksRepresentableCFG.EquivalenceOver.refl _)
        (schemeSliceEquivalenceOver B S hS Z)
        ((associatedMap B S hS hTop).1 ≫ (equivalenceOverInvMap B S hS V₁ eE ≫ E.fst))
        = hTop ≫ representingMap B S hS E.pt (schemeSlice B S hS Z) V₁ (yoneda.obj Z) eE
            (schemeSliceEquivalenceOver B S hS Z) E.fst := by
      rw [representingMap_comp (𝒜 := fibredCategory B S hS A)
        (ℬ := fibredCategory B S hS V₁) (𝒞 := schemeSlice B S hS Z) B S hS A V₁ (yoneda.obj Z)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (schemeSliceEquivalenceOver B S hS Z), representingMap_associatedMap]
      rw [representingMap_equivalenceOverInvMap_comp (𝒳 := E.pt) (𝒞 := schemeSlice B S hS Z)
        B S hS V₁ (yoneda.obj Z) eE (schemeSliceEquivalenceOver B S hS Z)]
    have hright : representingMap B S hS (fibredCategory B S hS A) (schemeSlice B S hS Z) A
        (yoneda.obj Z) (StacksRepresentableCFG.EquivalenceOver.refl _)
        (schemeSliceEquivalenceOver B S hS Z)
        (equivalenceOverInvMap B S hS A eA ≫ (cMor ≫ (D.fst ≫ K.fst)))
        = hTop ≫ representingMap B S hS E.pt (schemeSlice B S hS Z) V₁ (yoneda.obj Z) eE
            (schemeSliceEquivalenceOver B S hS Z) E.fst := by
      rw [representingMap_equivalenceOverInvMap_comp (𝒳 := F'.pt) (𝒞 := schemeSlice B S hS Z)
        B S hS A (yoneda.obj Z) eA (schemeSliceEquivalenceOver B S hS Z), ← hcongr]
      rw [representingMap_comp (𝒜 := F'.pt) (ℬ := E.pt) (𝒞 := schemeSlice B S hS Z)
        B S hS A V₁ (yoneda.obj Z) eA eE (schemeSliceEquivalenceOver B S hS Z), hTopDef]
    exact nonempty_iso_of_representingMap_eq (𝒜 := fibredCategory B S hS A)
      (𝒞 := schemeSlice B S hS Z) B S hS A (yoneda.obj Z)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (schemeSliceEquivalenceOver B S hS Z) (hleft.trans hright.symm)
  · exact isRelativelySmooth_comp B S hS (equivalenceOverInvMap B S hS A eA) (cMor ≫ D.fst)
      (isRelativelySmooth_equivalenceOverInvMap (𝒳 := F'.pt) B S hS A hA eA) ⟨hαRep, hαSm⟩
  · exact isSurjectiveOnObjects_comp B S hS
      (fibredCategory B S hS A).val.p F'.pt.val.p K.pt.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS A eA))
      (CatFiberedInGroupoids.homFunctor (cMor ≫ D.fst))
      (CatFiberedInGroupoids.homFunctor_comp_p (cMor ≫ D.fst))
      (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := F'.pt) B S hS A eA)
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
        (cMor ≫ D.fst) hαRep).2 hαSu)
  · exact isRelativelySmooth_comp B S hS (equivalenceOverInvMap B S hS V₁ eE) E.fst
      (isRelativelySmooth_equivalenceOverInvMap (𝒳 := E.pt) B S hS V₁ hV₁ eE)
      ⟨hEfstRep, hEfstSm⟩

/-- **The existential smooth-diagram test implies the relative property, Stacks 06FM.** The
forward half of the last assertion of Stacks 06FM.

For each scheme-valued point `z` of `𝒴`, the base change of `f` along it is representable by an
algebraic space and the slice is represented by `h_Z`, and
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre` identifies the induced morphism of
representing presheaves with the structural morphism of the lower-shriek extension that the
relative property tests.  So it is enough that the base change pass the smooth-diagram test,
which is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_schemePointBaseChange`, and then
theorem 2's forward half applies. -/
theorem hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsome : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasRelativeProperty.{u, u, u + 1, v} B S hS (spaceProperty B S hS P) f hf := by
  intro Z z hz T hT he
  refine (prop_algebraicSpaceMap_iff B S hS (spaceProperty B S hS P) Z T hT).2 ?_
  obtain ⟨eT⟩ := he
  have hΛ : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor Z.hom).obj T) :=
    isAlgebraicSpace_viewOver B Z.left.1 S Z.left.2 hS Z.hom T hT
  have hreloc := representingMap_relocalizeFibre B S hS Z f z T eT hz
  have hgoal := prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS P hP
      (𝒳 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) f).pt)
      (𝒴 := schemeSlice B S hS Z)
      ((OverShriek.relocalizePresheafFunctor Z.hom).obj T) (yoneda.obj Z) hΛ
      (isAlgebraicSpace_yoneda B S hS Z)
      (relocalizeFibreEquivalence B S hS Z f z T eT)
      (schemeSliceEquivalenceOver B S hS Z)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) f).fst
      (hasPropertyOnSomeSmoothDiagram_schemePointBaseChange B S hS P f Z z hz hsome)
  rwa [hreloc] at hgoal

/-- **Stacks 06FM, the assertion for a representable morphism.** Let `P` be a property of
morphisms of algebraic spaces over `S` smooth local on the source-and-target which is moreover
stable under base change and local at the target for the fppf precoverage, and let `f : 𝒳 ⟶ 𝒴`
be a 1-morphism of algebraic stacks over `S` representable by algebraic spaces. Then `f` passes
the existential smooth-diagram test of condition (2) exactly when it has the relative property
`P` in the sense of Stacks 03YK, i.e. of Properties of Stacks, Section 04XB.

Algebraicity of the source is not used in either direction; it is kept because it is part of the
statement of the tagged assertion. -/
@[stacks 06FM "representable morphism"]
theorem hasPropertyOnSomeSmoothDiagram_iff_relative
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (_h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P f ↔
      HasRelativeProperty.{u, u, u + 1, v} B S hS (spaceProperty B S hS P) f hf :=
  ⟨hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS P hP f hf,
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS P h𝒴 f hf⟩

end AlgebraicGeometry.Stack

end
