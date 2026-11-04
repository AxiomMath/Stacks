module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# The étale-smooth diagram criterion for a representable morphism (Stacks 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target in the sense of **Stacks 0CFZ**, stable under base change and local at the
target for the fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`
representable by algebraic spaces. The third assertion of Stacks 0CIF says that `f` passes the
existential étale-smooth diagram test exactly when it has the relative property `P` in the sense
of **Stacks 03YK**, i.e. of Properties of Stacks, Section 04XB.

This module proves the implication from the relative property to the diagram test.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty`: a
  representable 1-morphism with the relative property of Stacks 03YK passes the existential
  étale-smooth diagram test.

## Implementation notes

### The diagram

The diagram is the source's own, and it is the one the smooth analogue already builds: a
presentation `V ⟶ 𝒴` of the target by an algebraic space, obtained from the fourth clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` and transported to the category of elements of the
representable algebraic space of that scheme by
`AlgebraicGeometry.Stack.equivalenceOverInvMap` (the two steps together are
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation`), and
the base change of `f` along it. The apex of
the canonical 2-fibre product square over `(b, f)` is representable by an algebraic space `U`
(**Stacks 0300**) because `f` is representable by algebraic spaces and the slice is representable;
the left vertical 1-morphism is the backward 1-morphism of that representing equivalence followed
by the projection to `𝒳`, so

* the projection to the slice is the base change of `f` and therefore has the relative property
  (**Stacks 045C**), which the bridge of §04XB
  (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`) turns into `P` of the
  top horizontal morphism of algebraic spaces;
* the projection to `𝒳` is the base change of the presentation, hence smooth and surjective on
  objects — read off the other order of the two factors across
  `AlgebraicGeometry.Stack.twoFibreProductSwapMap` and
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_twoFibreProductSnd`, exactly as the smooth
  analogue does it.

Surjectivity of the left vertical 1-morphism is surjectivity on *points*, which is what the
étale-smooth test asks for, and it comes from surjectivity on objects through **Stacks 04XI**.

### The étale clause, which is the only new work

The étale-smooth test of Stacks 0CIF asks, beyond the smooth test of Stacks 06FM, that *every*
comparison 1-morphism from the diagram's cone into *every* 2-fibre product of `(b, f)` be étale
in the sense of Stacks 04XB. Theorem 2's route to such a clause — compute on representing
presheaves — is unavailable here, because `𝒳` and `𝒴` are arbitrary algebraic stacks and have no
representing presheaf. Instead the cone is shown to *be* a 2-fibre product, and then
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_isTwoFibreProduct` applies to any comparison
out of it.

That the cone is a 2-fibre product is
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`: the comparison of the cone with
the canonical square is the backward 1-morphism of the representing equivalence of the apex, whose
underlying functor is an equivalence, so terminality transports. The comparison is the same
pre-morphism the smooth analogue builds for
`AlgebraicGeometry.Stack.isRelativelySmooth_preHom_of_isTwoFibreProduct`, with its comparison
2-cells the 2-isomorphism of Stacks 04SW and the identity.

The second representability hypothesis of
`isRelativelyEtale_preHom_of_isTwoFibreProduct` — that the apex of the *target* square is
representable by an algebraic space — is not free, since the target square is arbitrary. It
follows from the canonical one: terminality gives a comparison into the canonical square, that
comparison is an equivalence by
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, and
`CategoryTheory.StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` carries the
representing equivalence across.

### The converse implication

The forward implication — the diagram test implies the relative property — is not proved here
but in `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelativeConverse`, as
`AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram`, and does
not follow the smooth analogue
(`AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram`). That analogue
reduces to the represented case through
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_schemePointBaseChange`, the base change
of the diagram along a scheme-valued point of the target, and at étale-smooth this base change
would need the base-changed diagram packaged at the level of algebraic *stacks*, so that its
apex needs an algebraicity witness (**Stacks 04TF**), and the étale clause base-changed at every
2-fibre product and every comparison. The converse module avoids both by applying Stacks 0CG1
directly at the level of algebraic spaces.

Nothing here carries `@[stacks 0CIF]`: one implication of an asserted equivalence is not the
tag's covering set. The key `"representable morphism"` is carried by the equivalence
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_relative`.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative property implies the existential étale-smooth diagram test, Stacks 0CIF.**
Let `P` be a property of morphisms of algebraic spaces over `S` stable under base change and
local at the target for the fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` representable by algebraic spaces. If `f` has the relative property `P` of
Stacks 03YK, then there is a diagram of algebraic spaces over `f` with smooth right vertical
1-morphism, surjective left vertical 1-morphism, étale comparison to every 2-fibre product, and
whose top horizontal morphism of algebraic spaces has `P`.

The diagram is built from a presentation of `𝒴` by a scheme and the base change of `f` along it;
see the implementation notes of this module. Neither étale-smooth locality of `P` nor any
hypothesis on the source beyond algebraicity is used in this direction.

This is one implication of the third assertion of Stacks 0CIF, so it is deliberately left
untagged; the converse is
`AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram`. -/
theorem hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hrel : HasRelativeProperty.{u, u, u + 1, v} B S hS P f.hom hf) :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS P f := by
  classical
  -- the right vertical 1-morphism of the diagram: the presentation of `𝒴`, read from an
  -- algebraic space
  obtain ⟨V, hV, b₀, hbsm, hbsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation B S hS 𝒴.property
  -- the canonical 2-fibre product square over `(b₀, f)`, in both orders of its two factors
  set R : Bicategory.TwoCommSq b₀ f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b₀ f.hom
  set R' : Bicategory.TwoCommSq f.hom b₀ :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₀
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b₀ f.hom
  have hR' : Bicategory.IsTwoFibreProduct R' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₀
  -- the projection to the slice is the base change of `f`, so it has the relative property
  have hRfstRep : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val 𝒴.val
      (fibredCategory B S hS V) f.hom b₀ R hR hf
  have hRfstRel : HasRelativeProperty.{u, u, u + 1, v} B S hS P R.fst hRfstRep :=
    hasRelativeProperty_baseChange.{u, u, u + 1, v} B S hS P 𝒳.val 𝒴.val
      (fibredCategory B S hS V) f.hom b₀ R hR hf hrel
  -- the projection to `𝒳` is the base change of `b₀`, read across the exchange of the factors
  have hreprfst' : IsRepresentableByAlgebraicSpaces B S hS R'.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS V) 𝒴.val 𝒳.val b₀ f.hom R' hR' hbsm.1
  have hsmfst' : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) R'.fst hreprfst' :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      (fibredCategory B S hS V) 𝒴.val 𝒳.val b₀ f.hom R' hR' hbsm.1 hbsm.2
  let sw := twoFibreProductSwapMap B S hS f.hom b₀
  have hswEquiv : Functor.IsEquivalence sw.hom.toFunctor := by
    show Functor.IsEquivalence (TwoFibreProductOver.swap _ _ _ _ _)
    infer_instance
  have he : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj), y ⋙ 𝒳.val.val.p = Over.map V.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) R.pt.val.p 𝒳.val.val.p y
          (CatFiberedInGroupoids.homFunctor R.snd))
        (TwoFibreProductOver.fst (Over.map V.hom) R'.pt.val.p 𝒳.val.val.p y
          (CatFiberedInGroupoids.homFunctor R'.fst))) :=
    fun V y hy => nonempty_equivalenceOver_fst_of_equivalence_source B S hS sw.hom R'.fst.hom
      V y hy
  have hreprsnd : IsRepresentableByAlgebraicSpaces B S hS R.snd.hom :=
    isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst he hreprfst'
  have hsmsnd : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) R.snd hreprsnd :=
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
      (Space.smoothMorphismProperty B S hS) R'.fst R.snd he hsmfst'
  have hsusnd : IsSurjectiveOnObjects B S hS R.pt.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor R.snd) :=
    isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS
      (fibredCategory B S hS V) 𝒴.val 𝒳.val b₀ f.hom hbsu
  -- Stacks 0300: the apex of the square is representable by an algebraic space
  obtain ⟨U, hU, ⟨eU₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴.val
    (fibredCategory B S hS V) 𝒳.val b₀.hom f.hom.hom hf
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  let eU : StacksRepresentableCFG.EquivalenceOver R.pt.val.p
    (presheafOfCategories (U ⋙ typeToCat)).p := eU₀
  let aInv : fibredCategory B S hS U ⟶ R.pt := equivalenceOverInvMap B S hS U eU
  -- the left vertical 1-morphism of the diagram
  let a₀ : fibredCategory B S hS U ⟶ 𝒳.val := aInv ≫ R.snd
  have hasm : IsRelativelySmooth B S hS a₀ :=
    isRelativelySmooth_comp B S hS aInv R.snd
      (isRelativelySmooth_equivalenceOverInvMap (𝒳 := R.pt) B S hS U hU eU) ⟨hreprsnd, hsmsnd⟩
  have hasu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor a₀) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p R.pt.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor aInv) (CatFiberedInGroupoids.homFunctor R.snd)
      (CatFiberedInGroupoids.homFunctor_comp_p R.snd)
      (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := R.pt) B S hS U eU) hsusnd
  -- the top horizontal morphism of algebraic spaces, from Stacks 04SW
  set hTop := representingMap B S hS (fibredCategory B S hS U)
    (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (aInv ≫ R.fst) with hTopDef
  have hPTop : P (ObjectProperty.homMk hTop :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) := by
    have h1 := (hasRelativeProperty_iff_prop_representingMap.{u, v} B S hS P R.fst hRfstRep
      U V hU hV eU (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hRfstRel
    rw [hTopDef, representingMap_comp (𝒜 := fibredCategory B S hS U) (ℬ := R.pt)
      (𝒞 := fibredCategory B S hS V) B S hS U U V
      (StacksRepresentableCFG.EquivalenceOver.refl _) eU
      (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_equivalenceOverInvMap (𝒳 := R.pt) B S hS U eU, Category.id_comp]
    exact h1
  -- the 1-morphism attached to the top morphism is 2-isomorphic to the comparison, by 04SW
  have hleft : representingMap B S hS (fibredCategory B S hS U)
      (fibredCategory B S hS V) U V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (associatedMap B S hS hTop).1 = hTop :=
    representingMap_associatedMap B S hS U V hTop
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS U) (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) hleft
  let eIso : (associatedMap B S hS hTop).1 ≅ aInv ≫ R.fst :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)
  -- the invertible 2-cell of the diagram, built so that the comparison below has identity
  -- comparison 2-cell along the left vertical 1-morphism
  let η : (associatedMap B S hS hTop).1 ≫ b₀ ≅ a₀ ≫ f.hom :=
    Bicategory.whiskerRightIso eIso b₀ ≪≫ Bicategory.associator aInv R.fst b₀ ≪≫
      Bicategory.whiskerLeftIso aInv R.iso ≪≫ (Bicategory.associator aInv R.snd f.hom).symm
  -- the comparison of the diagram's cone with the canonical 2-fibre product
  let k₁ : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a₀ b₀ hTop η) R :=
    { hom := aInv
      isoFst := eIso
      isoSnd := Iso.refl a₀
      compat := by
        have hid : Bicategory.whiskerRight (𝟙 a₀) f.hom = 𝟙 (a₀ ≫ f.hom) :=
          Bicategory.id_whiskerRight a₀ f.hom
        simp [η, hid] }
  have haInvEquiv : Functor.IsEquivalence aInv.hom.toFunctor := by
    show Functor.IsEquivalence eU.inv.functor
    exact eU.toEquivalence.symm.isEquivalence_functor
  -- so the cone is itself a 2-fibre product
  have hdiag : Bicategory.IsTwoFibreProduct (diagramCone B S hS f.hom a₀ b₀ hTop η) :=
    Bicategory.isTwoFibreProduct_of_isEquivalence_to hR k₁ haInvEquiv
  refine ⟨U, V, hU, hV, Bicategory.InducedBicategory.mkHom a₀,
    Bicategory.InducedBicategory.mkHom b₀, hTop, η, ?_, hbsm, ?_, hPTop⟩
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS
      (Bicategory.InducedBicategory.mkHom a₀ :
        algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳) hasm.1).2
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS a₀
        hasm.1).1 hasu)
  intro Q hQ k
  obtain ⟨eQ'⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    Q.pt.isFiberedInGroupoids R.pt.isFiberedInGroupoids
    (Quotient.out (hR.from Q)).hom.hom.toFunctor (Quotient.out (hR.from Q)).hom.hom.w
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQ hR (Quotient.out (hR.from Q)))
  exact isRelativelyEtale_preHom_of_isTwoFibreProduct B S hS hdiag hQ k
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) ⟨U, hU, ⟨eQ'.trans eU⟩⟩

end AlgebraicGeometry.Stack

end
