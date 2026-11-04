module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelPostcomposeRoutes
public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful

/-!
# The existential étale-smooth diagram criterion implies the universal one (Stacks 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on the
source-and-target (**Stacks 0CFZ**) and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over
`S`. This file proves the implication **(2) ⇒ (1)** of the first assertion of **Stacks 0CIF**: one
diagram of algebraic spaces over `f` with smooth right-hand vertical 1-morphism, surjective
left-hand vertical 1-morphism and étale comparison to the 2-fibre product, whose top horizontal
morphism has `P`, forces *every* such diagram to have `P` on its top horizontal morphism.

## The diagram, and the two routes it compares

Write `U, V, a, b, h, η` for the given diagram and `U', V', a', b', h', η'` for the arbitrary one,
and `hM`, `hM'` for the 1-morphisms of fibred categories induced by `h` and `h'`. The chase runs
over nine canonical 2-fibre products of **Stacks 003Q**:

```text
𝒦 = V' ×_𝒴 𝒳,   T₁ = 𝒦 ×_𝒳 U,    E  = T₁ ×_𝒦 U',
𝒥 = V  ×_𝒴 𝒳,   G  = 𝒥 ×_𝒳 U',   E₂ = G  ×_𝒥 U,
Sq₃ = V' ×_𝒴 V,  T₂ = Sq₃ ×_V U,  F' = Sq₃ ×_{V'} U'
```

all of them canonical, so that every projection is a base change on the nose. The comparisons `k`
of the arbitrary diagram's cone with `𝒦` and `m` of the given diagram's cone with `𝒥` are the
*explicit* ones, `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom`, so both of their
comparison 2-cells are identities and their composites with the projections are the diagrams' own
legs on the nose; each is étale because the corresponding clause holds at every 2-fibre product
and every comparison.

The final diagram of algebraic spaces is read at the apex `E`, and its two vertical 1-morphisms
are `E ⟶ U'` — the twofold base change of `a`, hence surjective on points — and `Sq₃ ⟶ V'`, the
base change of `b`, hence smooth. The top horizontal 1-morphism is `E ⟶ Sq₃`, and it is where
everything happens, because it has *two* descriptions:

* **route A**, `E ⟶ T₁ ⟶ T₂ ⟶ Sq₃`, through the two second-factor cancellations of
  **Stacks 02XD** that exhibit `T₁` and `T₂` as 2-fibre products of the one cospan `(b', a ≫ f)`.
  Its first leg is étale (a base change of `k`) and its second is an isomorphism of representing
  presheaves, so the composite has `P` by
  `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_comp_etale` — the single step
  at which `P` is used.
* **route B**, `E ⟶ E₂ ⟶ G ⟶ F' ⟶ Sq₃`, through the two cancellations that exhibit `G` and `F'`
  as 2-fibre products of the one cospan `(b, a' ≫ f)`. Its underlying 1-morphism `E ⟶ F'` is
  étale — an isomorphism, a base change of `m`, and an isomorphism — and `F'` is `Sq₃ ×_{V'} U'`,
  which **Stacks 04SD** identifies with the fibre product of the representing presheaves. So route
  B *is* the comparison into that fibre product which **Stacks 0CG1** (c) asks to be étale.

Both routes are pre-morphisms of 2-commutative squares (**Stacks 003O**) out of the one square `X`
with apex `E` over the cospan `(b', b)`, so
`CategoryTheory.Bicategory.twoFibreProduct_twoIso_of_preHom` identifies them up to a
2-isomorphism, and Stacks 04SW does not see a 2-isomorphism. Assembling each route out of named
pre-morphisms is what makes every compatibility square of Stacks 003O free: the one with content
is `CategoryTheory.CatFiberedInGroupoids.cancelFstPostcomposePreHom`, which serves both routes,
once in each of the two instantiations that exchange the two diagrams' roles.

## Main results

* `hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`, in the namespace
  `AlgebraicGeometry.Stack`: condition (2) of Stacks 0CIF implies condition (1).

## Implementation notes

No `@[stacks]` attribute. The first key of Stacks 0CIF, `"equivalence of parts (1) and (2)"`, is
an asserted *equivalence*, and one implication of an asserted equivalence is not a covering set —
the convention under which both halves of the third assertion were left untagged while only its
`iff` carries the key. The equivalence itself, whose converse implication `(1) ⇒ (2)` needs
Stacks 0CIA, is `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_some`, which
carries this key.

The square `X` is written as `(Ecan.postcompose …).swap` rather than as
`Ecan.swap.postcompose …`. The two are equal by
`CategoryTheory.Bicategory.TwoCommSq.swap_postcompose` but not definitionally, and the first
spelling is the one route A's pre-morphism lands in; route B's third leg is therefore rebuilt on
it from its own fields together with
`CategoryTheory.CatFiberedInGroupoids.swap_postcompose_iso_hom`, which is the only field of a
pre-morphism the discrepancy touches. Transporting the pre-morphism along the equality instead
would leave its underlying 1-morphism unreadable, and that 1-morphism is exactly what route B is
needed for.

Three places need the recorded `AlgebraicGeometry.Stack.representingMap` care: it is a reducible
abbreviation, so each of its three categories fibred in groupoids has to be named rather than left
to unification, and two of its functoriality steps are supplied as *terms* rather than by `rw`,
which does not fire against a pattern the goal visibly contains.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (2) of Stacks 0CIF implies condition (1).** Let `P` be étale-smooth local on the
source-and-target. If some diagram of algebraic spaces over `f : 𝒳 ⟶ 𝒴` with smooth right-hand
vertical 1-morphism, surjective left-hand vertical 1-morphism and étale comparison to every
2-fibre product of its cospan has `P` on its top horizontal morphism, then *every* diagram with
smooth right-hand vertical 1-morphism and étale comparison to every 2-fibre product has `P` on its
top horizontal morphism.

Neither diagram's left-hand vertical 1-morphism is assumed smooth, and `f` is not assumed
representable; the étale clause of the existential test supplies the representability that the
smooth analogue takes as a hypothesis. The chase and the two routes it compares are described in
the implementation notes of this module. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsome : HasPropertyOnSomeEtaleSmoothDiagram B S hS P f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f := by
  classical
  obtain ⟨U, V, hU, hV, a, b, hTop, η, hasu, hbsm, hcompar, hPtop⟩ := hsome
  intro U' V' hU' hV' a' b' h' η' hb'sm hcompar'
  let hM := (associatedMap B S hS hTop).1
  let hM' := (associatedMap B S hS h').1
  let DC := diagramCone B S hS f.hom a.hom b.hom hTop η
  let DC' := diagramCone B S hS f.hom a'.hom b'.hom h' η'
  let J := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom
  let KK := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b'.hom f.hom
  have hJ : Bicategory.IsTwoFibreProduct J :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  have hKK : Bicategory.IsTwoFibreProduct KK :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  let m := CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom f.hom DC
  let k := CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b'.hom f.hom DC'
  have hmet : IsRelativelyEtale B S hS m.hom := hcompar J hJ m
  have hket : IsRelativelyEtale B S hS k.hom := hcompar' KK hKK k
  let T₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} KK.snd a.hom
  let GG := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} J.snd a'.hom
  let Sq₃ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b'.hom b.hom
  let T₂ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.snd hM
  let F' := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.fst hM'
  let E := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} T₁.fst k.hom
  let E₂ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} GG.fst m.hom
  have hSq₃ : Bicategory.IsTwoFibreProduct Sq₃ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  -- the cancellations
  let A := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b'.hom f.hom a.hom
    (a.hom ≫ f.hom) (Iso.refl _)
  let D := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM
    (a.hom ≫ f.hom) η
  let A₂ := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b.hom f.hom a'.hom
    (a'.hom ≫ f.hom) (Iso.refl _)
  let D₂ := CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM'
    (a'.hom ≫ f.hom) η'
  let Ecan := CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} KK.snd a.hom k.hom
    a'.hom k.isoSnd.symm
  let E₂can := CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} J.snd a'.hom m.hom
    a.hom m.isoSnd.symm
  have hD : Bicategory.IsTwoFibreProduct D :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM
      (a.hom ≫ f.hom) η
  have hA₂ : Bicategory.IsTwoFibreProduct A₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b.hom f.hom
      a'.hom (a'.hom ≫ f.hom) (Iso.refl _)
  have hD₂ : Bicategory.IsTwoFibreProduct D₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM'
      (a'.hom ≫ f.hom) η'
  have hE₂can : Bicategory.IsTwoFibreProduct E₂can :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} J.snd a'.hom
      m.hom a.hom m.isoSnd.symm
  have hEcanSwap : Bicategory.IsTwoFibreProduct Ecan.swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} KK.snd a.hom
        k.hom a'.hom k.isoSnd.symm)
  let cmp := Quotient.out (hD.from A)
  let cmp₂ := Quotient.out (hD₂.from A₂)
  let wcmp := Quotient.out (hE₂can.from Ecan.swap)
  -- route A
  let X := (Ecan.postcompose f.hom hM hM' η η').swap
  let Y := E₂can.postcompose f.hom hM' hM η' η
  let uA2 := (CatFiberedInGroupoids.cancelFstPostcomposePreHom.{u, u, u + 1, u + 1} b'.hom b.hom
    f.hom a.hom hM η DC' k).swap
  let uA1 := cmp.postcomposeSnd hM η
  let uA0 := CatFiberedInGroupoids.cancelSndPostcomposeSndPreHom.{u, u, u + 1, u + 1} b'.hom
    b.hom hM (a.hom ≫ f.hom) η
  let uA : Bicategory.TwoCommSq.PreHom X Sq₃ := uA2.comp (uA1.comp uA0)
  -- route B
  let uB3₀ := wcmp.postcompose f.hom hM' hM η' η
  let uB2 := CatFiberedInGroupoids.cancelFstPostcomposePreHom.{u, u, u + 1, u + 1} b.hom b'.hom
    f.hom a'.hom hM' η' DC m
  let uB1 := (cmp₂.postcomposeSnd hM' η').swap
  let uB0 := CatFiberedInGroupoids.cancelFstPostcomposeSndPreHom.{u, u, u + 1, u + 1} b'.hom
    b.hom hM' (a'.hom ≫ f.hom) η'
  let uB3 : Bicategory.TwoCommSq.PreHom X Y :=
    { hom := uB3₀.hom
      isoFst := uB3₀.isoFst
      isoSnd := uB3₀.isoSnd
      compat := by
        rw [show X.iso.hom = (Ecan.swap.postcompose f.hom hM' hM η' η).iso.hom from
          CatFiberedInGroupoids.swap_postcompose_iso_hom.{u, u, u + 1, u + 1} Ecan f.hom hM hM'
            η η']
        exact uB3₀.compat }
  let uB : Bicategory.TwoCommSq.PreHom X Sq₃ := uB3.comp (uB2.comp (uB1.comp uB0))
  -- ### Representability of the pieces
  have hUrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU
  have hU'rep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U') :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U' hU'
  have hV'rep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS V') :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V' hV'
  have hVrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS V) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV
  have harep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hUrep a.hom
  have ha'rep : IsRepresentableByAlgebraicSpaces B S hS a'.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hU'rep a'.hom
  have hMrep : IsRepresentableByAlgebraicSpaces B S hS hM.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS hM hUrep hVrep
  have hM'rep : IsRepresentableByAlgebraicSpaces B S hS hM'.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS hM' hU'rep hV'rep
  have hKKsndrep : IsRepresentableByAlgebraicSpaces B S hS KK.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS b'.hom f.hom hb'sm.1
  have hJsndrep : IsRepresentableByAlgebraicSpaces B S hS J.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS b.hom f.hom hbsm.1
  have hT₁ : Bicategory.IsTwoFibreProduct T₁ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  have hGGsq : Bicategory.IsTwoFibreProduct GG :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  have hE : Bicategory.IsTwoFibreProduct E :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  have hE₂ : Bicategory.IsTwoFibreProduct E₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  have hT₂ : Bicategory.IsTwoFibreProduct T₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _
  have hF'sq : Bicategory.IsTwoFibreProduct F' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.fst hM'
  have hT₁fstrep : IsRepresentableByAlgebraicSpaces B S hS T₁.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) 𝒳.val KK.pt a.hom KK.snd T₁ hT₁ harep
  have hGGfstrep : IsRepresentableByAlgebraicSpaces B S hS GG.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U') 𝒳.val J.pt a'.hom J.snd GG hGGsq ha'rep
  have hT₁sndrep : IsRepresentableByAlgebraicSpaces B S hS T₁.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS KK.snd a.hom hKKsndrep
  have hGGsndrep : IsRepresentableByAlgebraicSpaces B S hS GG.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS J.snd a'.hom hJsndrep
  have hT₁rep : IsRepresentableByAlgebraicSpace B S hS T₁.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS T₁.pt (fibredCategory B S hS U)
      T₁.snd hT₁sndrep hUrep
  have hGGrep : IsRepresentableByAlgebraicSpace B S hS GG.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS GG.pt (fibredCategory B S hS U')
      GG.snd hGGsndrep hU'rep
  have hSq₃rep : IsRepresentableByAlgebraicSpace B S hS Sq₃.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS V) 𝒴.val (fibredCategory B S hS V') b.hom b'.hom Sq₃ hSq₃ hbsm.1
      hV'rep
  have hT₂rep : IsRepresentableByAlgebraicSpace B S hS T₂.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) (fibredCategory B S hS V) Sq₃.pt hM Sq₃.snd T₂ hT₂ hMrep hSq₃rep
  have hF'rep : IsRepresentableByAlgebraicSpace B S hS F'.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS U') (fibredCategory B S hS V') Sq₃.pt hM' Sq₃.fst F' hF'sq hM'rep
      hSq₃rep
  have hEsndrep : IsRepresentableByAlgebraicSpaces B S hS E.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS T₁.fst k.hom hT₁fstrep
  have hE₂sndrep : IsRepresentableByAlgebraicSpaces B S hS E₂.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS GG.fst m.hom hGGfstrep
  have hErep : IsRepresentableByAlgebraicSpace B S hS E.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS E.pt (fibredCategory B S hS U')
      E.snd hEsndrep hU'rep
  have hE₂rep : IsRepresentableByAlgebraicSpace B S hS E₂.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS E₂.pt (fibredCategory B S hS U)
      E₂.snd hE₂sndrep hUrep
  -- ### Étaleness and smoothness of the projections used
  have hEfstet : IsRelativelyEtale B S hS E.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U') KK.pt T₁.pt k.hom T₁.fst E hE
      hket
  have hE₂fstet : IsRelativelyEtale B S hS E₂.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U) J.pt GG.pt m.hom GG.fst E₂ hE₂
      hmet
  have hSq₃fstsm : IsRelativelySmooth B S hS Sq₃.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴.val
      (fibredCategory B S hS V') b.hom b'.hom Sq₃ hSq₃ hbsm
  have hSq₃sndsm : IsRelativelySmooth B S hS Sq₃.snd :=
    isRelativelySmooth_twoFibreProductSnd B S hS b'.hom b.hom hb'sm
  -- ### Surjectivity on objects of `E.snd`
  have haSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a.hom harep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS a harep).1 hasu
  have hT₁fstsu : IsSurjectiveOnObjects B S hS T₁.pt.val.p KK.pt.val.p
      (CatFiberedInGroupoids.homFunctor T₁.fst) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS T₁.fst
      hT₁fstrep).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳.val KK.pt a.hom
        KK.snd T₁ hT₁ harep haSu)
  have hEsndsu : IsSurjectiveOnObjects B S hS E.pt.val.p (fibredCategory B S hS U').val.p
      (CatFiberedInGroupoids.homFunctor E.snd) :=
    isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS T₁.pt KK.pt
      (fibredCategory B S hS U') T₁.fst k.hom hT₁fstsu
  -- ### The representing presheaves
  obtain ⟨W₂, hW₂, ⟨eW₂⟩⟩ := hT₂rep
  obtain ⟨W₃, hW₃, ⟨eW₃⟩⟩ := hSq₃rep
  obtain ⟨W₁, hW₁, ⟨eW₁⟩⟩ := hT₁rep
  obtain ⟨WG, hWG, ⟨eWG⟩⟩ := hGGrep
  obtain ⟨WF, hWF, ⟨eWF⟩⟩ := hF'rep
  obtain ⟨WE, hWE, ⟨eWE⟩⟩ := hErep
  obtain ⟨WE₂, hWE₂, ⟨eWE₂⟩⟩ := hE₂rep
  let eU' : StacksRepresentableCFG.EquivalenceOver (fibredCategory B S hS U').val.p
    (presheafOfCategories (U' ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  let eV' : StacksRepresentableCFG.EquivalenceOver (fibredCategory B S hS V').val.p
    (presheafOfCategories (V' ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  -- ### The four morphisms of algebraic spaces of the final diagram
  let φ := representingMap B S hS (fibredCategory B S hS U') (fibredCategory B S hS V') U' V'
    eU' eV' hM'
  let β := representingMap B S hS Sq₃.pt (fibredCategory B S hS V') W₃ V' eW₃ eV' Sq₃.fst
  let α := representingMap B S hS E.pt (fibredCategory B S hS U') WE U' eWE eU' E.snd
  let hh := representingMap B S hS E.pt Sq₃.pt WE W₃ eWE eW₃ uA.hom
  -- ### `β` is smooth, `α` is surjective on points
  have hβsm : Space.IsSmooth B S hS β :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS Sq₃.fst hSq₃fstsm.1 W₃ V' hW₃ hV' eW₃
      eV').1 hSq₃fstsm
  have hαsurj : Space.IsSurjective B S hS α :=
    isSurjective_representingMap_of_isSurjectiveOnObjects B S hS E.snd WE U' eWE eU' hEsndsu
  -- ### The top horizontal morphism has `P`
  have hEfstEt : Space.IsEtale B S hS
      (representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst) :=
    isEtale_representingMap_of_isRelativelyEtale B S hS E.fst hEfstet.1 WE W₁ hWE hW₁ eWE eW₁
      hEfstet
  have hcmpiso : IsIso (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b'.hom f.hom
        a.hom (a.hom ≫ f.hom) (Iso.refl _)) hD cmp W₁ W₂ eW₁ eW₂
  have hcmpEt : Space.IsEtale B S hS
      (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) :=
    Space.isEtale_of_isIso B S hS
      (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom)
  have hPk := prop_representingMap_twoFibreProductFst_comp_etale B S hS P hP hU hV hTop hPtop
    Sq₃.snd hSq₃sndsm W₃ hW₃ eW₃ W₂ hW₂ eW₂ hWE
    (representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst ≫
      representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom)
    (Space.isEtale_comp B S hS hEfstEt hcmpEt)
  have hPh : P (ObjectProperty.homMk hh : (⟨WE, hWE⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W₃, hW₃⟩) := by
    have e2 : representingMap B S hS T₁.pt Sq₃.pt W₁ W₃ eW₁ eW₃ (cmp.hom ≫ T₂.fst)
        = representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom ≫
          representingMap B S hS T₂.pt Sq₃.pt W₂ W₃ eW₂ eW₃ T₂.fst :=
      representingMap_comp B S hS W₁ W₂ W₃ eW₁ eW₂ eW₃ cmp.hom T₂.fst
    have e1 : hh = representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst ≫
        representingMap B S hS T₁.pt Sq₃.pt W₁ W₃ eW₁ eW₃ (cmp.hom ≫ T₂.fst) :=
      representingMap_comp B S hS WE W₁ W₃ eWE eW₁ eW₃ E.fst (cmp.hom ≫ T₂.fst)
    rwa [e1, e2, ← Category.assoc]
  -- ### The final square commutes
  have hcomm : α ≫ φ = hh ≫ β := by
    have e3 : α ≫ φ = representingMap B S hS E.pt (fibredCategory B S hS V') WE V' eWE eV'
        (E.snd ≫ hM') :=
      (representingMap_comp B S hS WE U' V' eWE eU' eV' E.snd hM').symm
    have e4 : hh ≫ β = representingMap B S hS E.pt (fibredCategory B S hS V') WE V' eWE eV'
        (uA.hom ≫ Sq₃.fst) :=
      (representingMap_comp B S hS WE W₃ V' eWE eW₃ eV' uA.hom Sq₃.fst).symm
    rw [e3, e4]
    exact representingMap_congr_twoIso (𝒜 := E.pt) (𝒞 := fibredCategory B S hS V') B S hS WE V'
      eWE eV' uA.isoFst
  -- ### The comparison into the fibre product is étale
  let δ := wcmp.hom ≫ (E₂.fst ≫ cmp₂.hom)
  have hδrep : representingMap B S hS E.pt F'.pt WE WF eWE eWF δ =
      representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom ≫
        (representingMap B S hS E₂.pt GG.pt WE₂ WG eWE₂ eWG E₂.fst ≫
          representingMap B S hS GG.pt F'.pt WG WF eWG eWF cmp₂.hom) :=
    (representingMap_comp B S hS WE WE₂ WF eWE eWE₂ eWF wcmp.hom
        (E₂.fst ≫ cmp₂.hom)).trans
      (congrArg (fun t => representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom ≫ t)
        (representingMap_comp B S hS WE₂ WG WF eWE₂ eWG eWF E₂.fst cmp₂.hom))
  have hwcmpiso : IsIso (representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS hEcanSwap hE₂can wcmp WE WE₂ eWE eWE₂
  have hcmp₂iso : IsIso (representingMap B S hS GG.pt F'.pt WG WF eWG eWF cmp₂.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS hA₂ hD₂ cmp₂ WG WF eWG eWF
  have hδEt : Space.IsEtale B S hS (representingMap B S hS E.pt F'.pt WE WF eWE eWF δ) := by
    rw [hδrep]
    exact Space.isEtale_comp B S hS
      (Space.isEtale_of_isIso B S hS
        (representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom))
      (Space.isEtale_comp B S hS
        (isEtale_representingMap_of_isRelativelyEtale B S hS E₂.fst hE₂fstet.1 WE₂ WG hWE₂ hWG
          eWE₂ eWG hE₂fstet)
        (Space.isEtale_of_isIso B S hS
          (representingMap B S hS GG.pt F'.pt WG WF eWG eWF cmp₂.hom)))
  have hsqF : representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd ≫ φ
      = representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst ≫ β := by
    rw [← representingMap_comp B S hS WF U' V' eWF eU' eV' F'.snd hM',
      ← representingMap_comp B S hS WF W₃ V' eWF eW₃ eV' F'.fst Sq₃.fst]
    exact (representingMap_congr_twoIso (𝒜 := F'.pt) (𝒞 := fibredCategory B S hS V') B S hS WF V'
      eWF eV' F'.iso).symm
  let _hfib : (twoFibreProductStructureFunctor B S hS Sq₃.pt (fibredCategory B S hS U')
    (fibredCategory B S hS V') Sq₃.fst hM').IsFibered := F'.pt.property.isFibered
  let cF := pullback.lift
      (representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd)
      (representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst) hsqF
  have hFiso : IsIso (pullback.lift
      (representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd)
      (representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst) hsqF) :=
    isIso_of_fibreProduct_projections B S hS β φ cF
      (fibreProductIsoRepresenting B S hS Sq₃.pt (fibredCategory B S hS U')
        (fibredCategory B S hS V') W₃ U' V' eW₃ eU' eV' Sq₃.fst hM' WF eWF)
      (by rw [pullback.lift_fst]
          exact fibreProductIsoRepresenting_hom_comp_representingMap_snd B S hS Sq₃.pt
            (fibredCategory B S hS U') (fibredCategory B S hS V') W₃ U' V' eW₃ eU' eV' Sq₃.fst
            hM' WF eWF)
      (by rw [pullback.lift_snd]
          exact fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS Sq₃.pt
            (fibredCategory B S hS U') (fibredCategory B S hS V') W₃ U' V' eW₃ eU' eV' Sq₃.fst
            hM' WF eWF)
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProduct_twoIso_of_preHom hSq₃ uA uB
  let ιB : E.snd ≅ δ ≫ F'.snd :=
    wcmp.isoFst ≪≫ Bicategory.whiskerLeftIso wcmp.hom
      (Bicategory.whiskerLeftIso E₂.fst cmp₂.isoSnd)
  have hliftEq : pullback.lift α hh hcomm =
      representingMap B S hS E.pt F'.pt WE WF eWE eWF δ ≫
        pullback.lift
          (representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd)
          (representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst) hsqF := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst,
        ← representingMap_comp B S hS WE WF U' eWE eWF eU' δ F'.snd]
      exact representingMap_congr_twoIso (𝒜 := E.pt) (𝒞 := fibredCategory B S hS U') B S hS WE U'
        eWE eU' ιB
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd,
        ← representingMap_comp B S hS WE WF W₃ eWE eWF eW₃ δ F'.fst]
      exact representingMap_congr_twoIso (𝒜 := E.pt) (𝒞 := Sq₃.pt) B S hS WE W₃ eWE eW₃ θ
  have hetale : Space.IsEtale B S hS (pullback.lift α hh hcomm) := by
    rw [hliftEq]
    exact Space.isEtale_comp B S hS hδEt
      (Space.isEtale_of_isIso B S hS (pullback.lift
        (representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd)
        (representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst) hsqF))
  -- ### Stacks 0CG1, (c) ⇒ (a)
  have hres := Space.prop_of_etale_smooth_surjective_square B S hS hP hU' hV' hWE hW₃ φ β α hh
    hcomm hβsm hαsurj hetale hPh
  have hφ : φ = h' := representingMap_associatedMap B S hS U' V' h'
  rwa [hφ] at hres

end AlgebraicGeometry.Stack

end
