module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognitionSnd

/-!
# The existential étale-smooth diagram test implies the relative property (Stacks 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on the
source-and-target (**Stacks 0CFZ**), stable under base change and local at the target for the fppf
precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable by
algebraic spaces. The converse implication —
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty` — is proved;
this module proves that the existential étale-smooth diagram test implies the relative property of
**Stacks 03YK**, which completes the third assertion of Stacks 0CIF.

## The route, and why it is not the smooth one

The smooth analogue reduces through
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_schemePointBaseChange` and then the forward
half of the representable-source-and-target assertion. At étale-smooth that would require producing
`AlgebraicGeometry.Stack.HasPropertyOnSomeEtaleSmoothDiagram` for the base-changed 1-morphism,
whose étale clause is quantified over *every* 2-fibre product of the new cospan and *every*
comparison out of the new cone, and in addition `IsAlgebraicStack` witnesses for the base-changed
source. Applying Stacks 0CG1 at the level of algebraic spaces directly removes both costs: no
algebraicity witness is needed anywhere and the étale condition is needed at *one* comparison.

So the whole direction reduces, by the Stacks 04XC/03YK plumbing, to the single statement below:
for `g : 𝒵 ⟶ 𝒴` with `𝒵` representable by an algebraic space, the first projection of `𝒵 ×_𝒴 𝒳`
has `P` on representing presheaves. That is proved by exhibiting a diagram of algebraic spaces

```text
A ---top---> W
|            |
γ            β
v            v
F ---φ---> G
```

whose right vertical is smooth, whose left vertical is surjective on points, whose top horizontal
has `P` and whose comparison `A ⟶ F ×_G W` is étale, and then applying Stacks 0CG1 (c) ⇒ (a) in
the form `AlgebraicGeometry.Space.prop_of_etale_smooth_surjective_square`.

## Which apex makes the diagram strict

The apex is the one choice that makes all four conditions free. Write `K = 𝒵 ×_𝒴 𝒳`, `W = 𝒵 ×_𝒴 V`
and `Q = 𝒳 ×_𝒴 V` for the canonical 2-fibre products of Stacks 003Q attached to the given diagram
`U ⟶ V`, `U ⟶ 𝒳`, `V ⟶ 𝒴`, and `M = W ×_𝒵 K` for the triple product. The apex is taken to be

```text
R = M ×_Q U
```

the base change along the pairing `M ⟶ Q` of the comparison `U ⟶ Q` of the given diagram, and the
two vertical 1-morphisms of the square are the two composites of `R`'s own projection to `M` with
`M`'s two projections. Then:

* the comparison `U ⟶ Q` is *explicit* — it is
  `CategoryTheory.CatFiberedInGroupoids.canonicalPreHom` of the diagram's cone with its legs
  exchanged — so its composites with the two projections of `Q` are the diagram's own legs on the
  nose, and it is étale because the diagram's clause holds at every 2-fibre product of `(b, f)` and
  every comparison, `CategoryTheory.Bicategory.isTwoFibreProduct_swap` supplying the one at the
  exchanged cospan;
* `R`'s projection to `M` is relatively étale by Stacks 045C at étaleness,
  `AlgebraicGeometry.Stack.isRelativelyEtale_baseChange`, since `R` is the *canonical* 2-fibre
  product of `(M ⟶ Q, U ⟶ Q)`;
* `R` is a 2-fibre product of `(K ⟶ 𝒳, U ⟶ 𝒳)` with legs `R.fst ≫ M.snd` and `R.snd`, so that leg
  is a base change of `U ⟶ 𝒳` and therefore surjective on points;
* `R` is *also* a 2-fibre product of `(W ⟶ V, U ⟶ V)` with legs `R.fst ≫ M.fst` and `R.snd`, so
  that leg is a base change of `U ⟶ V` and therefore has `P`;
* the square commutes by whiskering the filler of `M` with `R.fst`, Stacks 04SW not seeing the
  2-cell;
* and the comparison `A ⟶ F ×_G W` is the representing map of `R.fst` followed by the isomorphism
  of Stacks 04SD, so it is étale.

The two recognitions of `R` are the two readings of the one triple-product identity of Stacks 02XC
at a 2-fibre product which is recognised rather than canonical:
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare` applied to
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare` and to
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSndSquare`. Because both are
read through the *same* pairing `M ⟶ Q`, they are statements about one and the same apex `R`, which
is what lets the two legs of the square be `R.fst ≫ M.snd` and `R.fst ≫ M.fst` with no 2-cell
relating them to anything. No 2-cell is proved by hand anywhere in this module.

## Main results

* `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_of_etaleSmoothDiagram`:
  the base-changed statement above.
* `AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram`: the
  implication.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_relative`: the third assertion
  of Stacks 0CIF.

## Implementation notes

The key `"representable morphism"` of Stacks 0CIF is carried by
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_relative` alone, which is the
third assertion of that tag and is a single equivalence. Its two halves are each one implication
of that equivalence and so are not its covering set, and
`AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_of_etaleSmoothDiagram` is a step
in the proof rather than an assertion of the source, so both stay untagged. The sibling key
`"representable source and target"` sits on the single equivalence
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_represented`, which is the
precedent within this tag. The first key, `"equivalence of parts (1) and (2)"`, sits on
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_some`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XC](https://stacks.math.columbia.edu/tag/02XC)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A base change of a representable 1-morphism with the relative property `P` is representable and
has the relative property `P`. -/
private theorem exists_hasRelativeProperty_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) (hPf : HasRelativeProperty B S hS P f hf) :
    ∃ hRfst : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom,
      HasRelativeProperty.{u, u, u + 1, v} B S hS P R.fst hRfst :=
  ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 f g R hR hf,
    hasRelativeProperty_baseChange.{u, u, u + 1, v} B S hS P 𝒳 𝒴 𝒵 f g R hR hf hPf⟩

/-- **The base-changed step of the third assertion of Stacks 0CIF.** Let `P` be étale-smooth local
on the source-and-target, stable under base change and local at the target for the fppf
precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` passing the
existential étale-smooth diagram test. For every `g : 𝒵 ⟶ 𝒴` out of a category fibred in groupoids
representable by an algebraic space, the first projection of the canonical 2-fibre product
`𝒵 ×_𝒴 𝒳` has `P` as a morphism of representing presheaves.

The diagram of algebraic spaces and its apex are described in the implementation notes of this
module. -/
theorem prop_representingMap_twoFibreProductFst_of_etaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsome : HasPropertyOnSomeEtaleSmoothDiagram B S hS P f)
    {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵)
    (g : 𝒵 ⟶ 𝒴.val)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f.hom).pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒵.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f.hom).pt 𝒵 F G eF eG
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f.hom).fst) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) := by
  classical
  obtain ⟨U, V, hU, hV, a, b, h, η, hsurj, hbsm, hcompar, hPh⟩ := hsome
  -- the canonical squares `K = 𝒵 ×_𝒴 𝒳`, `Wq = 𝒵 ×_𝒴 V`, `Q₀ = 𝒳 ×_𝒴 V`, `Msq = Wq ×_𝒵 K`
  let hM := (associatedMap B S hS h).1
  let KK := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f.hom
  let Wq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g b.hom
  let Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom
  let Msq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Wq.fst KK.fst
  let μ := CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} g b.hom f.hom
  have hWq : Bicategory.IsTwoFibreProduct Wq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g b.hom
  have hQ₀ : Bicategory.IsTwoFibreProduct Q₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom
  -- the explicit comparison of the given diagram's cone with `𝒳 ×_𝒴 V`, and its étaleness
  let DC := diagramCone B S hS f.hom a.hom b.hom h η
  let kcone := CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom b.hom
    (Bicategory.TwoCommSq.swap DC)
  let kx := kcone.hom
  have hkxet : IsRelativelyEtale B S hS kx :=
    hcompar (Bicategory.TwoCommSq.swap Q₀) (Bicategory.isTwoFibreProduct_swap hQ₀)
      (Bicategory.TwoCommSq.PreHom.swap kcone)
  obtain ⟨hkxrep, -⟩ := id hkxet
  -- representability of the two charts' structure 1-morphisms
  have harep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) a.hom
  have hMrep : IsRepresentableByAlgebraicSpaces B S hS hM.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS hM
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  -- the right-hand chart of the base-changed diagram and its representing space
  obtain ⟨hWqfstRep, hWqfstSm⟩ := exists_hasRelativeProperty_baseChange B S hS
    (Space.smoothMorphismProperty B S hS) b.hom g Wq hWq hbsm.1 hbsm.2
  obtain ⟨W, hW, ⟨eW₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴.val 𝒵
    (fibredCategory B S hS V) g.hom b.hom.hom hbsm.1 h𝒵
  let eW : StacksRepresentableCFG.EquivalenceOver Wq.pt.val.p
    (presheafOfCategories (W ⋙ typeToCat)).p := eW₀
  -- the representing space of the triple product `Msq = (𝒵 ×_𝒴 V) ×_𝒵 (𝒵 ×_𝒴 𝒳)`
  have hKfstRep : IsRepresentableByAlgebraicSpaces B S hS KK.fst.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS KK.fst
      ⟨F, hF, ⟨eF⟩⟩ ⟨G, hG, ⟨eG⟩⟩
  obtain ⟨M, hMs, ⟨eM₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒵 Wq.pt KK.pt
    Wq.fst.hom KK.fst.hom hKfstRep ⟨W, hW, ⟨eW⟩⟩
  let eM : StacksRepresentableCFG.EquivalenceOver Msq.pt.val.p
    (presheafOfCategories (M ⋙ typeToCat)).p := eM₀
  -- the apex of the base-changed diagram, `R = Msq ×_{𝒳 ×_𝒴 V} U`, and its representing space
  let R := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} μ kx
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} μ kx
  obtain ⟨A, hA, ⟨eA₀⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS Q₀.pt Msq.pt
    (fibredCategory B S hS U) μ.hom kx.hom hkxrep ⟨M, hMs, ⟨eM⟩⟩
  let eA : StacksRepresentableCFG.EquivalenceOver R.pt.val.p
    (presheafOfCategories (A ⋙ typeToCat)).p := eA₀
  -- the two recognitions of the triple product, read at the one apex `R`
  let leftSq := CatFiberedInGroupoids.cancelSndEquivSquare.{u, u, u + 1, u + 1} KK.snd Q₀.fst
    (CatFiberedInGroupoids.tripleProductMorSnd.{u, u, u + 1, u + 1} g b.hom f.hom) kx a.hom
    (Iso.refl _)
  have hleft : Bicategory.IsTwoFibreProduct leftSq :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare.{u, u, u + 1, u + 1}
      KK.snd Q₀.fst _ kx a.hom (Iso.refl _)
      (CatFiberedInGroupoids.isEquivalence_tripleProductMorSnd.{u, u, u + 1, u + 1}
        g b.hom f.hom)
  let midSq := CatFiberedInGroupoids.cancelSndEquivSquare.{u, u, u + 1, u + 1} Wq.snd Q₀.snd
    (CatFiberedInGroupoids.tripleProductMor.{u, u, u + 1, u + 1} g b.hom f.hom) kx hM
    (Iso.refl _)
  have hmid : Bicategory.IsTwoFibreProduct midSq :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare.{u, u, u + 1, u + 1}
      Wq.snd Q₀.snd _ kx hM (Iso.refl _)
      (CatFiberedInGroupoids.isEquivalence_tripleProductMor.{u, u, u + 1, u + 1} g b.hom f.hom)
  -- the left-hand vertical is a base change of `a`, hence surjective on points
  have haSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a.hom harep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS a harep).1 hsurj
  obtain ⟨hγRep, hγSu⟩ := exists_hasRelativeProperty_baseChange B S hS
    (Space.surjectiveMorphismProperty B S hS) a.hom KK.snd leftSq hleft harep haSu
  -- the top horizontal 1-morphism is a base change of `h`, hence has `P`
  have hMorRel : HasRelativeProperty.{u, u, u + 1, v} B S hS P hM hMrep := by
    refine (hasRelativeProperty_iff_prop_representingMap.{u, v} B S hS P hM hMrep U V hU hV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_
    rwa [representingMap_associatedMap]
  obtain ⟨hTopRep, hTopRel⟩ := exists_hasRelativeProperty_baseChange B S hS P hM Wq.snd midSq hmid
    hMrep hMorRel
  -- the four morphisms of algebraic spaces of the base-changed square
  set φ := representingMap B S hS KK.pt 𝒵 F G eF eG KK.fst with hφdef
  set β := representingMap B S hS Wq.pt 𝒵 W G eW eG Wq.fst with hβdef
  set α := representingMap B S hS R.pt KK.pt A F eA eF (R.fst ≫ Msq.snd) with hαdef
  set hTop := representingMap B S hS R.pt Wq.pt A W eA eW (R.fst ≫ Msq.fst) with hTopdef
  -- the square commutes, by Stacks 04SW and the filler of the triple product
  have hYiso : (R.fst ≫ Msq.snd) ≫ KK.fst ≅ (R.fst ≫ Msq.fst) ≫ Wq.fst :=
    Bicategory.whiskerLeftIso R.fst Msq.iso.symm
  have hcomm : α ≫ φ = hTop ≫ β := by
    rw [hαdef, hφdef, hTopdef, hβdef,
      ← representingMap_comp B S hS A F G eA eF eG (R.fst ≫ Msq.snd) KK.fst,
      ← representingMap_comp B S hS A W G eA eW eG (R.fst ≫ Msq.fst) Wq.fst]
    exact representingMap_congr_twoIso B S hS A G eA eG hYiso
  -- the right-hand vertical is smooth
  have hβsm : Space.IsSmooth B S hS β :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS Wq.fst hWqfstRep W G hW hG eW eG).1
      ⟨hWqfstRep, hWqfstSm⟩
  -- the left-hand vertical is surjective on points
  have hαsurj : Space.IsSurjective B S hS α :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) (R.fst ≫ Msq.snd) hγRep A F hA hF eA eF).1 hγSu
  -- the top horizontal morphism of algebraic spaces has `P`
  have hPTop : P (ObjectProperty.homMk hTop :
      (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩) :=
    (hasRelativeProperty_iff_prop_representingMap.{u, v} B S hS P (R.fst ≫ Msq.fst) hTopRep
      A W hA hW eA eW).1 hTopRel
  -- the representing space of the triple product is the fibre product of representing presheaves
  let _hfib : (twoFibreProductStructureFunctor B S hS Wq.pt KK.pt 𝒵 Wq.fst KK.fst).IsFibered :=
    Msq.pt.property.isFibered
  have hpb := isPullback_representingMap_twoFibreProduct B S hS Wq.pt KK.pt 𝒵 W F G eW eF eG
    Wq.fst KK.fst M eM
  have hMiso : IsIso (pullback.lift _ _ hpb.w) := by
    rw [show pullback.lift _ _ hpb.w = hpb.isoPullback.hom from
      pullback.hom_ext (by rw [IsPullback.isoPullback_hom_fst]; exact pullback.lift_fst _ _ _)
        (by rw [IsPullback.isoPullback_hom_snd]; exact pullback.lift_snd _ _ _)]
    infer_instance
  -- the comparison into the fibre product is the base-changed étale comparison, up to that
  -- isomorphism
  have hliftEq : pullback.lift α hTop hcomm =
      representingMap B S hS R.pt Msq.pt A M eA eM R.fst ≫
        pullback.lift (representingMap B S hS Msq.pt KK.pt M F eM eF Msq.snd)
          (representingMap B S hS Msq.pt Wq.pt M W eM eW Msq.fst) hpb.w := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hαdef]
      exact representingMap_comp B S hS A M F eA eM eF R.fst Msq.snd
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hTopdef]
      exact representingMap_comp B S hS A M W eA eM eW R.fst Msq.fst
  have hRfstEt : IsRelativelyEtale B S hS R.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U) Q₀.pt Msq.pt kx μ R hR hkxet
  have hRfstEtRep :
      Space.IsEtale B S hS (representingMap B S hS R.pt Msq.pt A M eA eM R.fst) := by
    obtain ⟨hr, -⟩ := id hRfstEt
    exact isEtale_representingMap_of_isRelativelyEtale B S hS R.fst hr A M hA hMs eA eM hRfstEt
  have hetale : Space.IsEtale B S hS (pullback.lift α hTop hcomm) := by
    rw [hliftEq]
    exact Space.isEtale_comp B S hS hRfstEtRep (Space.isEtale_of_isIso B S hS _)
  have hres := Space.prop_of_etale_smooth_surjective_square B S hS hP hF hG hA hW φ β α hTop
    hcomm hβsm hαsurj hetale hPTop
  rwa [hφdef] at hres

/-- **The existential étale-smooth diagram test implies the relative property, Stacks 0CIF.** Let
`P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on the
source-and-target, stable under base change and local at the target for the fppf precoverage, and
let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable by algebraic spaces. If
there is a diagram of algebraic spaces over `f` with smooth right vertical 1-morphism, surjective
left vertical 1-morphism, étale comparison to every 2-fibre product and whose top horizontal
morphism of algebraic spaces has `P`, then `f` has the relative property `P` of Stacks 03YK.

This is the Stacks 04XC/03YK plumbing on top of the base-changed statement
`AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_of_etaleSmoothDiagram`: the
relative property is tested at a scheme-valued point, the fibre over it is relocalised, and the
test becomes exactly that statement at the slice of the site over the point. -/
theorem hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsome : HasPropertyOnSomeEtaleSmoothDiagram B S hS P f) :
    HasRelativeProperty.{u, u, u + 1, v} B S hS P f.hom hf := by
  intro Z z hz T hT he
  refine (prop_algebraicSpaceMap_iff B S hS P Z T hT).2 ?_
  obtain ⟨eT⟩ := he
  have hgoal := prop_representingMap_twoFibreProductFst_of_etaleSmoothDiagram
    B S hS P hP f hsome
    (isRepresentableByAlgebraicSpace_schemeSlice B S hS Z)
    (schemeSliceMap B S hS Z z hz)
    ((OverShriek.relocalizePresheafFunctor Z.hom).obj T) (yoneda.obj Z)
    (isAlgebraicSpace_viewOver B Z.left.1 S Z.left.2 hS Z.hom T hT)
    (isAlgebraicSpace_yoneda B S hS Z)
    (relocalizeFibreEquivalence B S hS Z f.hom z T eT)
    (schemeSliceEquivalenceOver B S hS Z)
  rwa [representingMap_relocalizeFibre B S hS Z f.hom z T eT hz] at hgoal

/-- **The third assertion of Stacks 0CIF.** For an étale-smooth local property `P` of morphisms of
algebraic spaces over `S` which is stable under base change and local at the target for the fppf
precoverage, and a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` representable by algebraic
spaces, the existential étale-smooth diagram test for `P` is equivalent to the relative property
`P` of Stacks 03YK.

This is the covering set of the key `"representable morphism"` of Stacks 0CIF: the key names a
single asserted equivalence, and neither half of it alone asserts that equivalence. -/
@[stacks 0CIF "representable morphism"]
theorem hasPropertyOnSomeEtaleSmoothDiagram_iff_relative
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS P f ↔
      HasRelativeProperty.{u, u, u + 1, v} B S hS P f.hom hf :=
  ⟨hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, v, w} B S hS P hP f hf,
    hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, v, w} B S hS P f hf⟩

end AlgebraicGeometry.Stack

end
