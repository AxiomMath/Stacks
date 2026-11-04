module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocallySeparatedFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE

/-!
# Stacks 04YU: locally separated representable 1-morphisms of algebraic stacks

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` which is representable by algebraic spaces. Stacks 04YU asserts that
`f` is locally separated, in the relative sense of Properties of Stacks, Section 04XB, exactly
when its relative diagonal `Δ_f` is an immersion of algebraic stacks, part (3) of Stacks 04YL.
This file proves it.

The source says only *"Proof omitted. Hint: Argue as in the proofs of Lemmas 04YS and 04YT"*,
and this file does exactly that: it is the sibling of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE` at the other separation axiom.
Every ingredient of that file is reused unchanged — the swap reconciliation of the two 2-fibre
products `𝒴' ×_𝒴 𝒳` and `𝒳 ×_𝒴 𝒴'`, the slice site of a scheme as an algebraic stack, and the
lift of a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` through the right-hand leg of the square of
Stacks 04YR over the site — and the only thing that changes is the property of morphisms of
algebraic spaces the conditions are read at: being an immersion instead of being a closed
immersion, hence local separatedness instead of separatedness, by parts (2) and (1) of
Stacks 03HL.

## Main results

* `AlgebraicGeometry.Stack.isLocallySeparated_iff_isImmersion_relativeDiagonalAlgebraicStacks`:
  **Stacks 04YU**.
* `AlgebraicGeometry.Stack.isLocallySeparated_iff_isImmersion_relativeDiagonal`: the same
  equivalence read in the ambient 2-category of categories fibred in groupoids, where the
  immersion condition is the bare quantifier of Section 04XB without the representability
  clause part (3) of Stacks 04YL carries.
* `AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_baseChange_iff_isLocallySeparated`: the
  two conditions agree after base change to a scheme-valued point of `𝒴`, which is the step
  Stacks' own proof performs.

## Implementation notes

The three uses of a property of morphisms of algebraic spaces over `S` — the swap
reconciliation `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_iff`, the
identification `AlgebraicGeometry.Stack.representingMap_relocalizeFibre` of the structural
morphism of the base change, and
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` — all need being locally separated
packaged as a `CategoryTheory.MorphismProperty` which respects isomorphisms. That packaging is
`AlgebraicGeometry.Space.locallySeparatedMorphismProperty` of
`StacksFrontier/AlgebraicGeometry/Spaces/LocallySeparatedFppfLocalAtTarget.lean`, which this file
imports; its stability under base change — the diagonal of the base-change stability of being an
immersion of presheaves — is the instance
`AlgebraicGeometry.Space.locallySeparatedMorphismProperty_isStableUnderBaseChange` there, and
`RespectsIso` follows from it.

**The absolute 2-fibre-product form of the base-change comparison is not used here**, for the
reason recorded in `StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE`: it reads a
relative diagonal as a base change along the absolute diagonal of a product, which is a
different cospan. Nothing below mentions it; the square used is the relative one of
`StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare`, with the order of its two
factors corrected by the swap.

Neither direction needs the fppf locality of being an immersion, which this library does not
have: the conditions of Section 04XB are tested on base changes along morphisms from
representable presheaves, which is legitimate for a property of the form
`CategoryTheory.MorphismProperty.presheaf`, and that is what
`AlgebraicGeometry.Space.IsImmersion` is.

## References

* [Stacks Project, Tag 04YU](https://stacks.math.columbia.edu/tag/04YU)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Conditions (1) and (2) of Stacks 04YU after base change to a scheme-valued point -/

section Bridge

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)

include hF e in
/-- **The two conditions of Stacks 04YU agree after base change to a scheme-valued point.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `y` be a scheme-valued point of
`𝒴` over `U`, and let `F` be an algebraic space over `U` representing the base change of `f`
along `y`. Then the relative diagonal of the base change `𝒳 ×_𝒴 U ⟶ U` is an immersion in the
sense of Stacks 04XB exactly when the structural morphism of `F`, read over `S`, is locally
separated.

This is the sibling of
`AlgebraicGeometry.Stack.isClosedImmersion_relativeDiagonal_baseChange_iff_isSeparated` at the
other separation axiom, and it is assembled the same way:
`AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_iff_isLocallySeparated_representingMap` —
the equivalence of Stacks 04YU over a *represented* base — read at the base change, which is
legitimate because of the swap reconciliation
`AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_iff`: the base change as the
relative property of Stacks 04XB presents it has the point as its first factor, while the
base-change square for the diagonal has the source as its first factor. The representing
presheaf of the base change over `S` is the lower-shriek extension of `F`, by Stacks 03I5, and
its structural morphism is the morphism of representing presheaves induced by the projection, by
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`. -/
theorem isImmersion_relativeDiagonal_baseChange_iff_isLocallySeparated :
    IsImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS
        (twoFibreProductAlgebraicStack B S hS f
          (schemeSliceStackMap.{u, w} B S hS U y hy)).val
        (schemeSliceStack.{u, w} B S hS U).val
        (twoFibreProductSquareAlgebraicStacks B S hS f
          (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom) ↔
      Space.IsLocallySeparated B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  have hri : MorphismProperty.RespectsIso (Space.locallySeparatedMorphismProperty B S hS) :=
    (Space.locallySeparatedMorphismProperty_isStableUnderBaseChange B S hS).respectsIso
  set 𝒴' : AlgebraicStacks.{u, w} B S hS := schemeSliceStack.{u, w} B S hS U
  set g : 𝒴' ⟶ 𝒴 := schemeSliceStackMap.{u, w} B S hS U y hy
  set Q := twoFibreProductAlgebraicStack B S hS f g
  set f' := (twoFibreProductSquareAlgebraicStacks B S hS f g).snd
  set A := (OverShriek.relocalizePresheafFunctor U.hom).obj F
  have hA : IsAlgebraicSpace B S hS A :=
    isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF
  set eP := relocalizeFibreEquivalence B S hS U f.hom y F e
  set eQ := (twoFibreProductSwapEquivalenceOver B S hS f.hom g.hom).symm.trans eP
  have hQrep : IsRepresentableByAlgebraicSpace B S hS Q.val := ⟨A, hA, ⟨eQ⟩⟩
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS f'.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴'.property hQrep f'.hom
  obtain ⟨T, hT, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    𝒴'.val Q.val Q.val f'.hom.hom f'.hom.hom hfrep hQrep
  have hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS Q.val 𝒴'.val f'.hom).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      (isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS _ ⟨T, hT, ⟨eT⟩⟩)
      hQrep (relativeDiagonal.{u, u, u + 1} B S hS Q.val 𝒴'.val f'.hom)
  let _hfib : (twoFibreProductStructureFunctor B S hS Q.val Q.val 𝒴'.val
      f'.hom f'.hom).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      f'.hom f'.hom).pt.property.isFibered
  refine Iff.trans (isImmersion_relativeDiagonal_iff_isLocallySeparated_representingMap B S hS
    Q.val 𝒴'.val f'.hom A (yoneda.obj U) eQ (schemeSliceEquivalenceOver B S hS U) hA
    (isAlgebraicSpace_yoneda B S hS U) T eT hT hΔ) ?_
  refine Iff.trans (Iff.symm (prop_representingMap_twoFibreProductFst_iff B S hS f.hom g.hom A
    eP eQ (yoneda.obj U) (schemeSliceEquivalenceOver B S hS U)
    (Space.locallySeparatedMorphismProperty B S hS) hA (isAlgebraicSpace_yoneda B S hS U))) ?_
  exact Iff.trans (Iff.of_eq (congrArg (fun k =>
      Space.locallySeparatedMorphismProperty B S hS (ObjectProperty.homMk k :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
      (representingMap_relocalizeFibre B S hS U f.hom y F e hy)))
    (Iff.symm (prop_algebraicSpaceMap_iff B S hS
      (Space.locallySeparatedMorphismProperty B S hS) U F hF))

end Bridge

/-! ### Stacks 04YU -/

section Equivalence

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)

include hf in
/-- **Stacks 04YU in the ambient 2-category.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` which is representable by algebraic spaces is locally separated, in the relative sense
of Stacks 04XB, exactly when its relative diagonal is an immersion in that sense.

Both directions go through the base change of `f` to a scheme-valued point, where
`AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_baseChange_iff_isLocallySeparated`
applies. For the backward direction the base change of `Δ_f` is read off the square of
Stacks 04YR over the site, by Stacks 045C in the form
`AlgebraicGeometry.Stack.relativeProperty_baseChange`. For the forward direction the
scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` at which the condition is tested is first lifted
through the right-hand leg of that square, by
`AlgebraicGeometry.Stack.exists_schemePoint_relativeDiagonal_baseChange`. -/
theorem isLocallySeparated_iff_isImmersion_relativeDiagonal :
    IsLocallySeparated B S hS f.hom ↔
      IsImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) := by
  constructor
  · rintro h W z hz G hG ⟨eG⟩
    have hy : (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor f.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor) ⋙ 𝒴.val.val.p =
        Over.map W.hom :=
      (congrArg (fun k => (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
          f.hom.hom.toFunctor f.hom.hom.toFunctor) ⋙ k) f.hom.hom.w).trans
        ((congrArg (fun k => z ⋙ k) TwoFibreProductOver.fst_comp_eq).trans hz)
    obtain ⟨F₀, hF₀, ⟨e₀⟩⟩ := hf W _ hy
    have hbr := (isImmersion_relativeDiagonal_baseChange_iff_isLocallySeparated B S hS f W _ hy
      F₀ hF₀ e₀).mpr (h W _ hy F₀ hF₀ ⟨e₀⟩)
    obtain ⟨zz, hzz, ⟨E⟩⟩ := exists_schemePoint_relativeDiagonal_baseChange B S hS f W z hz
      _ hy rfl
    exact hbr W zz hzz G hG ⟨E.trans eG⟩
  · rintro h U y hy F hF ⟨e⟩
    exact (isImmersion_relativeDiagonal_baseChange_iff_isLocallySeparated B S hS f U y hy
      F hF e).mp <| relativeProperty_baseChange.{u, u, u + 1} B S hS
        (Space.immersionProperty B S hS) 𝒳.val
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
        (diagonalMapDiag B S hS f (schemeSliceStackMap.{u, w} B S hS U y hy))
        (diagonalBaseChangeSquare B S hS f (schemeSliceStackMap.{u, w} B S hS U y hy))
        (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f
          (schemeSliceStackMap.{u, w} B S hS U y hy)) h

include hf in
/-- **Stacks 04YU.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces. Then `f` is locally separated, in the relative sense of
Stacks 04XB, if and only if its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is an immersion
of algebraic stacks, part (3) of Stacks 04YL.

The content is
`AlgebraicGeometry.Stack.isLocallySeparated_iff_isImmersion_relativeDiagonal`; the
representability clause that part (3) of Stacks 04YL carries on top of the quantifier of
Stacks 04XB is automatic, by part (1) of Stacks 04XS in the form
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`. -/
@[stacks 04YU]
theorem isLocallySeparated_iff_isImmersion_relativeDiagonalAlgebraicStacks :
    IsLocallySeparated B S hS f.hom ↔
      AlgebraicStacks.IsImmersion B S hS (relativeDiagonalAlgebraicStacks B S hS f) :=
  ⟨fun h => ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f,
      (isLocallySeparated_iff_isImmersion_relativeDiagonal B S hS f hf).mp h⟩,
    fun h => (isLocallySeparated_iff_isImmersion_relativeDiagonal B S hS f hf).mpr h.2⟩

end Equivalence

end AlgebraicGeometry.Stack

end
