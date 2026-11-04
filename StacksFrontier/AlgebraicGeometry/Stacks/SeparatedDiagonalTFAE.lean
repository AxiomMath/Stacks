module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict

/-!
# The four conditions of Stacks 04YS

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` which is representable by algebraic spaces. Stacks 04YS asserts the
equivalence of

1. `f` is separated,
2. `Δ_f` is a closed immersion,
3. `Δ_f` is proper, and
4. `Δ_f` is universally closed,

the last three in the relative sense of Properties of Stacks, Section 04XB. This file proves
that equivalence.

## Main results

* `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_tfae`: **Stacks 04YS**, the equivalence
  of all four conditions.
* `AlgebraicGeometry.Stack.isSeparated_iff_isClosedImmersion_relativeDiagonal`: the equivalence
  of conditions (1) and (2).
* `AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal`: part (2) of
  **Stacks 04XS** for a 1-morphism representable by algebraic spaces.
* `AlgebraicGeometry.Stack.representingMap_twoFibreProductFst` and
  `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_iff`: the morphism of
  algebraic spaces represented by the first projection of `𝒴' ×_𝒴 𝒳` is identified with the one
  represented by the second projection of `𝒳 ×_𝒴 𝒴'`.
* `AlgebraicGeometry.Stack.exists_schemePoint_relativeDiagonal_baseChange`: a scheme-valued point
  of `𝒳 ×_{f, 𝒴, f} 𝒳` lifts through the right-hand leg of the square of Stacks 04YR, with the
  two base changes of the two relative diagonals identified over the site of the test scheme.

## Implementation notes

The exchange of the two factors of a 2-fibre product is `CategoryTheory.TwoFibreProductOver.swap`,
whose identities `swap ⋙ fst = snd`, `swap ⋙ snd = fst` and `swap ⋙ swap = 𝟭` hold by `rfl`.

Part (2) of Stacks 04XS is proved here only for a 1-morphism representable by algebraic spaces.
The general statement, for an arbitrary 1-morphism of algebraic stacks, rests on Stacks 04XR and
is `AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack`; the tag
04XS therefore stays off everything below.

## References

* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v' u'

/-- If `p`, `q`, `r` and `s` are identities and `h' = h`, then `p ≫ h = (r ≫ q ≫ h') ≫ s`. -/
lemma comp_eq_of_eq_id_fwd {C : Type u'} [Category.{v'} C] {A A' : C}
    (p q r : A ⟶ A) (s : A' ⟶ A') (h h' : A ⟶ A')
    (hp : p = 𝟙 A) (hq : q = 𝟙 A) (hr : r = 𝟙 A) (hs : s = 𝟙 A') (hh : h' = h) :
    p ≫ h = (r ≫ q ≫ h') ≫ s := by
  subst hp hq hr hs hh; simp

/-- If `p`, `q`, `r` and `s` are identities and `h' = h`, then `p ≫ r ≫ q ≫ h' = h ≫ s`. -/
lemma comp_eq_of_eq_id_bwd {C : Type u'} [Category.{v'} C] {A A' : C}
    (p q r : A ⟶ A) (s : A' ⟶ A') (h h' : A ⟶ A')
    (hp : p = 𝟙 A) (hq : q = 𝟙 A) (hr : r = 𝟙 A) (hs : s = 𝟙 A') (hh : h' = h) :
    p ≫ r ≫ q ≫ h' = h ≫ s := by
  subst hp hq hr hs hh; simp

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Exchanging the two factors of a 2-fibre product -/

section Swap

variable {𝒳 𝒴 𝒴' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)

/-- **Exchanging the two factors of a 2-fibre product of categories fibred in groupoids over the
big fppf site of `S`**, as a 1-morphism `𝒴' ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒴 𝒴'`. It is
`CategoryTheory.TwoFibreProductOver.swap`, which is strictly over the site. -/
noncomputable def twoFibreProductSwap :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.swap 𝒴'.val.p 𝒳.val.p 𝒴.val.p
        g.hom.toFunctor f.hom.toFunctor
      w := TwoFibreProductOver.swap_comp_structureFunctor .. }

/-- The exchange composed with the projection to `𝒴'` of `𝒳 ×_𝒴 𝒴'` is the projection to `𝒴'` of
`𝒴' ×_𝒴 𝒳`, on the nose. -/
lemma twoFibreProductSwap_comp_snd :
    twoFibreProductSwap B S hS f g ≫
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd =
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).fst := rfl

/-- The exchange composed with the projection to `𝒳` of `𝒳 ×_𝒴 𝒴'` is the projection to `𝒳` of
`𝒴' ×_𝒴 𝒳`, on the nose. -/
lemma twoFibreProductSwap_comp_fst :
    twoFibreProductSwap B S hS f g ≫
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst =
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd := rfl

/-- The exchange is an involution, on the nose. -/
lemma twoFibreProductSwap_comp_twoFibreProductSwap :
    twoFibreProductSwap B S hS f g ≫ twoFibreProductSwap B S hS g f = 𝟙 _ := rfl

/-- **The exchange of the two factors, as an equivalence over the big fppf site of `S`.** Its unit
and counit are identities. -/
noncomputable def twoFibreProductSwapEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt.val.p
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.val.p :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (TwoFibreProductOver.swap_comp_structureFunctor
      𝒴'.val.p 𝒳.val.p 𝒴.val.p g.hom.toFunctor f.hom.toFunctor)
    { inv := TwoFibreProductOver.swap 𝒳.val.p 𝒴'.val.p 𝒴.val.p f.hom.toFunctor g.hom.toFunctor
      inv_over := TwoFibreProductOver.swap_comp_structureFunctor ..
      unitIso := Iso.refl _
      counitIso := Iso.refl _
      unit_vertical := fun _ => IsHomLift.id rfl
      counit_vertical := fun _ => IsHomLift.id rfl }

variable (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eA : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt.val.p
      (presheafOfCategories (A ⋙ typeToCat)).p)
    (eA' : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.val.p
      (presheafOfCategories (A ⋙ typeToCat)).p)

/-- **The automorphism of a representing presheaf induced by the exchange of the two factors.**
If one presheaf `A` represents both `𝒴' ×_𝒴 𝒳` and `𝒳 ×_𝒴 𝒴'`, the exchange 1-morphism induces
an isomorphism `A ≅ A` of representing presheaves. -/
noncomputable def representingMapSwapIso : A ≅ A where
  hom := representingMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt A A eA eA'
    (twoFibreProductSwap B S hS f g)
  inv := representingMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt A A eA' eA
    (twoFibreProductSwap B S hS g f)
  hom_inv_id := by
    rw [← representingMap_comp B S hS A A A eA eA' eA (twoFibreProductSwap B S hS f g)
      (twoFibreProductSwap B S hS g f), twoFibreProductSwap_comp_twoFibreProductSwap,
      representingMap_id]
  inv_hom_id := by
    rw [← representingMap_comp B S hS A A A eA' eA eA' (twoFibreProductSwap B S hS g f)
      (twoFibreProductSwap B S hS f g), twoFibreProductSwap_comp_twoFibreProductSwap,
      representingMap_id]

variable (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒴'.val.p (presheafOfCategories (H ⋙ typeToCat)).p)

/-- **The swap reconciliation.** The morphism of representing presheaves induced by the
projection `𝒴' ×_𝒴 𝒳 ⟶ 𝒴'` is the one induced by the projection `𝒳 ×_𝒴 𝒴' ⟶ 𝒴'`, precomposed
with the automorphism of the representing presheaf that the exchange of the two factors induces.
-/
theorem representingMap_twoFibreProductFst :
    representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt 𝒴' A H eA eH
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).fst =
      representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt A A eA eA'
          (twoFibreProductSwap B S hS f g) ≫
        representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴' A H eA' eH
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd := by
  rw [← representingMap_comp B S hS A A H eA eA' eH (twoFibreProductSwap B S hS f g)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd]
  rfl

/-- **The swap reconciliation, as an equivalence of properties.** A property of morphisms of
algebraic spaces over `S` which respects isomorphisms holds of the morphism of representing
presheaves induced by the projection `𝒴' ×_𝒴 𝒳 ⟶ 𝒴'` exactly when it holds of the one induced
by the projection `𝒳 ×_𝒴 𝒴' ⟶ 𝒴'`. -/
theorem prop_representingMap_twoFibreProductFst_iff
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (hA : IsAlgebraicSpace B S hS A) (hH : IsAlgebraicSpace B S hS H) :
    P (ObjectProperty.homMk (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt 𝒴' A H eA eH
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).fst) :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩) ↔
      P (ObjectProperty.homMk (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴' A H eA' eH
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd) :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩) := by
  refine P.arrow_mk_iso_iff (Arrow.isoMk
    (ObjectProperty.isoMk _ (representingMapSwapIso B S hS f g A eA eA'))
    (Iso.refl _) ?_)
  apply ObjectProperty.hom_ext
  exact ((representingMap_twoFibreProductFst B S hS f g A eA eA' H eH).symm).trans
    (Category.comp_id _).symm

end Swap

/-! ### The big fppf site of a scheme as an algebraic stack -/

section SliceStack

variable (U : BigFppfOver B S hS)

/-- **The big fppf site of a scheme `U` over `S`, viewed as a category fibred in groupoids over
the big fppf site of `S`, is an algebraic stack.** -/
theorem isAlgebraicStack_schemeSlice :
    IsAlgebraicStack.{u, w} B S hS (schemeSlice B S hS U).val :=
  isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS (schemeSlice B S hS U)
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, ⟨schemeSliceEquivalenceOver B S hS U⟩⟩

/-- The big fppf site of a scheme `U` over `S` as an object of the 2-category of algebraic stacks
over `S` (Stacks 03YP). -/
def schemeSliceStack : AlgebraicStacks.{u, w} B S hS :=
  ⟨schemeSlice B S hS U, isAlgebraicStack_schemeSlice.{u, w} B S hS U⟩

variable {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)

/-- A scheme-valued point of an algebraic stack, read as a 1-morphism of algebraic stacks out of
the big fppf site of the test scheme. -/
def schemeSliceStackMap : schemeSliceStack.{u, w} B S hS U ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom (schemeSliceMap B S hS U y hy)

end SliceStack

/-! ### The right-hand leg of the base-change square, objectwise -/

section MapDiagSimp

variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (wv : (twoFibreProduct B S hS 𝒴'.val (twoFibreProductAlgebraicStack B S hS f g).val
      (twoFibreProductAlgebraicStack B S hS f g).val
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom).val.obj)

/-- The first `𝒳`-component of the image of an object under the right-hand leg `r × r`. -/
@[simp] lemma diagonalMapDiag_hom_obj_x :
    ((diagonalMapDiag B S hS f g).hom.obj wv).x = wv.x.x := rfl

/-- The second `𝒳`-component of the image of an object under the right-hand leg `r × r`. -/
@[simp] lemma diagonalMapDiag_hom_obj_y :
    ((diagonalMapDiag B S hS f g).hom.obj wv).y = wv.y.x := rfl

/-- The comparison isomorphism of the image of an object under the right-hand leg `r × r`. -/
@[simp] lemma diagonalMapDiag_hom_obj_iso_hom :
    ((diagonalMapDiag B S hS f g).hom.obj wv).iso.hom =
      wv.x.iso.hom ≫ g.hom.hom.toFunctor.map wv.iso.hom ≫ wv.y.iso.inv := rfl

end MapDiagSimp

/-! ### Conditions (1) and (2) of Stacks 04YS after base change to a scheme-valued point -/

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
/-- **Conditions (1) and (2) of Stacks 04YS agree after base change to a scheme-valued point.**
Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `y` be a scheme-valued point
of `𝒴` over `U`, and let `F` be an algebraic space over `U` representing the base change of `f`
along `y`. Then the relative diagonal of the base change `𝒳 ×_𝒴 U ⟶ U` is a closed immersion in
the sense of Stacks 04XB exactly when the structural morphism of `F`, read over `S`, is
separated. -/
theorem isClosedImmersion_relativeDiagonal_baseChange_iff_isSeparated :
    IsClosedImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS
        (twoFibreProductAlgebraicStack B S hS f
          (schemeSliceStackMap.{u, w} B S hS U y hy)).val
        (schemeSliceStack.{u, w} B S hS U).val
        (twoFibreProductSquareAlgebraicStacks B S hS f
          (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom) ↔
      Space.IsSeparated B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
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
  refine Iff.trans (isClosedImmersion_relativeDiagonal_iff_isSeparated_representingMap B S hS
    Q.val 𝒴'.val f'.hom A (yoneda.obj U) eQ (schemeSliceEquivalenceOver B S hS U) hA
    (isAlgebraicSpace_yoneda B S hS U) T eT hT hΔ) ?_
  refine Iff.trans (Iff.symm (prop_representingMap_twoFibreProductFst_iff B S hS f.hom g.hom A
    eP eQ (yoneda.obj U) (schemeSliceEquivalenceOver B S hS U)
    (Space.separatedProperty B S hS) hA (isAlgebraicSpace_yoneda B S hS U))) ?_
  exact Iff.trans (Iff.of_eq (congrArg (fun k =>
      Space.separatedProperty B S hS (ObjectProperty.homMk k :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
      (representingMap_relocalizeFibre B S hS U f.hom y F e hy)))
    (Iff.symm (prop_algebraicSpaceMap_iff B S hS (Space.separatedProperty B S hS) U F hF))

include hF e in
/-- **Part (2) of Stacks 04XS for the relative diagonal of a base change to a scheme.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `y` be a scheme-valued point of
`𝒴` over `U`, and let `F` be an algebraic space over `U` representing the base change of `f`
along `y`. Then the relative diagonal of the base change `𝒳 ×_𝒴 U ⟶ U` is locally of finite
type in the sense of Stacks 04XB. -/
theorem presheaf_locallyOfFiniteType_relativeDiagonal_baseChange :
    ∀ (V : BigFppfOver B S hS)
      (zz : BigFppfOver B V.left.1 V.left.2 ⥤
        (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS U).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom.hom
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom.hom).val.obj)
      (_hzz : zz ⋙ (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS U).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom.hom
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom.hom).val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val.val.p
          (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS U).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom.hom
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom.hom).val.p zz
          (CatFiberedInGroupoids.homFunctor (relativeDiagonal.{u, u, u + 1} B S hS
            (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).val
            (schemeSliceStack.{u, w} B S hS U).val
            (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS U y hy)).snd.hom)))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (algebraicSpaceMap B S hS V
            ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj
              ⟨G, hG⟩)).hom := by
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
  let _hfib : (twoFibreProductStructureFunctor B S hS Q.val Q.val 𝒴'.val
      f'.hom f'.hom).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      f'.hom f'.hom).pt.property.isFibered
  exact isLocallyOfFiniteType_relativeDiagonal_of_representing B S hS Q.val 𝒴'.val f'.hom
    A (yoneda.obj U) eQ (schemeSliceEquivalenceOver B S hS U) hA
    (isAlgebraicSpace_yoneda B S hS U) T eT hT

end Bridge

/-! ### Lifting a scheme-valued point through the right-hand leg -/

section Lift

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (W : BigFppfOver B S hS)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (hz : z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map W.hom)
    (y : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map W.hom)

include hz in
/-- **Every scheme-valued point of `𝒳 ×_𝒴 𝒳` lifts through the right-hand leg of the
base-change square for the relative diagonal, and the base changes agree.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`, let `z` be a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳`
over `W`, and let `y` be the scheme-valued point of `𝒴` it induces. Write `𝒰 = 𝒳 ×_𝒴 W` for the
base change of `f` along `y`. Then there is a scheme-valued point of `𝒰 ×_W 𝒰` over `W` whose
base change of `Δ_{𝒰/W}` is equivalent, over the big fppf site of `W`, to the base change of
`Δ_f` along `z`. -/
theorem exists_schemePoint_relativeDiagonal_baseChange
    (hzy : z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor = y) :
    ∃ (zz : BigFppfOver B W.left.1 W.left.2 ⥤
        (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS W).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).val
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom.hom
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom.hom).val.obj)
      (_hzz : zz ⋙ (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS W).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).val
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).val
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom.hom
          (twoFibreProductSquareAlgebraicStacks B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom.hom).val.p = Over.map W.hom),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom)
          (twoFibreProductAlgebraicStack B S hS f
            (schemeSliceStackMap.{u, w} B S hS W y hy)).val.val.p
          (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS W).val
            (twoFibreProductAlgebraicStack B S hS f
              (schemeSliceStackMap.{u, w} B S hS W y hy)).val
            (twoFibreProductAlgebraicStack B S hS f
              (schemeSliceStackMap.{u, w} B S hS W y hy)).val
            (twoFibreProductSquareAlgebraicStacks B S hS f
              (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom.hom
            (twoFibreProductSquareAlgebraicStacks B S hS f
              (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom.hom).val.p zz
          (CatFiberedInGroupoids.homFunctor (relativeDiagonal.{u, u, u + 1} B S hS
            (twoFibreProductAlgebraicStack B S hS f
              (schemeSliceStackMap.{u, w} B S hS W y hy)).val
            (schemeSliceStack.{u, w} B S hS W).val
            (twoFibreProductSquareAlgebraicStacks B S hS f
              (schemeSliceStackMap.{u, w} B S hS W y hy)).snd.hom)))
        (TwoFibreProductOver.fst (Over.map W.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p z
          (CatFiberedInGroupoids.homFunctor
            (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)))) := by
  subst hzy
  set g := schemeSliceStackMap.{u, w} B S hS (𝒴 := 𝒴) W _ hy
  set Q := twoFibreProductAlgebraicStack B S hS f g
  set f' := (twoFibreProductSquareAlgebraicStacks B S hS f g).snd
  have hz₁ : (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor) ⋙ 𝒳.val.val.p =
      z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p :=
    congrArg (fun k => z ⋙ k) TwoFibreProductOver.fst_comp_eq
  have hz₂ : (z ⋙ TwoFibreProductOver.snd 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor) ⋙ 𝒳.val.val.p =
      z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p :=
    congrArg (fun k => z ⋙ k) TwoFibreProductOver.snd_comp_eq
  have hid : (𝟭 (BigFppfOver B W.left.1 W.left.2)) ⋙
      (schemeSliceStack.{u, w} B S hS W).val.val.p =
      z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p := hz.symm
  set u₁ := TwoFibreProductOver.lift 𝒳.val.val.p (schemeSliceStack.{u, w} B S hS W).val.val.p
    𝒴.val.val.p f.hom.hom.toFunctor
    (CatFiberedInGroupoids.homFunctor (schemeSliceMap B S hS W _ hy))
    (z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p)
    (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor)
    (𝟭 (BigFppfOver B W.left.1 W.left.2)) hz₁ hid (Iso.refl _)
    (fun V => IsHomLift.id ((Functor.congr_obj f.hom.hom.w ((z.obj V).x)).trans
      (z.obj V).hx))
  have hnat : ∀ {V V' : BigFppfOver B W.left.1 W.left.2} (k : V ⟶ V'),
      f.hom.hom.toFunctor.map ((z.map k).b) ≫ (z.obj V').iso.inv =
        (z.obj V).iso.inv ≫ f.hom.hom.toFunctor.map ((z.map k).a) := fun {V V'} k =>
    (CatFiberedInGroupoids.inv_comp_eq_comp_inv (z.obj V).iso (z.obj V').iso
      (f.hom.hom.toFunctor.map ((z.map k).a)) (f.hom.hom.toFunctor.map ((z.map k).b))
      (z.map k).w).symm
  set t₂ : (z ⋙ TwoFibreProductOver.snd 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor f.hom.hom.toFunctor) ⋙ f.hom.hom.toFunctor ≅
      (𝟭 (BigFppfOver B W.left.1 W.left.2)) ⋙
        CatFiberedInGroupoids.homFunctor (schemeSliceMap B S hS W
          (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
            f.hom.hom.toFunctor f.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor) hy) :=
    NatIso.ofComponents (fun V => (z.obj V).iso.symm) (fun k => hnat k)
  set u₂ := TwoFibreProductOver.lift 𝒳.val.val.p (schemeSliceStack.{u, w} B S hS W).val.val.p
    𝒴.val.val.p f.hom.hom.toFunctor
    (CatFiberedInGroupoids.homFunctor (schemeSliceMap B S hS W _ hy))
    (z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p)
    (z ⋙ TwoFibreProductOver.snd 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor)
    (𝟭 (BigFppfOver B W.left.1 W.left.2)) hz₂ hid t₂
    (fun V => by
      have := (z.obj V).vertical
      exact IsHomLift.lift_id_inv 𝒴.val.val.p ((z.obj V).base) ((z.obj V).iso))
  set zhat : BigFppfOver B W.left.1 W.left.2 ⥤
      (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS W).val Q.val Q.val
        f'.hom.hom f'.hom.hom).val.obj :=
    TwoFibreProductOver.lift Q.val.val.p Q.val.val.p
      (schemeSliceStack.{u, w} B S hS W).val.val.p f'.hom.hom.toFunctor f'.hom.hom.toFunctor
      (z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p) u₁ u₂
      (TwoFibreProductOver.lift_comp_structureFunctor ..)
      (TwoFibreProductOver.lift_comp_structureFunctor ..) (Iso.refl _)
      (fun V => IsHomLift.id (Functor.congr_obj hz V).symm)
  have hiso₁ : ∀ V, (zhat.obj V).x.iso.hom = 𝟙 _ := fun _ => rfl
  have hiso₀ : ∀ V, (zhat.obj V).iso.hom = 𝟙 _ := fun _ => rfl
  have hiso₂ : ∀ V, (zhat.obj V).y.iso.inv = (z.obj V).iso.hom := fun _ => rfl
  set θ : (zhat ⋙ (diagonalMapDiag B S hS f g).hom.toFunctor) ≅ z :=
    NatIso.ofComponents
      (fun V =>
        { hom := { hbase := 𝟙 _, a := 𝟙 _, b := 𝟙 _,
                   ha := IsHomLift.id (z.obj V).hx,
                   hb := IsHomLift.id (z.obj V).hy,
                   w := by
                     simp only [Functor.comp_obj, diagonalMapDiag_hom_obj_x,
                       diagonalMapDiag_hom_obj_y, diagonalMapDiag_hom_obj_iso_hom]
                     exact comp_eq_of_eq_id_fwd _ _ _ _ _ _
                       (f.hom.hom.toFunctor.map_id _)
                       ((congrArg g.hom.hom.toFunctor.map (hiso₀ V)).trans
                         (g.hom.hom.toFunctor.map_id _))
                       (hiso₁ V) (f.hom.hom.toFunctor.map_id _) (hiso₂ V) }
          inv := { hbase := 𝟙 _, a := 𝟙 _, b := 𝟙 _,
                   ha := IsHomLift.id (z.obj V).hx,
                   hb := IsHomLift.id (z.obj V).hy,
                   w := by
                     simp only [Functor.comp_obj, diagonalMapDiag_hom_obj_x,
                       diagonalMapDiag_hom_obj_y, diagonalMapDiag_hom_obj_iso_hom]
                     exact comp_eq_of_eq_id_bwd _ _ _ _ _ _
                       (f.hom.hom.toFunctor.map_id _)
                       ((congrArg g.hom.hom.toFunctor.map (hiso₀ V)).trans
                         (g.hom.hom.toFunctor.map_id _))
                       (hiso₁ V) (f.hom.hom.toFunctor.map_id _) (hiso₂ V) }
          hom_inv_id := by
            refine TwoFibreProductOver.Hom.ext' ?_ ?_ <;> exact Category.comp_id _
          inv_hom_id := by
            refine TwoFibreProductOver.Hom.ext' ?_ ?_ <;> exact Category.comp_id _ })
      (fun k => by
        refine TwoFibreProductOver.Hom.ext' ?_ ?_
        · show (z.map k).a ≫ 𝟙 _ = 𝟙 _ ≫ (z.map k).a
          simp
        · show (z.map k).b ≫ 𝟙 _ = 𝟙 _ ≫ (z.map k).b
          simp)
  have hzhatp : zhat ⋙ (twoFibreProduct B S hS (schemeSliceStack.{u, w} B S hS W).val Q.val
      Q.val f'.hom.hom f'.hom.hom).val.p = Over.map W.hom :=
    (TwoFibreProductOver.lift_comp_structureFunctor ..).trans hz
  refine ⟨zhat, hzhatp, ?_⟩
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS 𝒳.val
    (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
    (diagonalMapDiag B S hS f g) (diagonalBaseChangeSquare B S hS f g)
    (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f g) W zhat hzhatp
  exact ⟨E.trans (TwoFibreProductOver.reindexEquivalenceOver θ (fun V =>
    TwoFibreProductOver.structureFunctor_isHomLift (θ.hom.app V) (𝟙 _)
      (IsHomLift.id ((z.obj V).hx.trans (Functor.congr_obj hz V)))))⟩

end Lift

/-! ### The four conditions of Stacks 04YS -/

section Equivalence

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)

/-- A scheme-valued point `z` of `𝒳 ×_𝒴 𝒳` induces a scheme-valued point of `𝒴`. -/
private theorem comp_fst_comp_comp_eq (W : BigFppfOver B S hS)
    (z : BigFppfOver B W.left.1 W.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (hz : z ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map W.hom) :
    (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor f.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor) ⋙ 𝒴.val.val.p =
      Over.map W.hom :=
  (congrArg (fun k => (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor) ⋙ k) f.hom.hom.w).trans
    ((congrArg (fun k => z ⋙ k) TwoFibreProductOver.fst_comp_eq).trans hz)

include hf in
/-- **The equivalence of conditions (1) and (2) of Stacks 04YS.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` which is representable by algebraic spaces is separated, in the
relative sense of Stacks 04XB, exactly when its relative diagonal is a closed immersion in that
sense. -/
theorem isSeparated_iff_isClosedImmersion_relativeDiagonal :
    IsSeparated B S hS f.hom ↔
      IsClosedImmersion B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) := by
  constructor
  · rintro h W z hz G hG ⟨eG⟩
    have hy := comp_fst_comp_comp_eq B S hS f W z hz
    obtain ⟨F₀, hF₀, ⟨e₀⟩⟩ := hf W _ hy
    have hbr := (isClosedImmersion_relativeDiagonal_baseChange_iff_isSeparated B S hS f W _ hy
      F₀ hF₀ e₀).mpr (h W _ hy F₀ hF₀ ⟨e₀⟩)
    obtain ⟨zz, hzz, ⟨E⟩⟩ := exists_schemePoint_relativeDiagonal_baseChange B S hS f W z hz
      _ hy rfl
    exact hbr W zz hzz G hG ⟨E.trans eG⟩
  · rintro h U y hy F hF ⟨e⟩
    refine (isClosedImmersion_relativeDiagonal_baseChange_iff_isSeparated B S hS f U y hy
      F hF e).mp ?_
    exact relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.closedImmersionProperty B S hS)
      𝒳.val (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
      (diagonalMapDiag B S hS f (schemeSliceStackMap.{u, w} B S hS U y hy))
      (diagonalBaseChangeSquare B S hS f (schemeSliceStackMap.{u, w} B S hS U y hy))
      (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f
        (schemeSliceStackMap.{u, w} B S hS U y hy)) h

include hf in
/-- **Part (2) of Stacks 04XS for the relative diagonal of a 1-morphism of algebraic stacks
representable by algebraic spaces.** Every algebraic space representing a base change of `Δ_f`
along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has structural morphism all of whose
represented base changes are locally of finite type. -/
theorem presheaf_locallyOfFiniteType_relativeDiagonal :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
        = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
          (CatFiberedInGroupoids.homFunctor
            (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  rintro W z hz G hG ⟨eG⟩
  have hy := comp_fst_comp_comp_eq B S hS f W z hz
  obtain ⟨F₀, hF₀, ⟨e₀⟩⟩ := hf W _ hy
  obtain ⟨zz, hzz, ⟨E⟩⟩ := exists_schemePoint_relativeDiagonal_baseChange B S hS f W z hz
    _ hy rfl
  exact presheaf_locallyOfFiniteType_relativeDiagonal_baseChange B S hS f W _ hy F₀ hF₀ e₀
    W zz hzz G hG ⟨E.trans eG⟩

include hf in
/-- **Stacks 04YS.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces and write `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` for its relative
diagonal. The following are equivalent:

1. `f` is separated, in the relative sense of Stacks 04XB;
2. `Δ_f` is a closed immersion of algebraic stacks, part (2) of Stacks 04YL;
3. `Δ_f` is proper, in the relative sense of Stacks 04XB;
4. `Δ_f` is universally closed, in that sense. -/
@[stacks 04YS]
theorem isSeparated_relativeDiagonal_tfae :
    List.TFAE
      [IsSeparated B S hS f.hom,
       AlgebraicStacks.IsClosedImmersion B S hS
         (Bicategory.InducedBicategory.mkHom
           (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :
             𝒳 ⟶ relativeDiagonalTargetStack B S hS 𝒳 𝒴 f),
       IsProper B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom),
       UniversallyClosed B S hS
         (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)] := by
  tfae_have 1 → 2 := fun h =>
    ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f,
      (isSeparated_iff_isClosedImmersion_relativeDiagonal B S hS f hf).mp h⟩
  tfae_have 2 → 1 := fun h =>
    (isSeparated_iff_isClosedImmersion_relativeDiagonal B S hS f hf).mpr h.2
  tfae_have 2 → 3 := fun h => isProper_relativeDiagonal_of_isClosedImmersion B S hS f h.2
  tfae_have 3 → 4 := universallyClosed_of_isProper B S hS
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
  tfae_have 4 → 2 := fun h =>
    ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f,
      isClosedImmersion_relativeDiagonal_of_universallyClosed B S hS f hf
        (presheaf_locallyOfFiniteType_relativeDiagonal B S hS f hf) h⟩
  tfae_finish

end Equivalence

end AlgebraicGeometry.Stack

end
