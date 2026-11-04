module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base change of a property of 1-morphisms of algebraic stacks

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target ([Stacks, Tag 06F8]) and whose restriction to algebraic spaces is stable under
base change. The induced property of 1-morphisms of algebraic stacks — the existential
smooth-diagram test of [Stacks, Tag 06FM], `AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram`
— is stable under base change: for any 2-fibre product square over a cospan `g : 𝒴' ⟶ 𝒴`,
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, if `f` passes the test then so does the projection to `𝒴'`.
This is [Stacks, Tag 06FQ].

## Main results

* `AlgebraicGeometry.Stack.prop_pullbackSnd`: a `P` whose restriction to algebraic spaces is
  stable under base change is inherited by the second projection of a presheaf fibre product of
  algebraic spaces.
* `AlgebraicGeometry.Stack.prop_of_isPullback`: the same read off an arbitrary cartesian square
  of algebraic spaces, for a `P` also stable under precomposition with a smooth morphism.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_isEquivalence`: a 1-morphism whose underlying
  functor is an equivalence is surjective on objects.
* `AlgebraicGeometry.Stack.isRelativelySmooth_comp_of_isEquivalence` and
  `AlgebraicGeometry.Stack.isRelativelySmooth_of_isEquivalence_comp`: smoothness is preserved by
  postcomposition and by precomposition with an equivalence.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence`: the smooth-diagram
  test moves along an equivalence of the apex.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct`: hence it is
  independent of which 2-fibre product of the cospan is used.
* `AlgebraicGeometry.Stack.prop_representingMap_fst`: the morphism of representing presheaves
  induced by the first projection of a 2-fibre product of represented categories has `P` as soon
  as the one induced by the second leg of the cospan does.
* `hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace`, in the namespace
  `AlgebraicGeometry.Stack`: base change of the test along a 1-morphism out of a category
  representable by an algebraic space.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas`: descent of
  the test along a smooth 1-morphism surjective on objects.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_twoIso`: the same descent with
  no fibre-product hypothesis, along any smooth 1-morphism surjective on objects over any smooth
  1-morphism of targets.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange`:
  base change of the test, asking only that the restriction of `P` to algebraic spaces be stable
  under base change.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange`: base change of the test for
  a `P` smooth local on the source-and-target.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06D5](https://stacks.math.columbia.edu/tag/06D5)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of the property on algebraic spaces -/

/-- For a property `P` of morphisms of algebraic spaces over `S` whose restriction to the
category of algebraic spaces is stable under base change, the second projection of the presheaf
fibre product of `h : U ⟶ V` with `m : V' ⟶ V` has `P` as soon as `h` does. -/
theorem prop_pullbackSnd
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    {U V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (hV' : IsAlgebraicSpace B S hS V')
    (h : U ⟶ V) (m : V' ⟶ V) (hPh : P h) :
    P (pullback.snd h m) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := spaceProperty B S hS P)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)
      (ObjectProperty.homMk m : (⟨V', hV'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)) hPh

/-- For a property `P` of morphisms of algebraic spaces over `S` stable under precomposition
with a smooth morphism and whose restriction to algebraic spaces is stable under base change, a
morphism `m` with `P` and any morphism `n` with the same target, every cartesian square over
`(m, n)` has `P` on its projection to the source of `n`. -/
theorem prop_of_isPullback
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hprecomp : ∀ {X₀ Y₀ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hZ : IsAlgebraicSpace B S hS Z₀) (f : X₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀),
      Space.IsSmooth B S hS f → P g → P (f ≫ g))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    {X Y Y' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (hW : IsAlgebraicSpace B S hS W)
    (m : X ⟶ Y) (n : Y' ⟶ Y) (p : W ⟶ X) (q : W ⟶ Y')
    (sq : IsPullback p q m n) (hm : P m) :
    P q := by
  have hpb : IsPullback (pullback.fst m n) (pullback.snd m n) m n := IsPullback.of_hasPullback m n
  have hsnd : P (pullback.snd m n) := prop_pullbackSnd B S hS P hX hY hY' m n hm
  have hpbalg : IsAlgebraicSpace B S hS (pullback m n) :=
    isAlgebraicSpace_pullback B S hS m n hX hY' hY
  have he : (hpb.isoIsPullback X Y' sq).hom ≫ q = pullback.snd m n :=
    IsPullback.isoIsPullback_hom_snd X Y' hpb sq
  have hcomp : P ((hpb.isoIsPullback X Y' sq).inv ≫ (hpb.isoIsPullback X Y' sq).hom ≫ q) :=
    hprecomp hW hpbalg hY' (hpb.isoIsPullback X Y' sq).inv
      ((hpb.isoIsPullback X Y' sq).hom ≫ q)
      (Space.isSmooth_of_isIso B S hS hW hpbalg (hpb.isoIsPullback X Y' sq).inv)
      (by rwa [he])
  rwa [Iso.inv_hom_id_assoc] at hcomp

/-! ### Transports of the smooth-diagram criterion -/

/-- A 1-morphism whose underlying functor is an equivalence is surjective on objects in the
sense of Stacks 06D4, with no field extension. -/
theorem isSurjectiveOnObjects_of_isEquivalence
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (e : 𝒜 ⟶ ℬ)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e)) :
    IsSurjectiveOnObjects B S hS 𝒜.val.p ℬ.val.p (CatFiberedInGroupoids.homFunctor e) := by
  obtain ⟨F, hF, _, ε, _, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒜.val.p ℬ.val.p
      𝒜.isFiberedInGroupoids ℬ.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor e)
      (CatFiberedInGroupoids.homFunctor_comp_p e) he
  intro U hU y hy
  refine ⟨U, hU, 𝟙 U, F.obj y, (Functor.congr_obj hF y).trans hy, ε.hom.app y, ?_⟩
  exact hy ▸ hε y

/-- Smoothness in the sense of Stacks 04XB is preserved by postcomposition with a 1-morphism
whose underlying functor is an equivalence. -/
theorem isRelativelySmooth_comp_of_isEquivalence
    {𝒰 𝒦 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒰 ⟶ 𝒦) (e : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e))
    (ha : IsRelativelySmooth.{u, u, u + 1} B S hS a) :
    IsRelativelySmooth.{u, u, u + 1} B S hS (a ≫ e) := by
  obtain ⟨F, hF, η, ε, hη, _⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒦.val.p 𝒲.val.p
      𝒦.isFiberedInGroupoids 𝒲.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor e)
      (CatFiberedInGroupoids.homFunctor_comp_p e) he
  have hbEquiv : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor e) F
      η.symm ε).isEquivalence_inverse
  have haId : Functor.IsEquivalence (BasedFunctor.id 𝒰.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒰.val.obj))
  have hν : ∀ x : 𝒰.val.obj, 𝒦.val.p.IsHomLift (𝟙 (𝒰.val.p.obj x))
      ((Functor.isoWhiskerLeft (CatFiberedInGroupoids.homFunctor a) η).symm.hom.app x) := by
    intro x
    have hb : 𝒦.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x) = 𝒰.val.p.obj x :=
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) x
    have h1 : 𝒦.val.p.IsHomLift
        (𝟙 (𝒦.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x)))
        (η.inv.app ((CatFiberedInGroupoids.homFunctor a).obj x)) :=
      @IsHomLift.lift_id_inv _ _ _ _ 𝒦.val.p
        (𝒦.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x)) _ _
        (η.app ((CatFiberedInGroupoids.homFunctor a).obj x))
        (hη ((CatFiberedInGroupoids.homFunctor a).obj x))
    rwa [hb] at h1
  exact isRelativelySmooth_of_equivalences B S hS (a ≫ e) a (BasedFunctor.id 𝒰.val) ⟨F, hF⟩
    (BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft (CatFiberedInGroupoids.homFunctor a) η).symm hν) ha

/-- Smoothness in the sense of Stacks 04XB is preserved by precomposition with a 1-morphism
whose underlying functor is an equivalence. -/
theorem isRelativelySmooth_of_isEquivalence_comp
    {𝒰 𝒦 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (e : 𝒰 ⟶ 𝒦) (q : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e))
    (hq : IsRelativelySmooth.{u, u, u + 1} B S hS q) :
    IsRelativelySmooth.{u, u, u + 1} B S hS (e ≫ q) := by
  have he' : Functor.IsEquivalence e.hom.toFunctor := he
  have hid : Functor.IsEquivalence (BasedFunctor.id 𝒲.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒲.val.obj))
  exact isRelativelySmooth_of_equivalences B S hS (e ≫ q) q e.hom (BasedFunctor.id 𝒲.val)
    (Iso.refl _) hq

/-- Condition (2) of Stacks 06FM moves along an equivalence of the source: if `r : 𝒦 ⟶ 𝒴` is
2-isomorphic to `e ≫ q` for an `e` whose underlying functor is an equivalence, then `q : 𝒲 ⟶ 𝒴`
passes the existential smooth-diagram test as soon as `r` does. -/
theorem hasPropertyOnSomeSmoothDiagram_of_isEquivalence
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒦 𝒲 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (q : 𝒲 ⟶ 𝒴) (r : 𝒦 ⟶ 𝒴) (e : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e)) (θ : r ≅ e ≫ q)
    (hr : HasPropertyOnSomeSmoothDiagram B S hS P r) :
    HasPropertyOnSomeSmoothDiagram B S hS P q := by
  obtain ⟨U, V, hU, hV, a, b, h₀, ⟨η⟩, ha, hsurj, hb, hPh⟩ := hr
  refine ⟨U, V, hU, hV, a ≫ e, b, h₀,
    ⟨η ≪≫ Bicategory.whiskerLeftIso a θ ≪≫ (α_ a e q).symm⟩,
    isRelativelySmooth_comp_of_isEquivalence B S hS a e he ha, ?_, hb, hPh⟩
  exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p 𝒦.val.p 𝒲.val.p
    (CatFiberedInGroupoids.homFunctor a) (CatFiberedInGroupoids.homFunctor e)
    (CatFiberedInGroupoids.homFunctor_comp_p e) hsurj
    (isSurjectiveOnObjects_of_isEquivalence B S hS e he)

/-- Condition (2) of Stacks 06FM does not depend on the chosen 2-fibre product: if the
existential smooth-diagram test holds for the first projection of one 2-fibre product of a
cospan of categories fibred in groupoids, it holds for the first projection of any other. -/
theorem hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (R₁ R₂ : Bicategory.TwoCommSq g f)
    (h₁ : Bicategory.IsTwoFibreProduct R₁) (h₂ : Bicategory.IsTwoFibreProduct R₂)
    (hR : HasPropertyOnSomeSmoothDiagram B S hS P R₁.fst) :
    HasPropertyOnSomeSmoothDiagram B S hS P R₂.fst := by
  have d : Bicategory.TwoCommSq.PreHom R₁ R₂ := Quotient.out (h₂.from R₁)
  exact hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS P R₂.fst R₁.fst d.hom
    (Bicategory.isEquivalence_of_isTwoFibreProduct h₁ h₂ d) d.isoFst hR

/-- If the morphism of representing presheaves induced by `q` has `P`, then so does the one
induced by the first projection of the canonical 2-fibre product square of `(p, q)`, as soon as
the restriction of `P` to algebraic spaces is stable under base change. -/
theorem prop_representingMap_fst
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    (𝒜 ℬ 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (hT : IsAlgebraicSpace B S hS T)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (p : 𝒜 ⟶ 𝒞) (q : ℬ ⟶ 𝒞)
    [(twoFibreProductStructureFunctor B S hS 𝒜 ℬ 𝒞 p q).IsFibered]
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒜 ℬ 𝒞 p q)
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hq : P (representingMap B S hS ℬ 𝒞 G H eG eH q)) :
    P (representingMap B S hS
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt 𝒜 T F eT eF
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).fst) := by
  let Fa : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let Ga : AlgebraicSpaces B S hS := ⟨G, hG⟩
  let Ha : AlgebraicSpaces B S hS := ⟨H, hH⟩
  let Ta : AlgebraicSpaces B S hS := ⟨T, hT⟩
  have hsqA : IsPullback
      (ObjectProperty.homMk (representingMap B S hS
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt ℬ T G eT eG
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).snd) : Ta ⟶ Ga)
      (ObjectProperty.homMk (representingMap B S hS
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt 𝒜 T F eT eF
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).fst) : Ta ⟶ Fa)
      (ObjectProperty.homMk (representingMap B S hS ℬ 𝒞 G H eG eH q) : Ga ⟶ Ha)
      (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F H eF eH p) : Fa ⟶ Ha) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      (isPullback_representingMap_twoFibreProduct B S hS 𝒜 ℬ 𝒞 F G H eF eG eH p q T eT)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := spaceProperty B S hS P) hsqA hq

/-- Base change of condition (2) of Stacks 06FM along a 1-morphism out of a category
representable by an algebraic space: given a smooth diagram over `f : 𝒳 ⟶ 𝒴` whose left
vertical 1-morphism is surjective on objects and whose top horizontal morphism has `P`, the base
change of `f` along `c : 𝒯 ⟶ 𝒴` carries one too, as soon as `𝒯` is representable by an algebraic
space. -/
theorem hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    {𝒳 𝒴 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (c : 𝒯 ⟶ 𝒴)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯)
    (hsome : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasPropertyOnSomeSmoothDiagram B S hS P
      (twoFibreProductSquare.{u, u, u + 1, u + 1} c f).fst := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hsurj, hb, hPh⟩ := hsome
  obtain ⟨T₀, hT₀, ⟨e𝒯⟩⟩ := h𝒯
  set K := twoFibreProductSquare.{u, u, u + 1, u + 1} c f with hKdef
  set E := twoFibreProductSquare.{u, u, u + 1, u + 1} c b with hEdef
  have hE : Bicategory.IsTwoFibreProduct E :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c b
  have hEfst : IsRelativelySmooth.{u, u, u + 1} B S hS E.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴 𝒯 b c E hE hb
  obtain ⟨V₁, hV₁, ⟨eE⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴 𝒯
    (fibredCategory B S hS V) c.hom b.hom hb.1 ⟨T₀, hT₀, ⟨e𝒯⟩⟩
  have hMorRep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS h).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS h).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  set F' := twoFibreProductSquare.{u, u, u + 1, u + 1} E.snd (associatedMap B S hS h).1
    with hF'def
  obtain ⟨A, hA, ⟨eA⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) E.pt (fibredCategory B S hS U) E.snd.hom
    (associatedMap B S hS h).1.hom hMorRep ⟨V₁, hV₁, ⟨eE⟩⟩
  have hFib : (twoFibreProductStructureFunctor B S hS E.pt (fibredCategory B S hS U)
      (fibredCategory B S hS V) E.snd (associatedMap B S hS h).1).IsFibered :=
    F'.pt.isFiberedInGroupoids.isFibered
  have hPTop : P (representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst) :=
    prop_representingMap_fst B S hS P E.pt (fibredCategory B S hS U)
      (fibredCategory B S hS V) V₁ U V A hV₁ hU hV hA eE
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd (associatedMap B S hS h).1 eA
      (by rwa [representingMap_associatedMap B S hS U V h])
  set D := twoFibreProductSquare.{u, u, u + 1, u + 1} K.snd a with hDdef
  have hD : Bicategory.IsTwoFibreProduct D :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} K.snd a
  have hDfst : IsRelativelySmooth.{u, u, u + 1} B S hS D.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS U) 𝒳 K.pt a
      K.snd D hD ha
  have haSu := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u}
    B S hS a ha.1).1 hsurj
  have hDfstSurj := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u}
    B S hS D.fst hDfst.1).2
    (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳 K.pt a K.snd D hD
      ha.1 haSu)
  have hLD : Bicategory.IsTwoFibreProduct
      (cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)) :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)
  have hLF : Bicategory.IsTwoFibreProduct
      (cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1 (a ≫ f) η) :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1
      (a ≫ f) η
  have cPre : Bicategory.TwoCommSq.PreHom
      (cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1 (a ≫ f) η)
      (cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)) :=
    Quotient.out
      (hLD.from (cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1 (a ≫ f) η))
  have hcEq : Functor.IsEquivalence cPre.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hLF hLD cPre
  have hcomp : IsRelativelySmooth.{u, u, u + 1} B S hS (cPre.hom ≫ D.fst) :=
    isRelativelySmooth_of_isEquivalence_comp B S hS cPre.hom D.fst hcEq hDfst
  refine ⟨A, V₁, hA, hV₁,
    equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA ≫ (cPre.hom ≫ D.fst),
    equivalenceOverInvMap B S hS (𝒳 := E.pt) V₁ eE ≫ E.fst,
    representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst, ?_, ?_, ?_, ?_, hPTop⟩
  · have hcongr := representingMap_congr_twoIso (𝒜 := F'.pt) (𝒞 := 𝒯) B S hS A T₀ eA e𝒯
      cPre.isoFst
    have hleft : representingMap B S hS (fibredCategory B S hS A) 𝒯 A T₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯
        ((associatedMap B S hS (representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst)).1 ≫
          (equivalenceOverInvMap B S hS (𝒳 := E.pt) V₁ eE ≫ E.fst))
        = representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst ≫
          representingMap B S hS E.pt 𝒯 V₁ T₀ eE e𝒯 E.fst := by
      rw [representingMap_comp (𝒜 := fibredCategory B S hS A)
        (ℬ := fibredCategory B S hS V₁) (𝒞 := 𝒯) B S hS A V₁ T₀
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯, representingMap_associatedMap,
        representingMap_comp (𝒜 := fibredCategory B S hS V₁) (ℬ := E.pt) (𝒞 := 𝒯)
        B S hS V₁ V₁ T₀ (StacksRepresentableCFG.EquivalenceOver.refl _) eE e𝒯,
        representingMap_equivalenceOverInvMap (𝒳 := E.pt) B S hS V₁ eE, Category.id_comp]
    have hright : representingMap B S hS (fibredCategory B S hS A) 𝒯 A T₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯
        (equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA ≫ (cPre.hom ≫
          (cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)).fst))
        = representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst ≫
          representingMap B S hS E.pt 𝒯 V₁ T₀ eE e𝒯 E.fst := by
      rw [representingMap_comp (𝒜 := fibredCategory B S hS A) (ℬ := F'.pt) (𝒞 := 𝒯)
        B S hS A A T₀ (StacksRepresentableCFG.EquivalenceOver.refl _) eA e𝒯,
        representingMap_equivalenceOverInvMap (𝒳 := F'.pt) B S hS A eA, Category.id_comp]
      exact hcongr.symm.trans (representingMap_comp (𝒜 := F'.pt) (ℬ := E.pt) (𝒞 := 𝒯)
        B S hS A V₁ T₀ eA eE e𝒯 F'.fst E.fst)
    obtain ⟨e2, he2⟩ := Quotient.exact
      ((morphismSpaceEquiv B S hS (fibredCategory B S hS A) 𝒯 A T₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯).injective (hleft.trans hright.symm))
    exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e2 he2)⟩
  · exact isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_equivalenceOverInvMap B S hS (𝒳 := F'.pt) A hA eA) hcomp
  · exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS A).val.p F'.pt.val.p
      K.pt.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA))
      (CatFiberedInGroupoids.homFunctor (cPre.hom ≫ D.fst))
      (CatFiberedInGroupoids.homFunctor_comp_p (cPre.hom ≫ D.fst))
      (isSurjectiveOnObjects_equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA)
      (isSurjectiveOnObjects_comp B S hS F'.pt.val.p D.pt.val.p K.pt.val.p
        (CatFiberedInGroupoids.homFunctor cPre.hom)
        (CatFiberedInGroupoids.homFunctor D.fst)
        (CatFiberedInGroupoids.homFunctor_comp_p D.fst)
        (isSurjectiveOnObjects_of_isEquivalence B S hS cPre.hom hcEq) hDfstSurj)
  · exact isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_equivalenceOverInvMap B S hS (𝒳 := E.pt) V₁ hV₁ eE) hEfst

/-- Descent of condition (2) of Stacks 06FM along a smooth 1-morphism surjective on objects.
Let `t : 𝒯 ⟶ 𝒴'` be smooth and surjective on objects and let `M` be a 2-fibre product of the
cospan `(q, t)` for some `q : 𝒲 ⟶ 𝒴'`. If the base change `M.snd` of `q` along `t` passes the
existential smooth-diagram test, then so does `q`. -/
theorem hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒲 𝒴' 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (q : 𝒲 ⟶ 𝒴') (t : 𝒯 ⟶ 𝒴')
    (M : Bicategory.TwoCommSq q t) (hM : Bicategory.IsTwoFibreProduct M)
    (ht : IsRelativelySmooth.{u, u, u + 1} B S hS t)
    (htSurj : IsSurjectiveOnObjects B S hS 𝒯.val.p 𝒴'.val.p
      (CatFiberedInGroupoids.homFunctor t))
    (hsome : HasPropertyOnSomeSmoothDiagram B S hS P M.snd) :
    HasPropertyOnSomeSmoothDiagram B S hS P q := by
  have hMfst : IsRelativelySmooth.{u, u, u + 1} B S hS M.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS 𝒯 𝒴' 𝒲 t q M hM ht
  have htSurjRel := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u}
    B S hS t ht.1).1 htSurj
  have hMfstSurj := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u}
    B S hS M.fst hMfst.1).2
    (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) 𝒯 𝒴' 𝒲 t q M hM ht.1 htSurjRel)
  obtain ⟨U, V, hU, hV, a, b, h₀, ⟨η⟩, ha, hsurj, hb, hPh⟩ := hsome
  refine ⟨U, V, hU, hV, a ≫ M.fst, b ≫ t, h₀, ⟨?_⟩,
    isRelativelySmooth_comp B S hS a M.fst ha hMfst, ?_,
    isRelativelySmooth_comp B S hS b t hb ht, hPh⟩
  · exact (α_ _ b t).symm ≪≫ Bicategory.whiskerRightIso η t ≪≫ (α_ a M.snd t) ≪≫
      Bicategory.whiskerLeftIso a M.iso.symm ≪≫ (α_ a M.fst q).symm
  · exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p M.pt.val.p 𝒲.val.p
      (CatFiberedInGroupoids.homFunctor a) (CatFiberedInGroupoids.homFunctor M.fst)
      (CatFiberedInGroupoids.homFunctor_comp_p M.fst) hsurj hMfstSurj

/-- The smooth-diagram criterion descends along a smooth surjection of sources. Let
`f₁ : 𝒜 ⟶ ℬ` and `f₂ : 𝒜' ⟶ ℬ'` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S`, let `w : 𝒜 ⟶ 𝒜'` be smooth and surjective on objects, let `s : ℬ ⟶ ℬ'` be
smooth, and let `f₁ ≫ s` be 2-isomorphic to `w ≫ f₂`. Then `f₂` passes the existential
smooth-diagram test as soon as `f₁` does. -/
theorem hasPropertyOnSomeSmoothDiagram_of_comp_twoIso
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒜 𝒜' ℬ ℬ' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f₁ : 𝒜 ⟶ ℬ) (f₂ : 𝒜' ⟶ ℬ') (w : 𝒜 ⟶ 𝒜') (s : ℬ ⟶ ℬ')
    (hw : IsRelativelySmooth B S hS w)
    (hwsurj : IsSurjectiveOnObjects B S hS 𝒜.val.p 𝒜'.val.p
      (CatFiberedInGroupoids.homFunctor w))
    (hs : IsRelativelySmooth B S hS s)
    (θ : f₁ ≫ s ≅ w ≫ f₂)
    (h₁ : HasPropertyOnSomeSmoothDiagram B S hS P f₁) :
    HasPropertyOnSomeSmoothDiagram B S hS P f₂ := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hasurj, hb, hPh⟩ := h₁
  refine ⟨U, V, hU, hV, a ≫ w, b ≫ s, h, ⟨?_⟩,
    isRelativelySmooth_comp B S hS a w ha hw, ?_,
    isRelativelySmooth_comp B S hS b s hb hs, hPh⟩
  · exact (Bicategory.associator (associatedMap B S hS h).1 b s).symm ≪≫
      Bicategory.whiskerRightIso η s ≪≫ Bicategory.associator a f₁ s ≪≫
      Bicategory.whiskerLeftIso a θ ≪≫ (Bicategory.associator a w f₂).symm
  · exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p 𝒜.val.p 𝒜'.val.p
      (CatFiberedInGroupoids.homFunctor a) (CatFiberedInGroupoids.homFunctor w)
      (CatFiberedInGroupoids.homFunctor_comp_p w) hasurj hwsurj

/-- A property of morphisms of algebraic spaces over `S` whose restriction to algebraic spaces
is stable under base change induces, through the existential smooth-diagram criterion of
Stacks 06FM, a property of 1-morphisms of algebraic stacks over `S` stable under arbitrary
2-fibre-product base change. -/
theorem hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [hbase : (spaceProperty B S hS P).IsStableUnderBaseChange]
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P Q.fst.hom := by
  obtain ⟨hfib, hstack, hdiag, T, k, hk, hkprop⟩ := 𝒴'.property
  set t : schemeFibredCategory B S hS T ⟶ 𝒴'.val :=
    Bicategory.InducedBicategory.mkHom k with htdef
  have ht : IsRelativelySmooth.{u, u, u + 1} B S hS t :=
    ⟨hk, fun W y hy G hG he => (hkprop W y hy G hG he).2⟩
  have htSurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS T).val.p
      𝒴'.val.val.p (CatFiberedInGroupoids.homFunctor t) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS t hk).mpr
      (fun W y hy G hG he => (hkprop W y hy G hG he).1)
  set Rs := (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).swap with hRsdef
  have hRs : Bicategory.IsTwoFibreProduct Rs :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
  set M := twoFibreProductSquare.{u, u, u + 1, u + 1} Rs.fst t with hMdef
  have hM : Bicategory.IsTwoFibreProduct M :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Rs.fst t
  have hL : Bicategory.IsTwoFibreProduct
      ((cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom t (t ≫ g.hom) (Iso.refl _)).swap) :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom t (t ≫ g.hom)
        (Iso.refl _))
  have hK := hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace
    B S hS P f.hom (t ≫ g.hom)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS T) hf
  have hMsnd : HasPropertyOnSomeSmoothDiagram B S hS P M.snd :=
    hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P
      (twoFibreProductSquare.{u, u, u + 1, u + 1} (t ≫ g.hom) f.hom)
      ((cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom t (t ≫ g.hom) (Iso.refl _)).swap)
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} (t ≫ g.hom) f.hom) hL hK
  have hRsfst : HasPropertyOnSomeSmoothDiagram B S hS P Rs.fst :=
    hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas B S hS P Rs.fst t M hM ht
      htSurj hMsnd
  set Rst := twoFibreProductSquareAlgebraicStacks B S hS g f with hRstdef
  have hRst : Bicategory.IsTwoFibreProduct Rst :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  have d : Bicategory.TwoCommSq.PreHom Rst Q := Quotient.out (hQ.from Rst)
  have k' : Bicategory.TwoCommSq.PreHom Q Rst := Quotient.out (hRst.from Q)
  obtain ⟨θ, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (k'.comp d)
      (Bicategory.TwoCommSq.PreHom.id Q) :=
    Quotient.exact (hQ.hom_ext (Quotient.mk _ (k'.comp d)) (𝟙 Q))
  have hQu : Bicategory.IsTwoFibreProduct Q.underlying :=
    Bicategory.isTwoFibreProduct_of_section
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom)
      d.underlying k'.hom.hom
      (Bicategory.InducedBicategory.isoHom (f := (k'.comp d).hom)
        (g := (Bicategory.TwoCommSq.PreHom.id Q).hom) θ)
  exact hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P Rs Q.underlying
    hRs hQu hRsfst

/-- A property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target and whose restriction to algebraic spaces is stable under base change induces,
through the existential smooth-diagram criterion of Stacks 06FM, a property of 1-morphisms of
algebraic stacks over `S` stable under arbitrary 2-fibre-product base change. -/
@[stacks 06FQ]
theorem hasPropertyOnSomeSmoothDiagram_baseChange
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (_hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    [hbase : (spaceProperty B S hS P).IsStableUnderBaseChange]
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P Q.fst.hom :=
  hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange B S hS P f g Q hQ hf

end AlgebraicGeometry.Stack

end
