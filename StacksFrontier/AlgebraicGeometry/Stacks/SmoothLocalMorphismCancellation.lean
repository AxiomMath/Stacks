module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Cancelling a smooth-local property of 1-morphisms of algebraic stacks

Let `P` and `Q` be properties of morphisms of algebraic spaces over `S`, both smooth local on the
source-and-target, with `P` cancelling against `Q` for morphisms of algebraic spaces: `P (p ≫ q)`
and `Q q` give `P p`. Then the induced properties of 1-morphisms of algebraic stacks, given by the
existential smooth-diagram criterion, cancel the same way. At local finite presentation against
local finite type: if `g ∘ f` is locally of finite presentation and `g` is locally of finite type
then `f` is locally of finite presentation. At local finite type against `⊤`: if `g ∘ f` is
locally of finite type then so is `f`.

The criterion also cancels along the source: if `a : 𝒲 ⟶ 𝒱` is smooth and surjective on objects
and `a ≫ b` has a smooth diagram with `P`, then so does `b`. At smoothness: if `a` is smooth and
surjective and `a ≫ b` is smooth, then `b` is smooth.

## Main results

* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_top`: the property satisfied by every
  morphism of algebraic spaces over `S` is smooth local on the source-and-target.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_of_representableTarget`: the
  cancellation when the final target is the category fibred in groupoids of an algebraic space.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp`: the cancellation in general.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_comp`: if `f ≫ g` is
  locally of finite presentation and `g` is locally of finite type, then `f` is locally of finite
  presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp`: if `f ≫ g` is locally
  of finite type, then so is `f`.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_surjective`: the cancellation
  along a smooth 1-morphism of sources which is surjective on objects.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_surjective_of_isRelativelySmooth`
  and `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_surjective`: the smooth case of
  that cancellation, with smoothness of the source 1-morphism given in the relative sense and in
  the sense of the smooth-diagram criterion respectively.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06Q6](https://stacks.math.columbia.edu/tag/06Q6)
* [Stacks Project, Tag 06U9](https://stacks.math.columbia.edu/tag/06U9)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property satisfied by every morphism of algebraic spaces over `S` is smooth local on the
source-and-target. -/
theorem isSmoothLocalOnSourceAndTarget_top :
    IsSmoothLocalOnSourceAndTarget B S hS
      (⊤ : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) where
  precomp := fun _ _ _ _ _ _ _ => trivial
  pullbackSnd_of_smooth := fun _ _ _ _ _ _ _ => trivial
  iff_forall_exists_smooth_neighborhood {X Y} hX hY f :=
    ⟨fun _ x => ⟨X, Y, hX, hY, 𝟙 X, 𝟙 Y, f, x, isSmooth_id B S hS hX, isSmooth_id B S hS hY,
      pointsMap_id_apply B S hS x, by simp, trivial⟩, fun _ => trivial⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Cancellation of the existential smooth-diagram criterion over a representable target. Let `P`
cancel against `Q` for morphisms of algebraic spaces over `S`, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks and let `g : 𝒴 ⟶ 𝒮_{V₀}` be a 1-morphism into the category fibred in groupoids
of an algebraic space `V₀`. If every smooth diagram over `f ≫ g` has `P` on its top horizontal
morphism and every smooth diagram over `g` has `Q`, then some smooth diagram over `f` has `P`. -/
theorem hasPropertyOnSomeSmoothDiagram_of_comp_of_representableTarget
    (P Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hcancel : ∀ {U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V → IsAlgebraicSpace B S hS W →
      ∀ (p : U ⟶ V) (q : V ⟶ W), P (p ≫ q) → Q q → P p)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV₀ : IsAlgebraicSpace B S hS V₀)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ fibredCategory B S hS V₀)
    (hfg : HasPropertyOnEverySmoothDiagram B S hS P (f ≫ g))
    (hg : HasPropertyOnEverySmoothDiagram B S hS Q g) :
    HasPropertyOnSomeSmoothDiagram B S hS P f := by
  have hidsm : IsRelativelySmooth.{u, u, u + 1} B S hS (𝟙 (fibredCategory B S hS V₀)) :=
    isRelativelySmooth_id B S hS (isRepresentableByAlgebraicSpace_fibredCategory B S hS V₀ hV₀)
  have hideq : Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (𝟙 (fibredCategory B S hS V₀))) := by
    show Functor.IsEquivalence (𝟭 _)
    infer_instance
  have hidsu := isSurjectiveOnObjects_of_isEquivalence B S hS
    (𝟙 (fibredCategory B S hS V₀)) hideq
  have hT : IsAlgebraicStack.{u, w} B S hS (fibredCategory B S hS V₀).val :=
    isAlgebraicStack_fibredCategory.{u, w} B S hS V₀ hV₀
  obtain ⟨V₁, hV₁, b, hTopG, ⟨ηG⟩, hbsm, hbsu, hQG⟩ :=
    exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS Q h𝒴 hT g V₀ hV₀
      (𝟙 (fibredCategory B S hS V₀)) hidsm hidsu hg
  obtain ⟨U, hU, a, hTopF, ⟨ηF⟩, hasm, hasu, -⟩ :=
    exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS ⊤ h𝒳 h𝒴 f V₁ hV₁ b
      hbsm hbsu (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
  obtain ⟨κ⟩ := nonempty_twoIso_associatedMap_comp B S hS U V₁ V₀ hTopF hTopG
  set ηout : (associatedMap B S hS (hTopF ≫ hTopG)).1 ≫ (𝟙 (fibredCategory B S hS V₀)) ≅
      a ≫ (f ≫ g) :=
    Bicategory.rightUnitor _ ≪≫ κ ≪≫
      Bicategory.whiskerLeftIso _ (Bicategory.rightUnitor _).symm ≪≫
      Bicategory.whiskerLeftIso _ ηG ≪≫ (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso ηF g ≪≫ Bicategory.associator _ _ _ with hηout
  have hPtop : P (hTopF ≫ hTopG) :=
    hfg U V₀ hU hV₀ a (𝟙 (fibredCategory B S hS V₀)) (hTopF ≫ hTopG) ηout hasm hidsm
      fun R hR k => isRelativelySmooth_preHom_of_isTwoFibreProduct B S hS
        (Bicategory.isTwoFibreProduct_idCospan (f ≫ g)) hR
        (Bicategory.toIdCospan
          (diagramCone B S hS (f ≫ g) a (𝟙 (fibredCategory B S hS V₀)) (hTopF ≫ hTopG) ηout))
        k hasm
  exact ⟨U, V₁, hU, hV₁, a, b, hTopF, ⟨ηF⟩, hasm, hasu, hbsm,
    hcancel hU hV₁ hV₀ hTopF hTopG hPtop hQG⟩

/-- Cancellation of the existential smooth-diagram criterion. Let `P` and `Q` be properties of
morphisms of algebraic spaces over `S`, both smooth local on the source-and-target and both with
base-change-stable restriction to algebraic spaces, and let `P` cancel against `Q` for morphisms
of algebraic spaces. Then the induced properties of 1-morphisms of algebraic stacks cancel: if
`f ≫ g` has `P` and `g` has `Q`, then `f` has `P`. -/
theorem hasPropertyOnSomeSmoothDiagram_of_comp
    (P Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    (hQ : Space.IsSmoothLocalOnSourceAndTarget B S hS Q)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS Q).IsStableUnderBaseChange]
    (hcancel : ∀ {U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V → IsAlgebraicSpace B S hS W →
      ∀ (p : U ⟶ V) (q : V ⟶ W), P (p ≫ q) → Q q → P p)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : HasPropertyOnSomeSmoothDiagram B S hS P (f ≫ g).hom)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS Q g.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P f.hom := by
  obtain ⟨V₀, hV₀, t₀, ht₀sm, ht₀su⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒵.property
  set 𝒯 : AlgebraicStacks.{u, w} B S hS := algebraicSpaceStack.{u, w} B S hS V₀ hV₀ with h𝒯
  set t : 𝒯 ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom t₀ with ht
  set A := twoFibreProductSquareAlgebraicStacks B S hS g t with hAdef
  have hA : Bicategory.IsTwoFibreProduct A :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g t
  have hAu : Bicategory.IsTwoFibreProduct A.underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom t₀
  have hpsm : IsRelativelySmooth.{u, u, u + 1} B S hS A.fst.hom :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V₀) 𝒵.val 𝒴.val
      t₀ g.hom A.underlying hAu ht₀sm
  have hpsu : IsSurjectiveOnObjects B S hS A.pt.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor A.fst.hom) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS A.fst.hom
      hpsm.1).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS V₀) 𝒵.val 𝒴.val
        t₀ g.hom A.underlying hAu ht₀sm.1
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS t₀
          ht₀sm.1).1 ht₀su))
  set C := twoFibreProductSquareAlgebraicStacks B S hS A.fst f with hCdef
  have hC : Bicategory.IsTwoFibreProduct C :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS A.fst f
  have hAsw : Bicategory.IsTwoFibreProduct A.swap := Bicategory.isTwoFibreProduct_swap hA
  have hRout : Bicategory.IsTwoFibreProduct (A.swap.paste C) :=
    Bicategory.isTwoFibreProduct_paste hAsw hC
  have h1 : HasPropertyOnSomeSmoothDiagram B S hS P (C.fst ≫ A.swap.fst).hom :=
    hasPropertyOnSomeSmoothDiagram_baseChange.{u, w} B S hS P hP (f ≫ g) t
      (A.swap.paste C) hRout hfg
  have h2 : HasPropertyOnSomeSmoothDiagram B S hS Q A.swap.fst.hom :=
    hasPropertyOnSomeSmoothDiagram_baseChange.{u, w} B S hS Q hQ g t A.swap hAsw hg
  have h3 : HasPropertyOnSomeSmoothDiagram B S hS P C.fst.hom :=
    hasPropertyOnSomeSmoothDiagram_of_comp_of_representableTarget B S hS P Q hcancel
      C.pt.property A.pt.property V₀ hV₀ C.fst.hom A.swap.fst.hom
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP C.pt.property
        𝒯.property (C.fst ≫ A.swap.fst).hom).2 h1)
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS Q hQ A.pt.property
        𝒯.property A.swap.fst.hom).2 h2)
  exact hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas B S hS P f.hom A.fst.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} A.fst.hom f.hom).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        A.fst.hom f.hom))
    hpsm hpsu h3

/-- The smooth-diagram criterion cancels along a smooth surjection of sources. Let `a : 𝒲 ⟶ 𝒱`
and `b : 𝒱 ⟶ 𝒳` be 1-morphisms of categories fibred in groupoids over the big fppf site of `S`
with `a` smooth and surjective on objects. If `a ≫ b` passes the existential smooth-diagram test
for a property `P` of morphisms of algebraic spaces over `S`, then so does `b`. -/
theorem hasPropertyOnSomeSmoothDiagram_of_comp_surjective
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒲 𝒱 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒲 ⟶ 𝒱) (b : 𝒱 ⟶ 𝒳)
    (ha : IsRelativelySmooth B S hS a)
    (hasurj : IsSurjectiveOnObjects B S hS 𝒲.val.p 𝒱.val.p
      (CatFiberedInGroupoids.homFunctor a))
    (hab : HasPropertyOnSomeSmoothDiagram B S hS P (a ≫ b)) :
    HasPropertyOnSomeSmoothDiagram B S hS P b := by
  obtain ⟨U, V, hU, hV, a₀, b₀, h, ⟨η⟩, ha₀, ha₀surj, hb₀, hPh⟩ := hab
  refine ⟨U, V, hU, hV, a₀ ≫ a, b₀, h,
    ⟨η ≪≫ (Bicategory.associator a₀ a b).symm⟩,
    isRelativelySmooth_comp B S hS a₀ a ha₀ ha, ?_, hb₀, hPh⟩
  exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p 𝒲.val.p 𝒱.val.p
    (CatFiberedInGroupoids.homFunctor a₀) (CatFiberedInGroupoids.homFunctor a)
    (CatFiberedInGroupoids.homFunctor_comp_p a) ha₀surj hasurj

/-- Cancellation of the universal smooth-diagram criterion for algebraic stacks. -/
private theorem hasPropertyOnEverySmoothDiagram_of_comp
    (P Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    (hQ : Space.IsSmoothLocalOnSourceAndTarget B S hS Q)
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    [(spaceProperty B S hS Q).IsStableUnderBaseChange]
    (hcancel : ∀ {U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V → IsAlgebraicSpace B S hS W →
      ∀ (p : U ⟶ V) (q : V ⟶ W), P (p ≫ q) → Q q → P p)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : HasPropertyOnEverySmoothDiagram B S hS P (f ≫ g).hom)
    (hg : HasPropertyOnEverySmoothDiagram B S hS Q g.hom) :
    HasPropertyOnEverySmoothDiagram B S hS P f.hom :=
  (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP 𝒳.property 𝒴.property f.hom).2
    (hasPropertyOnSomeSmoothDiagram_of_comp.{u, w} B S hS P Q hP hQ hcancel f g
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP 𝒳.property 𝒵.property
        (f ≫ g).hom).1 hfg)
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS Q hQ 𝒴.property 𝒵.property
        g.hom).1 hg))

namespace AlgebraicStacks

/-- Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If `f ≫ g` is
locally of finite presentation and `g` is locally of finite type, then `f` is locally of finite
presentation. -/
@[stacks 06Q6]
theorem isLocallyOfFinitePresentation_of_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyOfFinitePresentation B S hS f :=
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  Stack.hasPropertyOnEverySmoothDiagram_of_comp.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (fun hU hV hW p q hpq hq =>
      Space.isLocallyOfFinitePresentation_of_comp B S hS hU hV hW p q hpq hq)
    f g hfg hg

/-- Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If `f ≫ g` is
locally of finite type, then so is `f`. -/
@[stacks 06U9]
theorem isLocallyOfFiniteType_of_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g)) :
    IsLocallyOfFiniteType B S hS f :=
  let : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let : (Stack.spaceProperty B S hS
      (⊤ : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))).IsStableUnderBaseChange :=
    ⟨fun _ _ => trivial⟩
  Stack.hasPropertyOnEverySmoothDiagram_of_comp.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (⊤ : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (Space.isSmoothLocalOnSourceAndTarget_top B S hS)
    (fun hU hV hW p q hpq _ => Space.isLocallyOfFiniteType_of_comp B S hS hU hV hW p q hpq)
    f g hfg (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)

/-- Smoothness cancels along a smooth surjective source, with the relative notion on the source.
Let `a : 𝒲 ⟶ 𝒱` and `b : 𝒱 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`. If `a` is
relatively smooth (`AlgebraicGeometry.Stack.IsRelativelySmooth`) and surjective, and `a ≫ b` is
smooth, then `b` is smooth. -/
theorem isSmooth_of_comp_surjective_of_isRelativelySmooth
    {𝒲 𝒱 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (a : 𝒲 ⟶ 𝒱) (b : 𝒱 ⟶ 𝒳)
    (ha : Stack.IsRelativelySmooth B S hS a.hom)
    (hasurj : Stack.IsSurjective B S hS a)
    (hab : IsSmooth B S hS (a ≫ b)) :
    IsSmooth B S hS b :=
  Stack.hasPropertyOnSomeSmoothDiagram_of_comp_surjective B S hS
    (fun _ _ k => Space.IsSmooth B S hS k) a.hom b.hom ha
    (Stack.isSurjectiveOnObjects_of_pointsMap_surjective B S hS a hasurj) hab

/-- Smoothness cancels along a smooth surjective source. Let `a : 𝒲 ⟶ 𝒱` and `b : 𝒱 ⟶ 𝒳` be
1-morphisms of algebraic stacks over `S`, with `a` representable by algebraic spaces, smooth and
surjective. If `a ≫ b` is smooth then `b` is smooth. -/
theorem isSmooth_of_comp_surjective
    {𝒲 𝒱 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (a : 𝒲 ⟶ 𝒱) (b : 𝒱 ⟶ 𝒳)
    (harep : Stack.IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (ha : IsSmooth B S hS a)
    (hasurj : Stack.IsSurjective B S hS a)
    (hab : IsSmooth B S hS (a ≫ b)) :
    IsSmooth B S hS b :=
  isSmooth_of_comp_surjective_of_isRelativelySmooth B S hS a b
    ⟨harep, (Stack.hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      𝒲.property 𝒱.property a.hom harep).1 ha⟩
    hasurj hab

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
