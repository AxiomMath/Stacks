module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilitySmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCompGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSnd
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidTwoFibreProduct

/-!
# The target of a smooth surjective algebraic 1-morphism from an algebraic stack (Stacks 0D5C)

Stacks 0D5C ends with the assertion that *any stack in groupoids which is the target of a smooth
algebraic morphism from an algebraic stack is an algebraic stack*, the morphism in question being
the 1-morphism `PolarizedCurves ⟶ 𝒞urves` that the remark has just shown to be algebraic, smooth
and surjective. This file proves that assertion for a 1-morphism `F : 𝒳 ⟶ 𝒴` of categories
fibred in groupoids over the big fppf site of a scheme `S`:

* `𝒳` is an algebraic stack and `𝒴` is a stack;
* `F` is algebraic (Stacks 06CF): its base change `(Sch/Z) ×_𝒴 𝒳` along every scheme-valued
  point of `𝒴` is an algebraic stack;
* `F` is smooth: each of those base changes is smooth over `(Sch/Z)` as a 1-morphism of algebraic
  stacks (Stacks 075U);
* `F` is surjective (on objects, Stacks 06D4).

Stacks has no separate definition of smoothness for an algebraic 1-morphism whose target is not
yet known to be algebraic; the base-change formulation above is the one that Stacks 06CF and
Stacks 03YK use for "algebraic" and for properties of 1-morphisms representable by algebraic
spaces. Surjectivity is part of the hypothesis exactly as in the remark, where the 1-morphism is
"algebraic, smooth, and surjective"; without it the empty stack, which is algebraic and maps
smoothly to every stack, would make every stack in groupoids algebraic.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_baseChange_comp`: the base change of `a ≫ F` along a
  scheme-valued point is algebraic, for `a` representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_comp_of_isAlgebraicStack_baseChange`:
  `a ≫ F` is representable by algebraic spaces when `a` is and `F` is algebraic, the source of `a`
  being represented by a scheme.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange_comp`: its base changes are
  smooth when `a` is smooth and `F` is.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_smooth_surjective_algebraicMorphism`:
  **Stacks 0D5C**, the target is an algebraic stack.

## Implementation notes

The proof composes a smooth surjective presentation `a : (Sch/U₀) ⟶ 𝒳` with `F`. The base change
of `a ≫ F` along a scheme-valued point `(Sch/Z) ⟶ 𝒴` is equivalent (Stacks 02XD,
`CategoryTheory.TwoFibreProductOver.cancelSnd`) to the base change of `a` along the second
projection of `𝒵 = (Sch/Z) ×_𝒴 𝒳`: it is an algebraic stack because `𝒵` is (Stacks 0302 and
Stacks 05UM), and its fibres are thin because both of its factors are represented by schemes, so
it is representable by an algebraic space (Stacks 04SZ). Its projection to `(Sch/Z)` is, through
that equivalence, the composite of the base change of `a` — smooth by Stacks 045C and Stacks 06FM
— with the base change of `F`, so it is smooth (Stacks 06FP), and Stacks 06FM read point by point
makes `a ≫ F` smooth relative to `𝒴`. Surjectivity composes (Stacks 06D6, with Stacks 06D7 for
`a`), and Stacks 05UL concludes.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 05UL](https://stacks.math.columbia.edu/tag/05UL)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (F : 𝒳 ⟶ 𝒴)
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  (Z : BigFppfOver B S hS) (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒴.val.obj)
  (hz : z ⋙ 𝒴.val.p = Over.map Z.hom)

/-- The comparison 1-morphism of Stacks 02XD from the base change of `a` along the second
projection of `(Sch/Z) ×_𝒴 𝒳` to the base change of `a ≫ F`. -/
private def cancelSndHom :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) F).snd a).pt ⟶
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS Z z hz) (a ≫ F)).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.cancelSnd (Over.map Z.hom) 𝒳.val.p 𝒴.val.p
        (schemeFibredCategory B S hS U₀).val.p z (CatFiberedInGroupoids.homFunctor F)
        (CatFiberedInGroupoids.homFunctor a) (CatFiberedInGroupoids.homFunctor (a ≫ F))
        (CatFiberedInGroupoids.homFunctor_comp_p F) (Iso.refl _)
        (fun _ => IsHomLift.id
          (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p (a ≫ F)) _))
      w := TwoFibreProductOver.cancelSnd_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ }

/-- The comparison `cancelSndHom` is an equivalence. -/
private theorem isEquivalence_cancelSndHom :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor (cancelSndHom B S hS F a Z z hz)) :=
  TwoFibreProductOver.isEquivalence_cancelSnd _ _ _ _ _ _ _ _ _
    (CatFiberedInGroupoids.homFunctor_comp_p a) _ _

/-- **Algebraicity of the base change of `a ≫ F` along a scheme-valued point.** If the base
change `𝒵 = (Sch/Z) ×_𝒴 𝒳` of `F` along a scheme-valued point is an algebraic stack and `a` is
representable by algebraic spaces, then the base change `(Sch/Z) ×_𝒴 (Sch/U₀)` of `a ≫ F` is an
algebraic stack: it is equivalent (Stacks 02XD) to `𝒵 ×_𝒳 (Sch/U₀)`, whose projection to `𝒵` is
representable by algebraic spaces (Stacks 0302), hence it is algebraic by Stacks 05UM. -/
theorem isAlgebraicStack_baseChange_comp
    (h𝒵 : IsAlgebraicStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) F).pt.val)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom) :
    IsAlgebraicStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) (a ≫ F)).pt.val := by
  let sqF := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS Z z hz) F
  let sqa := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} sqF.snd a
  have hsqa : IsAlgebraicStack.{u, w} B S hS sqa.pt.val :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS sqa.fst
      (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 sqF.pt
        (schemeFibredCategory B S hS U₀) sqF.snd.hom a.hom ha) h𝒵
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    sqa.pt.isFiberedInGroupoids
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS Z z hz) (a ≫ F)).pt.isFiberedInGroupoids _
    (cancelSndHom B S hS F a Z z hz).hom.w (isEquivalence_cancelSndHom B S hS F a Z z hz)
  exact isAlgebraicStack_of_equivalenceOver B S hS e hsqa

/-- The fibres of a faithful functor are thin: two morphisms of a fibre lie over the same
identity, so they have the same image. -/
@[sga "4 I 6.5.2" "(ii), necessity"]
theorem _root_.CategoryTheory.Functor.fiber_isThin_of_faithful {𝒞 𝒮 : Type*} [Category 𝒞]
    [Category 𝒮] (p : 𝒮 ⥤ 𝒞) [p.Faithful] (U : 𝒞) : Quiver.IsThin (p.Fiber U) := by
  intro P Q
  refine ⟨fun m₁ m₂ => Functor.Fiber.hom_ext (p.map_injective ?_)⟩
  have h₁ := m₁.2
  have h₂ := m₂.2
  change p.map m₁.1 = p.map m₂.1
  rw [IsHomLift.fac' p (𝟙 U) m₁.1, IsHomLift.fac' p (𝟙 U) m₂.1]

variable {B S hS F a} in
/-- **The composite `a ≫ F` is representable by algebraic spaces** when `a` is and every base
change of `F` along a scheme-valued point is an algebraic stack. The base change of `a ≫ F` along
a scheme-valued point `(Sch/Z) ⟶ 𝒴` is an algebraic stack
(`AlgebraicGeometry.Stack.isAlgebraicStack_baseChange_comp`) whose fibres are thin, both factors
of the 2-fibre product being represented by schemes; so it is a stack in setoids, hence
representable by an algebraic space over `S` (Stacks 04SZ), and so by one over `Z`. -/
theorem isRepresentableByAlgebraicSpaces_comp_of_isAlgebraicStack_baseChange
    (hFalg : ∀ (Z : BigFppfOver B S hS) (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒴.val.obj)
      (hz : z ⋙ 𝒴.val.p = Over.map Z.hom),
      IsAlgebraicStack.{u, w} B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS Z z hz) F).pt.val)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (a ≫ F).hom := by
  intro Z
  dsimp only
  intro z hz
  have halg := isAlgebraicStack_baseChange_comp.{u, w} B S hS F a Z z hz (hFalg Z z hz) ha
  let 𝒲 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS Z z hz) (a ≫ F)).pt
  have : (Over.map Z.hom).Faithful :=
    ⟨fun {_ _ k₁ k₂} h => Over.OverMorphism.ext (by
      simpa using congrArg CommaMorphism.left h)⟩
  have hset : 𝒲.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
    TwoFibreProductOver.isStackInSetoids_of_isStack (Functor.IsFiberedInGroupoids.over_map Z.hom)
      (schemeFibredCategory B S hS U₀).isFiberedInGroupoids
      (Functor.fiber_isThin_of_faithful (Over.map Z.hom))
      (Functor.fiber_isThin_of_faithful (Over.forget U₀)) halg.2.1.1
  obtain ⟨G, hG, ⟨e⟩⟩ := isRepresentableByAlgebraicSpace_of_isStackInSetoids.{u, w} B S hS 𝒲
    halg hset
  have hqf : (TwoFibreProductOver.fst (Over.map Z.hom) (schemeFibredCategory B S hS U₀).val.p
      𝒴.val.p z (CatFiberedInGroupoids.homFunctor (a ≫ F))).IsFiberedInGroupoids :=
    (Functor.isFiberedInGroupoids_comp_overMap_iff Z.hom _).1 (by
      rw [TwoFibreProductOver.fst_comp_eq]
      exact 𝒲.isFiberedInGroupoids)
  exact exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap B S hS Z _ hqf hG
    (StacksRepresentableCFG.EquivalenceOver.ofEq TwoFibreProductOver.fst_comp_eq.symm e)

variable {B S hS F a} in
/-- **The base change of `a ≫ F` along a scheme-valued point is smooth** when `a` is smooth and
representable by algebraic spaces and the base change of `F` along that point is a smooth
1-morphism of algebraic stacks (Stacks 075U). Up to the equivalence of Stacks 02XD, the base
change of `a ≫ F` is the composite of the base change of `a` along the second projection of the
base change of `F` — smooth by Stacks 045C and Stacks 06FM — with the base change of `F`, so it
is smooth by Stacks 06FP. -/
theorem hasPropertyOnSomeSmoothDiagram_baseChange_comp
    (h𝒵 : IsAlgebraicStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) F).pt.val)
    (hFsmooth : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ h => Space.IsSmooth B S hS h)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) F).fst)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hasm : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS)
      a ha) :
    HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ h => Space.IsSmooth B S hS h)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) (a ≫ F)).fst := by
  have hBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  let sqF := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS Z z hz) F
  let sqa := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} sqF.snd a
  have hfst : IsRepresentableByAlgebraicSpaces B S hS sqa.fst.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳 sqF.pt
      (schemeFibredCategory B S hS U₀) sqF.snd.hom a.hom ha
  have hrel : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) sqa.fst hfst :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS)
      (schemeFibredCategory B S hS U₀) 𝒳 sqF.pt a sqF.snd sqa
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _) ha hasm
  have h₁ : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ h => Space.IsSmooth B S hS h)
      sqa.fst :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS _ h𝒵 sqa.fst hfst hrel
  have hr : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ h => Space.IsSmooth B S hS h)
      (sqa.fst ≫ sqF.fst) :=
    hasPropertyOnSomeSmoothDiagram_comp_of_precomp B S hS _
      (Space.isSmooth_comp B S hS) (Space.isSmooth_comp B S hS)
      sqa.fst sqF.fst h₁ hFsmooth
  exact hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS _ _ (sqa.fst ≫ sqF.fst)
    (cancelSndHom B S hS F a Z z hz) (isEquivalence_cancelSndHom B S hS F a Z z hz)
    (Iso.refl _) hr

variable {B S hS F a} in
/-- **The relative smoothness of `a ≫ F`** (Stacks 03YK) when its base change along every
scheme-valued point is smooth: this is the forward half of Stacks 06FM, read point by point, as
in `AlgebraicGeometry.Stack.hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram`. -/
theorem hasRelativeProperty_smooth_of_forall_baseChange {𝒯 : CatFiberedInGroupoids.{u, u, u + 1,
    u + 1} (BigFppfOver B S hS)} (q : 𝒯 ⟶ 𝒴) (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom)
    (hbc : ∀ (Z : BigFppfOver B S hS) (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒴.val.obj)
      (hz : z ⋙ 𝒴.val.p = Over.map Z.hom),
      HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ h => Space.IsSmooth B S hS h)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS Z z hz) q).fst) :
    HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS) q hq := by
  intro Z z hz T hT he
  have : (spaceProperty B S hS (fun _ _ h => Space.IsSmooth B S hS h)).RespectsIso :=
    Space.holdsOnEveryEtaleChart_respectsIso B S hS _
  refine (prop_algebraicSpaceMap_iff B S hS (spaceProperty B S hS
    (fun _ _ h => Space.IsSmooth B S hS h)) Z T hT).2 ?_
  obtain ⟨eT⟩ := he
  have hΛ : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor Z.hom).obj T) :=
    isAlgebraicSpace_viewOver B Z.left.1 S Z.left.2 hS Z.hom T hT
  have hreloc := representingMap_relocalizeFibre B S hS Z q z T eT hz
  have hgoal := prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (𝒳 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) q).pt)
      (𝒴 := schemeSlice B S hS Z)
      ((OverShriek.relocalizePresheafFunctor Z.hom).obj T) (yoneda.obj Z) hΛ
      (isAlgebraicSpace_yoneda B S hS Z)
      (relocalizeFibreEquivalence B S hS Z q z T eT)
      (schemeSliceEquivalenceOver B S hS Z)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS Z z hz) q).fst
      (hbc Z z hz)
  rwa [hreloc] at hgoal

/-- **A stack in groupoids which is the target of a smooth, surjective, algebraic 1-morphism from
an algebraic stack is an algebraic stack** (Stacks 0D5C, the last assertion).

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`,
with `𝒳` an algebraic stack and `𝒴` a stack. Assume that `F` is algebraic in the sense of
Stacks 06CF — its base change `(Sch/Z) ×_𝒴 𝒳` along every scheme-valued point of `𝒴` is an
algebraic stack (`hFalg`) — and smooth, in the sense that each of these base changes is smooth
over `(Sch/Z)` as a 1-morphism of algebraic stacks (Stacks 075U, `hFsmooth`), and surjective
(Stacks 06D4, `hFsurj`). Then `𝒴` is an algebraic stack.

Choose a smooth surjective presentation `a : (Sch/U₀) ⟶ 𝒳`. The composite `a ≫ F` is
representable by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_comp_of_isAlgebraicStack_baseChange`),
smooth (`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange_comp`) and surjective
(Stacks 06D6 and Stacks 06D7), so it presents `𝒴` (Stacks 05UL). -/
theorem isAlgebraicStack_of_smooth_surjective_algebraicMorphism
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hFalg : ∀ (Z : BigFppfOver B S hS) (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒴.val.obj)
      (hz : z ⋙ 𝒴.val.p = Over.map Z.hom),
      IsAlgebraicStack.{u, w} B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS Z z hz) F).pt.val)
    (hFsmooth : ∀ (Z : BigFppfOver B S hS) (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒴.val.obj)
      (hz : z ⋙ 𝒴.val.p = Over.map Z.hom),
      HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ h => Space.IsSmooth B S hS h)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS Z z hz) F).fst)
    (hFsurj : IsSurjectiveOnObjects B S hS 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor F)) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val := by
  obtain ⟨_, _, _, U₀, g, hg, hgprop⟩ := h𝒳
  let a : schemeFibredCategory B S hS U₀ ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom g
  have ha : IsRepresentableByAlgebraicSpaces B S hS a.hom := hg
  have hasurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) a ha :=
    fun V y hy G hG he => (hgprop V y hy G hG he).1
  have hasm : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) a ha :=
    fun V y hy G hG he => (hgprop V y hy G hG he).2
  have hu : IsRepresentableByAlgebraicSpaces B S hS (a ≫ F).hom :=
    isRepresentableByAlgebraicSpaces_comp_of_isAlgebraicStack_baseChange hFalg ha
  have husm : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) (a ≫ F) hu :=
    hasRelativeProperty_smooth_of_forall_baseChange (a ≫ F) hu fun Z z hz =>
      hasPropertyOnSomeSmoothDiagram_baseChange_comp Z z hz (hFalg Z z hz) (hFsmooth Z z hz) ha
        hasm
  have husurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) (a ≫ F) hu :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS (a ≫ F) hu).1 <|
      isSurjectiveOnObjects_comp B S hS _ 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor a) (CatFiberedInGroupoids.homFunctor F)
        (CatFiberedInGroupoids.homFunctor_comp_p F)
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS a ha).2
          hasurj) hFsurj
  exact isAlgebraicStack_of_smoothPresentation B S hS (a ≫ F) h𝒴
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U₀) hu husurj husm

end AlgebraicGeometry.Stack
