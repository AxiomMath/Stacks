module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence.KernelNaturality
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence

/-!
# Pasting of base-change squares, and the projection formula along a composite

Let `R` be a commutative ring, let `X` be an affine scheme over `R`, let `f : X' ⟶ X` be a
morphism of schemes over `R` whose underlying morphism of schemes is affine and let `Y` be a
scheme over `R`.  For a quasi-coherent kernel `K` on `X ×_R Y` the integral transform of `K`
precomposed with the direct image along `f` is the integral transform of the inverse image of
`K` on `X' ×_R Y`.  This file studies the compatibility of the ingredients of this identification
with composition of the morphism `f`.

## Main results

* `AlgebraicGeometry.pushforwardSquareIso_paste` and
  `AlgebraicGeometry.baseChangeNatTrans_paste`: the identification of the two composite direct
  images around a commutative square of schemes, and the base-change morphism of Tag 02KG, are
  compatible with pasting two squares side by side.
* `AlgebraicGeometry.pushforwardSourceChangeIso_comp`: compatibility with composition of the
  normalisation of the two composite direct images in the formula of Tag 0FZB.
* `AlgebraicGeometry.comparison_comp`: the comparison of Tag 01CD along a composite of
  morphisms of schemes is the composite of the two comparisons, and
  `AlgebraicGeometry.pullbackTensorRightNatTrans_comp` is the same statement for the 2-square
  with the second tensor factor held fixed.
* `AlgebraicGeometry.projectionFormulaSourceNatTrans_eq_mateEquiv`: the projection-formula
  morphism of Tag 0FZE is the mate of that 2-square, and
  `AlgebraicGeometry.projectionFormulaSourceNatTrans_comp` is the resulting compatibility of the
  projection formula with composition of the morphism.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.IntegralTransformQcoh
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.Modules.Hom

/-! ### Pasting of base-change squares -/

section Paste

open Stacks.AlgebraicGeometry.AffinePushforward

attribute [local implicit_reducible] CategoryTheory.TwoSquare

namespace Scheme.Modules

end Scheme.Modules

variable {X₂ X₁ X₀ S₂ S₁ S₀ : Scheme.{u}}
  {g₁ : X₁ ⟶ X₀} {g₂ : X₂ ⟶ X₁} {f₀ : X₀ ⟶ S₀} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂}
  {h₁ : S₁ ⟶ S₀} {h₂ : S₂ ⟶ S₁}

/-- The mate of a vertical composite of squares, whiskered on both sides, is the horizontal
composite of the mates, whiskered by the conjugates. -/
private theorem mateEquiv_vComp_whisker {A B C D B' D' : Type*} [Category A] [Category B]
    [Category C] [Category D] [Category B'] [Category D'] {G : A ⥤ C} {H : B ⥤ D} {K : B' ⥤ D'}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : B ⥤ B'} {R₃ : B' ⥤ B}
    {L₄ : D ⥤ D'} {R₄ : D' ⥤ D} {L : A ⥤ B'} {R : B' ⥤ A} {L' : C ⥤ D'} {R' : D' ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj : L ⊣ R) (adj' : L' ⊣ R') (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    (e : L₁ ⋙ L₃ ⟶ L) (e' : L' ⟶ L₂ ⋙ L₄) :
    mateEquiv adj adj' (((α.vComp β).whiskerRight e').whiskerLeft e) =
      (((mateEquiv adj₃ adj₄ β).hComp (mateEquiv adj₁ adj₂ α)).whiskerBottom
        (conjugateEquiv (adj₂.comp adj₄) adj' e')).whiskerTop
        (conjugateEquiv adj (adj₁.comp adj₃) e) := by
  rw [conjugateEquiv_mateEquiv_vcomp adj (adj₁.comp adj₃) adj',
    mateEquiv_conjugateEquiv_vcomp (adj₁.comp adj₃) (adj₂.comp adj₄) adj', mateEquiv_hcomp]

/-- **The identification of the two composite direct images around a commutative square of
schemes is compatible with pasting two squares side by side**: the identification for the pasted
square is the horizontal composite of the two identifications. -/
theorem pushforwardSquareIso_paste (w₁ : g₁ ≫ f₀ = f₁ ≫ h₁) (w₂ : g₂ ≫ f₁ = f₂ ≫ h₂)
    (w : (g₂ ≫ g₁) ≫ f₀ = f₂ ≫ h₂ ≫ h₁) :
    (pushforwardSquareIso w).hom =
      Functor.whiskerRight (Scheme.Modules.pushforwardComp g₂ g₁).inv
          (Scheme.Modules.pushforward f₀) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Scheme.Modules.pushforward g₂) (pushforwardSquareIso w₁).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (pushforwardSquareIso w₂).hom (Scheme.Modules.pushforward h₁) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Scheme.Modules.pushforward f₂)
          (Scheme.Modules.pushforwardComp h₂ h₁).hom := by
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom]
  simp [← Functor.map_comp, ← op_comp]
  rfl

/-- The mate of the pasted square, before the adjunctions of the two composite morphisms are
identified with the composites of the adjunctions. -/
private theorem mateEquiv_paste (w₁ : g₁ ≫ f₀ = f₁ ≫ h₁) (w₂ : g₂ ≫ f₁ = f₂ ≫ h₂)
    (w : (g₂ ≫ g₁) ≫ f₀ = f₂ ≫ h₂ ≫ h₁) :
    mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (g₂ ≫ g₁))
        (Scheme.Modules.pullbackPushforwardAdjunction (h₂ ≫ h₁))
      (TwoSquare.whiskerLeft (TwoSquare.whiskerRight
          (TwoSquare.vComp (baseChangeNatTrans w₁) (baseChangeNatTrans w₂))
          (Scheme.Modules.pullbackComp h₂ h₁).inv)
        (Scheme.Modules.pullbackComp g₂ g₁).hom) =
      (pushforwardSquareIso w).hom := by
  rw [mateEquiv_vComp_whisker (Scheme.Modules.pullbackPushforwardAdjunction g₁)
      (Scheme.Modules.pullbackPushforwardAdjunction h₁)
      (Scheme.Modules.pullbackPushforwardAdjunction g₂)
      (Scheme.Modules.pullbackPushforwardAdjunction h₂)
      (Scheme.Modules.pullbackPushforwardAdjunction (g₂ ≫ g₁))
      (Scheme.Modules.pullbackPushforwardAdjunction (h₂ ≫ h₁)),
    Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, baseChangeNatTrans_eq,
    baseChangeNatTrans_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    pushforwardSquareIso_paste w₁ w₂]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, Category.assoc]

/-- **The base-change morphism of a square pasted from two commutative squares of schemes is the
vertical composite of the two base-change morphisms**, the inverse images along the two composite
morphisms being identified with the composites of the inverse images. -/
theorem baseChangeNatTrans_paste (w₁ : g₁ ≫ f₀ = f₁ ≫ h₁) (w₂ : g₂ ≫ f₁ = f₂ ≫ h₂)
    (w : (g₂ ≫ g₁) ≫ f₀ = f₂ ≫ h₂ ≫ h₁) :
    baseChangeNatTrans w =
      Functor.whiskerLeft (Scheme.Modules.pushforward f₀)
          (Scheme.Modules.pullbackComp h₂ h₁).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (baseChangeNatTrans w₁) (Scheme.Modules.pullback h₂) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (Scheme.Modules.pullback g₁) (baseChangeNatTrans w₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Scheme.Modules.pullbackComp g₂ g₁).hom
          (Scheme.Modules.pushforward f₂) := by
  rw [baseChangeNatTrans_eq, ← mateEquiv_paste w₁ w₂ w, Equiv.symm_apply_apply]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, Category.assoc]

/-- The affine base-change isomorphism of functors of Tag 02KG is the base-change morphism
whiskered by the functor along which it is restricted. -/
theorem baseChangeIsoOfFunctor_hom {C : Type*} [Category C] {P' P T' T : Scheme.{u}}
    {q' : P' ⟶ P} {p' : P' ⟶ T'} {p : P ⟶ T} {q : T' ⟶ T} (sq : IsPullback q' p' p q)
    [IsAffineHom p] (F : C ⥤ P.Modules) (hF : ∀ A, (F.obj A).IsQuasicoherent) :
    (baseChangeIsoOfFunctor sq F hF).hom = Functor.whiskerLeft F (baseChangeNatTrans sq.w) :=
  rfl

end Paste

/-! ### The comparison of Tag 01CD, and the projection formula, along a composite -/

section AlongComposite

open Stacks.RingedSpace PresheafOfModules TopologicalSpace
open scoped TensorProduct

attribute [local implicit_reducible] CategoryTheory.TwoSquare

/-- A four-fold composite of morphisms of sheaves of modules, evaluated at a local section
through the values of the four factors. -/
private theorem comp_chain {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : CategoryTheory.Sheaf J RingCat.{u}} {M N P Q O : SheafOfModules.{u} R}
    (c₁ : M ⟶ N) (c₂ : N ⟶ P) (c₃ : P ⟶ Q) (c₄ : Q ⟶ O) (V : Cᵒᵖ) (x : M.val.obj V)
    {y : N.val.obj V} {z : P.val.obj V} {w : Q.val.obj V} {r : O.val.obj V}
    (h₁ : Hom.app c₁.val V x = y) (h₂ : Hom.app c₂.val V y = z)
    (h₃ : Hom.app c₃.val V z = w) (h₄ : Hom.app c₄.val V w = r) :
    Hom.app (c₁ ≫ c₂ ≫ c₃ ≫ c₄).val V x = r := by
  have e : Hom.app (c₁ ≫ c₂ ≫ c₃ ≫ c₄).val V x =
      Hom.app c₄.val V (Hom.app c₃.val V (Hom.app c₂.val V (Hom.app c₁.val V x))) := rfl
  rw [e, h₁, h₂, h₃, h₄]

/-- The component of the mate of a 2-square: the unit, the square and the counit. -/
private theorem mateEquiv_app {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv]

/-- The mate of a 2-square whiskered at the bottom is the mate whiskered at the left. -/
private theorem mateEquiv_whiskerBottom {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (w : TwoSquare G L₁ L₂ H) (α : H ⟶ H') :
    mateEquiv adj₁ adj₂ (w.whiskerBottom α) = (mateEquiv adj₁ adj₂ w).whiskerLeft α := by
  refine NatTrans.ext (funext fun d => ?_)
  rw [mateEquiv_app]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, mateEquiv_app, Category.assoc,
    ← Functor.map_comp]
  exact congrArg
    (fun t => adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (w.natTrans.app (R₁.obj d) ≫ t))
    (α.naturality (adj₁.counit.app d)).symm

/-- The abstract comparison morphism of an adjunction and a pair of binary functors is the mate
of the comparison with its second argument held fixed. -/
private theorem adjunctionTensorMap_eq_mateEquiv_app {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) (G : D)
    (β : ((𝟭 C).prod' ((Functor.const C).obj H) ⋙ A) ⋙ L ⟶
      L ⋙ ((𝟭 D).prod' ((Functor.const D).obj (L.obj H)) ⋙ B))
    (hβ : ∀ A', β.app A' = α.app (A', H)) :
    adjunctionTensorMap adj A B α G H = (mateEquiv adj adj β).app G := by
  rw [mateEquiv_app, hβ, adjunctionTensorMap, Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-- The tensor product of two morphisms of sheaves of modules is tensoring by the first and then
by the second. -/
private theorem tensorSheaf_map_pair {X : RingedSpace.{u, u}}
    {M M' N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
    (p : M ⟶ M') (q : N ⟶ N') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
        ((p, q) : (M, N) ⟶ (M', N')) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
          ((p, 𝟙 N) : (M, N) ⟶ (M', N)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
          ((𝟙 M', q) : (M', N) ⟶ (M', N')) := by
  have factorization : (p, q) = (p ≫ 𝟙 M', 𝟙 N ≫ q) :=
    congrArg₂ (fun (left : M ⟶ M') (right : N ⟶ N') => (left, right))
      (Category.comp_id p).symm (Category.id_comp q).symm
  exact (congrArg
    (fun arrow : (M ⟶ M') × (N ⟶ N') =>
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
        (X := (M, N)) (Y := (M', N')) arrow) factorization).trans
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf)).map_comp
        ((p, 𝟙 N) : (M, N) ⟶ (M', N)) ((𝟙 M', q) : (M', N) ⟶ (M', N')))

section Right

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-- **Tag 01CD with the second tensor factor held fixed**, as the 2-square
`h^*(- ⊗ H) ⟶ h^*(-) ⊗ h^*H`. -/
def pullbackTensorRightNatTrans
    (H : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (S.toRingedSpace).sheaf).flip.obj
        (H)) ⋙ pullbackFunctor h.toLRSHom.toShHom ⟶
      pullbackFunctor h.toLRSHom.toShHom ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T.toRingedSpace).sheaf).flip.obj
            (((pullbackFunctor h.toLRSHom.toShHom).obj H))) where
  app source := comparison h.toLRSHom.toShHom source H
  naturality source target morphism := by
    let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S.toRingedSpace.sheaf
    let targetTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      T.toRingedSpace.sheaf
    let inverseImage := pullbackFunctor h.toLRSHom.toShHom
    have naturality :
        inverseImage.map ((sourceTensor.map morphism).app H ≫
            (sourceTensor.obj target).map (𝟙 H)) ≫
          comparison h.toLRSHom.toShHom target H =
        comparison h.toLRSHom.toShHom source H ≫
          (targetTensor.map (inverseImage.map morphism)).app (inverseImage.obj H) ≫
            (targetTensor.obj (inverseImage.obj target)).map (inverseImage.map (𝟙 H)) :=
      (comparisonNatTrans h.toLRSHom.toShHom).naturality (Prod.mkHom morphism (𝟙 H))
    have sourceIdentity := congrArg inverseImage.map
      ((congrArg (fun endomorphism => (sourceTensor.map morphism).app H ≫ endomorphism)
        ((sourceTensor.obj target).map_id H)).trans (Category.comp_id _))
    have targetIdentity :=
      (congrArg (targetTensor.obj (inverseImage.obj target)).map
        (inverseImage.map_id H)).trans
          ((targetTensor.obj (inverseImage.obj target)).map_id (inverseImage.obj H))
    exact (congrArg (fun component => component ≫ comparison h.toLRSHom.toShHom target H)
      sourceIdentity).symm.trans (naturality.trans
        ((congrArg (fun endomorphism => comparison h.toLRSHom.toShHom source H ≫
          (targetTensor.map (inverseImage.map morphism)).app (inverseImage.obj H) ≫ endomorphism)
            targetIdentity).trans
          (congrArg (fun component => comparison h.toLRSHom.toShHom source H ≫ component)
            (Category.comp_id _))))

/-- The value of `AlgebraicGeometry.pullbackTensorRightNatTrans` at a module is the comparison
morphism of Tag 01CD. -/
theorem pullbackTensorRightNatTrans_app
    (H G : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    (pullbackTensorRightNatTrans h H).app G = comparison h.toLRSHom.toShHom G H :=
  rfl

/-- **The projection-formula morphism of Tag 0FZE is a mate.**  It is the mate, under the
pullback--pushforward adjunction on both sides, of the comparison of Tag 01CD with the module on
the target held fixed in the right tensor factor. -/
theorem projectionFormulaSourceNatTrans_eq_mateEquiv (H : S.Modules) :
    projectionFormulaSourceNatTrans h H =
      mateEquiv (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom)
        (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom)
        (pullbackTensorRightNatTrans h H) := by
  refine NatTrans.ext (funext fun G => ?_)
  show projectionFormulaMap h G H = _
  refine Eq.trans ?_ (mateEquiv_app
    (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom)
    (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom)
    (pullbackTensorRightNatTrans h H) G).symm
  simp only [projectionFormulaMap]
  rfl

end Right

section Comp

variable {X₂ X₁ X₀ : Scheme.{u}} (g : X₂ ⟶ X₁) (k : X₁ ⟶ X₀)

/-- The identification of the inverse image along a composite of morphisms of schemes with the
composite of the inverse images, typed over ringed spaces. -/
def pullbackCompNatIso :
    pullbackFunctor (g ≫ k).toLRSHom.toShHom ≅
      pullbackFunctor k.toLRSHom.toShHom ⋙ pullbackFunctor g.toLRSHom.toShHom :=
  (Scheme.Modules.pullbackComp g k).symm

/-- The forward map of `AlgebraicGeometry.pullbackCompNatIso` is the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem pullbackCompNatIso_hom :
    (pullbackCompNatIso g k).hom = (Scheme.Modules.pullbackComp g k).inv := rfl

/-- The inverse of `AlgebraicGeometry.pullbackCompNatIso` is the forward map of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
theorem pullbackCompNatIso_inv :
    (pullbackCompNatIso g k).inv = (Scheme.Modules.pullbackComp g k).hom := rfl

/-- The identification of the inverse images along a composite carries the unit image of a local
section to the iterated unit image. -/
theorem pullbackCompNatIso_hom_app_pullbackUnit
    (M : SheafOfModules.{u} (structureRingSheaf X₀.toRingedSpace))
    (U : (Opens X₀.toRingedSpace.carrier)ᵒᵖ) (x : M.val.obj U) :
    Hom.app ((pullbackCompNatIso g k).hom.app M).val
        ((opensMap (g ≫ k).toLRSHom.toShHom).op.obj U)
        (pullbackUnit (g ≫ k).toLRSHom.toShHom M U x) =
      pullbackUnit g.toLRSHom.toShHom ((pullbackFunctor k.toLRSHom.toShHom).obj M)
        ((opensMap k.toLRSHom.toShHom).op.obj U)
        (pullbackUnit k.toLRSHom.toShHom M U x) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction k).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ k))
    (Scheme.Modules.pullbackComp g k).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (hom_congr_apply' (congrArg (fun φ => SheafOfModules.Hom.val φ) h) U x).symm

/-- The inverse of the identification of the inverse images along a composite carries the
iterated unit image of a local section to its unit image. -/
theorem pullbackCompNatIso_inv_app_pullbackUnit
    (M : SheafOfModules.{u} (structureRingSheaf X₀.toRingedSpace))
    (U : (Opens X₀.toRingedSpace.carrier)ᵒᵖ) (x : M.val.obj U) :
    Hom.app ((pullbackCompNatIso g k).inv.app M).val
        ((opensMap g.toLRSHom.toShHom).op.obj ((opensMap k.toLRSHom.toShHom).op.obj U))
        (pullbackUnit g.toLRSHom.toShHom ((pullbackFunctor k.toLRSHom.toShHom).obj M)
          ((opensMap k.toLRSHom.toShHom).op.obj U)
          (pullbackUnit k.toLRSHom.toShHom M U x)) =
      pullbackUnit (g ≫ k).toLRSHom.toShHom M U x := by
  rw [← pullbackCompNatIso_hom_app_pullbackUnit g k M U x]
  exact hom_congr_apply' (congrArg (fun φ => SheafOfModules.Hom.val φ)
    ((pullbackCompNatIso g k).hom_inv_id_app M)) _ _

/-- **The comparison of Tag 01CD along a composite of morphisms of schemes is the composite of
the two comparisons**, the inverse image along the composite being identified with the composite
of the inverse images. -/
theorem comparison_comp (A B : SheafOfModules.{u} (structureRingSheaf X₀.toRingedSpace)) :
    comparison (g ≫ k).toLRSHom.toShHom A B =
      ((pullbackCompNatIso g k).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              (X₀.toRingedSpace).sheaf))).obj (A, B))) ≫
        (pullbackFunctor g.toLRSHom.toShHom).map (comparison k.toLRSHom.toShHom A B) ≫
        comparison g.toLRSHom.toShHom ((pullbackFunctor k.toLRSHom.toShHom).obj A)
          ((pullbackFunctor k.toLRSHom.toShHom).obj B) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (X₂.toRingedSpace).sheaf))).map
          (((pullbackCompNatIso g k).inv.app A, (pullbackCompNatIso g k).inv.app B) :
            (((pullbackFunctor g.toLRSHom.toShHom).obj
                ((pullbackFunctor k.toLRSHom.toShHom).obj A),
              (pullbackFunctor g.toLRSHom.toShHom).obj
                ((pullbackFunctor k.toLRSHom.toShHom).obj B)) : _ × _) ⟶
              ((pullbackFunctor (g ≫ k).toLRSHom.toShHom).obj A,
                (pullbackFunctor (g ≫ k).toLRSHom.toShHom).obj B)) := by
  refine (comparison_unique (g ≫ k).toLRSHom.toShHom A B _ ?_).symm
  intro U a b
  refine (homEquiv_val_app (g ≫ k).toLRSHom.toShHom _ _ _ U _).trans ?_
  refine comp_chain _ _ _ _ _ _
    (pullbackCompNatIso_hom_app_pullbackUnit g k
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (X₀.toRingedSpace).sheaf))).obj (A, B)) U _)
    ((pullbackUnit_naturality g.toLRSHom.toShHom (comparison k.toLRSHom.toShHom A B)
        ((opensMap k.toLRSHom.toShHom).op.obj U) _).trans
      (congrArg (pullbackUnit g.toLRSHom.toShHom
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (X₁.toRingedSpace).sheaf))).obj
          ((pullbackFunctor k.toLRSHom.toShHom).obj A,
            (pullbackFunctor k.toLRSHom.toShHom).obj B))
        ((opensMap k.toLRSHom.toShHom).op.obj U))
        (comparison_pullbackUnit_unit_tmul k.toLRSHom.toShHom A B U a b)))
    (comparison_pullbackUnit_unit_tmul g.toLRSHom.toShHom
      ((pullbackFunctor k.toLRSHom.toShHom).obj A)
      ((pullbackFunctor k.toLRSHom.toShHom).obj B)
      ((opensMap k.toLRSHom.toShHom).op.obj U) _ _)
    ((tensorSheaf_map_unit_tmul X₂.toRingedSpace ((pullbackCompNatIso g k).inv.app A)
        ((pullbackCompNatIso g k).inv.app B) _ _ _).trans ?_)
  refine congrArg (Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf (X₂.toRingedSpace)) (𝟙
      (Stacks.RingedSpace.structureRingSheaf (X₂.toRingedSpace)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (X₂.toRingedSpace).presheaf) (((pullbackFunctor
      (g ≫ k).toLRSHom.toShHom).obj A)).val (((pullbackFunctor
      (g ≫ k).toLRSHom.toShHom).obj B)).val))
      ((opensMap (g ≫ k).toLRSHom.toShHom).op.obj U)) ?_
  exact congrArg₂ (· ⊗ₜ ·) (pullbackCompNatIso_inv_app_pullbackUnit g k A U a)
    (pullbackCompNatIso_inv_app_pullbackUnit g k B U b)

/-- **The 2-square of Tag 01CD in the right tensor factor is compatible with composition**: the
square of a composite is the vertical composite of the two squares, the inverse image along the
composite being identified with the composite of the inverse images. -/
theorem pullbackTensorRightNatTrans_comp
    (H : SheafOfModules.{u} (structureRingSheaf X₀.toRingedSpace)) :
    pullbackTensorRightNatTrans (g ≫ k) H =
      TwoSquare.whiskerBottom (TwoSquare.whiskerLeft (TwoSquare.whiskerRight
          (TwoSquare.vComp (pullbackTensorRightNatTrans k H)
            (pullbackTensorRightNatTrans g ((pullbackFunctor k.toLRSHom.toShHom).obj H)))
          (pullbackCompNatIso g k).hom) (pullbackCompNatIso g k).inv)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X₂.toRingedSpace).sheaf).flip.map ((pullbackCompNatIso g k).inv.app H)) := by
  refine NatTrans.ext (funext fun A => ?_)
  refine (pullbackTensorRightNatTrans_app (g ≫ k) H A).trans
    ((comparison_comp g k A H).trans ?_)
  dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, TwoSquare.natTrans, Functor.associator,
    Functor.whiskerLeft, Functor.whiskerRight]
  simp only [Category.assoc]
  rfl

/-- The identification of the direct image along a composite of morphisms of schemes with the
composite of the direct images, typed over ringed spaces. -/
def pushforwardCompNatIso :
    pushforwardFunctor g.toLRSHom.toShHom ⋙ pushforwardFunctor k.toLRSHom.toShHom ≅
      pushforwardFunctor (g ≫ k).toLRSHom.toShHom :=
  Scheme.Modules.pushforwardComp g k

/-- **The projection-formula morphism of Tag 0FZE along a composite of morphisms of schemes is
the horizontal composite of the two projection-formula morphisms**, the inverse and direct images
along the composite being identified with the composites of the inverse and direct images. -/
theorem projectionFormulaSourceNatTrans_comp (H : X₀.Modules) :
    projectionFormulaSourceNatTrans (g ≫ k) H =
      TwoSquare.whiskerLeft
        (TwoSquare.whiskerTop
          (TwoSquare.whiskerBottom
            (TwoSquare.hComp
              (projectionFormulaSourceNatTrans g
                ((pullbackFunctor k.toLRSHom.toShHom).obj H))
              (projectionFormulaSourceNatTrans k H))
            (pushforwardCompNatIso g k).hom)
          (pushforwardCompNatIso g k).inv)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (X₂.toRingedSpace).sheaf).flip.map ((pullbackCompNatIso g k).inv.app H)) := by
  have hc1 : CategoryTheory.conjugateEquiv
      (modulePullbackPushforwardAdjunction (g ≫ k).toLRSHom.toShHom)
      ((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).comp
        (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom))
      (pullbackCompNatIso g k).inv = (pushforwardCompNatIso g k).inv :=
    Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom g k
  have hc2 : CategoryTheory.conjugateEquiv
      ((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).comp
        (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom))
      (modulePullbackPushforwardAdjunction (g ≫ k).toLRSHom.toShHom)
      (pullbackCompNatIso g k).hom = (pushforwardCompNatIso g k).hom :=
    Scheme.Modules.conjugateEquiv_pullbackComp_inv g k
  rw [projectionFormulaSourceNatTrans_eq_mateEquiv (g ≫ k) H,
    pullbackTensorRightNatTrans_comp g k H]
  refine (mateEquiv_whiskerBottom
    (modulePullbackPushforwardAdjunction (g ≫ k).toLRSHom.toShHom)
    (modulePullbackPushforwardAdjunction (g ≫ k).toLRSHom.toShHom) _ _).trans ?_
  refine congrArg (fun square => TwoSquare.whiskerLeft square
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X₂.toRingedSpace.sheaf).flip.map ((pullbackCompNatIso g k).inv.app H))) ?_
  refine (mateEquiv_vComp_whisker (modulePullbackPushforwardAdjunction k.toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction k.toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction (g ≫ k).toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction (g ≫ k).toLRSHom.toShHom) _ _ _ _).trans ?_
  rw [hc1, hc2, projectionFormulaSourceNatTrans_eq_mateEquiv g,
    projectionFormulaSourceNatTrans_eq_mateEquiv k]
  rfl

end Comp

end AlongComposite

/-! ### The direct image along the source-change morphism of a composite -/

/-- **The normalisation of the two composite direct images of Tag 0FZB is compatible with
composition of the morphism**: for a composite `X'' ⟶ X' ⟶ X`, the identification of the direct
image along the source-change morphism followed by the second projection with the direct image
along the second projection is the composite of the two such identifications. -/
theorem pushforwardSourceChangeIso_comp (R : Type u) [CommRing R]
    (X X' X'' Y : Over (Spec (.of R))) (f' : X' ⟶ X) (f'' : X'' ⟶ X') :
    (Scheme.Modules.pushforwardComp (sourceChangeMap R X X'' Y (f'' ≫ f'))
          (pullback.snd X.hom Y.hom) ≪≫
        Scheme.Modules.pushforwardCongr
          (sourceChangeMap_comp_snd R X X'' Y (f'' ≫ f'))).hom =
      (Functor.isoWhiskerRight
          (Scheme.Modules.pushforwardCongr
            (sourceChangeMap_comp R X X' X'' Y f' f'').symm)
          (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
        Functor.isoWhiskerRight
          (Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'')
            (sourceChangeMap R X X' Y f')).symm
          (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Scheme.Modules.pushforward (sourceChangeMap R X' X'' Y f''))
          (Scheme.Modules.pushforwardComp (sourceChangeMap R X X' Y f')
              (pullback.snd X.hom Y.hom) ≪≫
            Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X' Y f')) ≪≫
        Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'')
            (pullback.snd X'.hom Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr
            (sourceChangeMap_comp_snd R X' X'' Y f'')).hom := by
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  simp [← Functor.map_comp, ← op_comp]
  rfl

end AlgebraicGeometry

end
