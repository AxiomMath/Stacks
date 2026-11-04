module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.LaxComparisonTranspose
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.RelativeInverseImageTranspose
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxRelativeTensor

/-!
# The comparison with the box product as a transpose

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y` with projections `p` and
`q`, `f = p ∘ a`, and `τ : W ⟶ (W, f^{-1}𝒪_S)` the identity-on-spaces morphism of ringed spaces.
The comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖` of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` (step (5) of
[Stacks, Tag 0FLR]) is the transpose along `τ^* ⊣ τ_*` of the comparison of [Stacks, Tag 01CD]
for `τ` followed by the two crossing legs `τ^*p'^*τ_{X,*}𝓕 ⟶ p^*𝓕` and `τ^*q'^*τ_{Y,*}𝓖 ⟶ q^*𝓖`.

## Main results

* `pullback_tensorMap_relativeInverseImageToPullbackOfFactors_counit`: the statement above, for
  `g` presented by both factorizations.
* `relativeBoxComparisonLeg₁_eq_ofFactors`: the first leg of the box comparison in that form.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage
open scoped CategoryTheory.Prod

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

section Factors

variable {W X' S' : Scheme.{u}} (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)

/-- The square comparing the two factorizations of `p`, for a morphism presented as a
factorization. -/
theorem toInverseImageBase_comp_relativeInverseImageProjectionOfFactors :
    toInverseImageBase g ≫ relativeInverseImageProjectionOfFactors p c g hg =
      p.toLRSHom.toShHom ≫ toInverseImageBase c := by
  subst hg
  exact toInverseImageBase_comp_relativeInverseImageProjection p c

/-- `pullback_relativeInverseImageToPullback_counit` for a morphism presented as a
factorization. -/
theorem pullback_relativeInverseImageToPullbackOfFactors_counit (F : X'.Modules) :
    (modulePullback (toInverseImageBase g)).map
        (relativeInverseImageToPullbackOfFactors p c g hg F) ≫
        (modulePullbackPushforwardAdjunction (toInverseImageBase g)).counit.app
          ((modulePullback p.toLRSHom.toShHom).obj F) =
      (Stacks.DerivedPullback.Composition.modulePullbackComp (toInverseImageBase g)
          (relativeInverseImageProjectionOfFactors p c g hg)).hom.app
          ((modulePushforward (toInverseImageBase c)).obj F) ≫
        eqToHom (congrArg (fun z : W.toRingedSpace ⟶ inverseImageBase c =>
          (modulePullback z).obj ((modulePushforward (toInverseImageBase c)).obj F))
          (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors p c g hg)) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
          (toInverseImageBase c)).inv.app ((modulePushforward (toInverseImageBase c)).obj F) ≫
        (modulePullback p.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction (toInverseImageBase c)).counit.app F) := by
  subst hg
  exact pullback_relativeInverseImageToPullback_counit p c F

end Factors

/-- The chase behind `pullback_tensorMap_relativeInverseImageToPullbackOfFactors_counit`, every
object and morphism a
variable. -/
private theorem chase_box {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X₀ X₁ : C} {Y₁ Y₁' Y₂ : D} (leg1 : X₀ ⟶ X₁) (leg2 : X₁ ⟶ R.obj Y₂)
    (ct1 : X₁ ⟶ R.obj Y₁') (εε : Y₁' ⟶ Y₂) (ct0 : X₀ ⟶ R.obj Y₁) (mm : Y₁ ⟶ Y₁')
    (ll : Y₁ ⟶ Y₂) (comp : L.obj X₀ ⟶ Y₁)
    (hL2 : leg2 = ct1 ≫ R.map εε) (hnat : leg1 ≫ ct1 = ct0 ≫ R.map mm) (hleg : mm ≫ εε = ll)
    (hcomp : adj.homEquiv _ _ comp = ct0) :
    L.map (leg1 ≫ leg2) ≫ adj.counit.app Y₂ = comp ≫ ll := by
  have h1 : adj.homEquiv _ _ (L.map (leg1 ≫ leg2) ≫ adj.counit.app Y₂) = leg1 ≫ leg2 :=
    (congrArg _ (Adjunction.homEquiv_counit _ _ _ _).symm).trans (Equiv.apply_symm_apply _ _)
  have h2 : adj.homEquiv _ _ (comp ≫ ll) = ct0 ≫ R.map ll :=
    (Adjunction.homEquiv_naturality_right _ _ _).trans (congrArg (· ≫ R.map ll) hcomp)
  refine (adj.homEquiv _ _).injective (h1.trans (Eq.trans ?_ h2.symm))
  rw [hL2, reassoc_of% hnat, ← R.map_comp, hleg]

/-- `chase_box` with the three maps out of the tensor product given componentwise. -/
private theorem chase_box2 {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (B' : D × D ⥤ D) {X₀ X₁ : C} {P₁ P₂ P₁' P₂' Q₁ Q₂ : D} (leg1 : X₀ ⟶ X₁)
    (leg2 : X₁ ⟶ R.obj (B'.obj (Q₁, Q₂))) (ct1 : X₁ ⟶ R.obj (B'.obj (P₁', P₂')))
    (e₁ : P₁' ⟶ Q₁) (e₂ : P₂' ⟶ Q₂) (ct0 : X₀ ⟶ R.obj (B'.obj (P₁, P₂))) (m₁ : P₁ ⟶ P₁')
    (m₂ : P₂ ⟶ P₂') (l₁ : P₁ ⟶ Q₁) (l₂ : P₂ ⟶ Q₂) (comp : L.obj X₀ ⟶ B'.obj (P₁, P₂))
    (hL2 : leg2 = ct1 ≫ R.map (B'.map (e₁ ×ₘ e₂)))
    (hnat : leg1 ≫ ct1 = ct0 ≫ R.map (B'.map (m₁ ×ₘ m₂))) (hX : m₁ ≫ e₁ = l₁)
    (hY : m₂ ≫ e₂ = l₂) (hcomp : adj.homEquiv _ _ comp = ct0) :
    L.map (leg1 ≫ leg2) ≫ adj.counit.app (B'.obj (Q₁, Q₂)) = comp ≫ B'.map (l₁ ×ₘ l₂) :=
  chase_box adj leg1 leg2 ct1 (B'.map (e₁ ×ₘ e₂)) ct0 (B'.map (m₁ ×ₘ m₂)) (B'.map (l₁ ×ₘ l₂))
    comp hL2 hnat (by rw [← B'.map_comp, prod_comp, hX, hY]) hcomp

section General

variable {W X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y) (g : W ⟶ S)
  (hp : p ≫ a = g) (hq : q ≫ b = g)

/-- **The tensor product of the two comparisons `p^{-1}𝓕 ⟶ p^*𝓕`, `q^{-1}𝓖 ⟶ q^*𝓖` followed by
the lax comparison is the transpose of the comparison of Stacks 01CD followed by the crossing
legs** (each a pulled-back comparison followed by a counit), along `τ^* ⊣ τ_*` for
`τ : W ⟶ (W, g^{-1}𝒪_S)` and `g` presented by both
factorizations. -/
theorem pullback_tensorMap_relativeInverseImageToPullbackOfFactors_counit
    (F : Modules X.toRingedSpace) (G : Modules Y.toRingedSpace) :
    (modulePullback (toInverseImageBase g)).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
            (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
            ((pushforward (toInverseImageBase a)).obj F)),
            ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
            ((pushforward (toInverseImageBase b)).obj G))))
            (Y := (((pushforward (toInverseImageBase g)).obj
            ((_root_.pullback p.toLRSHom.toShHom).obj F)),
            ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj
            G)))) ((relativeInverseImageToPullbackOfFactors p a g hp F),
            (relativeInverseImageToPullbackOfFactors q b g hq G)) ≫
          inverseImageTensorLax g ((_root_.pullback p.toLRSHom.toShHom).obj F)
              ((_root_.pullback q.toLRSHom.toShHom).obj G)) ≫
      (modulePullbackPushforwardAdjunction (toInverseImageBase g)).counit.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj
          (((_root_.pullback p.toLRSHom.toShHom).obj F),
          ((_root_.pullback q.toLRSHom.toShHom).obj G))) =
    Stacks.RingedSpace.comparison (toInverseImageBase g)
        ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj F)) ((_root_.pullback
        (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj G)) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        (((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
            (relativeInverseImageToPullbackOfFactors p a g hp F) ≫
            (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
            ((_root_.pullback p.toLRSHom.toShHom).obj F)) ×ₘ
          ((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
              (relativeInverseImageToPullbackOfFactors q b g hq G) ≫
              (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
              ((_root_.pullback q.toLRSHom.toShHom).obj G))) := by
  have hL2 : inverseImageTensorLax g ((_root_.pullback p.toLRSHom.toShHom).obj F)
      ((_root_.pullback q.toLRSHom.toShHom).obj G) =
      Stacks.RingedSpace.comparisonTranspose (toInverseImageBase g)
          ((pushforward (toInverseImageBase g)).obj ((_root_.pullback p.toLRSHom.toShHom).obj F))
          ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj G)) ≫
        (Stacks.RingedSpace.pushforwardFunctor (toInverseImageBase g)).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
              ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
              ((_root_.pullback p.toLRSHom.toShHom).obj F) ×ₘ
              (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
              ((_root_.pullback q.toLRSHom.toShHom).obj G))) :=
    inverseImageTensorLax_eq_comparisonTranspose g ((_root_.pullback p.toLRSHom.toShHom).obj F)
        ((_root_.pullback q.toLRSHom.toShHom).obj G)
  have hnat : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
      (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
      ((pushforward (toInverseImageBase a)).obj F)),
      ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
      ((pushforward (toInverseImageBase b)).obj G))))
      (Y := (((pushforward (toInverseImageBase g)).obj
      ((_root_.pullback p.toLRSHom.toShHom).obj F)),
      ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj G))))
      ((relativeInverseImageToPullbackOfFactors p a g hp F),
      (relativeInverseImageToPullbackOfFactors q b g hq G)) ≫ Stacks.RingedSpace.comparisonTranspose
      (toInverseImageBase g) ((pushforward (toInverseImageBase g)).obj
      ((_root_.pullback p.toLRSHom.toShHom).obj F)) ((pushforward (toInverseImageBase g)).obj
      ((_root_.pullback q.toLRSHom.toShHom).obj G)) =
      Stacks.RingedSpace.comparisonTranspose (toInverseImageBase g)
          ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
          ((pushforward (toInverseImageBase a)).obj F)) ((_root_.pullback
          (relativeInverseImageProjectionOfFactors q b g hq)).obj
          ((pushforward (toInverseImageBase b)).obj G)) ≫
        (modulePushforward (toInverseImageBase g)).map
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            ((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
            (relativeInverseImageToPullbackOfFactors p a g hp F) ×ₘ
            (Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
            (relativeInverseImageToPullbackOfFactors q b g hq G))) :=
    Stacks.RingedSpace.comparisonTranspose_naturality (toInverseImageBase g)
        (relativeInverseImageToPullbackOfFactors p a g hp F)
        (relativeInverseImageToPullbackOfFactors q b g hq G)
  have hcomp := Stacks.RingedSpace.homEquiv_comparison (toInverseImageBase g)
      ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
      ((pushforward (toInverseImageBase a)).obj F)) ((_root_.pullback
      (relativeInverseImageProjectionOfFactors q b g hq)).obj
      ((pushforward (toInverseImageBase b)).obj G))
  exact chase_box2 (Q₁ := ((_root_.pullback p.toLRSHom.toShHom).obj F))
      (Q₂ := ((_root_.pullback q.toLRSHom.toShHom).obj G))
      (P₁ := (Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).obj
      ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
      ((pushforward (toInverseImageBase a)).obj F)))
      (P₂ := (Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).obj
      ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
      ((pushforward (toInverseImageBase b)).obj G)))
    (P₁' := (Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).obj
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback p.toLRSHom.toShHom).obj F)))
        (P₂' := (Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).obj
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj G)))
    (modulePullbackPushforwardAdjunction (toInverseImageBase g))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(inverseImageBase g).presheaf, (inverseImageBase g).IsSheaf⟩)).map
        (X := (((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj F)),
        ((_root_.pullback (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj G))))
        (Y := (((pushforward (toInverseImageBase g)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj F)),
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj G))))
        ((relativeInverseImageToPullbackOfFactors p a g hp F),
        (relativeInverseImageToPullbackOfFactors q b g hq G)))
        (inverseImageTensorLax g ((_root_.pullback p.toLRSHom.toShHom).obj F)
        ((_root_.pullback q.toLRSHom.toShHom).obj G))
    (Stacks.RingedSpace.comparisonTranspose (toInverseImageBase g)
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback p.toLRSHom.toShHom).obj F))
        ((pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj G)))
    ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase g)).counit.app
        ((_root_.pullback p.toLRSHom.toShHom).obj F)) ((Stacks.RingedSpace.pullbackAdjunction
        (toInverseImageBase g)).counit.app ((_root_.pullback q.toLRSHom.toShHom).obj G))
    (Stacks.RingedSpace.comparisonTranspose (toInverseImageBase g)
        ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj F)) ((_root_.pullback
        (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj G)))
    ((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
        (relativeInverseImageToPullbackOfFactors p a g hp F))
        ((Stacks.RingedSpace.pullbackFunctor (toInverseImageBase g)).map
        (relativeInverseImageToPullbackOfFactors q b g hq G)) _ _
    (Stacks.RingedSpace.comparison (toInverseImageBase g)
        ((_root_.pullback (relativeInverseImageProjectionOfFactors p a g hp)).obj
        ((pushforward (toInverseImageBase a)).obj F)) ((_root_.pullback
        (relativeInverseImageProjectionOfFactors q b g hq)).obj
        ((pushforward (toInverseImageBase b)).obj G))) hL2 hnat rfl rfl hcomp

end General

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The first leg of the box comparison is the tensor product of the two comparisons, both in
their transported form, by definition. -/
theorem relativeBoxComparisonLeg₁_eq_ofFactors (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    relativeBoxComparisonLeg₁ a b F G =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
        (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)).map
        (X := ((_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.fst a b) a
            (pullback.fst a b ≫ a) rfl)).obj ((pushforward (toInverseImageBase a)).obj F.module),
          (_root_.pullback (relativeInverseImageProjectionOfFactors (pullback.snd a b) b
            (pullback.fst a b ≫ a) pullback.condition.symm)).obj
              ((pushforward (toInverseImageBase b)).obj G.module)))
        (Y := ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
            ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module),
          (pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
            ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module)))
        (relativeInverseImageToPullbackOfFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
            F.module,
          relativeInverseImageToPullbackOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
            pullback.condition.symm G.module) :=
  rfl

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
