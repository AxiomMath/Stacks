module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.Cotangent.Spaces.ModelCotangentAffineBase

/-!
# The inverse image along a morphism of algebraic spaces read on the models

Let `g : X ⟶ Y` be a morphism of algebraic spaces and `g_m` the morphism of ringed topoi between
the `Type u` models of the small étale ringed topoi of `X` and `Y`
(`AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom`, the composite
`ρ_Y ∘ g ∘ π_X`). This file computes its inverse image of sheaves of commutative rings on the
sheaves restricted from `Y_et`: for a sheaf of rings `R` on `Y_et`,

`g_m⁻¹(R|_model) ≅ (g⁻¹R)|_model`,

naturally in `R` (`AlgebraicGeometry.Space.modelPullbackInverseImageRingIso`), and under this
identification the structure map `g_m⁻¹𝒪_Y ⟶ 𝒪_X` of `g_m` is the restriction to the model of the
structure map `g⁻¹𝒪_Y ⟶ 𝒪_X` of `g`
(`AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom_fSharpInverseImage`).

The two model comparisons enter through their structure maps on underlying sheaves of sets: that
of `ρ_Y` is the counit of `ρ_Y⁻¹ ⊣ ρ_{Y*}`
(`AlgebraicGeometry.Space.smallEtaleModelInverseRingedToposHom_fSharpInverseImageForget`), and that
of `π_X` is the comparison of its inverse image with restriction to the model
(`AlgebraicGeometry.Space.smallEtaleModelRingedToposHom_fSharpInverseImageForget`).

## Main definitions

* `AlgebraicGeometry.Space.modelInverseImageSetIso`: `π_X⁻¹ ≅ (-)|_model` on sheaves of sets.
* `AlgebraicGeometry.Space.modelPullbackInverseImageSetIso`,
  `AlgebraicGeometry.Space.modelPullbackInverseImageRingIso`:
  `g_m⁻¹ ∘ (-)|_model ≅ (-)|_model ∘ g⁻¹`
  on sheaves of sets and of commutative rings.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModelPullbackRingedToposHom_fSharpInverseImage`

## References

* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_obstructionBaseChangeCotangent
    (Z : AlgebraicSpaces B S hS) (J : Type) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-! ### The comparisons of the model with the small étale site -/

section Comparisons

variable (B S hS) (X : AlgebraicSpaces B S hS)

/-- Restriction of sheaves of sets from the small étale site of `X` to its model: the direct image
along `ρ_X`. -/
abbrev modelSetRestriction :=
  (smallEtaleModelInverseRingedToposHom B S hS X).toToposHom.pushforward

/-- Restriction to the model is left adjoint to the direct image along `π_X`: the two are the
inverse and the functor of the equivalence of categories of sheaves induced by the model
equivalence. -/
def modelSetRestrictionAdjunction :
    modelSetRestriction B S hS X ⊣
      (smallEtaleModelRingedToposHom B S hS X).toToposHom.pushforward :=
  (Equivalence.sheafCongr (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
    (smallEtaleModelEquivalence B S hS X.1) (Type u)).symm.toAdjunction

/-- **The inverse image along `π_X` is restriction to the model**, on sheaves of sets: both are
left adjoint to the direct image along `π_X`. -/
def modelInverseImageSetIso :
    (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage ≅
      modelSetRestriction B S hS X :=
  (smallEtaleModelRingedToposHom B S hS X).toToposHom.adj.leftAdjointUniq
    (modelSetRestrictionAdjunction B S hS X)

/-- The structure map of `π_X` on underlying sheaves of sets, in direct-image form, is the unit
of the adjunction between restriction to the model and the direct image along `π_X`. -/
theorem forgetRing_map_smallEtaleModelRingedToposHom_fSharp :
    (smallEtaleRingedTopos B S hS X).forgetRing.map
        (smallEtaleModelRingedToposHom B S hS X).fSharp =
      (modelSetRestrictionAdjunction B S hS X).unit.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O) := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  rfl

/-- **The structure map of `π_X` on underlying sheaves of sets, in inverse-image form, is the
comparison of its inverse image with restriction to the model.** -/
theorem smallEtaleModelRingedToposHom_fSharpInverseImageForget :
    (smallEtaleModelRingedToposHom B S hS X).fSharpInverseImageForget =
      (modelInverseImageSetIso B S hS X).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O) := by
  let t : (smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O ⟶
      (smallEtaleModelRingedToposHom B S hS X).toToposHom.pushforward.obj
        ((smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.forgetRing.obj
          (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.O) :=
    (smallEtaleRingedTopos B S hS X).forgetRing.map (smallEtaleModelRingedToposHom B S hS X).fSharp
  have h := Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm
    (smallEtaleModelRingedToposHom B S hS X).toToposHom.adj
    (modelSetRestrictionAdjunction B S hS X) t
  have h1 : ((modelSetRestrictionAdjunction B S hS X).homEquiv _ _).symm t = 𝟙 _ :=
    (Equiv.symm_apply_eq _).2 ((forgetRing_map_smallEtaleModelRingedToposHom_fSharp B S hS X).trans
      ((modelSetRestrictionAdjunction B S hS X).homEquiv_id _).symm)
  exact h.symm.trans ((congrArg (fun m => (modelInverseImageSetIso B S hS X).hom.app
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O) ≫ m)
      h1).trans (Category.comp_id _))

/-- **The structure map of `ρ_Y` on underlying sheaves of sets, in inverse-image form, is the
counit of `ρ_Y⁻¹ ⊣ ρ_{Y*}`**: its direct-image form is the identity. -/
theorem smallEtaleModelInverseRingedToposHom_fSharpInverseImageForget :
    (smallEtaleModelInverseRingedToposHom B S hS X).fSharpInverseImageForget =
      (smallEtaleModelInverseRingedToposHom B S hS X).toToposHom.adj.counit.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O) := by
  have h : (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.forgetRing.map
      (smallEtaleModelInverseRingedToposHom B S hS X).fSharp = 𝟙 _ := by
    refine Sheaf.hom_ext_sections fun U s => ?_
    rfl
  exact (congrArg ((smallEtaleModelInverseRingedToposHom B S hS X).toToposHom.adj.homEquiv _ _).symm
    h).trans
      (((smallEtaleModelInverseRingedToposHom B S hS X).toToposHom.adj.homEquiv_counit _ _ _).trans
      ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)))

/-- The direct image along `ρ_X` is an equivalence. -/
instance isEquivalence_smallEtaleModelInverseRingedToposHom_pushforward :
    (smallEtaleModelInverseRingedToposHom B S hS X).toToposHom.pushforward.IsEquivalence :=
  (Equivalence.sheafCongr (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
    (smallEtaleModelEquivalence B S hS X.1) (Type u)).isEquivalence_inverse

end Comparisons

/-! ### Carrying a commutative square of restrictions to sheaves of rings -/

section Generic

universe w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {K₁ : GrothendieckTopology D₁} {K₂ : GrothendieckTopology D₂}
  [J₁.HasSheafCompose (forget RingCat.{w})] [J₂.HasSheafCompose (forget RingCat.{w})]
  [K₁.HasSheafCompose (forget RingCat.{w})] [K₂.HasSheafCompose (forget RingCat.{w})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K₁.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K₂.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (G₁ : C₁ ⥤ D₁) [G₁.IsContinuous J₁ K₁] (G₂ : C₂ ⥤ D₂) [G₂.IsContinuous J₂ K₂]
  (Φ : Sheaf J₁ (Type w) ⥤ Sheaf J₂ (Type w)) [hΦ : PreservesFiniteProducts Φ]
  (Ψ : Sheaf K₁ (Type w) ⥤ Sheaf K₂ (Type w)) [hΨ : PreservesFiniteProducts Ψ]
  [h₁ : PreservesFiniteProducts (G₁.sheafPushforwardContinuous (Type w) J₁ K₁)]
  [h₂ : PreservesFiniteProducts (G₂.sheafPushforwardContinuous (Type w) J₂ K₂)]
  [h₁Φ : PreservesFiniteProducts (G₁.sheafPushforwardContinuous (Type w) J₁ K₁ ⋙ Φ)]
  [hΨ₂ : PreservesFiniteProducts (Ψ ⋙ G₂.sheafPushforwardContinuous (Type w) J₂ K₂)]
  (σ : G₁.sheafPushforwardContinuous (Type w) J₁ K₁ ⋙ Φ ≅
    Ψ ⋙ G₂.sheafPushforwardContinuous (Type w) J₂ K₂)

/-- **A commutative square of functors of sheaves of sets, with two sides restrictions, carried to
sheaves of commutative rings**: `R|_{G₁} ↦ Φ(R|_{G₁})` and `R ↦ (ΨR)|_{G₂}` are isomorphic, the
ring operations carried along `σ`. -/
def restrictionSquareRingIso :
    G₁.sheafPushforwardContinuous CommRingCat.{w} J₁ K₁ ⋙ pullbackCommRingSheafFunctor J₂ Φ ≅
      pullbackCommRingSheafFunctor K₂ Ψ ⋙ G₂.sheafPushforwardContinuous CommRingCat.{w} J₂ K₂ :=
  Functor.isoWhiskerRight (restrictionCommRingNatIso J₁ K₁ G₁).symm _ ≪≫
    pullbackCommRingSheafFunctorComp J₁ J₂ _ Φ ≪≫
    pullbackCommRingSheafFunctorIsoOfNatIso J₂ σ ≪≫
    (pullbackCommRingSheafFunctorComp K₂ J₂ Ψ _).symm ≪≫
    Functor.isoWhiskerLeft _ (restrictionCommRingNatIso J₂ K₂ G₂)

theorem forget_map_restrictionSquareRingIso_hom_app [J₂.HasSheafCompose (forget CommRingCat.{w})]
    [K₁.HasSheafCompose (forget CommRingCat.{w})] [K₂.HasSheafCompose (forget CommRingCat.{w})]
    [J₁.HasSheafCompose (forget CommRingCat.{w})] (R : Sheaf K₁ CommRingCat.{w}) :
    (sheafCompose J₂ (forget CommRingCat.{w})).map
        ((restrictionSquareRingIso G₁ G₂ Φ Ψ σ).hom.app R) =
      σ.hom.app ((sheafCompose K₁ (forget CommRingCat.{w})).obj R) := by
  have hinv : (sheafCompose J₂ (forget CommRingCat.{w})).map
      (pullbackCommRingSheafComp K₂ J₂ Ψ (G₂.sheafPushforwardContinuous (Type w) J₂ K₂) R).inv =
        𝟙 _ := by
    have h := congrArg (sheafCompose J₂ (forget CommRingCat.{w})).map
      (pullbackCommRingSheafComp K₂ J₂ Ψ
        (G₂.sheafPushforwardContinuous (Type w) J₂ K₂) R).hom_inv_id
    rw [Functor.map_comp, forget_map_pullbackCommRingSheafComp_hom] at h
    exact (Category.id_comp _).symm.trans (h.trans (CategoryTheory.Functor.map_id _ _))
  let F := sheafCompose J₂ (forget CommRingCat.{w})
  let F' := sheafCompose K₁ (forget CommRingCat.{w})
  have hA : F.map (pullbackCommRingSheafMap J₂ Φ ((restrictionCommRingIso J₁ K₁ G₁ R).inv)) =
      𝟙 (Φ.obj ((G₁.sheafPushforwardContinuous (Type w) J₁ K₁).obj (F'.obj R))) :=
    (underlyingRingSheaf_map_pullbackCommRingSheafMap J₂ (Φ := Φ) _).trans
      ((congrArg Φ.map (restrictionCommRingIso_inv_forget J₁ K₁ G₁ R)).trans (Φ.map_id _))
  have hB := forget_map_pullbackCommRingSheafComp_hom J₁ J₂
    (G₁.sheafPushforwardContinuous (Type w) J₁ K₁) Φ R
  have hC := pullbackCommRingSheafIsoOfNatIso_hom_forget J₂ σ R
  have hD : F.map (pullbackCommRingSheafComp K₂ J₂ Ψ
      (G₂.sheafPushforwardContinuous (Type w) J₂ K₂) R).inv =
        𝟙 (F.obj (pullbackCommRingSheaf J₂ (G₂.sheafPushforwardContinuous (Type w) J₂ K₂)
          (pullbackCommRingSheaf K₂ Ψ R))) := hinv
  have hE : F.map (restrictionCommRingIso J₂ K₂ G₂ (pullbackCommRingSheaf K₂ Ψ R)).hom =
      𝟙 (F.obj (pullbackCommRingSheaf J₂ (G₂.sheafPushforwardContinuous (Type w) J₂ K₂)
          (pullbackCommRingSheaf K₂ Ψ R))) :=
    restrictionCommRingIso_hom_forget J₂ K₂ G₂ (pullbackCommRingSheaf K₂ Ψ R)
  refine (F.map_comp _ _).trans ?_
  refine (eq_whisker hA _).trans ((@Category.id_comp _ _
    (Φ.obj ((G₁.sheafPushforwardContinuous (Type w) J₁ K₁).obj (F'.obj R))) _ _).trans ?_)
  refine (F.map_comp _ _).trans ?_
  refine (eq_whisker hB _).trans ((Category.id_comp _).trans ?_)
  refine (F.map_comp _ _).trans ?_
  refine (eq_whisker hC _).trans ?_
  refine (whisker_eq _ (F.map_comp _ _)).trans ?_
  refine (whisker_eq _ ((eq_whisker hD _).trans (Category.id_comp _))).trans ?_
  exact (whisker_eq _ hE).trans (Category.comp_id _)

end Generic

/-! ### The inverse image along `g_m` on restricted sheaves -/

section PullbackInverseImage

variable {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)

/-- **`g_m⁻¹(F|_model) ≅ (g⁻¹F)|_model`** on sheaves of sets: the counit of `ρ_Y⁻¹ ⊣ ρ_{Y*}` (an
isomorphism, `ρ_{Y*}` being an equivalence) followed by `π_X⁻¹ ≅ (-)|_model`. -/
def modelPullbackInverseImageSetIso :
    modelSetRestriction B S hS Y ⋙
        (smallEtaleModelPullbackRingedToposHom g).toToposHom.inverseImage ≅
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage ⋙ modelSetRestriction B S hS X :=
  NatIso.ofComponents (fun F =>
      (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.mapIso
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.mapIso
            (asIso ((smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.adj.counit.app F)))
            ≪≫
        (modelInverseImageSetIso B S hS X).app
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.obj F))
    (fun {F F'} φ => by
      have h1 := (smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.adj.counit.naturality φ
      have h2 := (modelInverseImageSetIso B S hS X).hom.naturality
        ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map φ)
      have k1 : (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
            ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
              ((smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.inverseImage.map
                ((smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.pushforward.map φ))) ≫
          (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
            ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
              ((smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.adj.counit.app F')) =
          (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
            ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
              ((smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.adj.counit.app F)) ≫
          (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
            ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map φ) := by
        rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (fun t =>
            (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map t)) h1
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) k1)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

/-- The components of `modelPullbackInverseImageSetIso`. -/
theorem modelPullbackInverseImageSetIso_hom_app
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (modelPullbackInverseImageSetIso g).hom.app F =
      (smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
            ((smallEtaleModelInverseRingedToposHom B S hS Y).toToposHom.adj.counit.app F)) ≫
        (modelInverseImageSetIso B S hS X).hom.app
          ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.obj F) :=
  rfl

/-- Restriction of sheaves of sets to the model preserves finite products. -/
instance preservesFiniteProducts_modelRestriction (X : AlgebraicSpaces B S hS) :
    PreservesFiniteProducts ((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous
      (Type u) (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)) :=
  inferInstanceAs (PreservesFiniteProducts (modelSetRestriction B S hS X))

/-- `g_m⁻¹` preserves finite products. -/
instance preservesFiniteProducts_smallEtaleModelPullbackRingedToposHom_inverseImage :
    PreservesFiniteProducts (smallEtaleModelPullbackRingedToposHom g).toToposHom.inverseImage :=
  haveI := (smallEtaleModelPullbackRingedToposHom g).toToposHom.preservesFiniteLimits
  inferInstance

/-- `g⁻¹` preserves finite products. -/
instance preservesFiniteProducts_smallEtaleRingedToposHom_inverseImage :
    PreservesFiniteProducts (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage :=
  haveI := (smallEtaleRingedToposHom B S hS g).toToposHom.preservesFiniteLimits
  ⟨fun _ => PreservesFiniteLimits.preservesFiniteLimits _⟩

/-- `F ↦ g_m⁻¹(F|_model)` preserves finite products. -/
instance preservesFiniteProducts_modelRestriction_comp_inverseImage :
    PreservesFiniteProducts ((smallEtaleModelEquiv B S hS Y).inverse.sheafPushforwardContinuous
      (Type u) (smallEtaleModelTopology B S hS Y.1) (SmallEtale.topology B S hS Y.1) ⋙
        (smallEtaleModelPullbackRingedToposHom g).toToposHom.inverseImage) :=
  inferInstanceAs (PreservesFiniteProducts (modelSetRestriction B S hS Y ⋙
    (smallEtaleModelPullbackRingedToposHom g).toToposHom.inverseImage))

/-- `F ↦ (g⁻¹F)|_model` preserves finite products. -/
instance preservesFiniteProducts_inverseImage_comp_modelRestriction :
    PreservesFiniteProducts ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage ⋙
      (smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous
        (Type u) (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)) :=
  inferInstanceAs (PreservesFiniteProducts
    ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage ⋙
    modelSetRestriction B S hS X))

/-- **`g_m⁻¹(R|_model) ≅ (g⁻¹R)|_model`** on sheaves of commutative rings, naturally in `R`: the
ring operations carried along `modelPullbackInverseImageSetIso`. -/
def modelPullbackInverseImageRingIso :
    modelRingRestriction (X := Y) ⋙
        inverseImageCommRingFunctor.{u, u, u, u, u, u}
          (smallEtaleModelPullbackRingedToposHom g).toToposHom ≅
      smallEtaleInverseImageRing B S hS g ⋙ modelRingRestriction (X := X) :=
  restrictionSquareRingIso.{u} (J₁ := smallEtaleModelTopology B S hS Y.1)
    (J₂ := smallEtaleModelTopology B S hS X.1) (K₁ := SmallEtale.topology B S hS Y.1)
    (K₂ := SmallEtale.topology B S hS X.1)
    (hΦ := preservesFiniteProducts_smallEtaleModelPullbackRingedToposHom_inverseImage g)
    (hΨ := preservesFiniteProducts_smallEtaleRingedToposHom_inverseImage g)
    (smallEtaleModelEquiv B S hS Y).inverse
    (smallEtaleModelEquiv B S hS X).inverse
      (smallEtaleModelPullbackRingedToposHom g).toToposHom.inverseImage
    (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage (modelPullbackInverseImageSetIso g)

/-- On underlying sheaves of sets, `modelPullbackInverseImageRingIso` is
`modelPullbackInverseImageSetIso`. -/
theorem forget_map_modelPullbackInverseImageRingIso_hom_app
    (R : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}) :
    (sheafCompose (smallEtaleModelTopology B S hS X.1) (forget CommRingCat.{u})).map
        ((modelPullbackInverseImageRingIso g).hom.app R) =
      (modelPullbackInverseImageSetIso g).hom.app
        ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj R) :=
  forget_map_restrictionSquareRingIso_hom_app.{u} (J₁ := smallEtaleModelTopology B S hS Y.1)
    (J₂ := smallEtaleModelTopology B S hS X.1) (K₁ := SmallEtale.topology B S hS Y.1)
    (K₂ := SmallEtale.topology B S hS X.1)
    (hΦ := preservesFiniteProducts_smallEtaleModelPullbackRingedToposHom_inverseImage g)
    (hΨ := preservesFiniteProducts_smallEtaleRingedToposHom_inverseImage g)
    (h₁Φ := preservesFiniteProducts_modelRestriction_comp_inverseImage g)
    (hΨ₂ := preservesFiniteProducts_inverseImage_comp_modelRestriction g)
    (smallEtaleModelEquiv B S hS Y).inverse
    (smallEtaleModelEquiv B S hS X).inverse
      (smallEtaleModelPullbackRingedToposHom g).toToposHom.inverseImage
    (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage
      (modelPullbackInverseImageSetIso g) R

/-- **The structure map of `g_m` on underlying sheaves of sets is the restriction of that of `g`**,
read through `modelPullbackInverseImageSetIso`. -/
theorem smallEtaleModelPullbackRingedToposHom_fSharpInverseImageForget :
    (smallEtaleModelPullbackRingedToposHom g).fSharpInverseImageForget =
      (modelPullbackInverseImageSetIso g).hom.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O) ≫
        (modelSetRestriction B S hS X).map
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImageForget := by
  have h₁ := RingedToposHom.fSharpInverseImageForget_comp
    (smallEtaleModelInverseRingedToposHom B S hS Y) (smallEtaleModelCompRingedToposHom g)
  have h₂ := RingedToposHom.fSharpInverseImageForget_comp
    (smallEtaleRingedToposHom B S hS g) (smallEtaleModelRingedToposHom B S hS X)
  have hn := (modelInverseImageSetIso B S hS X).hom.naturality
    (smallEtaleRingedToposHom B S hS g).fSharpInverseImageForget
  have hρ := smallEtaleModelInverseRingedToposHom_fSharpInverseImageForget B S hS Y
  have hπ := smallEtaleModelRingedToposHom_fSharpInverseImageForget B S hS X
  exact h₁.trans ((congrArg (_ ≫ ·) h₂).trans ((congrArg₂ (fun a b =>
    (smallEtaleModelCompRingedToposHom g).toToposHom.inverseImage.map a ≫
      ((smallEtaleModelRingedToposHom B S hS X).toToposHom.inverseImage.map
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImageForget ≫ b)) hρ hπ).trans
    ((congrArg (_ ≫ ·) hn).trans (Category.assoc _ _ _).symm)))

/-- **The structure map of `g_m` is the restriction of that of `g`**: under
`g_m⁻¹𝒪_Y = g_m⁻¹(𝒪_Y|_model) ≅ (g⁻¹𝒪_Y)|_model`, the structure map `g_m⁻¹𝒪_Y ⟶ 𝒪_X` of the
model morphism is the restriction to the model of `g⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem smallEtaleModelPullbackRingedToposHom_fSharpInverseImage :
    (smallEtaleModelPullbackRingedToposHom g).fSharpInverseImage =
      (modelPullbackInverseImageRingIso g).hom.app (smallEtaleRingedTopos B S hS Y).O ≫
        (modelRingRestriction (X := X)).map
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage := by
  refine (sheafCompose (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.J
      (forget CommRingCat.{u})).map_injective
    ?_
  refine ((RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (smallEtaleModelPullbackRingedToposHom g)).trans
      (smallEtaleModelPullbackRingedToposHom_fSharpInverseImageForget g)).trans ?_
  refine Eq.trans ?_ ((sheafCompose (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos.J
    (forget CommRingCat.{u})).map_comp _ _).symm
  exact congrArg₂ (· ≫ ·) (forget_map_modelPullbackInverseImageRingIso_hom_app g _).symm
    (congrArg (modelSetRestriction B S hS X).map
      (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
        (smallEtaleRingedToposHom B S hS g)).symm)

end PullbackInverseImage

end AlgebraicGeometry.Space

end
