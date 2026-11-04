module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding

/-!
# Base change for a derived tensor product, with the fixed factor on the right

For a cartesian square of schemes and `(K, K', φ)` satisfying condition (1) of Stacks 0DJ8, the
same condition holds for

`L(g')^*(K ⊗^L D) ⟶ L(g')^*K ⊗^L L(g')^*D ⟶ K' ⊗^L L(g')^*D`

for every `D ∈ D(𝒪_X)`, at the derived tensor product the derived internal hom is stated at.
This is Stacks 0DJA (1) read through the commutativity constraint of Tag 0FPT, with which the
comparison of Tag 079U is compatible, and through `tensorBridge`.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_pullbackTensorIso_of_isPullback`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedPullbackTensor Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- The chase behind the right-slot form: the commutativity constraint and the comparison of the
two derived tensor products, pasted with the comparison of Tag 079U. -/
private theorem rightSlot_chase {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (pβi : A₀ ⟶ A₁) (pbr : A₁ ⟶ A₂) (uDK : A₂ ⟶ B₀) (t1φ : B₀ ⟶ B₅) (uKD : A₁ ⟶ B₁)
    (brK : B₁ ⟶ B₀) (tφ1 : B₁ ⟶ B₂) (brK' : B₂ ⟶ B₅) (βK : B₁ ⟶ B₃) (tφ2 : B₃ ⟶ B₄)
    (βK' : B₂ ⟶ B₄) (βiK' : B₄ ⟶ B₂)
    (h1 : pbr ≫ uDK = uKD ≫ brK) (h2 : tφ1 ≫ brK' = brK ≫ t1φ) (h3 : tφ1 ≫ βK' = βK ≫ tφ2)
    (h4 : βK' ≫ βiK' = 𝟙 _) :
    (pβi ≫ pbr) ≫ uDK ≫ t1φ = ((pβi ≫ uKD ≫ βK) ≫ tφ2) ≫ βiK' ≫ brK' := by
  simp only [Category.assoc]
  rw [reassoc_of% h1, ← h2, ← reassoc_of% h3, reassoc_of% h4]

/-- The uncurrying of a bifunctor at an identity paired with a morphism on the right. -/
private theorem uncurry_map_right {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) (A : C) {B B' : D} (ψ : B ⟶ B') :
    (Functor.uncurry.obj F).map (𝟙 A ×ₘ ψ) = (F.obj A).map ψ := by
  simp [Functor.uncurry]

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Stacks 0DJA (1), with the fixed factor on the right.**  For a cartesian square of schemes,
if the map of Stacks 0DJ7 at `(K, K', φ)` is an isomorphism at every point of `X'` and in every
degree, then so is the one at `L(g')^*(K ⊗^L D) ⟶ L(g')^*K ⊗^L L(g')^*D ⟶ K' ⊗^L L(g')^*D`, for
every `D` in `D(𝒪_X)`, at the derived tensor product of the internal hom. -/
theorem isIso_baseChangeCohomologyMap_pullbackTensorIso_of_isPullback
    (hpb : IsPullback g' f' f g) (K D : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ x' n))
    (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      ((internalHomTensorUncurried X.toRingedSpace).obj (K, D))
      ((internalHomTensorUncurried X'.toRingedSpace).obj
        (K', (derivedPullback g'.toLRSHom.toShHom).obj D))
      ((pullbackTensorIso g'.toLRSHom.toShHom).hom.app (K, D) ≫
        (internalHomTensorUncurried X'.toRingedSpace).map
          (φ ×ₘ 𝟙 ((derivedPullback g'.toLRSHom.toShHom).obj D))) x' n) := by
  have hβ : ∀ (Z : RingedSpace.{u, u}) (A B : DerivedCategory
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)),
      IsIso ((tensorBridge Z).inv.app (A, B) ≫
        Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom Z.sheaf A B) := by
    intro Z A B
    let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.sheaf
    let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Z.sheaf
    exact IsIso.comp_isIso' (Iso.isIso_inv ((tensorBridge Z).app (A, B))) (Iso.isIso_hom (β_ A B))
  let σ := (tensorBridge X.toRingedSpace).inv.app (K, D) ≫
    Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X.sheaf K D
  let τ := (tensorBridge X'.toRingedSpace).inv.app
      (K', (derivedPullback g'.toLRSHom.toShHom).obj D) ≫
    Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X'.sheaf K'
      ((derivedPullback g'.toLRSHom.toShHom).obj D)
  have hσ : IsIso σ := hβ _ _ _
  have hτ : IsIso τ := hβ _ _ _
  have key := isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback hpb D K K'
    φ h x' n
  have hsrc := (isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hpb.w _ _ _ σ hσ _
    x' n).2 key
  have heq : (derivedPullback g'.toLRSHom.toShHom).map σ ≫
      Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
        g'.toLRSHom.toShHom D K K' φ = ((pullbackTensorIso g'.toLRSHom.toShHom).hom.app (K, D) ≫
        (internalHomTensorUncurried X'.toRingedSpace).map
          (φ ×ₘ 𝟙 ((derivedPullback g'.toLRSHom.toShHom).obj D))) ≫ τ := by
    have h1 := derivedPullbackTensorIso_braiding g'.toLRSHom.toShHom K D
    have h2 := canonicalBraidingHom_naturality X'.toRingedSpace φ
      (𝟙 ((derivedPullback g'.toLRSHom.toShHom).obj D))
    have h3 := (tensorBridge X'.toRingedSpace).hom.naturality
      (φ ×ₘ 𝟙 ((derivedPullback g'.toLRSHom.toShHom).obj D))
    have h4 := (tensorBridge X'.toRingedSpace).hom_inv_id_app
      (K', (derivedPullback g'.toLRSHom.toShHom).obj D)
    refine (congrArg (· ≫ Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison
      g'.toLRSHom.toShHom D K K' φ) (Functor.map_comp (derivedPullback g'.toLRSHom.toShHom)
        ((tensorBridge X.toRingedSpace).inv.app (K, D))
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X.sheaf K D))).trans ?_
    exact rightSlot_chase _ _ _ _ _ _ _ _ _ _ _ _ h1 (h2.trans
      (congrArg (_ ≫ ·) (uncurry_map_right _ _ _))) h3 h4
  refine (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ _ τ hτ
    x' n).1 ?_
  exact isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _ heq.symm x' n hsrc

end AlgebraicGeometry
