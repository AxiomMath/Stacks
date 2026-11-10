module

public import StacksFrontier.Homology.DerivedIndexing.CoEdgeDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.DerivedFunctorBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerCoboundaryBaseChange

/-!
# The connecting morphism of right derived functors in two models of the derived categories

The `ℕ`-indexed right derived functors `R ⁱF` of Mathlib do not depend on a model of the derived
categories, but their connecting morphisms `R ⁰F(X₃) ⟶ R ¹F(X₁)`
(`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`), normalised through the
degree-zero identification `F ≅ R ⁰F`, are defined through one. Both models make `R ⁱF` an
effaceable δ-functor, so the identification of the degree-zero parts extends uniquely to the
higher degrees, and the extension is invertible
(`CategoryTheory.DeltaFunctor.DeltaFamily.liftFamily`,
`CategoryTheory.DeltaFunctor.DeltaFamily.liftFamily_ext`). Hence the two normalised connecting
morphisms of a short exact sequence differ by an automorphism of `R ¹F(X₁)`
(`Stacks.EtaleCohomology.Purity.exists_iso_rightDerivedConnecting_comp`). This is all that is
needed to carry a statement about the image of a connecting morphism (for instance that it
generates a stalk) from one model to another.

## Main definitions

* `Stacks.EtaleCohomology.Purity.rightDerivedZeroIsoOfModel`.
* `Stacks.EtaleCohomology.Purity.rightDerivedDeltaOfModel`.

## Main results

* `Stacks.EtaleCohomology.Purity.exists_iso_rightDerivedConnecting_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.Purity

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The higher right derived functors as a δ-functor, in the models `I`, `J`. -/
def rightDerivedDeltaOfModel (I : HasDerivedCategory C) (J : HasDerivedCategory D) :
    DeltaFunctor C D :=
  letI := I
  letI := J
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F

omit [PreservesFiniteLimits F] in
/-- In any models `I`, `J`, the degree-`n` functor of `rightDerivedDeltaOfModel F I J` is
`F.rightDerived n`. -/
theorem rightDerivedDeltaOfModel_functor (I : HasDerivedCategory C) (J : HasDerivedCategory D)
    (n : ℕ) : (rightDerivedDeltaOfModel F I J).functor n = F.rightDerived n := rfl

/-- The normalised degree-zero identification `F ≅ R ⁰F` in the models `I`, `J` of the derived
categories of the source and the target. -/
def rightDerivedZeroIsoOfModel (I : HasDerivedCategory C) (J : HasDerivedCategory D) :
    F ≅ (rightDerivedDeltaOfModel F I J).functor 0 :=
  letI := I
  letI := J
  NatIso.ofComponents
    (fun X => haveI := Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit F X
      asIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit F X) ≪≫
        (Stacks.DerivedIndexing.rightDerivedIso F 0).symm.app X)
    (fun φ => rightDerivedZeroUnit_comp_rightDerivedIso_inv_naturality F φ)

/-- The δ-functor `rightDerivedDeltaOfModel F I J` is effaceable. -/
instance effaceable_rightDerivedDeltaOfModel (I : HasDerivedCategory C)
    (J : HasDerivedCategory D) : (rightDerivedDeltaOfModel F I J).Effaceable :=
  DeltaFunctor.Effaceable.of_isZero_injective _ fun n X _ ↦
    F.isZero_rightDerived_obj_injective_succ n X

/-- A δ-functor, as a δ-family. -/
def deltaFamilyOfDeltaFunctor (H : DeltaFunctor C D) : DeltaFunctor.DeltaFamily C D where
  functor := H.functor
  δ hS n := H.δ hS n
  map_g_δ hS n := H.map_g_δ hS n
  δ_naturality hS hT φ n := H.δ_naturality hS hT φ n

/-- The comparison of two models in degree `n`: the extension of the identification of the
degree-zero parts. -/
def rightDerivedModelComparison (I₁ : HasDerivedCategory C) (J₁ : HasDerivedCategory D)
    (I₂ : HasDerivedCategory C) (J₂ : HasDerivedCategory D) (n : ℕ) :
    (rightDerivedDeltaOfModel F I₁ J₁).functor n ⟶ (rightDerivedDeltaOfModel F I₂ J₂).functor n :=
  (deltaFamilyOfDeltaFunctor (rightDerivedDeltaOfModel F I₂ J₂)).liftFamily
    (rightDerivedDeltaOfModel F I₁ J₁)
    ((rightDerivedZeroIsoOfModel F I₁ J₁).inv ≫ (rightDerivedZeroIsoOfModel F I₂ J₂).hom) n

/-- The comparison of two models commutes with the connecting morphisms of a short exact
sequence. -/
theorem δ_comp_rightDerivedModelComparison (I₁ : HasDerivedCategory C)
    (J₁ : HasDerivedCategory D) (I₂ : HasDerivedCategory C) (J₂ : HasDerivedCategory D)
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (rightDerivedDeltaOfModel F I₁ J₁).δ hS n ≫
        (rightDerivedModelComparison F I₁ J₁ I₂ J₂ (n + 1)).app S.X₁ =
      (rightDerivedModelComparison F I₁ J₁ I₂ J₂ n).app S.X₃ ≫
        (rightDerivedDeltaOfModel F I₂ J₂).δ hS n :=
  (deltaFamilyOfDeltaFunctor (rightDerivedDeltaOfModel F I₂ J₂)).δ_comp_liftFamily
    (F := rightDerivedDeltaOfModel F I₁ J₁) _ hS n

/-- In degree zero, the comparison of two models is the composite of the two degree-zero
identifications `R ⁰F ≅ F ≅ R ⁰F`. -/
theorem rightDerivedModelComparison_zero (I₁ : HasDerivedCategory C) (J₁ : HasDerivedCategory D)
    (I₂ : HasDerivedCategory C) (J₂ : HasDerivedCategory D) :
    rightDerivedModelComparison F I₁ J₁ I₂ J₂ 0 =
      (rightDerivedZeroIsoOfModel F I₁ J₁).inv ≫ (rightDerivedZeroIsoOfModel F I₂ J₂).hom := rfl

/-- The comparison from the first model to the second, followed by the comparison back, is the
identity. -/
theorem rightDerivedModelComparison_comp (I₁ : HasDerivedCategory C) (J₁ : HasDerivedCategory D)
    (I₂ : HasDerivedCategory C) (J₂ : HasDerivedCategory D) (n : ℕ) :
    rightDerivedModelComparison F I₁ J₁ I₂ J₂ n ≫ rightDerivedModelComparison F I₂ J₂ I₁ J₁ n =
      𝟙 _ := by
  let G₁ := deltaFamilyOfDeltaFunctor (rightDerivedDeltaOfModel F I₁ J₁)
  have key : ∀ {S : ShortComplex C} (hS : S.ShortExact) (m : ℕ),
      (rightDerivedDeltaOfModel F I₁ J₁).δ hS m ≫
          (rightDerivedModelComparison F I₁ J₁ I₂ J₂ (m + 1) ≫
            rightDerivedModelComparison F I₂ J₂ I₁ J₁ (m + 1)).app S.X₁ =
        (rightDerivedModelComparison F I₁ J₁ I₂ J₂ m ≫
          rightDerivedModelComparison F I₂ J₂ I₁ J₁ m).app S.X₃ ≫
            (rightDerivedDeltaOfModel F I₁ J₁).δ hS m := by
    intro S hS m
    rw [NatTrans.comp_app, NatTrans.comp_app, ← Category.assoc,
      δ_comp_rightDerivedModelComparison, Category.assoc, Category.assoc,
      δ_comp_rightDerivedModelComparison]
  have h := G₁.liftFamily_ext (fun m => rightDerivedModelComparison F I₁ J₁ I₂ J₂ m ≫
    rightDerivedModelComparison F I₂ J₂ I₁ J₁ m) key n
  have h1 := G₁.liftFamily_ext (fun m => 𝟙 ((rightDerivedDeltaOfModel F I₁ J₁).functor m))
    (fun hS m => by simp [G₁, deltaFamilyOfDeltaFunctor]) n
  have h0 : rightDerivedModelComparison F I₁ J₁ I₂ J₂ 0 ≫
      rightDerivedModelComparison F I₂ J₂ I₁ J₁ 0 = 𝟙 _ := by
    rw [rightDerivedModelComparison_zero, rightDerivedModelComparison_zero]
    simp
  exact h.trans ((congrArg (fun t => G₁.liftFamily _ t n) h0).trans h1.symm)

/-- **The two normalised connecting morphisms of a short exact sequence differ by an
automorphism of `R ¹F(X₁)`.** -/
theorem exists_iso_rightDerivedConnecting_comp (I₁ : HasDerivedCategory C)
    (J₁ : HasDerivedCategory D) (I₂ : HasDerivedCategory C) (J₂ : HasDerivedCategory D)
    {S : ShortComplex C} (hS : S.ShortExact) :
    ∃ φ : (F.rightDerived 1).obj S.X₁ ≅ (F.rightDerived 1).obj S.X₁,
      (rightDerivedZeroIsoOfModel F I₂ J₂).hom.app S.X₃ ≫
          (rightDerivedDeltaOfModel F I₂ J₂).δ hS 0 =
        ((rightDerivedZeroIsoOfModel F I₁ J₁).hom.app S.X₃ ≫
          (rightDerivedDeltaOfModel F I₁ J₁).δ hS 0) ≫ φ.hom := by
  refine ⟨⟨(rightDerivedModelComparison F I₁ J₁ I₂ J₂ 1).app S.X₁,
    (rightDerivedModelComparison F I₂ J₂ I₁ J₁ 1).app S.X₁,
    NatTrans.congr_app (rightDerivedModelComparison_comp F I₁ J₁ I₂ J₂ 1) S.X₁,
    NatTrans.congr_app (rightDerivedModelComparison_comp F I₂ J₂ I₁ J₁ 1) S.X₁⟩, ?_⟩
  change _ = _ ≫ (rightDerivedModelComparison F I₁ J₁ I₂ J₂ (0 + 1)).app S.X₁
  rw [Category.assoc, δ_comp_rightDerivedModelComparison, rightDerivedModelComparison_zero,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]

end Stacks.EtaleCohomology.Purity

end
