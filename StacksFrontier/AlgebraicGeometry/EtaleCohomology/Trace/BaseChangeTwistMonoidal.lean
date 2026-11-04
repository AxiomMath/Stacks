module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.CategoryTheory.Sites.SheafPushforwardLaxMonoidal
public import StacksFrontier.CategoryTheory.Abelian.ExtCupTwist

/-!
# The base change twist is monoidal

Let `a ≫ g = g ≫ b` be a commutative square of schemes with `g : Y' ⟶ Y`, `a : Y' ⟶ Y'`,
`b : Y ⟶ Y`, and let `ψ : 𝟭 ⟶ b_*` be the identification of the direct image along `b` with the
identity induced by an isomorphism `𝟭 ≅ b⁻¹` of the small étale site of `Y` (the situation of the
geometric Frobenius, [Stacks, Tag 03SR]). The base change twist
`τ = Stacks.EtaleCohomology.etaleModuleBaseChangeTwist : g⁻¹ ⟶ g⁻¹ ⋙ a_*` is a monoidal natural
transformation (`isMonoidal_etaleModuleBaseChangeTwist`), the direct images carrying the lax
structures right adjoint to the monoidal inverse images. Consequently its transposes
`σ_M : a⁻¹ g⁻¹ M ⟶ g⁻¹ M` are compatible with every pairing pulled back from `Y`
(`etaleModuleBaseChangeTwist_twistAction_hσ`), so the twisted action of `a` on `Ext` out of the
unit commutes with cup products of classes with coefficients pulled back from `Y`
(`Stacks.ExtCup.twistAction_cup`).

For the base change `π̄` of the geometric Frobenius this is the Frobenius equivariance of cup
products (`frobeniusBaseChangeTwist_twistAction_hσ`).

## Main results

* `Stacks.EtaleCohomology.isMonoidal_etaleModuleDirectImageComp`: the composition isomorphism
  of étale direct images is monoidal.
* `Stacks.EtaleCohomology.isMonoidal_etaleSheafPushforwardComparison`: the identification
  `𝟭 ≅ b_*` induced by an isomorphism `𝟭 ≅ b⁻¹` of the small étale site is monoidal.
* `Stacks.EtaleCohomology.isMonoidal_etaleModuleBaseChangeTwist`: the base change twist of a
  monoidal `ψ` is monoidal.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_twistAction_hσ`: the transposed base change
  twist is compatible with pairings pulled back along `g`.
* `Stacks.EtaleCohomology.frobeniusBaseChangeTwist_twistAction_hσ`: the same for the Frobenius
  base change twist.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

/-- The category of `Λ`-modules in `Type (u + 1)` has colimits of size `u + 1`. -/
local instance hasColimitsOfSize_moduleCat_baseChangeTwistMonoidal :
    HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

/-- The class of morphisms inverted by sheafification of étale presheaves of modules on `S` is
monoidal. -/
local instance (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

attribute [local instance] Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  Functor.sheafToPresheafLaxMonoidal
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

/-- The direct image of étale sheaves of modules is lax monoidal, as the right adjoint of the
monoidal inverse image. -/
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDirectImage.{u, 0} Λ f).LaxMonoidal :=
  (etaleModuleInverseImageAdj.{u, 0} Λ f).rightAdjointLaxMonoidal

/-- The adjunction `f⁻¹ ⊣ f_*` of étale sheaves of modules is monoidal. -/
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleInverseImageAdj.{u, 0} Λ f).IsMonoidal :=
  ⟨rfl, fun _ _ => rfl⟩

/-- The lax structure of the étale direct image reads on presheaves as precomposition with base
change. -/
lemma readsAsPrecomposition_etaleModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.ReadsAsPrecomposition (A := ModuleCat.{u + 1} Λ) Y.smallEtaleTopology
      X.smallEtaleTopology (smallEtaleBaseChange f) := by
  have : ∀ Z : X.Etaleᵒᵖ, IsFiltered (CostructuredArrow (smallEtaleBaseChange f).op Z) :=
    fun Z => IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange f) (Opposite.unop Z))
  have : ∀ (Z : X.Etaleᵒᵖ) (M : ModuleCat.{u + 1} Λ),
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange f).op Z)
        ((curriedTensor (ModuleCat.{u + 1} Λ)).obj M) :=
    fun _ M => inferInstanceAs (PreservesColimitsOfShape _ (MonoidalCategory.tensorLeft M))
  have : ∀ (Z : X.Etaleᵒᵖ) (M : ModuleCat.{u + 1} Λ),
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange f).op Z)
        ((curriedTensor (ModuleCat.{u + 1} Λ)).flip.obj M) :=
    fun _ M =>
      have : PreservesColimitsOfSize.{u, u + 1} (MonoidalCategory.tensorRight M) :=
        preservesColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} (MonoidalCategory.tensorRight M)
      inferInstanceAs (PreservesColimitsOfShape _ (MonoidalCategory.tensorRight M))
  exact Functor.readsAsPrecomposition_sheafPushforwardContinuous (smallEtaleBaseChange f)
    (ModuleCat.{u + 1} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- **The composition isomorphism of étale direct images is monoidal.** -/
instance isMonoidal_etaleModuleDirectImageComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    NatTrans.IsMonoidal (etaleModuleDirectImageComp.{u, 0} Λ f g fg hfg).hom :=
  Functor.isMonoidal_of_readsAsPrecomposition_comp _ _ _
    (readsAsPrecomposition_etaleModuleDirectImage Λ g)
    (readsAsPrecomposition_etaleModuleDirectImage Λ f)
    (readsAsPrecomposition_etaleModuleDirectImage Λ fg)
    (smallEtaleBaseChangeComp' f g fg hfg).hom _
    (fun M U => etaleModuleDirectImageComp_hom_app_hom_app Λ f g fg hfg M U)

/-- **The identification of the direct image along `b` with the identity, induced by an
isomorphism `𝟭 ≅ b⁻¹` of the small étale site, is monoidal.** -/
instance isMonoidal_etaleSheafPushforwardComparison {Y : Scheme.{u}} (b : Y ⟶ Y)
    (e : 𝟭 Y.Etale ≅ smallEtaleBaseChange b) :
    NatTrans.IsMonoidal (etaleSheafPushforwardComparison Y b e (ModuleCat.{u + 1} Λ)).hom :=
  Functor.isMonoidal_of_readsAsPrecomposition_id _
    (readsAsPrecomposition_etaleModuleDirectImage Λ b) e.inv _
    (fun M U => etaleSheafPushforwardComparison_hom_app_hom_app Y b e _ M (Opposite.unop U))

section Twist

variable {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y) (w : a ≫ g = g ≫ b)
  (ψ : 𝟭 (EtaleModules.{u, 0} Λ Y) ⟶ etaleModuleDirectImage.{u, 0} Λ b)

/-- **The base change twist of a monoidal `ψ : 𝟭 ⟶ b_*` is monoidal.** -/
instance isMonoidal_etaleModuleBaseChangeTwist [NatTrans.IsMonoidal ψ] :
    NatTrans.IsMonoidal (etaleModuleBaseChangeTwist.{u, 0} Λ g a b w ψ) := by
  have := isMonoidal_etaleModuleDirectImageComp Λ g b (a ≫ g) w
  have := isMonoidal_etaleModuleDirectImageComp Λ a g (a ≫ g) rfl
  have : NatTrans.IsMonoidal (etaleModuleBaseChangeTwistAdj.{u, 0} Λ g a b w ψ) := by
    unfold etaleModuleBaseChangeTwistAdj
    infer_instance
  unfold etaleModuleBaseChangeTwist
  infer_instance

/-- **The transposed base change twist is compatible with pairings pulled back along `g`.** For
`μ₀ : L₁ ⊗ L₂ ⟶ L₃` on `Y` and `μ = μ_{g⁻¹} ≫ g⁻¹ μ₀` on `Y'`, the transposes
`σ_L : a⁻¹ g⁻¹ L ⟶ g⁻¹ L` of the base change twist satisfy
`μ_{a⁻¹} ≫ a⁻¹ μ ≫ σ_{L₃} = (σ_{L₁} ⊗ σ_{L₂}) ≫ μ`. -/
theorem etaleModuleBaseChangeTwist_twistAction_hσ [NatTrans.IsMonoidal ψ]
    {L₁ L₂ L₃ : EtaleModules.{u, 0} Λ Y} (μ₀ : L₁ ⊗ L₂ ⟶ L₃) :
    μ (etaleModuleInverseImage.{u, 0} Λ a) ((etaleModuleInverseImage.{u, 0} Λ g).obj L₁)
        ((etaleModuleInverseImage.{u, 0} Λ g).obj L₂) ≫
      (etaleModuleInverseImage.{u, 0} Λ a).map (μ (etaleModuleInverseImage.{u, 0} Λ g) L₁ L₂ ≫
        (etaleModuleInverseImage.{u, 0} Λ g).map μ₀) ≫
      ((etaleModuleInverseImageAdj.{u, 0} Λ a).homEquiv _ _).symm
        ((etaleModuleBaseChangeTwist.{u, 0} Λ g a b w ψ).app L₃) =
    (((etaleModuleInverseImageAdj.{u, 0} Λ a).homEquiv _ _).symm
        ((etaleModuleBaseChangeTwist.{u, 0} Λ g a b w ψ).app L₁) ⊗ₘ
      ((etaleModuleInverseImageAdj.{u, 0} Λ a).homEquiv _ _).symm
        ((etaleModuleBaseChangeTwist.{u, 0} Λ g a b w ψ).app L₂)) ≫
      (μ (etaleModuleInverseImage.{u, 0} Λ g) L₁ L₂ ≫
        (etaleModuleInverseImage.{u, 0} Λ g).map μ₀) := by
  let τ := etaleModuleBaseChangeTwist.{u, 0} Λ g a b w ψ
  apply Adjunction.μ_comp_map_comp_homEquiv_symm
  have ht := NatTrans.IsMonoidal.tensor (τ := τ) L₁ L₂
  have hn := τ.naturality μ₀
  rw [comp_μ] at ht
  rw [Functor.map_comp]
  calc (τ.app L₁ ⊗ₘ τ.app L₂) ≫ μ (etaleModuleDirectImage.{u, 0} Λ a) _ _ ≫
        (etaleModuleDirectImage.{u, 0} Λ a).map (μ (etaleModuleInverseImage.{u, 0} Λ g) L₁ L₂) ≫
          (etaleModuleDirectImage.{u, 0} Λ a).map ((etaleModuleInverseImage.{u, 0} Λ g).map μ₀)
      = (μ (etaleModuleInverseImage.{u, 0} Λ g) L₁ L₂ ≫ τ.app (L₁ ⊗ L₂)) ≫
          (etaleModuleDirectImage.{u, 0} Λ a).map
            ((etaleModuleInverseImage.{u, 0} Λ g).map μ₀) := by
        rw [ht, Category.assoc, Category.assoc]
    _ = μ (etaleModuleInverseImage.{u, 0} Λ g) L₁ L₂ ≫
          (etaleModuleInverseImage.{u, 0} Λ g).map μ₀ ≫ τ.app L₃ := by
        rw [Category.assoc]
        exact congrArg (_ ≫ ·) hn.symm
    _ = _ := (Category.assoc _ _ _).symm

end Twist

section Frobenius

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The Frobenius base change twist is monoidal**: `L|_{Y_k̄} ⟶ π̄_*(L|_{Y_k̄})` is a monoidal
natural transformation. -/
instance isMonoidal_frobeniusBaseChangeTwist :
    NatTrans.IsMonoidal (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard) := by
  have : NatTrans.IsMonoidal
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} Λ)).hom :=
    isMonoidal_etaleSheafPushforwardComparison Λ _ _
  unfold frobeniusBaseChangeTwist
  infer_instance

/-- **The transposed Frobenius base change twist is compatible with pairings pulled back from
`Y`.** -/
theorem frobeniusBaseChangeTwist_twistAction_hσ {L₁ L₂ L₃ : EtaleModules.{u, 0} Λ Y.left}
    (μ₀ : L₁ ⊗ L₂ ⟶ L₃) :
    μ (etaleModuleInverseImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj L₁)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj L₂) ≫
      (etaleModuleInverseImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        (μ (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) L₁ L₂ ≫
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map μ₀) ≫
      ((etaleModuleInverseImageAdj.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).homEquiv _ _).symm
        ((frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app L₃) =
    (((etaleModuleInverseImageAdj.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).homEquiv _ _).symm
        ((frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app L₁) ⊗ₘ
      ((etaleModuleInverseImageAdj.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).homEquiv _ _).symm
        ((frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app L₂)) ≫
      (μ (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) L₁ L₂ ≫
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map μ₀) := by
  have : NatTrans.IsMonoidal
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{u + 1} Λ)).hom :=
    isMonoidal_etaleSheafPushforwardComparison Λ _ _
  exact etaleModuleBaseChangeTwist_twistAction_hσ Λ _ _ _ _ _ μ₀

end Frobenius

end Stacks.EtaleCohomology

end
