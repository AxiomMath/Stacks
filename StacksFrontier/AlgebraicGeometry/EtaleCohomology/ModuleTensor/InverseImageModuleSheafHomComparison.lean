module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.InverseImageRestrictScalarsMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizable

/-!
# Inverse image and the internal hom of étale sheaves of modules, across a change of rings

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. For étale sheaves of
`Λ`-modules `M`, `H` on `Y`, the inverse image of the evaluation `𝓗om(M, H) ⊗ M ⟶ H` corresponds,
under the internal hom property of `𝓗om(f⁻¹M, f⁻¹H)`
(`Stacks.ConstantSheaf.tensorHomBijective_moduleSheafHomEvaluation`), to the **comparison**
`f⁻¹ 𝓗om(M, H) ⟶ 𝓗om(f⁻¹M, f⁻¹H)`
(`Stacks.EtaleCohomology.etaleModuleInverseImageModuleSheafHomComparison`), for the monoidal
structure `Stacks.EtaleCohomology.etaleModuleInverseImageMonoidal` of the inverse image. It is
natural in `H`, and an isomorphism when `M` is dualizable
(`CategoryTheory.MonoidalCategory.isIso_of_tensorHomBijective_map`).

For a morphism of rings `ρ : Λ →+* Λ'`, a `Λ'`-module `M`, a `Λ`-module `M'` and
`p : M' ⟶ res_ρ M`, **precomposition with `p`** `res_ρ 𝓗om_{Λ'}(M, H) ⟶ 𝓗om_Λ(M', res_ρ H)`
(`Stacks.EtaleCohomology.etaleModuleRestrictScalarsHomPrecomp`) is characterized by its evaluation
`(α, m') ↦ α(p m')`. The comparison commutes with it
(`Stacks.EtaleCohomology.inverseImageRestrictScalars_comp_map_comparison_comp_homPrecomp`): this
is a consequence of the monoidality of `f⁻¹ ∘ res_ρ ≅ res_ρ ∘ f⁻¹`
(`Stacks.EtaleCohomology.μ_comp_map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars`).
For `M = μ_N`, `M' = μ_{ℓN}`, `p` the `ℓ`-th power map, it says that the identification
`i⁻¹ (H(-1)) ≅ (i⁻¹ H)(-1)` commutes with the transitions of the Tate twist, the step of the
tower form of cohomological purity of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageModuleSheafHomComparison`.
* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsHomPrecomp`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageModuleSheafHomComparison_spec`,
  `…_naturality`, `isIso_etaleModuleInverseImageModuleSheafHomComparison`.
* `Stacks.EtaleCohomology.inverseImageRestrictScalars_comp_map_comparison_comp_homPrecomp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Functor.LaxMonoidal Functor.OplaxMonoidal Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-! ### The evaluation is natural in the source -/

section Evaluation

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) (R : Type) [CommRing R]
  [(J.W (A := ModuleCat.{u + 1} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{u + 1} R)]

/-- The bilinear components of the evaluation are the pairing. -/
theorem tensorBilinear_moduleSheafHomEvaluation (F G : Sheaf J (ModuleCat.{u + 1} R)) (U : Cᵒᵖ)
    (α : (moduleSheafHom J R F G).obj.obj U) (x : F.obj.obj U) :
    Sheaf.tensorBilinear (moduleSheafHomEvaluation J R F G) U α x =
      moduleSheafHomPairing J R F G U α x :=
  sheafTensorBilinear_tensorDesc _ _ U α x

/-- **The evaluation is natural in both variables**:
`𝓗om(s, w) ⊗ F' ≫ ev = (𝓗om(F, G) ⊗ s) ≫ ev ≫ w`. -/
theorem moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation'
    {F F' G G' : Sheaf J (ModuleCat.{u + 1} R)} (s : F' ⟶ F) (w : G ⟶ G') :
    moduleSheafHomMap J R s w ▷ F' ≫ moduleSheafHomEvaluation J R F' G' =
      moduleSheafHom J R F G ◁ s ≫ moduleSheafHomEvaluation J R F G ≫ w := by
  refine sheafTensor_hom_ext fun U α x => ?_
  refine (sheafTensorBilinear_whiskerRight_comp _ _ U α x).trans ?_
  refine Eq.trans ?_ (sheafTensorBilinear_whiskerLeft_comp _ _ U α x).symm
  refine Eq.trans ?_ (sheafTensorBilinear_comp _ _ U α _).symm
  rw [tensorBilinear_moduleSheafHomEvaluation, tensorBilinear_moduleSheafHomEvaluation]
  rfl

end Evaluation

/-! ### The comparison `f⁻¹ 𝓗om(M, H) ⟶ 𝓗om(f⁻¹M, f⁻¹H)` -/

attribute [local instance] etaleModuleInverseImageMonoidal

section Comparison

variable {Λ : Type} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The comparison `f⁻¹ 𝓗om(M, H) ⟶ 𝓗om(f⁻¹M, f⁻¹H)`**: the morphism whose evaluation is the
inverse image of the evaluation, `μ ≫ f⁻¹(ev)`. -/
def etaleModuleInverseImageModuleSheafHomComparison (M H : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImage.{u, 0} Λ f).obj (moduleSheafHom Y.smallEtaleTopology Λ M H) ⟶
      moduleSheafHom X.smallEtaleTopology Λ ((etaleModuleInverseImage.{u, 0} Λ f).obj M)
        ((etaleModuleInverseImage.{u, 0} Λ f).obj H) :=
  Function.surjInv (tensorHomBijective_moduleSheafHomEvaluation X.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, 0} Λ f).obj M) ((etaleModuleInverseImage.{u, 0} Λ f).obj H)
      _).2
    (μ (etaleModuleInverseImage.{u, 0} Λ f) _ M ≫
      (etaleModuleInverseImage.{u, 0} Λ f).map
        (moduleSheafHomEvaluation Y.smallEtaleTopology Λ M H))

/-- The defining property of the comparison: its evaluation is `μ ≫ f⁻¹(ev)`. -/
@[reassoc]
theorem etaleModuleInverseImageModuleSheafHomComparison_spec (M H : EtaleModules.{u, 0} Λ Y) :
    etaleModuleInverseImageModuleSheafHomComparison f M H ▷
        (etaleModuleInverseImage.{u, 0} Λ f).obj M ≫
      moduleSheafHomEvaluation X.smallEtaleTopology Λ ((etaleModuleInverseImage.{u, 0} Λ f).obj M)
        ((etaleModuleInverseImage.{u, 0} Λ f).obj H) =
    μ (etaleModuleInverseImage.{u, 0} Λ f) _ M ≫
      (etaleModuleInverseImage.{u, 0} Λ f).map
        (moduleSheafHomEvaluation Y.smallEtaleTopology Λ M H) :=
  Function.surjInv_eq (tensorHomBijective_moduleSheafHomEvaluation X.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, 0} Λ f).obj M) ((etaleModuleInverseImage.{u, 0} Λ f).obj H)
      _).2 _

/-- **The comparison is natural in the target.** -/
theorem etaleModuleInverseImageModuleSheafHomComparison_naturality (M : EtaleModules.{u, 0} Λ Y)
    {H H' : EtaleModules.{u, 0} Λ Y} (w : H ⟶ H') :
    (etaleModuleInverseImage.{u, 0} Λ f).map (moduleSheafHomMap Y.smallEtaleTopology Λ (𝟙 M) w) ≫
        etaleModuleInverseImageModuleSheafHomComparison f M H' =
      etaleModuleInverseImageModuleSheafHomComparison f M H ≫
        moduleSheafHomMap X.smallEtaleTopology Λ (𝟙 _)
          ((etaleModuleInverseImage.{u, 0} Λ f).map w) := by
  refine (tensorHomBijective_moduleSheafHomEvaluation X.smallEtaleTopology Λ
    ((etaleModuleInverseImage.{u, 0} Λ f).obj M) ((etaleModuleInverseImage.{u, 0} Λ f).obj H')
    _).injective ?_
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    etaleModuleInverseImageModuleSheafHomComparison_spec,
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation,
    reassoc_of% (etaleModuleInverseImageModuleSheafHomComparison_spec f M H),
    μ_natural_left_assoc, ← Functor.map_comp, ← Functor.map_comp,
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation]

/-- **The comparison is an isomorphism when `M` is dualizable**: the inverse image is monoidal,
so it carries the internal hom `𝓗om(M, H)` to an internal hom from `f⁻¹M` to `f⁻¹H`. -/
theorem isIso_etaleModuleInverseImageModuleSheafHomComparison (M M' : EtaleModules.{u, 0} Λ Y)
    [ExactPairing M M'] (H : EtaleModules.{u, 0} Λ Y) :
    IsIso (etaleModuleInverseImageModuleSheafHomComparison f M H) :=
  isIso_of_tensorHomBijective_map (etaleModuleInverseImage.{u, 0} Λ f) M M'
    (tensorHomBijective_moduleSheafHomEvaluation Y.smallEtaleTopology Λ M H)
    (tensorHomBijective_moduleSheafHomEvaluation X.smallEtaleTopology Λ _ _) _
    (etaleModuleInverseImageModuleSheafHomComparison_spec f M H)

end Comparison

/-! ### Precomposition across a change of rings -/

section Precomp

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {Y : Scheme.{u}}

/-- The lax structure of restriction of scalars commutes with whiskering on the right. -/
@[reassoc]
theorem whiskerRight_comp_etaleModuleRestrictScalarsTensorHom {A A' : EtaleModules.{u, 0} Λ' Y}
    (a : A ⟶ A') (B : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleRestrictScalars ρ Y).map a ▷ (etaleModuleRestrictScalars ρ Y).obj B ≫
        etaleModuleRestrictScalarsTensorHom ρ A' B =
      etaleModuleRestrictScalarsTensorHom ρ A B ≫ (etaleModuleRestrictScalars ρ Y).map (a ▷ B) := by
  have h := tensorHom_comp_etaleModuleRestrictScalarsTensorHom ρ a (𝟙 B)
  rwa [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h

/-- The lax structure of restriction of scalars commutes with whiskering on the left. -/
@[reassoc]
theorem whiskerLeft_comp_etaleModuleRestrictScalarsTensorHom (A : EtaleModules.{u, 0} Λ' Y)
    {B B' : EtaleModules.{u, 0} Λ' Y} (b : B ⟶ B') :
    (etaleModuleRestrictScalars ρ Y).obj A ◁ (etaleModuleRestrictScalars ρ Y).map b ≫
        etaleModuleRestrictScalarsTensorHom ρ A B' =
      etaleModuleRestrictScalarsTensorHom ρ A B ≫ (etaleModuleRestrictScalars ρ Y).map (A ◁ b) := by
  have h := tensorHom_comp_etaleModuleRestrictScalarsTensorHom ρ (𝟙 A) b
  rwa [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h

/-- **Precomposition with `p : M' ⟶ res_ρ M`**, `res_ρ 𝓗om_{Λ'}(M, H) ⟶ 𝓗om_Λ(M', res_ρ H)`:
the morphism whose evaluation is `(α, m') ↦ α(p m')`. -/
def etaleModuleRestrictScalarsHomPrecomp {M : EtaleModules.{u, 0} Λ' Y}
    {M' : EtaleModules.{u, 0} Λ Y} (p : M' ⟶ (etaleModuleRestrictScalars ρ Y).obj M)
    (H : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleRestrictScalars ρ Y).obj (moduleSheafHom Y.smallEtaleTopology Λ' M H) ⟶
      moduleSheafHom Y.smallEtaleTopology Λ M' ((etaleModuleRestrictScalars ρ Y).obj H) :=
  Function.surjInv (tensorHomBijective_moduleSheafHomEvaluation Y.smallEtaleTopology Λ M'
      ((etaleModuleRestrictScalars ρ Y).obj H) _).2
    (_ ◁ p ≫ etaleModuleRestrictScalarsTensorHom ρ _ M ≫
      (etaleModuleRestrictScalars ρ Y).map (moduleSheafHomEvaluation Y.smallEtaleTopology Λ' M H))

/-- The defining property of precomposition: its evaluation is `(α, m') ↦ α(p m')`. -/
@[reassoc]
theorem etaleModuleRestrictScalarsHomPrecomp_spec {M : EtaleModules.{u, 0} Λ' Y}
    {M' : EtaleModules.{u, 0} Λ Y} (p : M' ⟶ (etaleModuleRestrictScalars ρ Y).obj M)
    (H : EtaleModules.{u, 0} Λ' Y) :
    etaleModuleRestrictScalarsHomPrecomp ρ p H ▷ M' ≫
        moduleSheafHomEvaluation Y.smallEtaleTopology Λ M'
          ((etaleModuleRestrictScalars ρ Y).obj H) =
      _ ◁ p ≫ etaleModuleRestrictScalarsTensorHom ρ _ M ≫
        (etaleModuleRestrictScalars ρ Y).map
          (moduleSheafHomEvaluation Y.smallEtaleTopology Λ' M H) :=
  Function.surjInv_eq (tensorHomBijective_moduleSheafHomEvaluation Y.smallEtaleTopology Λ M'
      ((etaleModuleRestrictScalars ρ Y).obj H) _).2 _

end Precomp

/-! ### The comparison commutes with precomposition across a change of rings -/

section Cross

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The comparison `f⁻¹ 𝓗om(M, H) ⟶ 𝓗om(f⁻¹M, f⁻¹H)` commutes with precomposition across a
change of rings.** Let `p : M' ⟶ res_ρ M` on `Y`, `p_X : N' ⟶ res_ρ N` on `X`, and
`s : N ⟶ f⁻¹M`, `s' : N' ⟶ f⁻¹M'` compatible with them (`s' ≫ f⁻¹p ≫ κ = p_X ≫ res_ρ s`). Then
`κ ≫ res_ρ(c ≫ 𝓗om(s, 1)) ≫ (p_X)^* = f⁻¹(p^*) ≫ c ≫ 𝓗om(s', κ)`, as morphisms
`f⁻¹ res_ρ 𝓗om(M, H) ⟶ 𝓗om(N', res_ρ f⁻¹H)`. -/
theorem inverseImageRestrictScalars_comp_map_comparison_comp_homPrecomp
    {M H : EtaleModules.{u, 0} Λ' Y} {M' : EtaleModules.{u, 0} Λ Y}
    (p : M' ⟶ (etaleModuleRestrictScalars ρ Y).obj M)
    {N : EtaleModules.{u, 0} Λ' X} {N' : EtaleModules.{u, 0} Λ X}
    (pX : N' ⟶ (etaleModuleRestrictScalars ρ X).obj N)
    (s : N ⟶ (etaleModuleInverseImage.{u, 0} Λ' f).obj M)
    (s' : N' ⟶ (etaleModuleInverseImage.{u, 0} Λ f).obj M')
    (hs : s' ≫ (etaleModuleInverseImage.{u, 0} Λ f).map p ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app M =
      pX ≫ (etaleModuleRestrictScalars ρ X).map s) :
    (etaleModuleInverseImageRestrictScalars ρ f).hom.app
          (moduleSheafHom Y.smallEtaleTopology Λ' M H) ≫
        (etaleModuleRestrictScalars ρ X).map
          (etaleModuleInverseImageModuleSheafHomComparison f M H ≫
            moduleSheafHomMap X.smallEtaleTopology Λ' s (𝟙 _)) ≫
        etaleModuleRestrictScalarsHomPrecomp ρ pX ((etaleModuleInverseImage.{u, 0} Λ' f).obj H) =
      (etaleModuleInverseImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsHomPrecomp ρ p H) ≫
        etaleModuleInverseImageModuleSheafHomComparison f M'
          ((etaleModuleRestrictScalars ρ Y).obj H) ≫
        moduleSheafHomMap X.smallEtaleTopology Λ s'
          ((etaleModuleInverseImageRestrictScalars ρ f).hom.app H) := by
  refine (tensorHomBijective_moduleSheafHomEvaluation X.smallEtaleTopology Λ N'
    ((etaleModuleRestrictScalars ρ X).obj ((etaleModuleInverseImage.{u, 0} Λ' f).obj H))
      _).injective ?_
  have hκ := (etaleModuleInverseImageRestrictScalars ρ f).hom.naturality
    (moduleSheafHomEvaluation Y.smallEtaleTopology Λ' M H)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hκ
  have hmon := μ_comp_map_restrictScalarsTensorHom_comp_inverseImageRestrictScalars ρ f
    (moduleSheafHom Y.smallEtaleTopology Λ' M H) M
  -- both sides are `_ ◁ s' ≫ _ ◁ f⁻¹p ≫ μ ≫ f⁻¹(res tensor) ≫ f⁻¹(res ev) ≫ κ`
  refine Eq.trans (calc
      _ = _ ◁ pX ≫ (etaleModuleInverseImageRestrictScalars ρ f).hom.app
              (moduleSheafHom Y.smallEtaleTopology Λ' M H) ▷ _ ≫
            etaleModuleRestrictScalarsTensorHom ρ _ N ≫ (etaleModuleRestrictScalars ρ X).map
              (_ ◁ s ≫ μ (etaleModuleInverseImage.{u, 0} Λ' f) _ M ≫
                (etaleModuleInverseImage.{u, 0} Λ' f).map
                  (moduleSheafHomEvaluation Y.smallEtaleTopology Λ' M H)) := by
            conv_lhs => rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
              etaleModuleRestrictScalarsHomPrecomp_spec, ← whisker_exchange_assoc,
              ← whisker_exchange_assoc, whiskerRight_comp_etaleModuleRestrictScalarsTensorHom_assoc,
              ← Functor.map_comp, comp_whiskerRight, Category.assoc,
              moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation', Category.comp_id,
              ← whisker_exchange_assoc, etaleModuleInverseImageModuleSheafHomComparison_spec]
      _ = _ ◁ (pX ≫ (etaleModuleRestrictScalars ρ X).map s) ≫
            (etaleModuleInverseImageRestrictScalars ρ f).hom.app
              (moduleSheafHom Y.smallEtaleTopology Λ' M H) ▷ _ ≫
            etaleModuleRestrictScalarsTensorHom ρ _ _ ≫ (etaleModuleRestrictScalars ρ X).map
              (μ (etaleModuleInverseImage.{u, 0} Λ' f) _ M) ≫
            (etaleModuleRestrictScalars ρ X).map ((etaleModuleInverseImage.{u, 0} Λ' f).map
                  (moduleSheafHomEvaluation Y.smallEtaleTopology Λ' M H)) := by
            dsimp only [Functor.comp_obj]
            conv_lhs => rw [Functor.map_comp, Functor.map_comp,
              ← whiskerLeft_comp_etaleModuleRestrictScalarsTensorHom_assoc,
              ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
      _ = _ ◁ s' ≫ _ ◁ (etaleModuleInverseImage.{u, 0} Λ f).map p ≫
            μ (etaleModuleInverseImage.{u, 0} Λ f) _ _ ≫
            (etaleModuleInverseImage.{u, 0} Λ f).map (etaleModuleRestrictScalarsTensorHom ρ _ M) ≫
            (etaleModuleInverseImage.{u, 0} Λ f).map ((etaleModuleRestrictScalars ρ Y).map
              (moduleSheafHomEvaluation Y.smallEtaleTopology Λ' M H)) ≫
            (etaleModuleInverseImageRestrictScalars ρ f).hom.app H := by
            dsimp only [Functor.comp_obj]
            conv_lhs => rw [← hs, MonoidalCategory.whiskerLeft_comp_assoc,
              MonoidalCategory.whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
              reassoc_of% hmon.symm, ← hκ]) ?_
  conv_rhs => rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation', ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, etaleModuleInverseImageModuleSheafHomComparison_spec_assoc,
    μ_natural_left_assoc, ← Functor.map_comp_assoc, etaleModuleRestrictScalarsHomPrecomp_spec,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← μ_natural_right_assoc]
  rfl

end Cross

end Stacks.EtaleCohomology

end
