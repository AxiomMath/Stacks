module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleUnitStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningCubeComparison
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleObstructionDescentNaturality

/-!
# The transposed comparison of ideals of a morphism of thickenings is `j^♯` on the ideals

Consider morphisms of algebraic spaces `j : W ⟶ X`, `f₂ : W ⟶ T₂`, `f₁ : X ⟶ T₁`, `γ : T₂ ⟶ T₁`
with `j ≫ f₁ = k = f₂ ≫ γ`, sheaves of modules `N_k` with maps `ι_k : N_k ⟶ 𝒪_{T_k}` and a map
`κ : N₁ ⟶ γ_*N₂` which is `γ^♯` on the maps into the structure sheaves. The map
`f₁^*N₁ ⟶ j_*f₂^*N₂` adjoint to `κ` followed by `γ_*` of the unit of `f₂` and
`γ_*f₂_* ≅ k_* ≅ f₁_*j_*` (Stacks 03LU), `Deformation.ToposThickening.cubeTopTranspose`, is `j^♯`
on the maps `f_k^*N_k ⟶ f_k^*𝒪 ⟶ 𝒪`
(`AlgebraicGeometry.Space.homEquiv_symm_comp_map_pullbackUnitStructureMap`).

The statement is first proved for any two adjunctions
(`CategoryTheory.Adjunction.homEquiv_symm_comp_map_comp_of_unit_maps`), then instantiated for
variable algebraic spaces. In Stacks 08WA (second proof, functoriality of the obstruction
classes of `Coh_{X/B}`) this is the comparison of the ideals of `X_{T'₂} ⊂ X_{T'₁}`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace CategoryTheory.Adjunction

/-- **The transpose of `κ ≫ R_γ(η) ≫ C'` is compatible with maps into the units**, for adjunctions
`L₁ ⊣ R₁`, `L₂ ⊣ R₂`, two comparisons `M₁ : R₂ ⋙ R_γ ≅ K`, `M₂ : R_j ⋙ R₁ ≅ K` and unit maps
`s` whose composites agree through `M₁` and `M₂`. -/
theorem homEquiv_symm_comp_map_comp_of_unit_maps {C₁ C₂ CX CW : Type*} [Category* C₁]
    [Category* C₂] [Category* CX] [Category* CW] {L₁ : C₁ ⥤ CX} {R₁ : CX ⥤ C₁}
    {L₂ : C₂ ⥤ CW} {R₂ : CW ⥤ C₂} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (Rγ : C₂ ⥤ C₁) (Rj : CW ⥤ CX)
    {K : CW ⥤ C₁} (M₁ : R₂ ⋙ Rγ ≅ K) (M₂ : Rj ⋙ R₁ ≅ K) {u₁ : C₁} {u₂ : C₂} {uX : CX} {uW : CW}
    (sγ : u₁ ⟶ Rγ.obj u₂) (s₂ : u₂ ⟶ R₂.obj uW) (s₁ : u₁ ⟶ R₁.obj uX) (sj : uX ⟶ Rj.obj uW)
    (s : u₁ ⟶ K.obj uW) (hs₁ : sγ ≫ Rγ.map s₂ ≫ M₁.hom.app uW = s)
    (hs₂ : s₁ ≫ R₁.map sj ≫ M₂.hom.app uW = s)
    {N₁ : C₁} {N₂ : C₂} (ι₁ : N₁ ⟶ u₁) (ι₂ : N₂ ⟶ u₂) (κ : N₁ ⟶ Rγ.obj N₂)
    (hκ : κ ≫ Rγ.map ι₂ = ι₁ ≫ sγ) :
    Deformation.ToposThickening.cubeTopTranspose a₁ a₂ M₂ M₁ κ ≫
        Rj.map (L₂.map ι₂ ≫ (a₂.homEquiv _ _).symm s₂) =
      L₁.map ι₁ ≫ (a₁.homEquiv _ _).symm s₁ ≫ sj := by
  unfold Deformation.ToposThickening.cubeTopTranspose
  set p₁ := (a₁.homEquiv _ _).symm s₁
  set p₂ := (a₂.homEquiv _ _).symm s₂
  have hp₁ : a₁.homEquiv _ _ p₁ = s₁ := Equiv.apply_symm_apply _ _
  have hp₂ : a₂.homEquiv _ _ p₂ = s₂ := Equiv.apply_symm_apply _ _
  refine (a₁.homEquiv _ _).injective ?_
  have hη : a₂.unit.app N₂ ≫ R₂.map (L₂.map ι₂ ≫ p₂) = ι₂ ≫ s₂ := by
    rw [← hp₂, ← a₂.homEquiv_naturality_left, a₂.homEquiv_unit]
  have hn := (M₁ ≪≫ M₂.symm).hom.naturality (L₂.map ι₂ ≫ p₂)
  simp only [Functor.comp_map] at hn
  rw [a₁.homEquiv_naturality_right, Equiv.apply_symm_apply, a₁.homEquiv_naturality_left,
    a₁.homEquiv_naturality_right, hp₁, Category.assoc, Category.assoc, ← hn,
    ← Functor.map_comp_assoc, hη]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hκ]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [reassoc_of% hs₁, ← hs₂]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact congrArg (ι₁ ≫ s₁ ≫ ·) (Category.comp_id _)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

-- Without these recorded instances, the instantiation of the abstract lemma below hits the
-- 200000-heartbeat isDefEq limit (82k unfoldings of `smallEtaleRingedTopos`).
attribute [local instance] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {W X T₂ T₁ : AlgebraicSpaces B S hS}

/-- **The transposed comparison `f₁^*N₁ ⟶ j_*f₂^*N₂` built from `κ : N₁ ⟶ γ_*N₂` is `j^♯` on the
maps into the structure sheaves**, when `κ` is `γ^♯` on the maps `N_k ⟶ 𝒪_{T_k}`. -/
theorem homEquiv_symm_comp_map_pullbackUnitStructureMap
    (j : W ⟶ X) (f₂ : W ⟶ T₂) (f₁ : X ⟶ T₁) (γ : T₂ ⟶ T₁) (k : W ⟶ T₁)
    (hk : j ≫ f₁ = k) (hk' : f₂ ≫ γ = k)
    {N₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS T₁).O)}
    {N₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS T₂).O)}
    (ι₁ : N₁ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS T₁).O))
    (ι₂ : N₂ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS T₂).O))
    (κ : N₁ ⟶ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.obj N₂)
    (hκ : κ ≫ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.map ι₂ =
      ι₁ ≫ RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS γ)) :
    Deformation.ToposThickening.cubeTopTranspose (af₁ := spaceModuleAdj f₁)
        (af₂ := spaceModuleAdj f₂) (d₁ := modulePushforwardCompIsoOfEq j f₁ k hk)
        (d₂ := modulePushforwardCompIsoOfEq f₂ γ k hk') κ ≫
      (smallEtaleRingedToposHom B S hS j).pushforwardModules.map
        (((smallEtaleRingedToposHom B S hS f₂).toModulesHom.pullbackModules).map ι₂ ≫
          RingedToposHom.pullbackUnitStructureMap (smallEtaleRingedToposHom B S hS f₂)) =
    ((smallEtaleRingedToposHom B S hS f₁).toModulesHom.pullbackModules).map ι₁ ≫
      RingedToposHom.pullbackUnitStructureMap (smallEtaleRingedToposHom B S hS f₁) ≫
      RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS j) := by
  have key := Adjunction.homEquiv_symm_comp_map_comp_of_unit_maps
    (spaceModuleAdj f₁) (spaceModuleAdj f₂)
    (smallEtaleRingedToposHom B S hS γ).pushforwardModules
    (smallEtaleRingedToposHom B S hS j).pushforwardModules
    (modulePushforwardCompIsoOfEq f₂ γ k hk') (modulePushforwardCompIsoOfEq j f₁ k hk)
    (RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS γ))
    (RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS f₂))
    (RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS f₁))
    (RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS j))
    (RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS k))
    (unitStructureMap_comp_map_unitStructureMap_comp_modulePushforwardCompIsoOfEq f₂ γ k hk')
    (unitStructureMap_comp_map_unitStructureMap_comp_modulePushforwardCompIsoOfEq j f₁ k hk)
    ι₁ ι₂ κ hκ
  exact key

end AlgebraicGeometry.Space

end
