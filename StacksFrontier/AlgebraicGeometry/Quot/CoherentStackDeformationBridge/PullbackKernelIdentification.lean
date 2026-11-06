module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackExtensionMap

/-!
# Kernel maps along morphisms of thickenings

For a morphism `D` of first-order thickenings `i₁ : X → Y₁`, `i₂ : X → Y₂` of ringed topoi with
square-zero ideals `ℐ₁`, `ℐ₂`, and a map `θ : F₁ ⟶ Ψ₀F₂` of modules, this file defines the induced
map `ℐ₁ ⊗ F₁ ⟶ Ψ₀(ℐ₂ ⊗ F₂)` of kernels and its restriction of scalars, and identifies the map of
kernels of a morphism of split thickenings of algebraic spaces through the retractions.

## Main definitions

* `Deformation.ToposThickening.ThickeningTargetMorphism.idealTensorMapOver`: the map
  `ℐ₁ ⊗ F₁ ⟶ Ψ₀(ℐ₂ ⊗ F₂)` over `θ`.
* `Deformation.ToposThickening.ThickeningTargetMorphism.restrictIdealTensorMapOver`: the map
  `i₁^♯(ℐ₁ ⊗ F₁) ⟶ j_* i₂^♯(ℐ₂ ⊗ F₂)` over `θ`.

## Main results

* `Deformation.ToposThickening.ThickeningTargetMorphism.f_comp_eq_restrictIdealTensorMapOver_comp`:
  a map of extensions over `θ` restricts on kernels to `restrictIdealTensorMapOver`.
* `AlgebraicGeometry.Space.pushforwardModules_map_restrictIso_inv_comp_eq_of_comp_eq`: the kernel
  identifications along a morphism of split thickenings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open AlgebraicGeometry (RingedTopos RingedToposHom)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- At a lower priority, instance search for `(smallEtaleRingedTopos X).J.HasSheafCompose
-- (forget RingCat)` exceeds its heartbeat limit.
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

universe e u

namespace Deformation.ToposThickening.ThickeningTargetMorphism

section IdealTensorMapOver

universe vX uX vY₁ uY₁ vY₂ uY₂ wM

variable {X : RingedTopos.{vX, uX, wM}} {Y₁ : RingedTopos.{vY₁, uY₁, wM}}
  {Y₂ : RingedTopos.{vY₂, uY₂, wM}}
  [X.J.HasSheafCompose (forget RingCat.{wM})] [Y₁.J.HasSheafCompose (forget RingCat.{wM})]
  [Y₂.J.HasSheafCompose (forget RingCat.{wM})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wM} RingCat.{wM})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{wM} RingCat.{wM})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{wM} RingCat.{wM})]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{wM})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{wM})]
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{wM}] [HasWeakSheafify Y₁.J AddCommGrpCat.{wM}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{wM}] [HasWeakSheafify Y₂.J AddCommGrpCat.{wM}]
  [HasSheafify Y₁.J AddCommGrpCat.{wM}] [HasSheafify Y₂.J AddCommGrpCat.{wM}]

/-- **The map `ℐ₁ ⊗ F₁ ⟶ Ψ₀(ℐ₂ ⊗ F₂)` over `θ : F₁ ⟶ Ψ₀F₂`**: `ℐ₁ ⊗ θ` followed by the comparison
`ℐ₁ ⊗ Ψ₀F₂ ⟶ Ψ₀(ℐ₂ ⊗ F₂)` of the map of square-zero ideals
(`Deformation.ToposThickening.ThickeningTargetMorphism.idealTensorMap`). -/
noncomputable abbrev idealTensorMapOver
    {F₁ : SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))}
    {F₂ : SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    (θ : F₁ ⟶ D.basePushforward.obj F₂) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I ⟶
      D.basePushforward.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I) :=
  @CategoryStruct.comp _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).obj F₁)
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).obj
      (D.basePushforward.obj F₂))
    (D.basePushforward.obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).obj
      hi₂.I).obj F₂))
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map θ)
    (D.idealTensorMap hi₁ hi₂ F₂)

/-- **The map `i₁^♯(ℐ₁ ⊗ F₁) ⟶ j_* i₂^♯(ℐ₂ ⊗ F₂)` over `θ : F₁ ⟶ Ψ₀F₂`**: restriction of scalars of
`Deformation.ToposThickening.ThickeningTargetMorphism.idealTensorMapOver` followed by
`Ψ₀N ≅ j_*N`. -/
noncomputable abbrev restrictIdealTensorMapOver
    {F₁ : SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))}
    {F₂ : SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    (θ : F₁ ⟶ D.basePushforward.obj F₂) :
    @Quiver.Hom (SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)) _
      ((structureRestrict i₁).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I))
      (D.j.pushforwardModules.obj ((structureRestrict i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I))) :=
  @CategoryStruct.comp (SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)) _
    ((structureRestrict i₁).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I))
    ((structureRestrict i₁).obj (D.basePushforward.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I)))
    (D.j.pushforwardModules.obj ((structureRestrict i₂).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I)))
    ((structureRestrict i₁).map (D.idealTensorMapOver hi₁ hi₂ θ))
    (D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj
      hi₂.I)).inv

/-- `Deformation.ToposThickening.ThickeningTargetMorphism.f_comp_eq_idealTensorMap_comp` with the
map of kernels
`Deformation.ToposThickening.ThickeningTargetMorphism.restrictIdealTensorMapOver`. -/
theorem f_comp_eq_restrictIdealTensorMapOver_comp
    {F₁ : SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))}
    {F₂ : SheafOfModules.{wM} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    (θ : F₁ ⟶ D.basePushforward.obj F₂)
    (E₁ : Abelian.YonedaExtension ((structureRestrict i₁).obj F₁)
      ((structureRestrict i₁).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I)) 0)
    (hE₁ : (extensionActionMap hi₁ E₁).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I))
    (E₂ : Abelian.YonedaExtension ((structureRestrict i₂).obj F₂)
      ((structureRestrict i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I)) 0)
    (hE₂ : (extensionActionMap hi₂ E₂).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I))
    (u : E₁.Z.left ⟶ D.j.pushforwardModules.obj E₂.Z.left)
    (hu : u ≫ D.j.pushforwardModules.map E₂.g ≫ (D.restrictIso F₂).hom =
      E₁.g ≫ (structureRestrict i₁).map θ) :
    E₁.f ≫ u = D.restrictIdealTensorMapOver hi₁ hi₂ θ ≫ D.j.pushforwardModules.map E₂.f :=
  (D.f_comp_eq_idealTensorMap_comp hi₁ hi₂ θ E₁ hE₁ E₂ hE₂ u hu).trans (Category.assoc _ _ _).symm

end IdealTensorMapOver

end Deformation.ToposThickening.ThickeningTargetMorphism

namespace AlgebraicGeometry.Space

/-- The kernel map of a morphism of split thickenings read through the retractions, in an
arbitrary diagram of categories: if `kk ≫ Ψ(x₂) ≫ E = x₁ ≫ T_k(φ)`, then `c_*` of `kk` followed by
the comparisons `r`, `C` is `x₁` followed by `R_k`, `φ`, `R_a⁻¹` and `x₂⁻¹`. -/
private theorem map_comp_comp_eq_of_comp_map_comp_eq {𝒦 𝒜 𝒳 𝒴₁ 𝒴₂ : Type*} [Category 𝒦]
    [Category 𝒜] [Category 𝒳] [Category 𝒴₁] [Category 𝒴₂]
    (Tk : 𝒳 ⥤ 𝒦) (Ta : 𝒳 ⥤ 𝒜) (Ψ : 𝒜 ⥤ 𝒦) (resk : 𝒦 ⥤ 𝒴₁) (resa : 𝒜 ⥤ 𝒴₂)
    (bst : 𝒴₂ ⥤ 𝒴₁) (cst : 𝒴₁ ⥤ 𝒳) (c2st : 𝒴₂ ⥤ 𝒳) {M₁ M₂ : 𝒳} (φ : M₁ ⟶ M₂) {K₁ : 𝒦}
    {K₂ : 𝒜} (x₁ : K₁ ⟶ Tk.obj M₁) (x₂ : K₂ ⟶ Ta.obj M₂) (x₂' : Ta.obj M₂ ⟶ K₂)
    (hx₂ : x₂ ≫ x₂' = 𝟙 K₂) (Eh : Ψ.obj (Ta.obj M₂) ⟶ Tk.obj M₂)
    (Ei : Tk.obj M₂ ⟶ Ψ.obj (Ta.obj M₂)) (hE : Eh ≫ Ei = 𝟙 _) (kk : K₁ ⟶ Ψ.obj K₂)
    (hkey : kk ≫ Ψ.map x₂ ≫ Eh = x₁ ≫ Tk.map φ)
    (rI₁ : resk.obj (Ψ.obj (Ta.obj M₂)) ⟶ bst.obj (resa.obj (Ta.obj M₂)))
    (rI₂ : resk.obj (Ψ.obj K₂) ⟶ bst.obj (resa.obj K₂))
    (hrI : resk.map (Ψ.map x₂') ≫ rI₂ = rI₁ ≫ bst.map (resa.map x₂'))
    (C₁ : cst.obj (bst.obj (resa.obj (Ta.obj M₂))) ⟶ c2st.obj (resa.obj (Ta.obj M₂)))
    (C₂ : cst.obj (bst.obj (resa.obj K₂)) ⟶ c2st.obj (resa.obj K₂))
    (hC : cst.map (bst.map (resa.map x₂')) ≫ C₂ = C₁ ≫ c2st.map (resa.map x₂'))
    (Rk₁ : cst.obj (resk.obj (Tk.obj M₁)) ⟶ M₁) (Rk₂ : cst.obj (resk.obj (Tk.obj M₂)) ⟶ M₂)
    (hRk : cst.map (resk.map (Tk.map φ)) ≫ Rk₂ = Rk₁ ≫ φ)
    (Ra : M₂ ⟶ c2st.obj (resa.obj (Ta.obj M₂))) (Ra' : c2st.obj (resa.obj (Ta.obj M₂)) ⟶ M₂)
    (hRa : Ra' ≫ Ra = 𝟙 _) (hR : cst.map (resk.map Ei ≫ rI₁) ≫ C₁ ≫ Ra' = Rk₂) :
    cst.map (resk.map kk ≫ rI₂) ≫ C₂ =
      cst.map (resk.map x₁) ≫ Rk₁ ≫ φ ≫ Ra ≫ c2st.map (resa.map x₂') := by
  have hk : kk = x₁ ≫ Tk.map φ ≫ Ei ≫ Ψ.map x₂' := by
    rw [← reassoc_of% hkey, reassoc_of% hE, ← Ψ.map_comp, hx₂, Ψ.map_id, Category.comp_id]
  have hR' : cst.map (resk.map Ei) ≫ cst.map rI₁ ≫ C₁ = Rk₂ ≫ Ra := by
    rw [← hR]
    simp only [Functor.map_comp, Category.assoc, hRa, Category.comp_id]
  have e₁ : resk.map (x₁ ≫ Tk.map φ ≫ Ei ≫ Ψ.map x₂') ≫ rI₂ =
      resk.map x₁ ≫ resk.map (Tk.map φ) ≫ resk.map Ei ≫ rI₁ ≫ bst.map (resa.map x₂') := by
    simp only [Functor.map_comp, Category.assoc, hrI]
  subst hk
  rw [e₁]
  simp only [Functor.map_comp, Category.assoc, hC, reassoc_of% hR', reassoc_of% hRk]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Naturality

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS}

/-- The naturality of `c_* k_* ≅ 𝟭`, with `k_*` read as `i^♯`-restriction of `k_*` over
`k_*𝒪`. -/
private theorem pushforwardModulesRetractionIso_hom_naturality_thickened {k : X₀ ⟶ X₁}
    (c : X₁ ⟶ X₀) (h₁ : k ≫ c = 𝟙 X₀)
    {M₁ M₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)} (φ : M₁ ⟶ M₂) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).map φ)) ≫
      (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M₂ =
    (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M₁ ≫ φ :=
  (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.naturality φ

/-- The naturality of `Ψ₀N ≅ j_*N` (inverse direction), with `j_*` the direct image along `b`. -/
private theorem restrictIso_inv_naturality_smallEtale (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁)
    {k : X₀ ⟶ X₁} (e₁ : a ≫ b = k)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)}
    {K₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (baseRing.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)))}
    (x : (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M ⟶ K₂) :
    (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickeningTargetOfEq a b k e₁).basePushforward.map x) ≫
      ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso K₂).inv =
    ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv ≫
      (smallEtaleRingedToposHom B S hS b).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).map x) :=
  (smallEtaleThickeningTargetOfEq a b k e₁).restrictIso_inv_naturality x

-- The kernel's check of this naturality exceeds the default heartbeats.
set_option maxHeartbeats 1000000 in
/-- The naturality of `c_* b_* ≅ c₂_*` at a map restricted from `a_*𝒪`-modules. -/
private theorem pushforwardModulesCompAt_trans_eqToIso_hom_naturality_restrict (a : X₀ ⟶ X₂)
    (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀) {c₂ : X₂ ⟶ X₀} (e₂ : b ≫ c = c₂)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)}
    {K₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (baseRing.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)))}
    (x : (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M ⟶ K₂) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((smallEtaleRingedToposHom B S hS b).pushforwardModules.map
          ((structureRestrict (smallEtaleRingedToposHom B S hS a)).map x)) ≫
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj K₂) =
    (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
        ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
      (smallEtaleRingedToposHom B S hS c₂).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).map x) :=
  (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.naturality
      ((structureRestrict (smallEtaleRingedToposHom B S hS a)).map x)

end Naturality

/-- **The kernel identifications along a morphism of split thickenings**: for `a ≫ b = k`,
`b ≫ c = c₂`, `k ≫ c = 𝟙`, `a ≫ c₂ = 𝟙`, modules `K₁ ≅ k_*M₁`, `K₂ ≅ a_*M₂` and a map
`κ : K₁ ⟶ Ψ₀K₂` which is `φ : M₁ ⟶ M₂` through `Ψ₀ ∘ a_* ≅ k_*`, the map `c_*K₁ ⟶ c₂_*K₂` given
by `κ`, `Ψ₀K₂ ≅ j_*K₂` and `c_*b_* ≅ c₂_*` is `φ` read through the identifications along `k` and
`a`. -/
theorem pushforwardModules_map_restrictIso_inv_comp_eq_of_comp_eq
    {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀) {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k)
    (e₂ : b ≫ c = c₂) (h₁ : k ≫ c = 𝟙 X₀) (h₂ : a ≫ c₂ = 𝟙 X₀)
    {M₁ M₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)} (φ : M₁ ⟶ M₂)
    {K₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (baseRing.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS k)))}
    {K₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (baseRing.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)))}
    (x₁ : K₁ ≅ (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj M₁)
    (x₂ : K₂ ≅ (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M₂)
    (kk : K₁ ⟶ (smallEtaleThickeningTargetOfEq a b k e₁).basePushforward.obj K₂)
    (hkey : kk ≫ (smallEtaleThickeningTargetOfEq a b k e₁).basePushforward.map x₂.hom ≫
        (smallEtaleThickenedModulesCompIso a b k e₁).hom.app M₂ =
      x₁.hom ≫ (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).map φ) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map kk ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso K₂).inv) ≫
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj K₂) =
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map x₁.hom) ≫
      (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M₁ ≫ φ ≫
      (CoherentSituation.pushforwardModulesRetractionIso a c₂ h₂).inv.app M₂ ≫
      (smallEtaleRingedToposHom B S hS c₂).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).map x₂.inv) :=
  map_comp_comp_eq_of_comp_map_comp_eq
    (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k))
    (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a))
    (smallEtaleThickeningTargetOfEq a b k e₁).basePushforward
    (structureRestrict (smallEtaleRingedToposHom B S hS k))
    (structureRestrict (smallEtaleRingedToposHom B S hS a))
    (smallEtaleRingedToposHom B S hS b).pushforwardModules
    (smallEtaleRingedToposHom B S hS c).pushforwardModules
    (smallEtaleRingedToposHom B S hS c₂).pushforwardModules φ x₁.hom x₂.hom x₂.inv x₂.hom_inv_id
    ((smallEtaleThickenedModulesCompIso a b k e₁).hom.app M₂)
    ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M₂)
    ((smallEtaleThickenedModulesCompIso a b k e₁).hom_inv_id_app M₂) kk hkey
    ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M₂)).inv
    ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso K₂).inv
    (restrictIso_inv_naturality_smallEtale a b e₁ x₂.inv)
    ((pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
      ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M₂))
    ((pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
      ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj K₂))
    (pushforwardModulesCompAt_trans_eqToIso_hom_naturality_restrict a b c e₂ x₂.inv)
    ((CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M₁)
    ((CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M₂)
    (pushforwardModulesRetractionIso_hom_naturality_thickened c h₁ φ)
    ((CoherentSituation.pushforwardModulesRetractionIso a c₂ h₂).inv.app M₂)
    ((CoherentSituation.pushforwardModulesRetractionIso a c₂ h₂).hom.app M₂)
    ((CoherentSituation.pushforwardModulesRetractionIso a c₂ h₂).hom_inv_id_app M₂)
    (pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso a b c e₁ e₂ h₁ h₂ M₂)

end AlgebraicGeometry.Space

end
