module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity

/-!
# `lim 𝒪_{Xₙ} ⟶ 𝒪_{X₀}` is surjective over affine charts

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerSpace`, the body of the proof of
[Stacks Project, Tag 0D3X] forms the extension
`0 → lim 𝒪_{X₁} ⊗ Iₙ → lim 𝒪_{Xₙ} → 𝒪_{X₁} → 0`; that the right hand map is onto is the
vanishing of `R¹ lim` of the kernels. On the small étale site of `X₀` this file proves it on the
sections over every affine étale chart `W`, and hence local surjectivity of the reduction
`𝒜 = lim Aₙ ⟶ 𝒪_{X₀}`:

* each `Aₙ = aₙ⁻¹𝒪_{Xₙ}` is the middle term of an extension of `𝒪_{X₀}` by the quasi-coherent
  `𝒪_{X₀} ⊗ Iₙ` (`towerExtension`, `towerExtensionIdealIso`), so `Aₙ(W) ⟶ 𝒪_{X₀}(W)` is onto;
* the transitions `A_{n+1} ⟶ Aₙ` are inverse images of the structure maps of the closed
  immersions `Xₙ ⟶ X_{n+1}`, hence locally surjective, hence onto over `W` by
  `AlgebraicGeometry.Space.surjective_extensionHom_app_of_isQuasicoherentOnSite`;
* sections of the limit are the limit of the sections, and a limit of a tower of surjections
  maps onto its first term.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.surjective_towerRingSystem_map_app`:
  `A_{n+1}(W) ⟶ Aₙ(W)` is surjective.
* `AlgebraicGeometry.ProperFlatFibre.surjective_towerRingLimitReduction_app`:
  `𝒜(W) ⟶ 𝒪_{X₀}(W)` is surjective.
* `AlgebraicGeometry.ProperFlatFibre.isLocallySurjective_towerRingLimitReduction`:
  `𝒜 ⟶ 𝒪_{X₀}` is locally surjective.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3E](https://stacks.math.columbia.edu/tag/0D3E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)

/-- A morphism of sheaves of rings with a right inverse is locally surjective. -/
theorem _root_.CategoryTheory.Sheaf.isLocallySurjective_of_comp_eq_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G : Sheaf J CommRingCat.{u}} (f : F ⟶ G) (g : G ⟶ F)
    (h : g ≫ f = 𝟙 G) : Sheaf.IsLocallySurjective f :=
  Presheaf.isLocallySurjective_of_surjective J f.hom fun U x =>
    ⟨g.hom.app U x, congrArg (fun k : G ⟶ G => k.hom.app U x) h⟩

/-- The inverse of an isomorphism of sheaves of rings undoes it on sections. -/
theorem _root_.CategoryTheory.Sheaf.inv_hom_app_hom_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G : Sheaf J CommRingCat.{u}} (g : F ≅ G) (U : Cᵒᵖ)
    (x : F.obj.obj U) : g.inv.hom.app U (g.hom.hom.app U x) = x :=
  congrArg (fun k : F ⟶ F => k.hom.app U x) g.hom_inv_id

/-- Surjectivity on sections transports along isomorphisms of the source and the target. -/
theorem _root_.CategoryTheory.Sheaf.surjective_hom_app_of_conj {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G F' G' : Sheaf J CommRingCat.{u}} (f : F ⟶ G)
    (eF : F ≅ F') (eG : G ≅ G') {U : Cᵒᵖ}
    (hf' : Function.Surjective ((eF.inv ≫ f ≫ eG.hom).hom.app U)) :
    Function.Surjective (f.hom.app U) := by
  intro y
  obtain ⟨x, hx⟩ := hf' (eG.hom.hom.app U y)
  refine ⟨eF.inv.hom.app U x, ?_⟩
  exact (Sheaf.inv_hom_app_hom_app eG U _).symm.trans
    ((congrArg (eG.inv.hom.app U) hx).trans (Sheaf.inv_hom_app_hom_app eG U y))

/-- A composite of morphisms of sheaves of rings surjective on the sections over `U` is surjective
on the sections over `U`. -/
theorem _root_.CategoryTheory.Sheaf.surjective_comp_hom_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G H : Sheaf J CommRingCat.{u}} (f : F ⟶ G) (g : G ⟶ H)
    {U : Cᵒᵖ} (hf : Function.Surjective (f.hom.app U)) (hg : Function.Surjective (g.hom.app U)) :
    Function.Surjective ((f ≫ g).hom.app U) :=
  hg.comp hf

/-- An isomorphism of sheaves of rings is surjective on sections. -/
theorem _root_.CategoryTheory.Sheaf.surjective_hom_app_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G : Sheaf J CommRingCat.{u}} (g : F ≅ G) (U : Cᵒᵖ) :
    Function.Surjective (g.hom.hom.app U) := fun x =>
  ⟨g.inv.hom.app U x, Sheaf.inv_hom_app_hom_app g.symm U x⟩

include hsurj hsq he in
/-- **The transition morphisms `Xₘ ⟶ Xₙ` are closed immersions**, base changes of `Yₘ ⟶ Yₙ`. -/
theorem isClosedImmersion_towerTransition {m n : ℕ} (k : m ⟶ n) :
    Space.IsClosedImmersion B S hS (towerTransition ξ k).hom := by
  have hb : Space.IsClosedImmersion B S hS
      (schemeSpaceMap ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)).hom :=
    (Space.presheaf_yoneda_map_iff B S hS
      AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
        ((ξ ⋙ cartesianProperFlatProjection B S hS).map k)).2
      (isClosedImmersion_towerBase_map ξ hsurj hsq e he k)
  exact (Space.isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_towerTransition ξ k).flip) hb

include hsurj hsq he in
/-- **The ideal `𝒪_{X₀} ⊗ Iₙ` of the extension `towerExtension` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_towerExtensionIdeal (n : ℕ) :
    (towerExtensionIdeal ξ hsurj hsq e he n).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (towerExtensionIdealIso ξ hsurj hsq e he n).symm
    (Space.isQuasicoherentOnSite_baseRingTensorModule B S hS _ _ _)

include hsurj hsq he in
/-- **The transitions `A_{n+1} ⟶ Aₙ` are locally surjective**: each is the inverse image along
`aₙ` of the structure map of the closed immersion `Xₙ ⟶ X_{n+1}` (Stacks 03MB). -/
theorem isLocallySurjective_towerRingSystem_map_succ (n : ℕ) :
    Sheaf.IsLocallySurjective ((towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op) := by
  rw [towerRingSystem_map_succ]
  unfold Space.inverseImageStructureSheafMapOfEq Space.inverseImageStructureSheafMap
  apply +allowSynthFailures Sheaf.isLocallySurjective_comp
  · exact Sheaf.isLocallySurjective_of_comp_eq_id _ (eqToHom (congrArg
      (Space.inverseImageStructureSheaf B S hS) (towerInclusion_comp_towerTransition ξ n)))
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
  apply +allowSynthFailures Sheaf.isLocallySurjective_comp
  · exact Sheaf.isLocallySurjective_of_comp_eq_id _ _ (Iso.hom_inv_id_app _ _)
  · exact Space.isLocallySurjective_inverseImage_structureSharpInverseImage B S hS
      (towerInclusion ξ n) (towerTransition ξ (homOfLE (Nat.le_succ n)))
      (isClosedImmersion_towerTransition ξ hsurj hsq e he _)

/-- The transition of middle terms lies over `𝒪_{X₀}`. -/
theorem towerExtensionTransition_reduction (n : ℕ) :
    ((towerRingSystemExtensionIso ξ hsurj hsq e he n.succ (𝟙 _)).inv ≫
      (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op ≫
        (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom) ≫
        (towerExtension ξ hsurj hsq e he n (𝟙 _)).reduction =
      (towerExtension ξ hsurj hsq e he n.succ (𝟙 _)).reduction := by
  rw [Category.assoc, Category.assoc,
    towerRingSystemExtensionIso_hom_comp_reduction, Iso.inv_comp_eq,
    towerRingSystemExtensionIso_hom_comp_reduction]
  exact ((towerRingReduction ξ).naturality (homOfLE (Nat.le_succ n)).op).trans
    (Category.comp_id _)

include hsurj hsq he in
/-- The transition of middle terms is locally surjective. -/
theorem isLocallySurjective_towerExtensionTransition (n : ℕ) :
    Sheaf.IsLocallySurjective ((towerRingSystemExtensionIso ξ hsurj hsq e he n.succ (𝟙 _)).inv ≫
      (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op ≫
        (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom) := by
  have := isLocallySurjective_towerRingSystem_map_succ ξ hsurj hsq e he n
  exact Sheaf.isLocallySurjective_comp _ _

include hsurj hsq he in
/-- The transition of middle terms is surjective over every affine étale chart. -/
theorem surjective_towerExtensionTransition_app (n : ℕ)
    (W : Space.SmallEtale B S hS (towerSpace ξ 0).1)
    (hW : Space.IsAffineChart B S hS (towerSpace ξ 0).1 W) :
    Function.Surjective (((towerRingSystemExtensionIso ξ hsurj hsq e he n.succ (𝟙 _)).inv ≫
      (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op ≫
        (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom).hom.app (op W)) :=
  Space.surjective_extensionHom_app_of_isQuasicoherentOnSite
    (towerInclusion ξ n.succ ≫ 𝟙 _)
    (towerExtension ξ hsurj hsq e he n.succ (𝟙 _)) (towerExtension ξ hsurj hsq e he n (𝟙 _))
    (isQuasicoherentOnSite_towerExtensionIdeal ξ hsurj hsq e he n.succ)
    (isQuasicoherentOnSite_towerExtensionIdeal ξ hsurj hsq e he n)
    _ (towerExtensionTransition_reduction ξ hsurj hsq e he n)
    (isLocallySurjective_towerExtensionTransition ξ hsurj hsq e he n) W hW

/-- `A_{n+1}(W) ⟶ Aₙ(W)` is surjective as soon as its conjugate by the identifications with
middle terms is. -/
theorem surjective_towerRingSystem_map_app_of_conj (n : ℕ)
    (W : Space.SmallEtale B S hS (towerSpace ξ 0).1)
    (ht : Function.Surjective (((towerRingSystemExtensionIso ξ hsurj hsq e he n.succ (𝟙 _)).inv ≫
      (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op ≫
        (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _)).hom).hom.app (op W))) :
    Function.Surjective
      (((towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op).hom.app (op W)) :=
  Sheaf.surjective_hom_app_of_conj _ _ _ ht

include hsurj hsq he in
/-- **`A_{n+1}(W) ⟶ Aₙ(W)` is surjective over every affine étale chart `W` of `X₀`.** -/
theorem surjective_towerRingSystem_map_app (n : ℕ)
    (W : Space.SmallEtale B S hS (towerSpace ξ 0).1)
    (hW : Space.IsAffineChart B S hS (towerSpace ξ 0).1 W) :
    Function.Surjective
      (((towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op).hom.app (op W)) :=
  surjective_towerRingSystem_map_app_of_conj ξ hsurj hsq e he n W
    (surjective_towerExtensionTransition_app ξ hsurj hsq e he n W hW)

include hsurj hsq he in
/-- **`Aₙ(W) ⟶ 𝒪_{X₀}(W)` is surjective over every affine étale chart `W`**: it is the reduction
of an extension with quasi-coherent ideal. -/
theorem surjective_towerRingReduction_app (n : ℕ)
    (W : Space.SmallEtale B S hS (towerSpace ξ 0).1)
    (hW : Space.IsAffineChart B S hS (towerSpace ξ 0).1 W) :
    Function.Surjective (((towerRingReduction ξ).app (op n)).hom.app (op W)) := by
  have h := Space.surjective_reduction_app_of_isQuasicoherentOnSite (towerInclusion ξ n ≫ 𝟙 _)
    (towerExtension ξ hsurj hsq e he n (𝟙 _))
    (isQuasicoherentOnSite_towerExtensionIdeal ξ hsurj hsq e he n) W hW
  rw [← towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _)]
  exact Sheaf.surjective_comp_hom_app _ _ (Sheaf.surjective_hom_app_of_iso _ _) h

include hsurj hsq he in
/-- **`𝒜(W) ⟶ A₀(W)` is surjective over every affine étale chart `W`**: sections of the limit
are compatible families, and the transitions are surjective over `W`. -/
theorem surjective_limit_π_towerRingSystem_app
    (W : Space.SmallEtale B S hS (towerSpace ξ 0).1)
    (hW : Space.IsAffineChart B S hS (towerSpace ξ 0).1 W) :
    Function.Surjective ((limit.π (towerRingSystem ξ) (op 0)).hom.app (op W)) := by
  have hl : IsLimit (((evaluation _ CommRingCat.{u}).obj (op W)).mapCone
      ((sheafToPresheaf _ CommRingCat.{u}).mapCone (limit.cone (towerRingSystem ξ)))) :=
    isLimitOfPreserves _ (isLimitOfPreserves _ (limit.isLimit _))
  exact Concrete.surjective_π_app_zero_of_surjective_map hl
    (fun n => surjective_towerRingSystem_map_app ξ hsurj hsq e he n W hW)

include hsurj hsq he in
/-- **`𝒜(W) ⟶ 𝒪_{X₀}(W)` is surjective over every affine étale chart `W` of `X₀`**, the exactness
on the right of `0 → lim 𝒪 ⊗ Iₙ → lim 𝒪_{Xₙ} → 𝒪_{X₁} → 0` in the proof of Stacks 0D3X. -/
theorem surjective_towerRingLimitReduction_app
    (W : Space.SmallEtale B S hS (towerSpace ξ 0).1)
    (hW : Space.IsAffineChart B S hS (towerSpace ξ 0).1 W) :
    Function.Surjective ((towerRingLimitReduction ξ).hom.app (op W)) :=
  Sheaf.surjective_comp_hom_app _ _ (surjective_limit_π_towerRingSystem_app ξ hsurj hsq e he W hW)
    (surjective_towerRingReduction_app ξ hsurj hsq e he 0 W hW)

include hsurj hsq he in
/-- **The reduction `𝒜 = lim Aₙ ⟶ 𝒪_{X₀}` is locally surjective.** -/
theorem isLocallySurjective_towerRingLimitReduction :
    Presheaf.IsLocallySurjective (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (towerRingLimitReduction ξ).hom :=
  Space.isLocallySurjective_of_surjective_app_isAffineChart _
    (surjective_towerRingLimitReduction_app ξ hsurj hsq e he)

end AlgebraicGeometry.ProperFlatFibre

end
