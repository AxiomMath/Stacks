module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageStalkTowerNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPartStalkCompactSupport

/-!
# The proper base change chain at a stalk, natural in the coefficients

Let `g : U ⟶ W` be separated of finite type with a compactification, `w` a point of `W` with
finite residue field `κ`, `U_w` the fibre, `G` an ℓ-adic sheaf on `U` and `R = Rʳ g_! G`. The proof
of `Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), proper base change Tag 0F7L, the Leray
comparison Tag 0F7J) passes from the rational limit of `n ↦ H⁰_c(Spec κ̄, i⁻¹ Rₙ)` to
`Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)` through a chain of isomorphisms. This file assembles that chain
into one isomorphism (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkChainIso`) and
proves that it carries the Frobenius of `κ` to the Frobenius of `κ`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkChainIso_frobenius`) and the
endomorphism induced by any `φ : G ⟶ G` on `R` to the one induced on `G|_{U_w}`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkChainIso_naturality`).

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-! ### Whiskering isomorphisms along lifted towers -/

section Generic

variable {C C₁ C₂ C' D J : Type*} [Category* C] [Category* C₁] [Category* C₂] [Category* C']
  [Category* D] [Category* J]

/-- An isomorphism of functors on a full subcategory, whiskered along a lifted tower, commutes with
the endomorphisms induced by an endomorphism of the tower. -/
theorem isoWhiskerLeft_lift_hom_naturality (P : ObjectProperty C) (T : J ⥤ C)
    (hT : ∀ j, P (T.obj j)) (α : T ⟶ T) {A A' : C ⥤ D} (β : P.ι ⋙ A ≅ P.ι ⋙ A') :
    Functor.whiskerRight α A ≫ (Functor.isoWhiskerLeft (ObjectProperty.lift P T hT) β).hom =
      (Functor.isoWhiskerLeft (ObjectProperty.lift P T hT) β).hom ≫ Functor.whiskerRight α A' := by
  ext j
  exact β.hom.naturality (ObjectProperty.homMk (X := (ObjectProperty.lift P T hT).obj j)
    (Y := (ObjectProperty.lift P T hT).obj j) (α.app j))

/-- The inverse of an isomorphism of composite functors on a full subcategory, whiskered along a
lifted tower, commutes with the endomorphisms induced by an endomorphism of the tower. -/
theorem isoWhiskerLeft_lift_isoWhiskerRight_symm_hom_naturality (P : ObjectProperty C) (T : J ⥤ C)
    (hT : ∀ j, P (T.obj j)) (α : T ⟶ T) (F₁ : C ⥤ C₁) (F₂ : C₁ ⥤ C') (G₁ : C ⥤ C₂)
    (G₂ : C₂ ⥤ C') (H : C' ⥤ D) (β : P.ι ⋙ G₁ ⋙ G₂ ≅ P.ι ⋙ F₁ ⋙ F₂) :
    Functor.whiskerRight (Functor.whiskerRight α F₁) (F₂ ⋙ H) ≫
        (Functor.isoWhiskerLeft (ObjectProperty.lift P T hT)
          (Functor.isoWhiskerRight β H)).symm.hom =
      (Functor.isoWhiskerLeft (ObjectProperty.lift P T hT) (Functor.isoWhiskerRight β H)).symm.hom ≫
        Functor.whiskerRight (Functor.whiskerRight α G₁) (G₂ ⋙ H) := by
  exact isoWhiskerLeft_lift_hom_naturality P T hT α (A := F₁ ⋙ F₂ ⋙ H) (A' := G₁ ⋙ G₂ ⋙ H)
    (Functor.isoWhiskerRight β H).symm

end Generic

section Chain

variable {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (w : W.1) [Fintype (W.1.residueField w)] (hB : B.Contains ((B.inclusion.map g).fiber w))
  [IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)]
  (kbar : Type u) [Field kbar] [Algebra (W.1.residueField w) kbar] [IsAlgClosed kbar] (p n : ℕ)
  [Fact p.Prime] [CharP (W.1.residueField w) p] (hcard : Fintype.card (W.1.residueField w) = p ^ n)

/-- `M ↦ H⁰_c(Spec κ̄, i⁻¹ M)` on sheaves of `ℤ_ℓ`-modules on `W`, `i : Spec κ(w) ⟶ W`. -/
abbrev residuePointCohomology : EtaleModules.{u, 0} ℤ_[ℓ] W.1 ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
  etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w)) ⋙
    compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
      (CompactificationOf.ofProper (𝟙 _)) kbar 0

/-- The Frobenius of `κ(w)` on `M ↦ H⁰_c(Spec κ̄, i⁻¹ M)`. -/
abbrev residuePointFrobenius :
    residuePointCohomology B ℓ w kbar ⟶ residuePointCohomology B ℓ w kbar :=
  Functor.whiskerLeft
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w)))
    (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
      (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)

/-- The structure morphism of the fibre `U_w` over `κ(w)`, as used by the Leray comparison. -/
abbrev fibreStructureResidueField : (B.inclusion.map g).fiber w ⟶ Spec (.of (W.1.residueField w)) :=
  (B.inclusion.map g).fiberToSpecResidueField w ≫ 𝟙 (Spec (.of (W.1.residueField w)))

variable (G : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ)
  (hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r)
  (jgw : CompactificationOf (Over.mk ((B.inclusion.map g).fiberToSpecResidueField w)))
  (jU : CompactificationOf (Over.mk (fibreStructureResidueField B g w)))
  (Ψ : (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
          (CompactificationOf.ofProper (𝟙 _)) kbar 0 ≅
      (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r)

/-- The levels of the flat model of `G` restricted to the fibre, as ℓ-power torsion sheaves. -/
abbrev fibreFlatModelTorsionTower :
    ℕᵒᵖ ⥤ (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).FullSubcategory :=
  ObjectProperty.lift _ (LAdicSheaf.flatModelTorsionTower G ⋙ (IsLPowerTorsion ℓ U.1).ι ⋙
      etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (fibreι B g w hB)))
    (fun m => ⟨m.unop + 1, by
      change ℓ ^ (m.unop + 1) • 𝟙 ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
        (B.inclusion.map (fibreι B g w hB))).obj (towerObj (LAdicSheaf.padicTower B U ℓ
          (LAdicSheaf.flatModel B ℓ G)) m.unop)) = 0
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
        LAdicSheaf.padicTower_annihilated B U ℓ _ m.unop, Functor.map_zero]⟩)

/-- Proper base change (Tag 0F7L) for `Rʳ g_!` on ℓ-power torsion sheaves along the fibre at
`w`. -/
def fibreLowerShriekBaseChangeIso :
    (IsLPowerTorsion ℓ U.1).ι ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (fibreι B g w hB)) ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ≅
      (IsLPowerTorsion ℓ U.1).ι ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w)) :=
  lowerShriekHomologyBaseChangeIso ℤ_[ℓ]
      (IsPullback.of_hasPullback (B.inclusion.map g) (W.1.fromSpecResidueField w) :
        IsPullback (B.inclusion.map (fibreι B g w hB))
          ((B.inclusion.map g).fiberToSpecResidueField w) (B.inclusion.map g)
          (B.inclusion.map (residueFieldPointHom B w))) jg jgw (IsLPowerTorsion ℓ U.1)
      (fun _ ⟨N, hN⟩ => ⟨ℓ ^ N, pow_pos (Fact.out : ℓ.Prime).pos N, hN⟩) r

/-- The proper base change isomorphism (Tag 0F7L) along the levels of the flat model. -/
def higherDirectImageStalkBaseChangeIso :
    LAdicSheaf.lowerShriekTower B ℓ g jg G r ⋙ residuePointCohomology B ℓ w kbar ≅
      fibreFlatModelTorsionTower B ℓ g w hB G ⋙
        (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
          (CompactificationOf.ofProper (𝟙 _)) kbar 0 :=
  (Functor.isoWhiskerLeft (LAdicSheaf.flatModelTorsionTower G)
    (Functor.isoWhiskerRight (fibreLowerShriekBaseChangeIso B ℓ g jg w hB r jgw)
      (compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
        (CompactificationOf.ofProper (𝟙 _)) kbar 0))).symm

/-- The stable images of `n ↦ Rʳ g_! G'ₙ` are the levels of `Rʳ g_! G`, read through
`M ↦ H⁰_c(Spec κ̄, i⁻¹ M)`. -/
def higherDirectImageStalkStableImageIso :
    haveI := hcond.fst
    LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) ⋙
        residuePointCohomology B ℓ w kbar ≅
      (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower ⋙
        residuePointCohomology B ℓ w kbar :=
  haveI := hcond.fst
  Functor.isoWhiskerRight (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r hcond) _

/-- Rationally, the stable images of `n ↦ Rʳ g_! G'ₙ` are pro-isomorphic to the tower. -/
def higherDirectImageStalkStableIso :
    haveI := hcond.fst
    (rationalLim.{u + 1} (ℓ := ℓ)).obj
        ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower ⋙
          residuePointCohomology B ℓ w kbar) ≅
      (rationalLim.{u + 1} (ℓ := ℓ)).obj
        (LAdicSheaf.lowerShriekTower B ℓ g jg G r ⋙ residuePointCohomology B ℓ w kbar) :=
  haveI := hcond.fst
  haveI := (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).isIso_limMap_whiskerRight_stableImageι
    (residuePointCohomology B ℓ w kbar)
  @asIso _ _ _ _ ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerRight
    (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageι (residuePointCohomology B ℓ w kbar)))
    (by
      change IsIso ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (limMap _))
      infer_instance)

/-- The Leray comparison (Tag 0F7J) along the levels of the flat model on the fibre. -/
def higherDirectImageStalkLerayIso :
    fibreFlatModelTorsionTower B ℓ g w hB G ⋙
        (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
          (CompactificationOf.ofProper (𝟙 _)) kbar 0 ≅
      fibreFlatModelTorsionTower B ℓ g w hB G ⋙
        (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r :=
  Functor.isoWhiskerLeft (fibreFlatModelTorsionTower B ℓ g w hB G) Ψ

/-- The levels of the flat model restricted to the fibre are those of the restriction. -/
def higherDirectImageStalkFibreLevelIso :
    fibreFlatModelTorsionTower B ℓ g w hB G ⋙
        (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r ≅
      LAdicSheaf.padicTower B (fibreObj B g w hB) ℓ
          (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r :=
  Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ (fibreι B g w hB)
    (LAdicSheaf.flatModel B ℓ G))
    (compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r)

/-- The restriction of the flat model to the fibre is isogenous to the restriction of `G`. -/
def higherDirectImageStalkIsogenyIso :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.inverseImage (fibreι B g w hB) G) r :=
  LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B (fibreObj B g w hB) ℓ
    (fibreStructureResidueField B g w) jU kbar
    (LAdicSheaf.inverseImageMap (fibreι B g w hB)
      (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (LAdicSheaf.inverseImageMap (fibreι B g w hB)
      (LAdicSheaf.toTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (LAdicSheaf.torsionBound G) (by
      change (LAdicSheaf.inverseImageFunctor (fibreι B g w hB)).map _ ≫
        (LAdicSheaf.inverseImageFunctor (fibreι B g w hB)).map _ = _
      rw [← Functor.map_comp, LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel,
        Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl) (by
      change (LAdicSheaf.inverseImageFunctor (fibreι B g w hB)).map _ ≫
        (LAdicSheaf.inverseImageFunctor (fibreι B g w hB)).map _ = _
      rw [← Functor.map_comp, LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel,
        Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl) r

/-- **The proper base change chain at the stalk**: the rational limit of
`n ↦ H⁰_c(Spec κ̄, i⁻¹ (Rʳ g_! G)ₙ)` is `Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)`. -/
def LAdicSheaf.higherDirectImageStalkChainIso :
    (rationalLim.{u + 1} (ℓ := ℓ)).obj
        (LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) ⋙
          residuePointCohomology B ℓ w kbar) ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.inverseImage (fibreι B g w hB) G) r :=
  (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (higherDirectImageStalkStableImageIso B ℓ g jg w kbar G r hcond) ≪≫
    higherDirectImageStalkStableIso B ℓ g jg w kbar G r hcond ≪≫
    (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (higherDirectImageStalkBaseChangeIso B ℓ g jg w hB kbar G r jgw) ≪≫
    (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (higherDirectImageStalkLerayIso B ℓ g w hB kbar G r jgw jU Ψ) ≪≫
    (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (higherDirectImageStalkFibreLevelIso B ℓ g w hB kbar G r jU) ≪≫
    (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (LAdicSheaf.padicTowerCohomologyIso B (fibreObj B g w hB) ℓ
        (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r) ≪≫
    higherDirectImageStalkIsogenyIso B ℓ g w hB kbar G r jU

/-! ### Naturality in the endomorphisms of `G` -/

section Naturality

variable (φ : G ⟶ G)

/-- The endomorphism of the levels of the flat model on the fibre induced by `φ : G ⟶ G`, read
through a functor `H`. -/
def fibreFlatModelTowerEnd {D : Type*} [Category* D]
    (H : EtaleModules.{u, 0} ℤ_[ℓ] ((B.inclusion.map g).fiber w) ⥤ D) :
    fibreFlatModelTorsionTower B ℓ g w hB G ⋙
        (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙ H ⟶
      fibreFlatModelTorsionTower B ℓ g w hB G ⋙
        (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙ H :=
  Functor.whiskerRight (Functor.whiskerRight
    (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G)))
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (fibreι B g w hB)))) H

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkStableImageIso` carries the endomorphism of the
levels of `Rʳ g_! G` induced by `φ : G ⟶ G` to the endomorphism of the stable images induced by
`φ`. -/
theorem higherDirectImageStalkStableImageIso_naturality :
    haveI := hcond.fst
    Functor.whiskerRight
        (LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ))
        (residuePointCohomology B ℓ w kbar) ≫
      (higherDirectImageStalkStableImageIso B ℓ g jg w kbar G r hcond).hom =
    (higherDirectImageStalkStableImageIso B ℓ g jg w kbar G r hcond).hom ≫
      Functor.whiskerRight ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageMap
        (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ)) (residuePointCohomology B ℓ w kbar) := by
  have := hcond.fst
  ext m : 2
  induction m using Opposite.rec with
  | op m =>
    exact functor_map_comp_eq_of_comp_eq (residuePointCohomology B ℓ w kbar)
      (LAdicSheaf.higherDirectImageShriekEnd_padicLevelMap B ℓ g jg G r hcond φ m)

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] [AlgebraicGeometry.IsNoetherian W.1]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkStableIso` carries the endomorphism of the stable
images induced by `φ : G ⟶ G` to the endomorphism of `n ↦ Rʳ g_! G'ₙ` induced by `φ`. -/
theorem higherDirectImageStalkStableIso_naturality :
    haveI := hcond.fst
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerRight
        ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageMap
          (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ)) (residuePointCohomology B ℓ w kbar)) ≫
      (higherDirectImageStalkStableIso B ℓ g jg w kbar G r hcond).hom =
    (higherDirectImageStalkStableIso B ℓ g jg w kbar G r hcond).hom ≫
      (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerRight
        (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ) (residuePointCohomology B ℓ w kbar)) := by
  have := hcond.fst
  refine functor_map_comp_eq_of_comp_eq _ ?_
  ext m : 2
  exact functor_map_comp_eq_of_comp_eq (residuePointCohomology B ℓ w kbar) (NatTrans.congr_app
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageMap_ι
      (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ)) m)

omit [AlgebraicGeometry.IsNoetherian W.1]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- The proper base change isomorphism `Stacks.EtaleCohomology.higherDirectImageStalkBaseChangeIso`
carries the endomorphism of `n ↦ Rʳ g_! G'ₙ` induced by `φ : G ⟶ G` to the endomorphism of the
levels of the flat model on the fibre induced by `φ`. -/
theorem higherDirectImageStalkBaseChangeIso_naturality :
    Functor.whiskerRight (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ)
        (residuePointCohomology B ℓ w kbar) ≫
      (higherDirectImageStalkBaseChangeIso B ℓ g jg w hB kbar G r jgw).hom =
    (higherDirectImageStalkBaseChangeIso B ℓ g jg w hB kbar G r jgw).hom ≫
      fibreFlatModelTowerEnd B ℓ g w hB G φ
        (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
          compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar 0) :=
  isoWhiskerLeft_lift_isoWhiskerRight_symm_hom_naturality (IsLPowerTorsion ℓ U.1)
    (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G))
    (fun m => ⟨m.unop + 1, LAdicSheaf.padicTower_annihilated B U ℓ _ m.unop⟩)
    (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G)))
    (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r)
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (residueFieldPointHom B w)))
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (fibreι B g w hB)))
    (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
    (compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
      (CompactificationOf.ofProper (𝟙 _)) kbar 0)
    (fibreLowerShriekBaseChangeIso B ℓ g jg w hB r jgw)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  [Fintype (W.1.residueField w)] [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- The Leray comparison `Stacks.EtaleCohomology.higherDirectImageStalkLerayIso` commutes with the
endomorphisms of the levels of the flat model on the fibre induced by `φ : G ⟶ G`. -/
theorem higherDirectImageStalkLerayIso_naturality :
    fibreFlatModelTowerEnd B ℓ g w hB G φ
        (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
          compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar 0) ≫
      (higherDirectImageStalkLerayIso B ℓ g w hB kbar G r jgw jU Ψ).hom =
    (higherDirectImageStalkLerayIso B ℓ g w hB kbar G r jgw jU Ψ).hom ≫
      fibreFlatModelTowerEnd B ℓ g w hB G φ
        (compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r) :=
  isoWhiskerLeft_lift_hom_naturality (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w))
    (LAdicSheaf.flatModelTorsionTower G ⋙ (IsLPowerTorsion ℓ U.1).ι ⋙
      etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (fibreι B g w hB)))
    _ (Functor.whiskerRight
      (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G)))
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (fibreι B g w hB)))) Ψ

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  [Fintype (W.1.residueField w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkFibreLevelIso` carries the endomorphism of the
levels of the flat model on the fibre induced by `φ : G ⟶ G` to the endomorphism of the levels of
the restriction of the flat model induced by `φ`. -/
theorem higherDirectImageStalkFibreLevelIso_naturality :
    fibreFlatModelTowerEnd B ℓ g w hB G φ
        (compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r) ≫
      (higherDirectImageStalkFibreLevelIso B ℓ g w hB kbar G r jU).hom =
    (higherDirectImageStalkFibreLevelIso B ℓ g w hB kbar G r jU).hom ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap (fibreι B g w hB)
          (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))))
        (compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r) := by
  ext m : 2
  exact functor_map_comp_eq_of_comp_eq
    (compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r)
    (NatTrans.congr_app
    (LAdicSheaf.padicTowerInverseImageIso_hom_naturality B ℓ (fibreι B g w hB)
      (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))) m)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [IsAlgClosed kbar] in
/-- On `Hʳ_c` of the fibre, the map induced by `φ : G ⟶ G` on the flat model followed by the map
induced by the flat model `G' ⟶ G` is the map induced by `G' ⟶ G` followed by the map induced by
`φ`. -/
theorem higherDirectImageStalkIsogeny_naturality :
    LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
        (fibreStructureResidueField B g w) jU kbar (LAdicSheaf.inverseImageMap (fibreι B g w hB)
          (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))) r ≫
      LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
        (fibreStructureResidueField B g w) jU kbar (LAdicSheaf.inverseImageMap (fibreι B g w hB)
          (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G))) r =
    LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
        (fibreStructureResidueField B g w) jU kbar (LAdicSheaf.inverseImageMap (fibreι B g w hB)
          (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G))) r ≫
      LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
        (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.inverseImageMap (fibreι B g w hB) φ) r := by
  rw [← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp,
    ← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp]
  congr 1
  exact functor_map_comp_eq_of_comp_eq (LAdicSheaf.inverseImageFunctor (fibreι B g w hB))
    (LAdicSheaf.torsionFreeModelMap_comp_fromTorsionFreeModel ..)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [IsAlgClosed kbar] in
/-- The comparison `Stacks.EtaleCohomology.LAdicSheaf.padicTowerCohomologyIso` of the rational
limit of the levels with `Hʳ_c` of the fibre commutes with the maps induced by `φ : G ⟶ G` on the
flat model. -/
theorem higherDirectImageStalkCohomologyIso_naturality :
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerRight
        (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap (fibreι B g w hB)
          (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))))
        (compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r)) ≫
      ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
        (LAdicSheaf.padicTowerCohomologyIso B (fibreObj B g w hB) ℓ
          (fibreStructureResidueField B g w) jU kbar
          (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r)).hom =
    ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
        (LAdicSheaf.padicTowerCohomologyIso B (fibreObj B g w hB) ℓ
          (fibreStructureResidueField B g w) jU kbar
          (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r)).hom ≫
      (rationalLim.{u + 1} (ℓ := ℓ)).map
        (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap (X := fibreObj B g w hB)
          (fibreStructureResidueField B g w) jU kbar (LAdicSheaf.inverseImageMap (fibreι B g w hB)
            (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))) r) :=
  functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
    (LAdicSheaf.padicTowerCohomologyIso_hom_naturality B ℓ (X := fibreObj B g w hB)
      (fibreStructureResidueField B g w) jU kbar (LAdicSheaf.inverseImageMap (fibreι B g w hB)
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))) r)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkIsogenyIso` carries the rational map induced by
`φ : G ⟶ G` on the restricted flat model to the rational map induced by `φ` on the restriction of
`G`. -/
theorem higherDirectImageStalkIsogenyIso_naturality :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
          (fibreStructureResidueField B g w) jU kbar (LAdicSheaf.inverseImageMap (fibreι B g w hB)
            (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G))) r) ≫
      (higherDirectImageStalkIsogenyIso B ℓ g w hB kbar G r jU).hom =
    (higherDirectImageStalkIsogenyIso B ℓ g w hB kbar G r jU).hom ≫
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
          (fibreStructureResidueField B g w) jU kbar
          (LAdicSheaf.inverseImageMap (fibreι B g w hB) φ) r) :=
  functor_map_comp_eq_of_comp_eq (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
    (higherDirectImageStalkIsogeny_naturality B ℓ g w hB kbar G r jU φ)

omit [IsAlgClosed kbar] in
/-- **The proper base change chain at the stalk is natural in `G`**: it carries the endomorphism
of `Rʳ g_! G` induced by `φ : G ⟶ G` to the endomorphism of `G|_{U_w}` induced by `φ`. -/
theorem LAdicSheaf.higherDirectImageStalkChainIso_naturality :
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerRight
        (LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ))
        (residuePointCohomology B ℓ w kbar)) ≫
      (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).hom =
    (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).hom ≫
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
          (fibreStructureResidueField B g w) jU kbar
          (LAdicSheaf.inverseImageMap (fibreι B g w hB) φ) r) := by
  have := hcond.fst
  exact comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkStableImageIso_naturality B ℓ g jg w kbar G r hcond φ))
    (comm_comp_of_comm (higherDirectImageStalkStableIso_naturality B ℓ g jg w kbar G r hcond φ)
    (comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkBaseChangeIso_naturality B ℓ g jg w hB kbar G r jgw φ))
    (comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkLerayIso_naturality B ℓ g w hB kbar G r jgw jU Ψ φ))
    (comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkFibreLevelIso_naturality B ℓ g w hB kbar G r jU φ))
    (comm_comp_of_comm (higherDirectImageStalkCohomologyIso_naturality B ℓ g w hB kbar G r jU φ)
      (higherDirectImageStalkIsogenyIso_naturality B ℓ g w hB kbar G r jU φ))))))

end Naturality

/-! ### The Frobenius of `κ(w)` -/

section Frobenius

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkStableImageIso` commutes with the Frobenius of
`κ(w)`. -/
theorem higherDirectImageStalkStableImageIso_frobenius :
    haveI := hcond.fst
    Functor.whiskerLeft
        (LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r))
        (residuePointFrobenius B ℓ w kbar p n hcard) ≫
      (higherDirectImageStalkStableImageIso B ℓ g jg w kbar G r hcond).hom =
    (higherDirectImageStalkStableImageIso B ℓ g jg w kbar G r hcond).hom ≫
      Functor.whiskerLeft (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower
        (residuePointFrobenius B ℓ w kbar p n hcard) := by
  have := hcond.fst
  exact Functor.whiskerLeft_comp_whiskerRight _ _

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] [AlgebraicGeometry.IsNoetherian W.1]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkStableIso` commutes with the Frobenius of
`κ(w)`. -/
theorem higherDirectImageStalkStableIso_frobenius :
    haveI := hcond.fst
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower
        (residuePointFrobenius B ℓ w kbar p n hcard)) ≫
      (higherDirectImageStalkStableIso B ℓ g jg w kbar G r hcond).hom =
    (higherDirectImageStalkStableIso B ℓ g jg w kbar G r hcond).hom ≫
      (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
        (LAdicSheaf.lowerShriekTower B ℓ g jg G r)
        (residuePointFrobenius B ℓ w kbar p n hcard)) := by
  have := hcond.fst
  exact functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
    (Functor.whiskerLeft_comp_whiskerRight _ _)

omit [AlgebraicGeometry.IsNoetherian W.1]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- The proper base change isomorphism `Stacks.EtaleCohomology.higherDirectImageStalkBaseChangeIso`
commutes with the Frobenius of `κ(w)`. -/
theorem higherDirectImageStalkBaseChangeIso_frobenius :
    Functor.whiskerLeft (LAdicSheaf.lowerShriekTower B ℓ g jg G r)
        (residuePointFrobenius B ℓ w kbar p n hcard) ≫
      (higherDirectImageStalkBaseChangeIso B ℓ g jg w hB kbar G r jgw).hom =
    (higherDirectImageStalkBaseChangeIso B ℓ g jg w hB kbar G r jgw).hom ≫
      Functor.whiskerLeft (fibreFlatModelTorsionTower B ℓ g w hB G)
        (Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
          (Functor.whiskerLeft
            (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
            (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
              (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0))) := by
  exact Functor.whiskerLeft_comp_whiskerRight
    (Functor.whiskerLeft (LAdicSheaf.flatModelTorsionTower G)
      (fibreLowerShriekBaseChangeIso B ℓ g jg w hB r jgw).inv)
    (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
      (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  [AlgebraicGeometry.IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- The Leray comparison `Stacks.EtaleCohomology.higherDirectImageStalkLerayIso` commutes with the
Frobenius of `κ(w)`, given that `Ψ` does. -/
theorem higherDirectImageStalkLerayIso_frobenius
    (hΨ : Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (Functor.whiskerLeft
          (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
          (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)) ≫ Ψ.hom =
      Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (compactSupportSheafFrobenius ℤ_[ℓ]
          (fibreStructureResidueField B g w) jU kbar p n hcard r)) :
    Functor.whiskerLeft (fibreFlatModelTorsionTower B ℓ g w hB G)
        (Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
          (Functor.whiskerLeft
            (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
            (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
              (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0))) ≫
      (higherDirectImageStalkLerayIso B ℓ g w hB kbar G r jgw jU Ψ).hom =
    (higherDirectImageStalkLerayIso B ℓ g w hB kbar G r jgw jU Ψ).hom ≫
      Functor.whiskerLeft (fibreFlatModelTorsionTower B ℓ g w hB G)
        (Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
          (compactSupportSheafFrobenius ℤ_[ℓ]
            (fibreStructureResidueField B g w) jU kbar p n hcard r)) := by
  ext m : 2
  exact NatTrans.congr_app hΨ ((fibreFlatModelTorsionTower B ℓ g w hB G).obj m)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkFibreLevelIso` commutes with the Frobenius of
`κ(w)` on the compactly supported cohomology of the fibre. -/
theorem higherDirectImageStalkFibreLevelIso_frobenius :
    Functor.whiskerLeft (fibreFlatModelTorsionTower B ℓ g w hB G)
        (Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
          (compactSupportSheafFrobenius ℤ_[ℓ]
            (fibreStructureResidueField B g w) jU kbar p n hcard r)) ≫
      (higherDirectImageStalkFibreLevelIso B ℓ g w hB kbar G r jU).hom =
    (higherDirectImageStalkFibreLevelIso B ℓ g w hB kbar G r jU).hom ≫
      Functor.whiskerLeft (LAdicSheaf.padicTower B (fibreObj B g w hB) ℓ
          (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)))
        (compactSupportSheafFrobenius ℤ_[ℓ]
          (fibreStructureResidueField B g w) jU kbar p n hcard r) := by
  exact Functor.whiskerLeft_comp_whiskerRight
    (LAdicSheaf.padicTowerInverseImageIso B ℓ (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)).hom
    (compactSupportSheafFrobenius ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar p n hcard r)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [IsAlgClosed kbar] in
/-- The comparison `Stacks.EtaleCohomology.LAdicSheaf.padicTowerCohomologyIso` carries the
Frobenius of `κ(w)` on the levels to the rational Frobenius on `Hʳ_c` of the fibre. -/
theorem higherDirectImageStalkCohomologyIso_frobenius :
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft (LAdicSheaf.padicTower B
        (fibreObj B g w hB) ℓ (LAdicSheaf.inverseImage (fibreι B g w hB)
          (LAdicSheaf.flatModel B ℓ G)))
        (compactSupportSheafFrobenius ℤ_[ℓ]
          (fibreStructureResidueField B g w) jU kbar p n hcard r)) ≫
      ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
        (LAdicSheaf.padicTowerCohomologyIso B (fibreObj B g w hB) ℓ
          (fibreStructureResidueField B g w) jU kbar
          (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r)).hom =
    ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
        (LAdicSheaf.padicTowerCohomologyIso B (fibreObj B g w hB) ℓ
          (fibreStructureResidueField B g w) jU kbar
          (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r)).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard
        (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r :=
  functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
    (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B (fibreObj B g w hB) ℓ
      (fibreStructureResidueField B g w) jU kbar p n hcard
      (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r)

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] [IsAlgClosed kbar] in
/-- `Stacks.EtaleCohomology.higherDirectImageStalkIsogenyIso` commutes with the rational Frobenius
on `Hʳ_c` of the fibre. -/
theorem higherDirectImageStalkIsogenyIso_frobenius :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard
        (LAdicSheaf.inverseImage (fibreι B g w hB) (LAdicSheaf.flatModel B ℓ G)) r ≫
      (higherDirectImageStalkIsogenyIso B ℓ g w hB kbar G r jU).hom =
    (higherDirectImageStalkIsogenyIso B ℓ g w hB kbar G r jU).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard
        (LAdicSheaf.inverseImage (fibreι B g w hB) G) r :=
  (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B
    (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar
    (LAdicSheaf.inverseImageMap (fibreι B g w hB)
      (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (LAdicSheaf.inverseImageMap (fibreι B g w hB)
      (LAdicSheaf.toTorsionFreeModel G (LAdicSheaf.torsionBound G))) _ _ _ r
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ]
      (fibreStructureResidueField B g w) jU kbar p n
      hcard)).symm

omit [IsAlgClosed kbar] in
/-- **The proper base change chain at the stalk carries the Frobenius of `κ(w)` on
`n ↦ H⁰_c(Spec κ̄, i⁻¹ (Rʳ g_! G)ₙ)` to `π^*` on `Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)`**, given the
Leray comparison `Ψ` with Frobenius. -/
theorem LAdicSheaf.higherDirectImageStalkChainIso_frobenius
    (hΨ : Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (Functor.whiskerLeft
          (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
          (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)) ≫ Ψ.hom =
      Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (compactSupportSheafFrobenius ℤ_[ℓ]
          (fibreStructureResidueField B g w) jU kbar p n hcard r)) :
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
        (LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r))
        (residuePointFrobenius B ℓ w kbar p n hcard)) ≫
      (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).hom =
    (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard
        (LAdicSheaf.inverseImage (fibreι B g w hB) G) r := by
  have := hcond.fst
  exact comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkStableImageIso_frobenius B ℓ g jg w kbar p n hcard G r hcond))
    (comm_comp_of_comm (higherDirectImageStalkStableIso_frobenius B ℓ g jg w kbar p n
      hcard G r hcond)
    (comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkBaseChangeIso_frobenius B ℓ g jg w hB kbar p n hcard G r jgw))
    (comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkLerayIso_frobenius B ℓ g w hB kbar p n hcard G r jgw jU Ψ hΨ))
    (comm_comp_of_comm (functor_map_comp_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ))
      (higherDirectImageStalkFibreLevelIso_frobenius B ℓ g w hB kbar p n hcard G r jU))
    (comm_comp_of_comm (higherDirectImageStalkCohomologyIso_frobenius B ℓ g w hB kbar p n
      hcard G r jU)
      (higherDirectImageStalkIsogenyIso_frobenius B ℓ g w hB kbar p n hcard G r jU))))))

end Frobenius

end Chain

end Stacks.EtaleCohomology
