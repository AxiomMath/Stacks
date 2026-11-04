module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# Global types of modules under `𝓕 ↦ 𝓕^a`

Descent, Lemma 05VG compares fifteen properties of modules across the comparison
`𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX.  This file carries the comparison as the
**associated-module functor itself**, so the statements below have no hypothesis beyond
`𝓕` being quasi-coherent, which is the source category of 03DX.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.QcohTypeComparison

universe w v₁ u₁ v₂ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {R₁ : Sheaf J₁ RingCat.{w}}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{w}}
  [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (Φ : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
  [PreservesColimitsOfSize.{w, w} Φ]
  (u : Φ.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)

/-- The comparison carries the free module on `I` to the free module on `I`. -/
def mapFreeIso (I : Type w) :
    Φ.obj (SheafOfModules.free (R := R₁) I) ≅ SheafOfModules.free (R := R₂) I :=
  (GlobalTypeComparison.isColimitCofanMap Φ u _
      (SheafOfModules.isColimitFreeCofan I)).coconePointUniqueUpToIso
    (SheafOfModules.isColimitFreeCofan I)

variable {Φ}

omit [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Freeness is invariant under isomorphism. -/
theorem isFree_of_iso {F G : SheafOfModules.{w} R₁} (e : F ≅ G) (h : G.IsFree) : F.IsFree := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := h
  exact ⟨B, fun b ↦ ι b ≫ e.inv, ⟨hc.ofIsoColimit (Cocone.ext e.symm fun b ↦ by simp)⟩⟩

/-- A free module is free. -/
theorem isFree_free (I : Type w) : (SheafOfModules.free (R := R₁) I).IsFree :=
  ⟨I, SheafOfModules.ιFree, ⟨SheafOfModules.isColimitFreeCofan I⟩⟩

/-- The free module on `ULift (Fin n)` is a coproduct of `n` copies of the structure sheaf,
indexed by `Fin n` itself. -/
def isColimitFreeCofanFin (n : ℕ) :
    IsColimit (Cofan.mk (SheafOfModules.free (R := R₁) (ULift.{w} (Fin n)))
      fun i : Fin n ↦ (SheafOfModules.freeCofan (R := R₁)
        (ULift.{w} (Fin n))).inj (Equiv.ulift.symm i)) :=
  (Cofan.isColimitEquivOfEquiv (ε := Equiv.ulift.symm)
    (SheafOfModules.freeCofan (R := R₁) (ULift.{w} (Fin n))))
    (SheafOfModules.isColimitFreeCofan _)

/-- The free module on `ULift (Fin n)` is finite free. -/
theorem isFiniteFree_free_ulift (n : ℕ) :
    SheafOfModules.IsFiniteFree R₁ (SheafOfModules.free (R := R₁) (ULift.{w} (Fin n))) :=
  (SheafOfModules.isFiniteFree_iff_exists_isColimit R₁ _).2 ⟨n, _, ⟨isColimitFreeCofanFin n⟩⟩

variable (Φ) (P : ObjectProperty (SheafOfModules.{w} R₁))

omit [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [PreservesColimitsOfSize.{w, w} Φ] in
/-- Two objects with the property `P` which the comparison identifies are isomorphic:
the comparison is fully faithful on the full subcategory cut out by `P`. -/
theorem nonempty_iso_of_mapIso (hff : (P.ι ⋙ Φ).FullyFaithful)
    {F G : SheafOfModules.{w} R₁} (hF : P F) (hG : P G) (e : Φ.obj F ≅ Φ.obj G) :
    Nonempty (F ≅ G) :=
  ⟨P.ι.mapIso (hff.preimageIso (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) e)⟩

variable (hff : (P.ι ⋙ Φ).FullyFaithful)
  (hfree : ∀ I : Type w, P (SheafOfModules.free (R := R₁) I))

include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (1), at the comparison
functor itself.**  A module with the property `P` is free if and only if its image under the
comparison is free. -/
theorem isFree_iff {F : SheafOfModules.{w} R₁} (hF : P F) :
    F.IsFree ↔ (Φ.obj F).IsFree := by
  constructor
  · rintro ⟨B, ι, ⟨hc⟩⟩
    exact ⟨B, _, ⟨GlobalTypeComparison.isColimitCofanMap Φ u ι hc⟩⟩
  · rintro ⟨B, κ, ⟨hc⟩⟩
    obtain ⟨e⟩ := nonempty_iso_of_mapIso Φ P hff hF (hfree B)
      (hc.coconePointUniqueUpToIso (SheafOfModules.isColimitFreeCofan B) ≪≫
        (mapFreeIso Φ u B).symm)
    exact isFree_of_iso e (isFree_free B)

/-- The comparison functor `Φ` preserves colimits indexed by small categories in universe `0`. -/
local instance : PreservesColimitsOfSize.{0, 0} Φ := preservesColimitsOfSize_shrink _

include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (2), at the comparison
functor itself.**  A module with the property `P` is finite free if and only if its image
under the comparison is finite free, with the same rank. -/
theorem isFiniteFree_iff {F : SheafOfModules.{w} R₁} (hF : P F) :
    SheafOfModules.IsFiniteFree R₁ F ↔ SheafOfModules.IsFiniteFree R₂ (Φ.obj F) := by
  rw [SheafOfModules.isFiniteFree_iff_exists_isColimit,
    SheafOfModules.isFiniteFree_iff_exists_isColimit]
  constructor
  · rintro ⟨n, ι, ⟨hc⟩⟩
    exact ⟨n, _, ⟨GlobalTypeComparison.isColimitCofanMap Φ u ι hc⟩⟩
  · rintro ⟨n, κ, ⟨hc⟩⟩
    obtain ⟨e⟩ := nonempty_iso_of_mapIso Φ P hff hF (hfree (ULift.{w} (Fin n)))
      (hc.coconePointUniqueUpToIso (isColimitFreeCofanFin (R₁ := R₂) n) ≪≫
        (mapFreeIso Φ u (ULift.{w} (Fin n))).symm)
    exact (SheafOfModules.isFiniteFree_iff_exists_isColimit R₁ F).1
      (Stacks.SheafOfModules.isFiniteFree_of_iso e.symm (isFiniteFree_free_ulift n))

end Stacks.Sheaves.QcohTypeComparison

namespace AlgebraicGeometry

universe u

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of the indicated big site preserves all colimits, recorded
at the retyping `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOfSheaf`. -/
theorem preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{w, w'} (τ : SiteKind) :
    PreservesColimitsOfSize.{w, w'} (baseAssociatedModuleOfSheaf B S hS τ) :=
  inferInstanceAs (PreservesColimitsOfSize.{w, w'} (baseAssociatedModule B S hS τ))

/-- The associated module of the structure sheaf of `S` is the structure sheaf of the
indicated big site. -/
def baseAssociatedModuleUnitIso (τ : SiteKind) :
    (baseAssociatedModuleOfSheaf B S hS τ).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit (FibredSite.baseRingStructureSheaf B S hS τ) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} (baseStructureMap B S hS τ))
    (isIso_basePullbackObjUnitToUnit B S hS τ)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (1), on the big site.**  A
quasi-coherent `𝒪_S`-module is free if and only if `𝓕^a` is free as an `𝒪`-module on
`(Sch/S)_τ`. -/
@[stacks 05VG "free, big site (Sch/S)_τ at every τ, at the comparison functor of 03DX itself"]
theorem isFree_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsFree ↔ ((baseAssociatedModuleQcoh B S hS τ).obj F).IsFree :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  Stacks.Sheaves.QcohTypeComparison.isFree_iff _ (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (2), on the big site.**  A
quasi-coherent `𝒪_S`-module is finite free if and only if `𝓕^a` is finite free as an
`𝒪`-module on `(Sch/S)_τ`, and with the same rank. -/
@[stacks 05VG "finite free, big site (Sch/S)_τ at every τ, at the comparison functor of 03DX \
itself"]
theorem isFiniteFree_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    SheafOfModules.IsFiniteFree S.ringCatSheaf F.obj ↔
      SheafOfModules.IsFiniteFree (FibredSite.baseRingStructureSheaf B S hS τ)
        ((baseAssociatedModuleQcoh B S hS τ).obj F) :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  Stacks.Sheaves.QcohTypeComparison.isFiniteFree_iff _ (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

end BigFppfOver

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of the small étale site preserves all colimits, recorded at
the retyping `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`. -/
theorem preservesColimitsOfSize_associatedModuleOfSheaf.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (associatedModuleOfSheaf B S hS) :=
  inferInstanceAs (PreservesColimitsOfSize.{w, w'} (associatedModule B S hS))

/-- The associated module of the structure sheaf of `S` is the structure sheaf of the small
étale site. -/
def associatedModuleUnitIso :
    (AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf B S hS).obj
        (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit (AlgebraicGeometry.SmallEtale.structureSheaf B S hS) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS))
    (isIso_pullbackObjUnitToUnit B S hS)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (1), on the small étale
site.**  A quasi-coherent `𝒪_S`-module is free if and only if `𝓕^a` is free as an
`𝒪`-module on `S_étale`. -/
@[stacks 05VG "free, small site at τ = étale, at the comparison functor of 03DX itself"]
theorem isFree_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsFree ↔ ((associatedModuleQcoh B S hS).obj F).IsFree :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  Stacks.Sheaves.QcohTypeComparison.isFree_iff _ (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (2), on the small étale
site.**  A quasi-coherent `𝒪_S`-module is finite free if and only if `𝓕^a` is finite free as
an `𝒪`-module on `S_étale`, and with the same rank. -/
@[stacks 05VG "finite free, small site at τ = étale, at the comparison functor of 03DX itself"]
theorem isFiniteFree_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    SheafOfModules.IsFiniteFree S.ringCatSheaf F.obj ↔
      SheafOfModules.IsFiniteFree (structureSheaf B S hS)
        ((associatedModuleQcoh B S hS).obj F) :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  Stacks.Sheaves.QcohTypeComparison.isFiniteFree_iff _ (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

end SmallEtale

end AlgebraicGeometry

end
