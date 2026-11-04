module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision

/-!
# `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` as the rational limit of a tower of sheaves

The compactly supported ℓ-adic cohomology `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` of an ℓ-adic sheaf `F`
(`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomology`) is built from
the inverse system `n ↦ Hⁱ_c(X_k̄, Fₙ)`.  The levels of `F`, read on Mathlib's small étale site,
form a tower of sheaves of `ℤ_ℓ`-modules (`Stacks.EtaleCohomology.LAdicSheaf.padicTower`) whose
image under the functor `G ↦ Hⁱ_c(X_k̄, G)`
(`Stacks.EtaleCohomology.compactSupportSheafCohomology`) is this inverse system, with the geometric
Frobenius matching on both sides.  Hence a bound on the absolute values of the Frobenius
characteristic roots on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the same bound on the rational limit of the tower.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.padicTower`: the tower of levels of `F` on Mathlib's small
  étale site.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerCohomologyIso`: its `Hⁱ_c` is the inverse system
  `n ↦ Hⁱ_c(X_k̄, Fₙ)`.

## Main results

* `LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff`:
  the weight bound on `π_X^*` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the one on the rational limit of the
  tower.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The tower of levels `n ↦ Fₙ`** of an ℓ-adic sheaf, as sheaves of `ℤ_ℓ`-modules on Mathlib's
small étale site of `X`, with the transition maps of `F`. -/
public def LAdicSheaf.padicTower (F : LAdicSheaf B X ℓ) :
    ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1 :=
  Functor.ofOpSequence
    (X := fun n => (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
      (LAdicSheaf.padicLevel B X ℓ F n))
    (fun n => (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicTransition B X ℓ F n))

/-- The map of the tower of levels from `n + 1` to `n` is the transition map of `F`. -/
public theorem LAdicSheaf.padicTower_map_succ (F : LAdicSheaf B X ℓ) (n : ℕ) :
    (LAdicSheaf.padicTower B X ℓ F).map (homOfLE (n.le_add_right 1)).op =
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicTransition B X ℓ F n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **`Hⁱ_c` of the tower of levels is the inverse system `n ↦ Hⁱ_c(X_k̄, Fₙ)`.** -/
public def LAdicSheaf.padicTowerCohomologyIso (F : LAdicSheaf B X ℓ) (i : ℤ) :
    LAdicSheaf.padicTower B X ℓ F ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i ≅
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i where
  hom := NatTrans.ofOpSequence (fun _ => 𝟙 _) (fun n => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    change (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).map
      ((LAdicSheaf.padicTower B X ℓ F).map (homOfLE (n.le_add_right 1)).op) = _
    rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ,
      LAdicSheaf.padicTower_map_succ]
    rfl)
  inv := NatTrans.ofOpSequence (fun _ => 𝟙 _) (fun n => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    change _ = (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).map
      ((LAdicSheaf.padicTower B X ℓ F).map (homOfLE (n.le_add_right 1)).op)
    rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ,
      LAdicSheaf.padicTower_map_succ]
    rfl)
  hom_inv_id := NatTrans.ext (funext fun _ => Category.comp_id _)
  inv_hom_id := NatTrans.ext (funext fun _ => Category.comp_id _)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The identification of the tower cohomology with the inverse system of `F` carries the
canonical Frobenius of the tower to `π_X^*` on the inverse system. -/
public theorem LAdicSheaf.padicTowerCohomologyIso_hom_frobenius (F : LAdicSheaf B X ℓ) (i : ℤ) :
    Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i) ≫
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).hom =
    (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) := by
  ext n : 2
  rfl

/-- **The weight bound on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the weight bound on the rational limit of the
tower of levels**, for the canonical geometric Frobenius on both. -/
public theorem
    LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff
    (F : LAdicSheaf B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B X ℓ F ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i))]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom ↔
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim.{u + 1} (ℓ := ℓ)).map
        (Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
          (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom := by
  let e := (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i)
  let L : ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B X ℓ F ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) ≃ₗ[ℚ_[ℓ]]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    e.toLinearEquiv
  have hcomm : ∀ v, L (((rationalLim.{u + 1} (ℓ := ℓ)).map
      (Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom v) =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom
        (L v) := fun v => by
    have h := congrArg (fun t => ((rationalLim.{u + 1} (ℓ := ℓ)).map t).hom v)
      (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f j kbar p q hcard F i)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hcomm' : ∀ v, L.symm
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom
        v) =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom (L.symm v) := fun v => by
    rw [L.symm_apply_eq, hcomm, L.apply_symm_apply]
  exact ⟨fun h => h.of_surjective (p := L.symm.toLinearMap) hcomm' L.symm.surjective,
    fun h => h.of_injective (j := L.symm.toLinearMap) hcomm' L.symm.injective⟩

end Stacks.EtaleCohomology

end
