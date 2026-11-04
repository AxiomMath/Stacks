module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModelLevelZeroFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevelPowExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness

/-!
# The level zero of the flat model of the sheaf of a representation

Let `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous and `ℱ_ρ` its ℓ-adic sheaf. The levels of `ℱ_ρ` are
flat (`Stacks.EtaleCohomology.powExact_representationLevelSheaf`), so the level zero of the
torsion-free model `ℓᴺ ℱ_ρ` is the level zero of `ℱ_ρ`, whatever `N`
(`Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelLevelZeroIsoOfPowExact`): read as a sheaf of
`ℤ_ℓ`-modules on Mathlib's small étale site, it is the restriction of scalars along
`ℤ_ℓ → ℤ/ℓ` of the lisse sheaf of `(ℤ/ℓ)^r` with `π₁` acting through `ρ` modulo `ℓ`
(`Stacks.EtaleCohomology.representationLAdicSheafFlatModelLevelZeroIso`). This is the bottom level
`K'₀` of the flat model of the family sheaf in Laumon's argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), on which `R¹pr₁!` is computed fibre by
fibre.

## Main results

* `Stacks.EtaleCohomology.representationLAdicSheafFlatModelLevelZeroIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]

/-- `ℓⁿ` is nonzero, for the finiteness of `ℤ/ℓⁿ`. -/
local instance neZero_pow_representationFlatModelLevelZero (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- **The level zero of the flat model of `ℱ_ρ` is the lisse sheaf of `(ℤ/ℓ)^r`**, with `π₁`
acting through `ρ` modulo `ℓ`, read as a sheaf of `ℤ_ℓ`-modules on Mathlib's small étale site. -/
def representationLAdicSheafFlatModelLevelZeroIso :
    towerObj (LAdicSheaf.padicTower B X ℓ (LAdicSheaf.flatModel B ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ))) 0 ≅
      (etaleModuleRestrictScalars (PadicInt.toZModPow (0 + 1)) X.1).obj
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (0 + 1)))).obj
          (levelModule.{u + 1, u + 1} ρ hρ (0 + 1))) :=
  letI F := representationLAdicSheaf B X x
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ
  (LAdicSheaf.padicTowerObjIsoOfLevelIso (F₁ := LAdicSheaf.flatModel B ℓ F) (F₂ := F) 0
      (LAdicSheaf.torsionFreeModelLevelZeroIsoOfPowExact F
        (LAdicSheaf.powExact_underlyingLAdicLevel_representationLAdicSheaf B X x ρ hρ) _) :
      towerObj (LAdicSheaf.padicTower B X ℓ (LAdicSheaf.flatModel B ℓ F)) 0 ≅
        towerObj (LAdicSheaf.padicTower B X ℓ F) 0) ≪≫
    (((sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (0 + 1))).app
      (F.level 0)).symm :
      towerObj (LAdicSheaf.padicTower B X ℓ F) 0 ≅
        (etaleModuleRestrictScalars (PadicInt.toZModPow (0 + 1)) X.1).obj
          (LAdicSheaf.etaleLevel B X ℓ F 0)) ≪≫
    (etaleModuleRestrictScalars (PadicInt.toZModPow (0 + 1)) X.1).mapIso
      ((SmallEtale.sheafEquiv B X.1 X.property
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (0 + 1))))).functor.mapIso
        (eqToIso (lisseSheaf_obj_levelModule B X x ρ hρ (0 + 1)).symm))

end Stacks.EtaleCohomology

end
