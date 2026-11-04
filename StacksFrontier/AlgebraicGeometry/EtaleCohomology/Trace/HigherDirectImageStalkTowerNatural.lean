module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekEnd

/-!
# Naturality of the towers in the proper base change at a stalk

The proof of
`Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek` ([Tag
03VH](https://stacks.math.columbia.edu/tag/03VH)) identifies towers of `ℤ_ℓ`-modules through
explicit isomorphisms. This file proves that these isomorphisms are natural in the morphisms of
ℓ-adic sheaves: the tower of levels of an inverse image
(`Stacks.EtaleCohomology.LAdicSheaf.padicTowerInverseImageIso`), the tower cohomology
(`Stacks.EtaleCohomology.LAdicSheaf.padicTowerCohomologyIso`), and the map from the torsion-free
model `ℓᴺ G ⟶ G`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerInverseImageIso_hom_naturality`
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerCohomologyIso_hom_naturality`
* `Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelMap_comp_fromTorsionFreeModel`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

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

/-- **The tower of levels of an inverse image is natural in the sheaf.** -/
theorem LAdicSheaf.padicTowerInverseImageIso_hom_naturality {X X' : B.Scheme} [IsNoetherian X.1]
    [IsNoetherian X'.1] (g : X' ⟶ X) {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)) ≫
      (LAdicSheaf.padicTowerInverseImageIso B ℓ g G).hom =
    (LAdicSheaf.padicTowerInverseImageIso B ℓ g F).hom ≫
      LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap g φ) := by
  ext n : 2
  induction n using Opposite.rec with
  | op n => exact padicLevelInverseImageIso_hom_naturality B g ℓ n (φ.app n)

section Cohomology

variable {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The tower cohomology is natural in the sheaf.** -/
theorem LAdicSheaf.padicTowerCohomologyIso_hom_naturality {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ G) (i : ℤ) :
    Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
        (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i) ≫
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar G i).hom =
    (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i := by
  ext n : 2
  simp only [NatTrans.comp_app, LAdicSheaf.padicTowerCohomologyIso]
  rfl

end Cohomology

section TorsionFree

variable {X : B.Scheme} [IsNoetherian X.1]

/-- **The map `ℓᴺ G ⟶ G` from the torsion-free model is natural in `G`.** -/
theorem LAdicSheaf.torsionFreeModelMap_comp_fromTorsionFreeModel
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) (N : ℕ) :
    LAdicSheaf.torsionFreeModelMap φ N ≫ LAdicSheaf.fromTorsionFreeModel G N =
      LAdicSheaf.fromTorsionFreeModel F N ≫ φ := by
  refine LAdicSheaf.Hom.ext _ _ _ fun n => ?_
  apply (underlyingLevelFunctor B X ℓ n).map_injective
  refine (cancel_epi (LAdicSheaf.torsionFreeModelπ F N n)).1 ?_
  show LAdicSheaf.torsionFreeModelπ F N n ≫ (underlyingLevelFunctor B X ℓ n).map
      ((LAdicSheaf.torsionFreeModelMap φ N).app n ≫ (LAdicSheaf.fromTorsionFreeModel G N).app n) =
    LAdicSheaf.torsionFreeModelπ F N n ≫ (underlyingLevelFunctor B X ℓ n).map
      ((LAdicSheaf.fromTorsionFreeModel F N).app n ≫ φ.app n)
  refine (congrArg (_ ≫ ·) ((underlyingLevelFunctor B X ℓ n).map_comp
    ((LAdicSheaf.torsionFreeModelMap φ N).app n)
    ((LAdicSheaf.fromTorsionFreeModel G N).app n))).trans
    (Eq.trans ?_ (congrArg (_ ≫ ·) ((underlyingLevelFunctor B X ℓ n).map_comp
      ((LAdicSheaf.fromTorsionFreeModel F N).app n) (φ.app n))).symm)
  have e (H : LAdicSheaf.{u, u + 1} B X ℓ) :
      LAdicSheaf.torsionFreeModelπ H N n ≫ LAdicSheaf.fromTorsionFreeModelUnderlying H N n =
        (ℓ ^ N) • LAdicSheaf.underlyingTransitionLE B X ℓ H (Nat.le_add_left n N) := by
    simp only [LAdicSheaf.fromTorsionFreeModelUnderlying]
    rw [LAdicSheaf.torsionFreeModelπ_ι_assoc, Preadditive.nsmul_comp, Category.id_comp]
  have hnat : (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫
      LAdicSheaf.underlyingTransitionLE B X ℓ G (Nat.le_add_left n N) =
      LAdicSheaf.underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) ≫
        (underlyingLevelFunctor B X ℓ n).map (φ.app n) :=
    ((LAdicSheaf.underlyingLAdicTowerMap B X ℓ φ).naturality
      (homOfLE (Nat.le_add_left n N)).op).symm
  calc _ = (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫
        LAdicSheaf.torsionFreeModelπ G N n ≫
          (underlyingLevelFunctor B X ℓ n).map (LAdicSheaf.fromTorsionFreeModelApp G N n) :=
        LAdicSheaf.torsionFreeModelπ_map_app_assoc φ N n _
    _ = (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫
        ((ℓ ^ N) • LAdicSheaf.underlyingTransitionLE B X ℓ G (Nat.le_add_left n N)) := by
        rw [LAdicSheaf.underlyingLevelFunctor_map_fromTorsionFreeModelApp, e]
    _ = (ℓ ^ N) • (LAdicSheaf.underlyingTransitionLE B X ℓ F (Nat.le_add_left n N) ≫
        (underlyingLevelFunctor B X ℓ n).map (φ.app n)) := by
        rw [Preadditive.comp_nsmul, hnat]
    _ = LAdicSheaf.torsionFreeModelπ F N n ≫
          (underlyingLevelFunctor B X ℓ n).map (LAdicSheaf.fromTorsionFreeModelApp F N n) ≫
            (underlyingLevelFunctor B X ℓ n).map (φ.app n) := by
        rw [LAdicSheaf.underlyingLevelFunctor_map_fromTorsionFreeModelApp, ← Category.assoc, e,
          Preadditive.nsmul_comp]

end TorsionFree

end Stacks.EtaleCohomology
