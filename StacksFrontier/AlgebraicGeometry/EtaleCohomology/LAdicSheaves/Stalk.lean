module

public import Mathlib.NumberTheory.Padics.RingHoms
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FiniteLevelStalk

/-!
# The stalk of an ℓ-adic sheaf

The stalk of an ℓ-adic sheaf at a geometric point is the inverse limit of its module-valued
finite-level étale stalks, taken as a module over the ℓ-adic integers `ℤ_[ℓ]`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.stalk` — the module of compatible finite-level germs.
* `Stacks.EtaleCohomology.LAdicSheaf.stalkProjection` — its projection to a finite level.

## Implementation notes

Level `n` has coefficients in `ℤ/ℓⁿ⁺¹ℤ`, and its `ℤ_[ℓ]`-action is through reduction modulo
`ℓⁿ⁺¹`; the canonical transition is linear for these actions. The stalk is the submodule of
the product of the finite-level stalks cut out by transition compatibility, so its projections
are module maps without choosing representatives.

## References

* [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The `ℤ_[ℓ]`-action on a finite-level stalk, through reduction of `ℤ_[ℓ]` modulo
`ℓⁿ⁺¹`. -/
public instance LAdicSheaf.levelStalkModule (F : LAdicSheaf B X ℓ) (x : GeometricPoint X.1)
    (n : ℕ) : Module (PadicInt ℓ) (finiteLevelStalk B X ℓ F x n) :=
  Module.compHom _ (PadicInt.toZModPow (n + 1))

/-- The canonical transition between consecutive finite-level stalks, read as a map of
`ℤ_[ℓ]`-modules. -/
public noncomputable def LAdicSheaf.stalkTransition (F : LAdicSheaf B X ℓ)
    (x : GeometricPoint X.1) (n : ℕ) :
    finiteLevelStalk B X ℓ F x (n + 1) →ₗ[PadicInt ℓ] finiteLevelStalk B X ℓ F x n where
  toFun := (finiteLevelStalkTransition B X ℓ F x n).hom
  map_add' := map_add _
  map_smul' a b := by
    change (finiteLevelStalkTransition B X ℓ F x n).hom ((PadicInt.toZModPow (n + 2) a) • b) =
      (PadicInt.toZModPow (n + 1) a) • (finiteLevelStalkTransition B X ℓ F x n).hom b
    rw [map_smul]
    change (finiteLevelRingHom ℓ n (PadicInt.toZModPow (n + 2) a)) •
        (finiteLevelStalkTransition B X ℓ F x n).hom b = _
    simp [finiteLevelRingHom, PadicInt.cast_toZModPow (n + 1) (n + 2) (n + 1).le_succ a]

/-- The inverse limit of the finite-level stalks, as a submodule of their product: the
compatible families of finite-level germs. -/
public noncomputable def LAdicSheaf.stalkSubmodule (F : LAdicSheaf B X ℓ)
    (x : GeometricPoint X.1) :
    Submodule (PadicInt ℓ) (∀ n, finiteLevelStalk B X ℓ F x n) where
  carrier := {a | ∀ n, LAdicSheaf.stalkTransition B X ℓ F x n (a (n + 1)) = a n}
  zero_mem' _ := by simp
  add_mem' ha hb n := by simp [ha n, hb n]
  smul_mem' c a ha n := by simp [ha n]

/-- The stalk of an ℓ-adic sheaf at a geometric point: the inverse limit of its finite-level
stalks, as a `ℤ_[ℓ]`-module. -/
@[stacks 03UQ "stalk_of_a_sheaf", sga "4½ Rapport 2.2" "fiber definition"]
public abbrev LAdicSheaf.stalk (F : LAdicSheaf B X ℓ) (x : GeometricPoint X.1) :
    Type (u + 1) :=
  ↥(LAdicSheaf.stalkSubmodule B X ℓ F x)

/-- The canonical projection of the stalk of an ℓ-adic sheaf to its level-`n` stalk. -/
public noncomputable def LAdicSheaf.stalkProjection (F : LAdicSheaf B X ℓ)
    (x : GeometricPoint X.1) (n : ℕ) :
    LAdicSheaf.stalk B X ℓ F x →ₗ[PadicInt ℓ] finiteLevelStalk B X ℓ F x n where
  toFun a := a.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Stacks.EtaleCohomology

end
