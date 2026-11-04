module

public import Mathlib
public import StacksFrontier.Algebra.Module.ProZeroTower

/-!
# The adic completion as the compatible sequences of the quotient tower

Mathlib's `AdicCompletion I M` is the submodule of compatible families in
`∀ n, M ⧸ (Iⁿ • ⊤)`, with compatibility imposed for *every* pair `m ≤ n`. The tower
`Stacks.ProZero.towerSections` of `StacksFrontier/Algebra/Module/ProZeroTower.lean` imposes it only
for the successor transitions, which is the shape in which a tower of modules of sections is
written down. This file identifies the two, and so makes the pro-zero criterion of that file
applicable to a map out of a module that happens to be adically complete:
`Stacks.ProZero.bijective_toAdicTowerSections` says that for an `I`-adically complete module the
canonical map into the compatible sequences of its own quotient tower is a bijection.

## Main definitions

* `Stacks.ProZero.adicTower`, `Stacks.ProZero.adicTowerTransition` — the tower `M ⧸ Iⁿ M` and its
  successor transition maps.
* `Stacks.ProZero.adicTowerSectionsEquiv` — its compatible sequences are `AdicCompletion I M`.
* `Stacks.ProZero.toAdicTowerSections` — the canonical map from `M`.

## Main results

* `Stacks.ProZero.towerMapLE_adicTower` — the composite transition maps of the tower are
  Mathlib's `AdicCompletion.transitionMap`.
* `Stacks.ProZero.bijective_toAdicTowerSections` — for an `I`-adically complete module the
  canonical map into the compatible sequences of the quotient tower is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace Stacks.ProZero

variable {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{v} A)

/-- The tower of quotients `M ⧸ Iⁿ M`. -/
abbrev adicTower (n : ℕ) : ModuleCat.{v} A := ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))

/-- The successor transition maps of the tower `M ⧸ Iⁿ M`. -/
def adicTowerTransition (n : ℕ) : adicTower I M (n + 1) ⟶ adicTower I M n :=
  ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ n))

/-- `AdicCompletion.transitionMap` sends the class of `x` modulo `Iⁿ M` to its class modulo
`Iᵐ M`. -/
theorem transitionMap_mk {m n : ℕ} (h : m ≤ n) (x : M) :
    AdicCompletion.transitionMap I M h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : M ⧸ (I ^ m • (⊤ : Submodule A M))) := rfl

/-- The composite transition maps of the tower `M ⧸ Iⁿ M` are Mathlib's
`AdicCompletion.transitionMap`. -/
theorem towerMapLE_adicTower {n m : ℕ} (h : n ≤ m) :
    towerMapLE (adicTower I M) (adicTowerTransition I M) h =
      ModuleCat.ofHom (AdicCompletion.transitionMap I M h) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [towerMapLE_self]
      exact ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ rfl))
  | succ m hnm ih =>
      rw [← towerMapLE_trans (adicTower I M) (adicTowerTransition I M) hnm (Nat.le_succ m), ih,
        towerMapLE_succ]
      exact ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ rfl))

/-- The compatible sequences of the tower `M ⧸ Iⁿ M` are the `I`-adic completion of `M`. The two
differ only in whether compatibility is imposed for the successor transitions alone or for all of
them, and `Stacks.ProZero.towerSections_apply_le` says that is the same condition. -/
def adicTowerSectionsEquiv :
    towerSections (adicTower I M) (adicTowerTransition I M) ≃ₗ[A] AdicCompletion I M where
  toFun x := ⟨x.1, fun {m n} h ↦
    (congrArg (fun φ : adicTower I M n ⟶ adicTower I M m ↦ φ (x.1 n))
        (towerMapLE_adicTower I M h)).symm.trans
      (towerSections_apply_le (adicTower I M) (adicTowerTransition I M) x h)⟩
  invFun y := ⟨y.1, fun n ↦ y.property (Nat.le_succ n)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The canonical map from `M` to the compatible sequences of its quotient tower, sending `x` to
the sequence of its classes modulo the `Iⁿ M`. -/
def toAdicTowerSections : M →ₗ[A] towerSections (adicTower I M) (adicTowerTransition I M) where
  toFun x := ⟨fun n ↦ Submodule.Quotient.mk x, fun n ↦ transitionMap_mk I M (Nat.le_succ n) x⟩
  map_add' x y := Subtype.ext (funext fun n ↦ by simp)
  map_smul' a x := Subtype.ext (funext fun n ↦ by simp)

/-- Composing the canonical map into the compatible sequences of the quotient tower with
`Stacks.ProZero.adicTowerSectionsEquiv` gives the canonical map `AdicCompletion.of I M`. -/
theorem adicTowerSectionsEquiv_toAdicTowerSections :
    (adicTowerSectionsEquiv I M).toLinearMap ∘ₗ toAdicTowerSections I M =
      AdicCompletion.of I M :=
  LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

/-- **For an adically complete module the canonical map into the compatible sequences of its own
quotient tower is a bijection.** This is `AdicCompletion.of_bijective` transported along the
identification of those compatible sequences with the adic completion. -/
theorem bijective_toAdicTowerSections [IsAdicComplete I M] :
    Function.Bijective (toAdicTowerSections I M) := by
  have hcomp : (adicTowerSectionsEquiv I M) ∘ (toAdicTowerSections I M) =
      AdicCompletion.of I M :=
    funext fun x ↦ congrFun (congrArg (fun φ : M →ₗ[A] AdicCompletion I M ↦ (φ : M → _))
      (adicTowerSectionsEquiv_toAdicTowerSections I M)) x
  have hb : Function.Bijective ((adicTowerSectionsEquiv I M) ∘ (toAdicTowerSections I M)) := by
    rw [hcomp]
    exact AdicCompletion.of_bijective I M
  exact (Function.Bijective.of_comp_iff' (adicTowerSectionsEquiv I M).bijective _).1 hb

end Stacks.ProZero

end
