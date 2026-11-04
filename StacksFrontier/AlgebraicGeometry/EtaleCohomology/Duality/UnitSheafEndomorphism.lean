module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.CategoryTheory.Abelian.ExtTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# Endomorphisms of the constant sheaf on a preconnected scheme

On a preconnected scheme `X` every endomorphism of the constant sheaf `Λ_X = ℤ/N` of
`ℤ/N`-modules on the small étale site is multiplication by a scalar: maps out of `Λ_X` are global
sections of the target, and the global sections of `Λ_X` are the locally constant maps, which are
constant. Hence conjugating an `Ext` class between constant sheaves by an endomorphism and a left
inverse of it does nothing: the two scalars multiply to one.

## Main results

* `Stacks.EtaleCohomology.KummerFlag.exists_eq_smul_id`
* `Stacks.EtaleCohomology.KummerFlag.sandwich_eq_self_of_comp_eq_id`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

variable {X : Scheme.{u}} {N : ℕ}

/-- The identification of the endomorphisms of `Λ_X` with the locally constant maps. -/
def unitSheafEndEquiv (N : ℕ) :
    (unitSheaf (X := X) N ⟶ unitSheaf N) ≃ LocallyConstant X (ULift.{u + 1} (ZMod N)) :=
  (homUnitSheafEquiv N _).trans (unitSheafSectionsEquiv N)

/-- `unitSheafEndEquiv` is additive. -/
theorem unitSheafEndEquiv_add (f g : unitSheaf (X := X) N ⟶ unitSheaf N) :
    unitSheafEndEquiv N (f + g) = unitSheafEndEquiv N f + unitSheafEndEquiv N g := by
  simp only [unitSheafEndEquiv, homUnitSheafEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit,
    Functor.map_add, Preadditive.comp_add, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_add]
  exact map_add (((sheafToPresheaf _ _).mapIso
    (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0} (ZMod N) X
      (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))).app
        (op (etaleSiteTerminal X))).toLinearEquiv _ _

/-- `unitSheafEndEquiv` commutes with multiplication by a natural number. -/
theorem unitSheafEndEquiv_nsmul (m : ℕ) (f : unitSheaf (X := X) N ⟶ unitSheaf N) :
    unitSheafEndEquiv N (m • f) = m • unitSheafEndEquiv N f := by
  induction m with
  | zero =>
    rw [zero_smul, zero_smul]
    have h := unitSheafEndEquiv_add (X := X) (N := N) 0 0
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  | succ m ih => rw [succ_nsmul, unitSheafEndEquiv_add, ih, succ_nsmul]

/-- `unitSheafEndEquiv` sends the identity of `Λ_X` to the constant map `1`. -/
theorem unitSheafEndEquiv_id (x : X) :
    unitSheafEndEquiv N (𝟙 (unitSheaf (X := X) N)) x = ULift.up 1 := by
  simp only [unitSheafEndEquiv, homUnitSheafEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit]
  show (unitSheafSectionsEquiv N) (((constantSheafAdj X.smallEtaleTopology
    (ModuleCat.{u + 1} (ZMod N)) (etaleSiteTerminalIsTerminal X)).unit.app _).hom (ULift.up 1))
      x = _
  rw [Stacks.ConstantSheaf.constantSheafAdj_unit_app]
  have h := constantSheafToSmallEtaleLocallyConstantMapsModule_unit.{u, 0} (ZMod N) X
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) (op (etaleSiteTerminal X)) (ULift.up 1)
  exact congrArg (fun f : LocallyConstant X (ULift.{u + 1} (ZMod N)) => f x) h

/-- **Every endomorphism of the constant sheaf of a preconnected scheme is a scalar.** -/
theorem exists_eq_smul_id [NeZero N] [PreconnectedSpace X]
    (w : unitSheaf (X := X) N ⟶ unitSheaf N) : ∃ c : ZMod N, w = c • 𝟙 _ := by
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    set c := (unitSheafEndEquiv N w x₀).down with hc
    refine ⟨c, (unitSheafEndEquiv N).injective (LocallyConstant.ext fun x => ?_)⟩
    have e : c • 𝟙 (unitSheaf (X := X) N) = c.val • 𝟙 _ := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_zmod_val]
    rw [e, unitSheafEndEquiv_nsmul, LocallyConstant.smul_apply, unitSheafEndEquiv_id,
      (unitSheafEndEquiv N w).apply_eq_of_preconnectedSpace x x₀]
    apply ULift.ext
    show c = (c.val • (1 : ZMod N))
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  · have : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨0, (unitSheafEndEquiv N).injective ?_⟩
    ext x
    exact isEmptyElim x

/-- **Conjugation by an endomorphism of the constant sheaf and a left inverse of it is trivial**
on `Ext` between constant sheaves of a preconnected scheme. -/
theorem sandwich_eq_self_of_comp_eq_id [NeZero N] [PreconnectedSpace X]
    {w w' : unitSheaf (X := X) N ⟶ unitSheaf N} (h : w' ≫ w = 𝟙 _) {n : ℕ}
    (x : Ext (unitSheaf (X := X) N) (unitSheaf (X := X) N) n) :
    Stacks.ExtTransport.sandwich w' w n x = x := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_id w
  obtain ⟨c', rfl⟩ := exists_eq_smul_id w'
  rw [Stacks.ExtTransport.sandwich_apply, Ext.mk₀_smul, Ext.mk₀_smul, Ext.smul_comp, Ext.comp_smul,
    Ext.mk₀_id_comp, Ext.comp_mk₀_id, smul_smul]
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at h
  simpa [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp] using
    congrArg (fun r => (Ext.mk₀ r).comp x (zero_add n)) h

end Stacks.EtaleCohomology.KummerFlag

end
