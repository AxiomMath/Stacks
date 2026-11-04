module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap

/-!
# The transition maps of a coherent adic system

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf and `(F_n)` a coherent adic system along
`ℐ` in the sense of `Stacks.Coherent.IsCoherentAdicSystem`. The predicate is a conjunction of
three clauses, the last of them existentially quantified over an isomorphism; this file supplies
named accessors for the three clauses and derives the two facts about the transition maps that
every argument with these systems uses:

* each transition `F_{n+1} ⟶ F_n` is an epimorphism, because it *is* the quotient projection by
  `ℐ ⁿ⁺¹` up to isomorphism; hence so is every `F_n ⟶ F_m` with `m ≤ n`;
* that transition remains an *isomorphism* after dividing both sides by any `𝒥 ʳ` containing
  `ℐ ᵐ⁺¹`, since modulo such a `𝒥 ʳ` the quotient by `ℐ ᵐ⁺¹` is invisible.

The second is the engine behind the change-of-ideal equivalence [Stacks, Tag 0EHR].

## Main definitions

* `Stacks.Coherent.IsCoherentAdicSystem.quotientIso` — the isomorphism
  `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1} ≅ F_n` provided by the third clause.

## Main results

* `Stacks.Coherent.IsCoherentAdicSystem.isCoherent`,
  `idealPowerMultiple_eq_bot` and `cokernel_π_comp_quotientIso` — the three clauses.
* `Stacks.Coherent.IsCoherentAdicSystem.isQuasicoherent` — each term is quasi-coherent.
* `Stacks.Coherent.IsCoherentAdicSystem.epi_map_succ` and
  `Stacks.Coherent.IsCoherentAdicSystem.epi_map` — the transitions are epimorphisms.
* `Stacks.Coherent.IsCoherentAdicSystem.isIso_idealPowerQuotientMap_map` — a transition becomes
  an isomorphism after reduction modulo an ideal power containing `ℐ ᵐ⁺¹`.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`, which is why the annihilating exponent at `n` is `n + 1`.

The third clause of `IsCoherentAdicSystem` asserts the *existence* of a compatible isomorphism,
so `quotientIso` is `Exists.choose` and is noncomputable; `cokernel_π_comp_quotientIso` is its
specification. Two morphisms of `ℕᵒᵖ` with the same source and target are equal because `ℕᵒᵖ` is a
preorder category, so composites of transitions are compared with `Subsingleton.elim` rather than
by computing with `homOfLE`.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0EHR](https://stacks.math.columbia.edu/tag/0EHR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules}

namespace IsCoherentAdicSystem

/-- First clause: every term of a coherent adic system is coherent. -/
public theorem isCoherent (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} (F.obj (op n)) :=
  hF.1 n

/-- Second clause: the `n`-th term of a coherent adic system is annihilated by `ℐ ⁿ⁺¹`. -/
public theorem idealPowerMultiple_eq_bot (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    idealPowerMultiple I (n + 1) (F.obj (op n)) = ⊥ :=
  hF.2.1 n

/-- Third clause: the identification `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1} ≅ F_n`. -/
public def quotientIso (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    idealPowerQuotient I (n + 1) (F.obj (op (n + 1))) ≅ F.obj (op n) :=
  (hF.2.2 n).choose

/-- Under `quotientIso`, the canonical quotient projection is the transition map of the system. -/
public theorem cokernel_π_comp_quotientIso (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (F.obj (op (n + 1)))).ι ≫
        (hF.quotientIso n).hom =
      F.map (homOfLE (Nat.le_succ n)).op :=
  (hF.2.2 n).choose_spec

/-- Every term of a coherent adic system is quasi-coherent, being coherent. -/
public theorem isQuasicoherent (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    (F.obj (op n)).IsQuasicoherent :=
  have := hF.isCoherent n
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (F.obj (op n))).1

/-- Composing the successor transition with `n ⟶ m` in `ℕᵒᵖ` gives the transition from `n + 1`. -/
private theorem succ_op_comp_op_homOfLE {m n : ℕ} (hmn : m ≤ n) :
    (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op =
      (homOfLE (Nat.le_trans hmn (Nat.le_succ n))).op :=
  Subsingleton.elim _ _

/-- Each transition map of a coherent adic system is an epimorphism: it is the projection onto a
quotient, composed with an isomorphism. -/
public theorem epi_map_succ (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    Epi (F.map (homOfLE (Nat.le_succ n)).op) := by
  rw [← hF.cokernel_π_comp_quotientIso n]
  have : Epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1) (F.obj (op (n + 1)))).ι) := by
    change Epi (Cofork.ofπ _ ((cokernel.condition (C := X.Modules)
      (idealPowerMultiple I (n + 1) (F.obj (op (n + 1)))).ι).trans zero_comp.symm)).π
    exact Cofork.IsColimit.epi (cokernelIsCokernel _)
  infer_instance

/-- Every transition map `F_n ⟶ F_m` of a coherent adic system, for `m ≤ n`, is an epimorphism. -/
public theorem epi_map (hF : IsCoherentAdicSystem I F) {m n : ℕ} (hmn : m ≤ n) :
    Epi (F.map (homOfLE hmn).op) := by
  induction hmn with
  | refl => simpa using (inferInstance : Epi (𝟙 (F.obj (op m))))
  | @step n hmn ih =>
      have h₁ : Epi (F.map (homOfLE (Nat.le_succ n)).op) := hF.epi_map_succ n
      have h₂ : Epi (F.map (homOfLE hmn).op) := ih
      rw [← succ_op_comp_op_homOfLE hmn, Functor.map_comp]
      infer_instance

/-- **The reduction step for a coherent adic system.** For `m ≤ n` and `ℐ ᵐ⁺¹ ⊆ 𝒥 ʳ`, the
transition `F_n ⟶ F_m` becomes an isomorphism after dividing both sides by `𝒥 ʳ`.

For `n = m + 1` the transition is the quotient projection by `ℐ ᵐ⁺¹`, which `𝒥 ʳ` already
contains, so reducing modulo `𝒥 ʳ` makes it invertible; the general case is the composite of such
steps, the hypothesis `ℐ ᵐ⁺¹ ⊆ 𝒥 ʳ` passing to every intermediate index because `ℐ ⁿ⁺¹ ⊆ ℐ ᵐ⁺¹`
for `m ≤ n`. -/
public theorem isIso_idealPowerQuotientMap_map (hF : IsCoherentAdicSystem I F)
    (J : X.IdealSheafData) (r : ℕ) {m n : ℕ} (hmn : m ≤ n) (hpow : I ^ (m + 1) ≤ J ^ r) :
    IsIso (idealPowerQuotientMap J J r r le_rfl (F.map (homOfLE hmn).op)) := by
  induction hmn with
  | refl =>
      have hmap : F.map (homOfLE (le_refl m)).op = 𝟙 _ := by simp
      rw [hmap, idealPowerQuotientMap_id]
      infer_instance
  | @step n hmn ih =>
      have hpow' : I ^ (n + 1) ≤ J ^ r :=
        (Scheme.IdealSheafData.pow_le_pow_of_le I (Nat.add_le_add_right hmn 1)).trans hpow
      have : (F.obj (op (n + 1))).IsQuasicoherent := hF.isQuasicoherent (n + 1)
      have hstep : IsIso (idealPowerQuotientMap J J r r le_rfl
          (F.map (homOfLE (Nat.le_succ n)).op)) :=
        isIso_idealPowerQuotientMap_of_cokernel_π_comp J I r (n + 1) hpow'
          (hF.quotientIso n) _ (hF.cokernel_π_comp_quotientIso n)
      have hIso := ih
      rw [← succ_op_comp_op_homOfLE hmn, Functor.map_comp, idealPowerQuotientMap_comp]
      infer_instance

end IsCoherentAdicSystem

end Stacks.Coherent

end
