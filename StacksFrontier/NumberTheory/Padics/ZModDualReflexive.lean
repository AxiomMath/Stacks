module

public import StacksFrontier.NumberTheory.Padics.LAdicInvariantCharacters

/-!
# Finite modules over `ℤ/N` are reflexive

For a finite `ℤ/Nℤ`-module `M` the evaluation map `M → Hom(Hom(M, ℤ/N), ℤ/N)` is bijective.
Through the standard character `ℤ/N → ℂ^×`, the homomorphisms `M → ℤ/N` are the complex
characters of the finite abelian group `M`, which are as many as the elements of `M`
(Pontryagin duality for finite abelian groups, `AddChar.card_eq`). Hence `#Hom(M, ℤ/N) = #M`;
the characters separate points, since otherwise they would all factor through a proper quotient;
and evaluation is an injection between sets of the same finite cardinality.

## Main results

* `Stacks.LAdic.natCard_addMonoidHom_zmod_eq`
* `Stacks.LAdic.exists_addMonoidHom_zmod_apply_ne_zero`
* `Stacks.LAdic.bijective_dual_eval_zmod`
-/

@[expose] public noncomputable section

open Function

namespace Stacks.LAdic

variable {N : ℕ} [NeZero N]

/-- **A finite abelian group killed by `N` has exactly as many homomorphisms to `ℤ/N` as it has
elements.** -/
theorem natCard_addMonoidHom_zmod_eq {A : Type*} [AddCommGroup A] [Finite A]
    (hA : ∀ a : A, N • a = 0) : Nat.card (A →+ ZMod N) = Nat.card A := by
  classical
  have : Fintype A := Fintype.ofFinite A
  refine le_antisymm ?_ (natCard_le_natCard_addMonoidHom_zmod hA)
  have hinj : Injective
      (fun f : A →+ ZMod N => (ZMod.stdAddChar (N := N)).compAddMonoidHom f) := by
    intro f g h
    ext a
    exact ZMod.injective_stdAddChar (congrArg (fun χ : AddChar A ℂ => χ a) h)
  calc Nat.card (A →+ ZMod N) ≤ Nat.card (AddChar A ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Fintype.card (AddChar A ℂ) := Nat.card_eq_fintype_card
    _ = Fintype.card A := AddChar.card_eq
    _ = Nat.card A := Nat.card_eq_fintype_card.symm

/-- **The homomorphisms to `ℤ/N` separate the points** of a finite abelian group killed by `N`. -/
theorem exists_addMonoidHom_zmod_apply_ne_zero {A : Type*} [AddCommGroup A] [Finite A]
    (hA : ∀ a : A, N • a = 0) {x : A} (hx : x ≠ 0) : ∃ f : A →+ ZMod N, f x ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  let C := AddSubgroup.zmultiples x
  let π := QuotientAddGroup.mk' C
  have hQ : ∀ b : A ⧸ C, N • b = 0 := fun b => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective C b
    rw [← map_nsmul, hA, map_zero]
  have hsurj : Surjective (fun g : (A ⧸ C) →+ ZMod N => g.comp π) := by
    intro f
    refine ⟨QuotientAddGroup.lift C f fun c hc => ?_, AddMonoidHom.ext fun a => rfl⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
    rw [AddMonoidHom.mem_ker, map_zsmul, h f, smul_zero]
  have : Finite ((A ⧸ C) →+ ZMod N) :=
    Finite.of_injective (fun g : (A ⧸ C) →+ ZMod N => (g : A ⧸ C → ZMod N))
      DFunLike.coe_injective
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [natCard_addMonoidHom_zmod_eq hA, natCard_addMonoidHom_zmod_eq hQ] at h1
  have h2 : Nat.card A = Nat.card (A ⧸ C) * Nat.card C :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C
  have h3 : 1 < Nat.card C := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨0, by simp⟩, ⟨x, AddSubgroup.mem_zmultiples x⟩,
      fun h0 => hx (congrArg Subtype.val h0).symm⟩
  have h4 : 0 < Nat.card (A ⧸ C) := Nat.card_pos
  nlinarith

/-- A finite `ℤ/N`-module is killed by `N`, and its dual is finite with as many elements. -/
private theorem finite_natCard_dual_zmod (A : Type*) [AddCommGroup A] [Module (ZMod N) A]
    [Finite A] : (∀ a : A, N • a = 0) ∧ Finite (Module.Dual (ZMod N) A) ∧
      Nat.card (Module.Dual (ZMod N) A) = Nat.card A := by
  have hA : ∀ a : A, N • a = 0 := fun a => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]
  have hD : Nat.card (Module.Dual (ZMod N) A) = Nat.card A := by
    rw [← Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv N).toEquiv,
      natCard_addMonoidHom_zmod_eq hA]
  exact ⟨hA, Nat.finite_of_card_ne_zero (hD ▸ Nat.card_pos.ne'), hD⟩

/-- **A finite `ℤ/N`-module is reflexive**: evaluation into the double dual is bijective. -/
theorem bijective_dual_eval_zmod (M : Type*) [AddCommGroup M] [Module (ZMod N) M] [Finite M] :
    Bijective (Module.Dual.eval (ZMod N) M) := by
  obtain ⟨hM, _, hD⟩ := finite_natCard_dual_zmod (N := N) M
  obtain ⟨-, _, hDD⟩ := finite_natCard_dual_zmod (N := N) (Module.Dual (ZMod N) M)
  have hinj : Injective (Module.Dual.eval (ZMod N) M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra h0
    obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero hM h0
    exact hf (LinearMap.congr_fun hx ((AddMonoidHom.toZModLinearMapEquiv N).toEquiv f))
  exact hinj.bijective_of_nat_card_le (hDD.trans hD).le

end Stacks.LAdic

end
