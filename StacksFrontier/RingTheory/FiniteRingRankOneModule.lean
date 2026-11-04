module

public import StacksFrontier.RingTheory.CyclicComaximal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A module over a finite ring with the counts of the ring is the ring

Let `Λ` be a finite commutative ring and `E` a finite `Λ`-module with `#E = #Λ` and
`#(E / 𝔪E) ≤ #(Λ / 𝔪)` for every maximal ideal `𝔪`. Then `E ≅ Λ`.

## Main results

* `Stacks.FiniteRingRankOne.exists_span_singleton_sup_smul_top_eq_top`: if
  `#(E / 𝔪E) ≤ #(Λ / 𝔪)`, then `E = Λ t + 𝔪E` for some `t : E`.
* `Stacks.FiniteRingRankOne.nonempty_linearEquiv_self_of_natCard`: if `#E = #Λ` and
  `#(E / 𝔪E) ≤ #(Λ / 𝔪)` for every maximal ideal `𝔪`, then `E ≅ Λ`.
-/


@[expose] public section

namespace Stacks.FiniteRingRankOne

variable {Λ : Type*} [CommRing Λ] [Finite Λ] {E : Type*} [AddCommGroup E] [Module Λ E] [Finite E]

omit [Finite Λ] in
/-- **`E / 𝔪E` is cyclic when it has at most `#(Λ / 𝔪)` elements**: one element `t` with
`E = Λ t + 𝔪E`. -/
theorem exists_span_singleton_sup_smul_top_eq_top (𝔪 : Ideal Λ) [𝔪.IsMaximal]
    (h : Nat.card (E ⧸ 𝔪 • (⊤ : Submodule Λ E)) ≤ Nat.card (Λ ⧸ 𝔪)) :
    ∃ t : E, Submodule.span Λ {t} ⊔ 𝔪 • (⊤ : Submodule Λ E) = ⊤ := by
  let := Ideal.Quotient.field 𝔪
  have : Finite (E ⧸ 𝔪 • (⊤ : Submodule Λ E)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  by_cases hQ : Nontrivial (E ⧸ 𝔪 • (⊤ : Submodule Λ E))
  · obtain ⟨q, hq⟩ := exists_ne (0 : E ⧸ 𝔪 • (⊤ : Submodule Λ E))
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hinj : Function.Injective fun c : Λ ⧸ 𝔪 =>
        c • (Submodule.Quotient.mk t : E ⧸ 𝔪 • (⊤ : Submodule Λ E)) :=
      smul_left_injective (Λ ⧸ 𝔪) hq
    have hbij := hinj.bijective_of_nat_card_le h
    refine ⟨t, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨c, hc⟩ := hbij.2 (Submodule.Quotient.mk x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hx : (Submodule.Quotient.mk x : E ⧸ 𝔪 • (⊤ : Submodule Λ E)) =
        Submodule.Quotient.mk (a • t) :=
      hc.symm.trans (Module.Quotient.mk_smul_mk (M := E) (I := 𝔪) a t)
    have hmem : x - a • t ∈ 𝔪 • (⊤ : Submodule Λ E) := (Submodule.Quotient.eq _).1 hx
    rw [← add_sub_cancel (a • t) x]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self t)) hmem
  · rw [not_nontrivial_iff_subsingleton] at hQ
    refine ⟨0, eq_top_iff.2 fun x _ => Submodule.mem_sup_right ?_⟩
    exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)

/-- **A finite module over a finite ring with `#E = #Λ` and `#(E / 𝔪E) ≤ #(Λ / 𝔪)` for every
maximal ideal `𝔪` is isomorphic to `Λ`.** -/
theorem nonempty_linearEquiv_self_of_natCard (hcard : Nat.card E = Nat.card Λ)
    (h : ∀ 𝔪 : Ideal Λ, 𝔪.IsMaximal →
      Nat.card (E ⧸ 𝔪 • (⊤ : Submodule Λ E)) ≤ Nat.card (Λ ⧸ 𝔪)) :
    Nonempty (E ≃ₗ[Λ] Λ) := by
  classical
  have : Fintype (MaximalSpectrum Λ) := Fintype.ofFinite _
  let I : MaximalSpectrum Λ → Ideal Λ := fun P => P.asIdeal
  let J := ∏ P ∈ (Finset.univ : Finset (MaximalSpectrum Λ)), I P
  obtain ⟨t, ht⟩ := Stacks.CyclicComaximal.exists_sup_span_singleton_eq_top (J • ⊤) I
    Finset.univ (fun P _ Q _ hPQ => Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal
      fun he => hPQ (MaximalSpectrum.ext he)) le_rfl fun P _ => by
      obtain ⟨t, ht⟩ := exists_span_singleton_sup_smul_top_eq_top (E := E) (I P)
        (h P.asIdeal P.isMaximal)
      exact ⟨t, by rw [ht, sup_top_eq]⟩
  have hJ : J ≤ Ideal.jacobson ⊥ := le_sInf fun 𝔪 h𝔪 =>
    Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ (⟨𝔪, h𝔪.2⟩ : MaximalSpectrum Λ)))
  have htop : Submodule.span Λ {t} = ⊤ := by
    refine eq_top_iff.2 (Submodule.le_of_le_smul_of_le_jacobson_bot
      (Module.Finite.fg_top (R := Λ) (M := E)) hJ ?_)
    rw [sup_comm, ht]
  let φ : Λ →ₗ[Λ] E := LinearMap.toSpanSingleton Λ E t
  have hsurj : Function.Surjective φ := by
    rwa [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
  exact ⟨(LinearEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hcard.ge)).symm⟩

end Stacks.FiniteRingRankOne

end
