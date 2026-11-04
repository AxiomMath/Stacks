module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow

/-!
# Finiteness of a module from finiteness of its reduction modulo an ideal

Let `R` be a commutative ring, `I ⊆ R` an ideal and `N` an `R`-module whose reduction `N ⧸ IN`
is a finite `R`-module. Then `N` itself is finite as soon as the `I`-adic filtration of `N`
degenerates: either `IᵏN = 0` for some `k`, or `N` is the `I`-adic completion of a module and the
coefficients are enlarged to `R^∧`.

## Main results

* `Module.Finite.of_pow_smul_top_eq_bot`: Nakayama for an ideal acting nilpotently — if
  `IᵏN = 0` and `N ⧸ IN` is finite, then `N` is finite.
* `Module.Finite.adicCompletion_of_finite_quotient_smul_top`: if `N ⧸ IN` is a finite
  `R`-module and `I` is finitely generated, then `N^∧` is a finite `R^∧`-module.

## Implementation notes

`IᵏN` is written Mathlib's way, as `I ^ k • (⊤ : Submodule R N)`. The hypothesis of the first
result is that `I` acts nilpotently on `N`, not that `I` is a nilpotent ideal of `R`: the two
differ exactly by the annihilator of `N`, and it is the former that the reductions of an adic
tower satisfy. Both results keep the ring and the module in independent universes, which is what
a statement about a module category with a free universe parameter needs.

## References

* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
-/

@[expose] public section

universe u v

/-- **Nakayama for a nilpotently acting ideal.** If `IᵏN = 0` and the reduction `N ⧸ IN` is a
finite `R`-module, then `N` is a finite `R`-module: lifts of generators of the reduction span a
submodule `P` with `P + IN = N`, hence `P + IʲN = N` for every `j`, and `IᵏN = 0`. -/
public theorem Module.Finite.of_pow_smul_top_eq_bot {R : Type u} [CommRing R] (I : Ideal R)
    {k : ℕ} (N : Type v) [AddCommGroup N] [Module R N]
    (hnil : I ^ k • (⊤ : Submodule R N) = ⊥)
    (hfin : Module.Finite R (N ⧸ (I • ⊤ : Submodule R N))) :
    Module.Finite R N := by
  classical
  set K : Submodule R N := I • ⊤ with hK
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp (Module.finite_def.mp hfin)
  set σ : (N ⧸ K) → N := Function.surjInv K.mkQ_surjective with hσ
  have hσeq : ∀ x, K.mkQ (σ x) = x := fun x => Function.surjInv_eq K.mkQ_surjective x
  set P : Submodule R N := Submodule.span R (σ '' S) with hP
  have hmap : Submodule.map K.mkQ P = ⊤ := by
    rw [hP, Submodule.map_span, ← hSspan]
    congr 1
    rw [Set.image_image]
    simp only [hσeq]
    exact Set.image_id S
  have htop : P ⊔ K = ⊤ := by
    have h := Submodule.comap_map_eq K.mkQ P
    rw [hmap, Submodule.comap_top, Submodule.ker_mkQ] at h
    exact h.symm
  have step : ∀ j : ℕ, P ⊔ I ^ j • (⊤ : Submodule R N) = ⊤ := by
    intro j
    induction j with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
    | succ j ih =>
      refine le_antisymm le_top ?_
      refine le_trans (le_of_eq ih.symm) (sup_le le_sup_left ?_)
      have hsplit : I ^ j • (⊤ : Submodule R N) =
          I ^ j • P ⊔ I ^ (j + 1) • (⊤ : Submodule R N) := by
        conv_lhs => rw [← htop]
        rw [Submodule.smul_sup, hK, ← Submodule.mul_smul, ← pow_succ]
      rw [hsplit]
      exact sup_le (le_sup_of_le_left Submodule.smul_le_right) le_sup_right
  have hPtop : P = ⊤ := by
    have h := step k
    rwa [hnil, sup_bot_eq] at h
  exact Module.finite_def.mpr (Submodule.fg_def.mpr ⟨σ '' S, hSfin.image σ, hPtop ▸ hP ▸ rfl⟩)

/-- If `N ⧸ IN` is a finite `R`-module and `I` is finitely generated, then the `I`-adic
completion `N^∧` is a finite module over the completed ring `R^∧`. -/
public theorem Module.Finite.adicCompletion_of_finite_quotient_smul_top {R : Type u} [CommRing R]
    {I : Ideal R} (hI : I.FG) (N : Type v) [AddCommGroup N] [Module R N]
    (hfin : Module.Finite R (N ⧸ (I • ⊤ : Submodule R N))) :
    Module.Finite (AdicCompletion I R) (AdicCompletion I N) := by
  have _ : IsPrecomplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    (AdicCompletion.isAdicComplete_self I hI).toIsPrecomplete
  have e := AdicCompletion.quotPowSMulTopEquiv hI N 1
  rw [pow_one] at e
  have hres : Module.Finite R (AdicCompletion I N ⧸
      ((I.map (algebraMap R (AdicCompletion I R)) •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I N))).restrictScalars R)) := by
    rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
    exact hfin.equiv e.symm
  have _ := hres.equiv (Submodule.Quotient.restrictScalarsEquiv R _)
  have _ := Module.Finite.of_restrictScalars_finite R (AdicCompletion I R)
    (AdicCompletion I N ⧸ (I.map (algebraMap R (AdicCompletion I R)) •
      (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I N))))
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top _
    (IsHausdorff.map_algebraMap_iff.mpr (AdicCompletion.instIsHausdorff I N)).iInf_pow_smul
    (Module.Finite.of_restrictScalars_finite (AdicCompletion I R)
      (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) _)

end
