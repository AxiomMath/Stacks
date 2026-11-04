module

public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# A module killed by `pⁿ` is its own `p`-adic completion

If `pⁿ` kills an `R`-module `X`, the canonical map `X → X̂` to its `p`-adic completion is
bijective: the `p`-adic filtration of `X` is zero from level `n` on.  Consequently an additive map
between two such modules is bijective as soon as its `p`-adic completion is.  This is how a
bijectivity statement for completions, such as [Stacks, Lemma 60.20.1, Tag 07KK] in the form
`Crystalline.bijective_mapAddHom_of_tmul_ιMulti`, is read at a single level `pⁿ`.

## Main results

* `Crystalline.CompletedLevels.bijective_of_pow_nsmul_eq_zero` — `X → X̂` is bijective.
* `Crystalline.CompletedLevels.bijective_of_bijective_mapAddHom` — a map between such modules with
  bijective completion is bijective.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public section

open DividedPowers

namespace Crystalline

namespace CompletedLevels

section Torsion

variable (p n : ℕ) {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] [Module R X]

/-- **A module killed by `pⁿ` is its own `p`-adic completion.** -/
theorem bijective_of_pow_nsmul_eq_zero (hX : ∀ x : X, (p ^ n : ℕ) • x = 0) :
    Function.Bijective (AdicCompletion.of (pAdicIdeal (A := R) p) X) := by
  have hinj : ∀ x y : X,
      (Submodule.Quotient.mk x : X ⧸ (pAdicIdeal (A := R) p ^ n • (⊤ : Submodule R X))) =
        Submodule.Quotient.mk y → x = y := by
    intro x y h
    rw [Submodule.Quotient.eq] at h
    obtain ⟨z, hz⟩ := (PAdicCompletion.mem_pow_smul_top_iff p R n _).mp h
    rw [← sub_eq_zero, hz, hX]
  refine ⟨fun x y hxy ↦ ?_, fun xh ↦ ?_⟩
  · have h := congrArg (fun z : AdicCompletion (pAdicIdeal (A := R) p) X ↦ z.val n) hxy
    exact hinj x y h
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (xh.val n)
    refine ⟨x, AdicCompletion.ext fun k ↦ ?_⟩
    rcases le_total k n with hkn | hnk
    · rw [← xh.property hkn, ← hx]
      rfl
    · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (xh.val k)
      have hyx : y = x := by
        have h := xh.property hnk
        rw [← hy, ← hx] at h
        exact hinj y x h
      rw [← hy, hyx]
      rfl

/-- **An additive map between modules killed by `pⁿ` whose `p`-adic completion is bijective is
bijective.** -/
theorem bijective_of_bijective_mapAddHom {S : Type*} [CommRing S] {Y : Type*} [AddCommGroup Y]
    [Module S Y] (hX : ∀ x : X, (p ^ n : ℕ) • x = 0) (hY : ∀ y : Y, (p ^ n : ℕ) • y = 0)
    (f : X →+ Y) (hf : Function.Bijective (PAdicCompletion.mapAddHom p R S f)) :
    Function.Bijective f := by
  have hoX := bijective_of_pow_nsmul_eq_zero p n (R := R) hX
  have hoY := bijective_of_pow_nsmul_eq_zero p n (R := S) hY
  have hcomm : ∀ x, PAdicCompletion.mapAddHom p R S f (AdicCompletion.of _ X x) =
      AdicCompletion.of _ Y (f x) := PAdicCompletion.mapAddHom_of p R S f
  refine ⟨fun x y hxy ↦ hoX.1 (hf.1 ?_), fun z ↦ ?_⟩
  · rw [hcomm, hcomm, hxy]
  · obtain ⟨w, hw⟩ := hf.2 (AdicCompletion.of _ Y z)
    obtain ⟨x, rfl⟩ := hoX.2 w
    exact ⟨x, hoY.1 ((hcomm x).symm.trans hw)⟩

end Torsion

end CompletedLevels

end Crystalline
