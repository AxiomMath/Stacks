module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictToDenseOpen

/-!
# The `ℓ`-primary dévissage of the assertions for torsion sheaves on curves

In the proof of Stacks Project Tag 03SC, once the coefficient sheaf `F` has been reduced to a
constructible sheaf killed by some positive integer `m`, the source splits `F` into its
`ℓ`-primary parts and then uses `0 → F[ℓ] → F → F/F[ℓ] → 0` to reduce to a sheaf killed by a
prime `ℓ`, that is a sheaf of `𝔽_ℓ`-vector spaces. This file carries that reduction for the
eight statements of Situation 0A52, bundled as `Stacks.EtaleCohomology.CurveCohomologyStatements`.

## Main results

* `Stacks.EtaleCohomology.curveCohomologyStatements_of_nsmul_id_eq_zero`: if the eight statements
  hold for every sheaf of a class `P` killed by a prime, and `P` passes from the middle term of a
  short exact sequence to its outer terms, then they hold for every sheaf of `P` killed by a
  positive integer.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage`, the
primary decomposition is replaced by a single strong induction on the annihilator along the
sequences `0 → F[a] → F → F/F[a] → 0` of `Stacks.EtaleCohomology.kernelQuotientShortComplex`, so
that only closure under extensions (Tag 0A5C) is used and no splitting of idempotents is needed.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {Z Z' : Scheme.{u}} (i : Z' ⟶ Z) {k : Type u} [Field k] (π : Z ⟶ Spec (.of k))
  (l p : ℕ)
  {constructible : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The prime-power step of the `ℓ`-primary dévissage.** Let `P` be a class of abelian sheaves
on the small étale site of `Z` which passes from the middle term of a short exact sequence to
the outer terms, and from which constructibility does too. If the eight statements of Situation
0A52 hold for every sheaf of `P` killed by `a`, they hold for every sheaf of `P` killed by a
power of `a`. -/
theorem curveCohomologyStatements_of_nsmul_id_eq_zero_of_pow
    (P : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (hconstructible :
      ∀ S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        S.ShortExact → constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    (a : ℕ)
    (h : ∀ G, P G → a • 𝟙 G = 0 → CurveCohomologyStatements.{u, v, w} i π l p constructible G) :
    ∀ (n : ℕ) (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}), P F →
      a ^ n • 𝟙 F = 0 → CurveCohomologyStatements.{u, v, w} i π l p constructible F := by
  intro n
  induction n with
  | zero =>
    intro F _ hF
    exact curveCohomologyStatements_of_isZero.{u, v, w} i π l p
      ((IsZero.iff_id_eq_zero F).mpr (by simpa using hF))
  | succ n ih =>
    intro F hPF hF
    have hS := kernelQuotientShortComplex_shortExact (a • 𝟙 F)
    have hPS := hP _ hS hPF
    exact curveCohomologyStatements_X₂_of_shortExact_of_constructible_and.{u, v, w} i π l p hS
      (hconstructible _ hS) (h _ hPS.1 (nsmul_id_kernel_eq_zero F a))
      (ih _ hPS.2 (nsmul_id_cokernel_eq_zero F a (a ^ n) (by rwa [← pow_succ'])))

/-- **Stacks Project, Tag 03SC, the `ℓ`-primary dévissage.** Let `P` be a class of abelian
sheaves on the small étale site of `Z` which passes from the middle term of a short exact
sequence to the outer terms, and from which constructibility does too. If the eight statements
of Situation 0A52 hold for every sheaf of `P` killed by a prime number, they hold for every sheaf
of `P` killed by a positive integer.

In the source `P` is the class of constructible abelian sheaves, which descends along short
exact sequences by Proposition 09BH, and the conclusion is the reduction of a constructible sheaf
killed by `m` to a constructible sheaf of `𝔽_ℓ`-vector spaces. -/
theorem curveCohomologyStatements_of_nsmul_id_eq_zero
    (P : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (hconstructible :
      ∀ S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        S.ShortExact → constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∀ G, P G → ℓ • 𝟙 G = 0 →
      CurveCohomologyStatements.{u, v, w} i π l p constructible G) :
    ∀ (m : ℕ), m ≠ 0 → ∀ F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, P F →
      m • 𝟙 F = 0 → CurveCohomologyStatements.{u, v, w} i π l p constructible F := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm F hPF hF
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm) with hm1 | hm1
    · exact curveCohomologyStatements_of_isZero.{u, v, w} i π l p
        ((IsZero.iff_id_eq_zero F).mpr (by simpa [← hm1] using hF))
    · have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
      have hfpos : 0 < m.factorization m.minFac :=
        hp.factorization_pos_of_dvd hm (Nat.minFac_dvd m)
      obtain ⟨b, hb⟩ := Nat.ordProj_dvd m m.minFac
      have hbne : b ≠ 0 := by
        rintro rfl
        rw [Nat.mul_zero] at hb
        exact hm hb
      have htwo : 2 ≤ m.minFac ^ m.factorization m.minFac :=
        hp.two_le.trans (by
          calc m.minFac = m.minFac ^ 1 := (pow_one _).symm
            _ ≤ m.minFac ^ m.factorization m.minFac :=
                Nat.pow_le_pow_right hp.one_lt.le hfpos)
      have hblt : b < m := by
        rw [hb]
        calc b < 2 * b := by omega
          _ ≤ m.minFac ^ m.factorization m.minFac * b := Nat.mul_le_mul_right b htwo
      have hS := kernelQuotientShortComplex_shortExact
        ((m.minFac ^ m.factorization m.minFac) • 𝟙 F)
      have hPS := hP _ hS hPF
      exact curveCohomologyStatements_X₂_of_shortExact_of_constructible_and.{u, v, w} i π l p hS
        (hconstructible _ hS)
        (curveCohomologyStatements_of_nsmul_id_eq_zero_of_pow.{u, v, w} i π l p P hP
          hconstructible m.minFac (h _ hp) (m.factorization m.minFac) _ hPS.1
          (nsmul_id_kernel_eq_zero F _))
        (ih b hblt hbne _ hPS.2 (nsmul_id_cokernel_eq_zero F _ b (by rw [← hb]; exact hF)))

end Stacks.EtaleCohomology

end
