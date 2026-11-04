module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.PrimaryDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances

/-!
# Vanishing of étale cohomology of a torsion sheaf from that of its torsion subsheaves

Let `X` be a quasi-compact and quasi-separated scheme and let `F` be a torsion abelian sheaf on
the small étale site of `X`. Then `F` is the filtered union of its subsheaves `F[n!]` killed by
`n!` (`Stacks.Torsion.isIso_torsionFiltrationDesc`), and étale cohomology of `X` commutes with
filtered colimits (Tag 03Q5). Hence `H^q(X, F)` vanishes as soon as every `H^q(X, F[n!])` does.

In the proof of Stacks Project Tag 03SC this is the first reduction, from an arbitrary torsion
sheaf to sheaves killed by a positive integer, for the three vanishing statements of Situation
0A52. Each `F[n!]` is a subsheaf of `F`, so it inherits any torsion condition imposed on `F`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_Γ_of_torsionFiltration`: the statement for the
  right derived functors of global sections.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_torsionFiltration`: the same for
  `CategoryTheory.Sheaf.H`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_nsmul_id_eq_zero`: on an arbitrary site, if
  degree-`q` cohomology vanishes on every sheaf of an extension-stable class `P` killed by a
  prime, it vanishes on every sheaf of `P` killed by a positive integer.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_torsion_of_prime`: the two reductions composed.
  On a quasi-compact quasi-separated scheme, if degree-`q` étale cohomology vanishes on every
  sheaf of `P` killed by a prime, it vanishes on every torsion sheaf of `P`.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0DDC](https://stacks.math.columbia.edu/tag/0DDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe v u

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})

/-- **The cohomology of a torsion sheaf vanishes if that of each of its torsion subsheaves
does.** For `X` quasi-compact and quasi-separated and `F` a torsion abelian sheaf on its small
étale site, if `R^qΓ(X, F[n!]) = 0` for every `n` then `R^qΓ(X, F) = 0`. -/
theorem isZero_rightDerived_Γ_of_torsionFiltration
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ)
    (h : ∀ n, IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived
      q).obj ((Stacks.Torsion.torsionFiltration X.smallEtaleTopology F).obj n))) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived q).obj
      F) := by
  set R := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived q
  set D := Stacks.Torsion.torsionFiltration X.smallEtaleTopology F
  have hd : IsIso (Stacks.Torsion.torsionFiltrationDesc X.smallEtaleTopology F) :=
    Stacks.Torsion.isIso_torsionFiltrationDesc X.smallEtaleTopology F hF
  have hpost : IsIso (colimit.post D R) := isIso_colimit_post_rightDerived_Γ_smallEtale.{v} X q D
  have hcol : IsZero (colimit (D ⋙ R)) := by
    rw [IsZero.iff_id_eq_zero]
    exact colimit.hom_ext fun n => (h n).eq_of_src _ _
  exact (hcol.of_iso (asIso (colimit.post D R)).symm).of_iso
    (R.mapIso (asIso (Stacks.Torsion.torsionFiltrationDesc X.smallEtaleTopology F))).symm

/-- **The cohomology of a torsion sheaf vanishes if that of each of its torsion subsheaves
does**, for `CategoryTheory.Sheaf.H`. -/
theorem subsingleton_sheafH_of_torsionFiltration
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ)
    (h : ∀ n, Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v}
      ((Stacks.Torsion.torsionFiltration X.smallEtaleTopology F).obj n) q)) :
    Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} F q) :=
  (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
      X.smallEtaleTopology F q).2
    (isZero_rightDerived_Γ_of_torsionFiltration.{v} X F hF q fun n =>
      (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
        X.smallEtaleTopology _ q).1 (h n))

section Devissage

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- If `P` passes to the outer terms of short exact sequences, a sheaf of `P` killed by `k * b` has
vanishing degree-`q` cohomology once `P`-sheaves killed by `k` and by `b` do. -/
private theorem subsingleton_sheafH_of_nsmul_id_mul_eq_zero
    (P : Sheaf J AddCommGrpCat.{v} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf J AddCommGrpCat.{v}), S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (q k b : ℕ) (hk : ∀ G, P G → k • 𝟙 G = 0 → Subsingleton (Sheaf.H.{v, v} G q))
    (hb : ∀ G, P G → b • 𝟙 G = 0 → Subsingleton (Sheaf.H.{v, v} G q))
    (F : Sheaf J AddCommGrpCat.{v}) (hPF : P F) (hF : (k * b) • 𝟙 F = 0) :
    Subsingleton (Sheaf.H.{v, v} F q) := by
  have hS := kernelQuotientShortComplex_shortExact (k • 𝟙 F)
  have hPS := hP _ hS hPF
  have := hk _ hPS.1 (nsmul_id_kernel_eq_zero F k)
  have := hb _ hPS.2 (nsmul_id_cokernel_eq_zero F k b hF)
  exact subsingleton_sheafCohomology_X₂_of_shortExact hS q

/-- **Reduction of a prime-power annihilator to a prime one, for vanishing of cohomology.** Let
`P` be a class of abelian sheaves passing from the middle term of a short exact sequence to its
outer terms. If degree-`q` cohomology vanishes on every sheaf of `P` killed by `a`, it vanishes on
every sheaf of `P` killed by a power of `a`. -/
theorem subsingleton_sheafH_of_nsmul_id_eq_zero_of_pow (P : Sheaf J AddCommGrpCat.{v} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf J AddCommGrpCat.{v}), S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (q a : ℕ) (h : ∀ G, P G → a • 𝟙 G = 0 → Subsingleton (Sheaf.H.{v, v} G q)) :
    ∀ (n : ℕ) (F : Sheaf J AddCommGrpCat.{v}), P F → a ^ n • 𝟙 F = 0 →
      Subsingleton (Sheaf.H.{v, v} F q) := by
  intro n
  induction n with
  | zero =>
    intro F _ hF
    exact Sheaf.subsingleton_H_of_isZero ((IsZero.iff_id_eq_zero F).mpr (by simpa using hF)) q
  | succ n ih =>
    intro F hPF hF
    exact subsingleton_sheafH_of_nsmul_id_mul_eq_zero J P hP q a (a ^ n) h
      ih F hPF (by rwa [← pow_succ'])

/-- **Reduction of an arbitrary annihilator to a prime one, for vanishing of cohomology.** Let
`P` be a class of abelian sheaves passing from the middle term of a short exact sequence to its
outer terms. If degree-`q` cohomology vanishes on every sheaf of `P` killed by a prime, it
vanishes on every sheaf of `P` killed by a positive integer. -/
theorem subsingleton_sheafH_of_nsmul_id_eq_zero (P : Sheaf J AddCommGrpCat.{v} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf J AddCommGrpCat.{v}), S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (q : ℕ) (h : ∀ ℓ : ℕ, ℓ.Prime → ∀ G, P G → ℓ • 𝟙 G = 0 →
      Subsingleton (Sheaf.H.{v, v} G q)) :
    ∀ (m : ℕ), m ≠ 0 → ∀ F : Sheaf J AddCommGrpCat.{v}, P F → m • 𝟙 F = 0 →
      Subsingleton (Sheaf.H.{v, v} F q) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm F hPF hF
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm) with hm1 | hm1
    · exact Sheaf.subsingleton_H_of_isZero
        ((IsZero.iff_id_eq_zero F).mpr (by simpa [← hm1] using hF)) q
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
      exact subsingleton_sheafH_of_nsmul_id_mul_eq_zero J P hP q _ b
        (subsingleton_sheafH_of_nsmul_id_eq_zero_of_pow J P hP q m.minFac (h _ hp)
          (m.factorization m.minFac))
        (ih b hblt hbne) F hPF (by rw [← hb]; exact hF)

end Devissage

/-- **Reduction of a torsion sheaf to sheaves killed by a prime, for vanishing of étale
cohomology.** Let `X` be a quasi-compact quasi-separated scheme and `P` a class of abelian
sheaves on its small étale site passing from the middle term of a short exact sequence to its
outer terms. If degree-`q` étale cohomology vanishes on every sheaf of `P` killed by a prime
number, it vanishes on every torsion sheaf of `P`.

These are the first two reductions in the source's proof of Tag 03SC, for its three vanishing
statements: a torsion sheaf is the union of its subsheaves killed by `n!`, with cohomology
commuting with that union by Tag 03Q5, and a sheaf killed by `n!` is a successive extension of
sheaves killed by primes. In the source `P` is the class of constructible sheaves; any such class
can be used here. -/
theorem subsingleton_sheafH_of_torsion_of_prime
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop)
    (hP : ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
      S.ShortExact → P S.X₂ → P S.X₁ ∧ P S.X₃)
    (q : ℕ) (h : ∀ ℓ : ℕ, ℓ.Prime → ∀ G, P G → ℓ • 𝟙 G = 0 →
      Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} G q))
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (hPF : P F) :
    Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} F q) :=
  subsingleton_sheafH_of_torsionFiltration.{v} X F hF q fun n =>
    subsingleton_sheafH_of_nsmul_id_eq_zero X.smallEtaleTopology P hP q h
      (Nat.factorial n.down) (Nat.factorial_ne_zero _) _
      (hP _ (kernelQuotientShortComplex_shortExact ((Nat.factorial n.down) • 𝟙 F)) hPF).1
      (nsmul_id_kernel_eq_zero F _)

end Stacks.EtaleCohomology

end
