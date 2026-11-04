module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSectionsSurjective.Fractions

/-!
# One exponent and exact cross relations for a section away from a closed set

Let `R` be a commutative ring, `N` an `R`-module, `W` an open of `Spec R` and `G` a finite set of
elements of `R` whose basic opens lie in `W`. A section of `Ñ` on `W` restricts on each `D(f)`,
`f ∈ G`, to a fraction `m_f / f ^ k_f`; this file makes the exponent uniform and upgrades the
compatibility of these fractions to an **exact** identity `f' ^ n • y f = f ^ n • y f'` in `N`.

The upgrade is the step that has content. At a prime `p ∈ D(f f')` the two fractions agree in
`N_p`, so some element outside `p` annihilates `w = f' ^ k_{f'} m_f - f ^ k_f m_{f'}`; hence the
annihilator of `w` is contained in no prime of `D(f f')`, so `f f'` lies in its radical and some
power of `f f'` kills `w`. Replacing the numerators by `f ^ (n - k_f) m_f` for `n` twice an upper
bound for all the exponents involved then clears every such power at once, and leaves the
fractions unchanged.

## Main results

* `mk_pow_cancel_le`: `(a ^ (n - i) • m) / a ^ n = m / a ^ i` in a localization at a prime
  avoiding `a`.
* `exists_uniform_fractions`: one exponent `n` and numerators `y` describing the section on every
  `D(f)`, `f ∈ G`, together with the exact cross relations.

## Implementation notes

No finiteness or Noetherian hypothesis is used, and `G` need not generate anything: the exact
cross relations hold for *any* finite set of elements whose basic opens lie in `W`. Only the final
assembly of the homomorphism needs a generating set.

The auxiliary families `k`, `m` and `jj` are chosen as **total** functions on `R` (respectively
`R × R`), with membership of `G` a hypothesis of their defining property, so that `choose` yields
ordinary functions and no subtypes or `dite`s enter the exponent arithmetic.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.StructureSheaf
open PrimeSpectrum (basicOpen)

universe w

namespace Stacks.AlgebraicGeometry.IdealPowerSections

variable {R : Type w} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]

/-- Raising the denominator from `a ^ i` to `a ^ n` and the numerator from `m` to
`a ^ (n - i) • m` does not change the fraction. -/
public lemma mk_pow_cancel_le {p : PrimeSpectrum R} {a : R} (ha : a ∉ p.asIdeal) {i n : ℕ}
    (hin : i ≤ n) (m : N) :
    (LocalizedModule.mk (a ^ (n - i) • m) ⟨a ^ n, Submonoid.pow_mem _ ha n⟩ :
        Localizations N p) =
      LocalizedModule.mk m ⟨a ^ i, Submonoid.pow_mem _ ha i⟩ := by
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul, ← pow_add]
  rw [Nat.add_sub_cancel' hin]

/-- If every prime avoiding `s` contains an element outside it annihilating `w`, then a power of
`s` annihilates `w`. -/
private theorem exists_pow_smul_eq_zero_of_forall_isPrime {s : R} {w : N}
    (h : ∀ P : Ideal R, P.IsPrime → s ∉ P → ∃ u ∉ P, u • w = 0) :
    ∃ n : ℕ, s ^ n • w = 0 := by
  obtain ⟨n, hn⟩ : s ∈ Ideal.radical (LinearMap.ker (LinearMap.toSpanSingleton R N w)) := by
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr ?_
    rintro P ⟨hPle, hPp⟩
    by_contra hsP
    obtain ⟨u, hu, huw⟩ := h P hPp hsP
    exact hu (hPle (by simpa [LinearMap.toSpanSingleton_apply] using huw))
  exact ⟨n, by simpa [LinearMap.toSpanSingleton_apply] using hn⟩

/-- If a power `(f * f') ^ j` kills `f' ^ k' • x - f ^ k • y`, then for `K` bounding `k`, `k'` and
`j`, the numerators `f ^ (2K - k) • x` and `f' ^ (2K - k') • y` satisfy the exact cross relation at
exponent `2K`. -/
private theorem pow_smul_pow_sub_smul_eq_of_mul_pow_smul_sub_eq_zero {f f' : R} {x y : N}
    {k k' j K : ℕ} (hk : k ≤ K) (hk' : k' ≤ K) (hj : j ≤ K)
    (h : (f * f') ^ j • (f' ^ k' • x - f ^ k • y) = 0) :
    f' ^ (K + K) • f ^ (K + K - k) • x = f ^ (K + K) • f' ^ (K + K - k') • y := by
  -- the exponents available, all as `Nat` facts
  have h₁ : K + K - k - j + j = K + K - k := by omega
  have h₂ : K + K - k' - j + (j + k') = K + K := by omega
  have h₃ : K + K - k - j + (j + k) = K + K := by omega
  have h₄ : K + K - k' - j + j = K + K - k' := by omega
  -- the discrepancy identity, with the two monomials separated
  rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at h
  have hc₁ : (f * f') ^ j * f' ^ k' = f ^ j * f' ^ (j + k') := by ring
  have hc₂ : (f * f') ^ j * f ^ k = f ^ (j + k) * f' ^ j := by ring
  rw [hc₁, hc₂] at h
  -- clear the extra powers
  have key₁ : f ^ (K + K - k - j) * f' ^ (K + K - k' - j) * (f ^ j * f' ^ (j + k')) =
      f' ^ (K + K) * f ^ (K + K - k) := by
    rw [mul_mul_mul_comm, ← pow_add, ← pow_add, h₁, h₂, mul_comm]
  have key₂ : f ^ (K + K - k - j) * f' ^ (K + K - k' - j) * (f ^ (j + k) * f' ^ j) =
      f ^ (K + K) * f' ^ (K + K - k') := by
    rw [mul_mul_mul_comm, ← pow_add, ← pow_add, h₃, h₄]
  have hmul := congrArg
    (fun z : N => (f ^ (K + K - k - j) * f' ^ (K + K - k' - j)) • z) h
  simp only [smul_smul] at hmul
  rw [key₁, key₂] at hmul
  simpa only [smul_smul] using hmul

/-- **One exponent and exact cross relations.** For a section `g` of `Ñ` on `W` and a finite set
`G` of elements of `R` with `D(f) ≤ W` for `f ∈ G`, there is a single exponent `n` and a family of
numerators `y` such that `g` is the fraction `y f / f ^ n` at every point of `D(f)`, and such that
the compatibility `f' ^ n • y f = f ^ n • y f'` holds exactly in `N`. -/
public theorem exists_uniform_fractions {W : Opens (PrimeSpectrum.Top R)}
    (g : ∀ x : ↥W, Localizations N x.1) (hg : g ∈ sectionsSubmodule N W)
    (G : Finset R) (hGW : ∀ f ∈ G, basicOpen f ≤ W) :
    ∃ (n : ℕ) (y : R → N),
      (∀ f ∈ G, ∀ (p : PrimeSpectrum R) (hp : f ∉ p.asIdeal) (hpW : p ∈ W),
          g ⟨p, hpW⟩ = LocalizedModule.mk (y f) ⟨f ^ n, Submonoid.pow_mem _ hp n⟩) ∧
      ∀ f ∈ G, ∀ f' ∈ G, f' ^ n • y f = f ^ n • y f' := by
  classical
  -- one fraction per element of `G`, at its own exponent
  have hA : ∀ a : R, ∃ (kk : ℕ) (mm : N), a ∈ G → ∀ (p : PrimeSpectrum R) (hp : a ∉ p.asIdeal)
      (hpW : p ∈ W), g ⟨p, hpW⟩ = LocalizedModule.mk mm ⟨a ^ kk, Submonoid.pow_mem _ hp kk⟩ := by
    intro a
    by_cases ha : a ∈ G
    · obtain ⟨kk, mm, h⟩ := exists_mk_eq_of_mem_sectionsSubmodule g hg a (hGW a ha)
      exact ⟨kk, mm, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h ha⟩
  choose k m hkm using hA
  -- a power of `f f'` kills the discrepancy of the numerators
  have hB : ∀ a b : R, ∃ jj : ℕ, a ∈ G → b ∈ G →
      (a * b) ^ jj • (b ^ k b • m a - a ^ k a • m b) = 0 := by
    intro a b
    by_cases ha : a ∈ G
    · by_cases hb : b ∈ G
      · obtain ⟨jj, hjj⟩ := exists_pow_smul_eq_zero_of_forall_isPrime (s := a * b)
            (w := b ^ k b • m a - a ^ k a • m b) fun P hPp hab => by
          have hap : a ∉ P := fun h => hab (Ideal.mul_mem_right b P h)
          have hbp : b ∉ P := fun h => hab (Ideal.mul_mem_left P a h)
          have hQW : (⟨P, hPp⟩ : PrimeSpectrum R) ∈ W :=
            hGW a ha ((PrimeSpectrum.mem_basicOpen a _).mpr hap)
          obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp
            ((hkm a ha ⟨P, hPp⟩ hap hQW).symm.trans (hkm b hb ⟨P, hPp⟩ hbp hQW))
          refine ⟨u, u.2, ?_⟩
          rw [smul_sub, sub_eq_zero]
          simpa [Submonoid.smul_def, smul_smul] using hu
        exact ⟨jj, fun _ _ => hjj⟩
      · exact ⟨0, fun _ h => absurd h hb⟩
    · exact ⟨0, fun h _ => absurd h ha⟩
  choose jj hjj using hB
  -- an upper bound for every exponent in play, and twice it as the uniform exponent
  set K : ℕ := max (G.sup k) ((G ×ˢ G).sup fun q => jj q.1 q.2)
  have hkK : ∀ a ∈ G, k a ≤ K := fun a ha => le_trans (Finset.le_sup ha) (le_max_left _ _)
  have hjjK : ∀ a ∈ G, ∀ b ∈ G, jj a b ≤ K := fun a ha b hb =>
    le_trans (Finset.le_sup (f := fun q : R × R => jj q.1 q.2)
        (show (a, b) ∈ G ×ˢ G from Finset.mem_product.mpr ⟨ha, hb⟩))
      (le_max_right _ _)
  refine ⟨K + K, fun a => a ^ (K + K - k a) • m a, fun f hf p hp hpW => ?_,
    fun f hf f' hf' => ?_⟩
  · exact (hkm f hf p hp hpW).trans
      (mk_pow_cancel_le hp (le_trans (hkK f hf) (Nat.le_add_right K K)) (m f)).symm
  · exact pow_smul_pow_sub_smul_eq_of_mul_pow_smul_sub_eq_zero (hkK f hf) (hkK f' hf')
      (hjjK f hf f' hf') (hjj f f' hf hf')

end Stacks.AlgebraicGeometry.IdealPowerSections

end
