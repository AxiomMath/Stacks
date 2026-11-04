module

public import StacksFrontier.RingTheory.LocalCohomology.BasicOpenSections.Const

/-!
# Normalizing the local fractions of a section

A locally fractional section `s` of a module `M` on an open `U` of `Spec A` is, near each point,
a constant fraction `m / g` (`Stacks.LocalCohomology.exists_basicOpen_forall_eq_mk`). When `U` is
quasi-compact, finitely many of those fractions `a i / b i` already cover `U`, and they can be
chosen so that `b j • a i = b i • a j` holds in `M`.

## Main results

* `Stacks.LocalCohomology.exists_pow_smul_smul_eq`: two local fractions of one section agree
  after multiplication by a power of the product of their denominators.
* `Stacks.LocalCohomology.exists_fintype_forall_eq_mk`: the normalized finite family of local
  fractions of a section on a quasi-compact open.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open PrimeSpectrum (basicOpen)

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (M : ModuleCat.{v} A)

/-- Two local fractions `m₁ / g₁` and `m₂ / g₂` representing the same locally fractional section
agree in `M` after multiplication by a power of `g₁ * g₂`. -/
theorem exists_pow_smul_smul_eq {U : Opens (PrimeSpectrum.Top A)} (s : moduleSections M U)
    (g₁ g₂ : A) (h₁ : basicOpen g₁ ≤ U) (h₂ : basicOpen g₂ ≤ U) (m₁ m₂ : M)
    (H₁ : ∀ y : basicOpen g₁, s.1 ⟨y.1, h₁ y.2⟩ = LocalizedModule.mk m₁ ⟨g₁, y.2⟩)
    (H₂ : ∀ y : basicOpen g₂, s.1 ⟨y.1, h₂ y.2⟩ = LocalizedModule.mk m₂ ⟨g₂, y.2⟩) :
    ∃ n : ℕ, (g₁ * g₂) ^ n • (g₂ • m₁) = (g₁ * g₂) ^ n • (g₁ • m₂) := by
  have hloc : ∀ p : PrimeSpectrum A, g₁ * g₂ ∉ p.asIdeal →
      ∃ u ∈ p.asIdeal.primeCompl, u • (g₂ • m₁ - g₁ • m₂) = 0 := by
    intro p hp
    have hp₁ : g₁ ∉ p.asIdeal := fun h ↦ hp (p.asIdeal.mul_mem_right _ h)
    have hp₂ : g₂ ∉ p.asIdeal := fun h ↦ hp (p.asIdeal.mul_mem_left _ h)
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp ((H₁ ⟨p, hp₁⟩).symm.trans (H₂ ⟨p, hp₂⟩))
    simp only [Submonoid.smul_def] at hu
    exact ⟨u.1, u.2, (smul_sub _ _ _).trans (sub_eq_zero.mpr hu)⟩
  obtain ⟨n, hn⟩ :=
    exists_pow_smul_eq_zero_of_forall_mem_basicOpen (M := M) (g₁ * g₂) _ hloc
  exact ⟨n, by rwa [smul_sub, sub_eq_zero] at hn⟩

/-- On a quasi-compact open `U` a locally fractional section `s` of `M` is described by a finite
family of fractions `a i / b i`, with `D(b i) ⊆ U` covering `U`, whose numerators and denominators
satisfy `b j • a i = b i • a j` in `M`. -/
theorem exists_fintype_forall_eq_mk (U : Opens (PrimeSpectrum.Top A))
    (hU : IsCompact (U : Set (PrimeSpectrum.Top A))) (s : moduleSections M U) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → A) (hbU : ∀ i, basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, basicOpen (b i)) ∧ (∀ i j, b j • a i = b i • a j) ∧
        ∀ (i : ι) (y : basicOpen (b i)),
          s.1 ⟨y.1, hbU i y.2⟩ = LocalizedModule.mk (a i) ⟨b i, y.2⟩ := by
  choose g hxg hgU m H using fun x : U ↦ exists_basicOpen_forall_eq_mk M U s x.1 x.2
  choose n hn using fun i j : U ↦
    exists_pow_smul_smul_eq M s (g i) (g j) (hgU i) (hgU j) (m i) (m j) (H i) (H j)
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun i : U ↦ (basicOpen (g i) : Set (PrimeSpectrum A)))
    (fun _ ↦ (basicOpen _).2) fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg ⟨x, hx⟩)
  obtain ⟨N, hNle⟩ : ∃ N : ℕ, ∀ i j : t, n i.1 j.1 ≤ N :=
    ⟨(t ×ˢ t).sup fun x ↦ n x.1 x.2,
      fun i j ↦ Finset.le_sup (f := fun x : U × U ↦ n x.1 x.2) (b := (i.1, j.1))
        (Finset.mem_product.mpr ⟨i.2, j.2⟩)⟩
  have hpow : ∀ i : t, basicOpen (g i.1 ^ (N + 1)) = basicOpen (g i.1) := fun i ↦
    PrimeSpectrum.basicOpen_pow _ _ N.succ_pos
  have hbU : ∀ i : t, basicOpen (g i.1 ^ (N + 1)) ≤ U := fun i ↦ (hpow i).trans_le (hgU i.1)
  refine ⟨t, inferInstance, fun i ↦ g i.1 ^ N • m i.1, fun i ↦ g i.1 ^ (N + 1), hbU,
    fun x hx ↦ ?_, fun i j ↦ ?_, fun i y ↦ ?_⟩
  · obtain ⟨i, hit, hxi⟩ := by simpa only [Set.mem_iUnion, exists_prop] using ht hx
    exact Opens.mem_iSup.mpr ⟨⟨i, hit⟩, (hpow ⟨i, hit⟩).ge hxi⟩
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hNle i j)
    calc g j.1 ^ (N + 1) • (g i.1 ^ N • m i.1)
        = (g i.1 * g j.1) ^ N • (g j.1 • m i.1) := by module
      _ = (g i.1 * g j.1) ^ N • (g i.1 • m j.1) := by
        rw [hd, pow_add, mul_comm ((g i.1 * g j.1) ^ n i.1 j.1), mul_smul, mul_smul, hn i.1 j.1]
      _ = g i.1 ^ (N + 1) • (g j.1 ^ N • m j.1) := by module
  · refine (H i.1 ⟨y.1, (hpow i).le y.2⟩).trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
    simp only [Submonoid.smul_def, one_smul, ← smul_assoc, smul_eq_mul, pow_succ']

end Stacks.LocalCohomology

end
