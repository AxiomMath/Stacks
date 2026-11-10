module

public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.LocalFractions

/-!
# Clearing denominators: a global section of `M(n)~` times a power of a generator comes from `M`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `S`-module and
`X = Proj 𝒮`, and let `f₀, …, f_r` be degree-one elements whose standard opens cover `X`. A global
section `s` of `M(n)~` is, on each `D₊(f_b)`, a single fraction `m_b / f_b ^ {k_b}`
(`Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_forall_sectionValue_eq_mk`). The usual
denominator-clearing argument then produces, for each index `a`, a power `f_a ^ K` carrying `s`
into the image of the canonical map `𝒨 (K + n) ⟶ Γ(X, M(K + n)~)` of Equation 01MR.

The argument is the classical one. On the overlap `D₊(f_a f_b)` the two fractions agree, so
`(f_a f_b) ^ N` annihilates `w_{ab} = f_b ^ {k_b} · m_a - f_a ^ {k_a} · m_b` for some `N`; taking
`N` large enough to serve every `b` at once and putting `K = k_a + N`, the section `f_a ^ K · s`
has value `f_a ^ N · m_a / 1` at every point of every `D₊(f_b)`, hence everywhere.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_pow_smul_eq_zero_of_forall_mk_eq_zero`: a
  homogeneous element dying in every localized fiber over `D₊(g)` is killed by a power of `g`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.exists_pow_smul_eq_degreeNToGlobalSections`: **the
  denominator-clearing statement**, that `f_a ^ K · s` comes from a homogeneous element of `M`.

## Implementation notes

The vanishing criterion is proved by the same route as
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_eq_zero_of_degreeSection_eq_zero` does
for the regular module: the fraction `w / g ^ 0` is an element of the degree-zero localization
whose section over `D₊(g)` is zero, and the standard-open comparison
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroToSection` is injective.

The uniform exponent `N` is a `Finset.sup` over the second index only: the statement is for a
*fixed* `a`, and its consumer only needs each `f_a` to lie in the radical of the ideal of scalars
carrying `s` into the image, so no exponent uniform in `a` is wanted.

## References

* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent degreeNToGlobalSections homogeneousScalarGlobalSections)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- A fraction `mk w s` vanishes iff some element of the submonoid kills `w`. -/
private theorem mk_eq_zero_iff_exists_smul_eq_zero {T : Submonoid S} (w : M) (s : T) :
    LocalizedModule.mk w s = 0 ↔ ∃ u : T, u • w = 0 := by
  rw [← LocalizedModule.zero_mk (1 : T), LocalizedModule.mk_eq]
  simp only [Submonoid.smul_def, one_smul, smul_zero]

/-- A degree-one element to the `k`-th power shifts the degree of a homogeneous element by `k`. -/
private theorem pow_smul_mem_graded {τ : Type*} [SetLike τ M] (𝒨 : ℤ → τ)
    [SetLike.GradedSMul 𝒮 𝒨] {f : S} (hf : f ∈ 𝒮 1) {m : M} {e : ℤ} (hm : m ∈ 𝒨 e)
    (k : ℕ) {d : ℤ} (hd : (k : ℤ) + e = d) : f ^ k • m ∈ 𝒨 d :=
  hd ▸ SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) (by simpa using SetLike.pow_mem_graded k hf) hm

/-- **A homogeneous element dying in every fiber over `D₊(g)` is killed by a power of `g`.** The
fraction `w / g ^ 0` lies in the degree-zero part of the localization away from `g`, its section
over `D₊(g)` is the zero function, and the standard-open comparison is injective; so the fraction
itself is zero, which says that a power of `g` kills `w`. -/
theorem exists_pow_smul_eq_zero_of_forall_mk_eq_zero {g : S} {c : ℕ} (hg : g ∈ 𝒮 c) (hc : 0 < c)
    {e : ℤ} (w : M) (hw : w ∈ 𝒨 e)
    (h : ∀ (y : ProjectiveSpectrum.top 𝒮),
      g ∈ y.asHomogeneousIdeal.toIdeal.primeCompl →
        LocalizedModule.mk w (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) = 0) :
    ∃ N : ℕ, g ^ N • w = 0 := by
  have hw' : w ∈ shiftedGrading 𝒨 e (0 • (c : ℤ)) := by
    simpa only [shiftedGrading, zero_smul, zero_add] using hw
  have hzero : degreeZeroToSection 𝒮 (shiftedGrading 𝒨 e) g
      (degreeZeroFraction 𝒮 (shiftedGrading 𝒨 e) hg 0 w hw') = 0 := by
    refine Subtype.ext (funext fun y => ?_)
    have hval := degreeZeroToSection_fraction 𝒮 (shiftedGrading 𝒨 e) hg 0 w hw' y
    have hone : (⟨g ^ 0, y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem y.2 0⟩ :
        y.1.asHomogeneousIdeal.toIdeal.primeCompl) = 1 := Subtype.ext (pow_zero g)
    rw [hval, hone]
    exact h y.1 y.2
  have hz0 : degreeZeroFraction 𝒮 (shiftedGrading 𝒨 e) hg 0 w hw' = 0 :=
    degreeZeroToSection_injective 𝒮 (shiftedGrading 𝒨 e) hg hc
      (hzero.trans (map_zero _).symm)
  have hmk : LocalizedModule.mk w (⟨g ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers g) = 0 :=
    congrArg Subtype.val hz0
  obtain ⟨⟨_, N, rfl⟩, hu⟩ := (mk_eq_zero_iff_exists_smul_eq_zero w _).1 hmk
  exact ⟨N, hu⟩

/-- **Clearing denominators.** Let the degree-one elements `f b` be such that no homogeneous
prime of `Proj 𝒮` contains all of them — equivalently, their standard opens cover `Proj 𝒮` — let
`s` be a global section of `M(n)~` and fix an index `a`. Then some power `f a ^ K` carries `s`
into the image of the canonical map `𝒨 (K + n) ⟶ Γ(Proj 𝒮, M(K + n)~)` of Equation 01MR.

On `D₊(f b)` the section is a single fraction `m b / f b ^ k b`; the two fractions agree on the
overlaps, so a power of `f a * f b` kills `f b ^ {k b} · m a - f a ^ {k a} · m b`, and with `N`
large enough to serve every `b` the element `f a ^ N · m a` of degree `k a + N + n` represents
`f a ^ {k a + N} · s` at every point. -/
theorem exists_pow_smul_eq_degreeNToGlobalSections {ι : Type*} [Finite ι] (f : ι → S)
    (hf : ∀ i, f i ∈ 𝒮 1)
    (hcover : ∀ y : ProjectiveSpectrum.top 𝒮,
      ∃ i, f i ∈ y.asHomogeneousIdeal.toIdeal.primeCompl)
    {n : ℤ} (s : shiftedSectionsComponent 𝒮 𝒨 n) (a : ι) :
    ∃ (K : ℕ) (m : M) (hm : m ∈ 𝒨 ((K : ℤ) + n)),
      homogeneousScalarGlobalSections 𝒮 𝒨 K n
          ⟨f a ^ K, by simpa using SetLike.pow_mem_graded K (hf a)⟩ s =
        degreeNToGlobalSections 𝒮 𝒨 ((K : ℤ) + n) ⟨m, hm⟩ := by
  classical
  -- the fraction representing `s` on each `D₊(f b)`
  have hlocal : ∀ b : ι, ∃ (k : ℕ) (m : M), m ∈ 𝒨 ((k : ℤ) + n) ∧
      ∀ (y : ProjectiveSpectrum.top 𝒮) (hy : f b ∈ y.asHomogeneousIdeal.toIdeal.primeCompl),
        sectionValue 𝒮 𝒨 n s y =
          LocalizedModule.mk m
            ⟨f b ^ k, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy k⟩ := by
    intro b
    obtain ⟨k, m, hm, hval⟩ := exists_forall_sectionValue_eq_mk 𝒮 𝒨 s (hf b) Nat.one_pos
    exact ⟨k, m, by simpa using hm, hval⟩
  choose k m hm hval using hlocal
  -- the two fractions agree on the overlaps, so a power of `f a * f b` kills the difference
  have hpair : ∀ b : ι, ∃ N : ℕ,
      (f a * f b) ^ N • (f b ^ k b • m a - f a ^ k a • m b) = 0 := by
    intro b
    refine exists_pow_smul_eq_zero_of_forall_mk_eq_zero 𝒮 𝒨
      (SetLike.mul_mem_graded (hf a) (hf b)) (by omega)
      (e := ((k a : ℤ) + (k b : ℤ) + n)) _ ?_ ?_
    · exact sub_mem (pow_smul_mem_graded 𝒮 𝒨 (hf b) (hm a) (k b) (by ring))
        (pow_smul_mem_graded 𝒮 𝒨 (hf a) (hm b) (k a) (by ring))
    · intro y hy
      have hya : f a ∈ y.asHomogeneousIdeal.toIdeal.primeCompl := fun hmem =>
        hy (Ideal.mul_mem_right _ _ hmem)
      have hyb : f b ∈ y.asHomogeneousIdeal.toIdeal.primeCompl := fun hmem =>
        hy (Ideal.mul_mem_left _ _ hmem)
      have heq : LocalizedModule.mk (m a)
            (⟨f a ^ k a, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hya (k a)⟩ :
              y.asHomogeneousIdeal.toIdeal.primeCompl) =
          LocalizedModule.mk (m b)
            (⟨f b ^ k b, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hyb (k b)⟩ :
              y.asHomogeneousIdeal.toIdeal.primeCompl) :=
        (hval a y hya).symm.trans (hval b y hyb)
      rw [LocalizedModule.mk_eq] at heq
      obtain ⟨u, hu⟩ := heq
      rw [mk_eq_zero_iff_exists_smul_eq_zero]
      refine ⟨u, ?_⟩
      simp only [Submonoid.smul_def, smul_sub] at hu ⊢
      rw [hu, sub_self]
  choose N hN using hpair
  have := Fintype.ofFinite ι
  set N₀ : ℕ := Finset.univ.sup N with hN₀
  have hNle : ∀ b : ι, N b ≤ N₀ := fun b => Finset.le_sup (Finset.mem_univ b)
  have hN' : ∀ b : ι, (f a * f b) ^ N₀ • (f b ^ k b • m a - f a ^ k a • m b) = 0 := by
    intro b
    have hsplit : (f a * f b) ^ N₀ = (f a * f b) ^ (N₀ - N b) * (f a * f b) ^ N b := by
      rw [← pow_add]
      congr 1
      have := hNle b
      omega
    rw [hsplit, mul_smul, hN b, smul_zero]
  -- the element of `M` representing `f a ^ (k a + N₀) · s`
  refine ⟨k a + N₀, f a ^ N₀ • m a, ?_, ?_⟩
  · exact pow_smul_mem_graded 𝒮 𝒨 (hf a) (hm a) N₀ (by push_cast; ring)
  · refine shiftedSectionsComponent_ext 𝒮 𝒨 fun y => ?_
    obtain ⟨b, hyb⟩ := hcover y
    have hpow : f b ^ N₀ ∈ y.asHomogeneousIdeal.toIdeal.primeCompl :=
      y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hyb N₀
    rw [sectionValue_homogeneousScalarGlobalSections, sectionValue_degreeNToGlobalSections,
      hval b y hyb, LocalizedModule.smul'_mk]
    refine LocalizedModule.mk_eq.mpr ⟨⟨f b ^ N₀, hpow⟩, ?_⟩
    have h0 : ((f a * f b) ^ N₀ : S) • (f b ^ k b • m a) =
        ((f a * f b) ^ N₀ : S) • (f a ^ k a • m b) := by
      rw [← sub_eq_zero, ← smul_sub]
      exact hN' b
    rw [smul_smul, smul_smul] at h0
    have hL : (⟨f b ^ N₀, hpow⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) •
          (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) •
            ((⟨f a ^ (k a + N₀), by simpa using SetLike.pow_mem_graded (k a + N₀) (hf a)⟩ :
              𝒮 (k a + N₀)) : S) • m b =
        ((f a * f b) ^ N₀ * f a ^ k a : S) • m b := by
      simp only [Submonoid.smul_def, one_smul, smul_smul]
      congr 1
      ring
    have hR : (⟨f b ^ N₀, hpow⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) •
          (⟨f b ^ k b, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hyb (k b)⟩ :
            y.asHomogeneousIdeal.toIdeal.primeCompl) • (f a ^ N₀ • m a) =
        ((f a * f b) ^ N₀ * f b ^ k b : S) • m a := by
      simp only [Submonoid.smul_def, smul_smul]
      congr 1
      ring
    exact hL.trans (h0.symm.trans hR.symm)

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
