module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GoodSequenceFiveFold
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Automorphisms
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthOnePrimeSupport
public import StacksFrontier.RingTheory.Support.Finite
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length

/-!
# The multiplicity of a two-periodic complex as a sum of determinant orders

For a finite module over a Noetherian local ring whose support has dimension one, the
multiplicity of a two-periodic complex with finite-length cohomology is minus the sum, over the
minimal points of the support, of the orders of the periodic determinants of its localizations.

Applied to the `(2, 1)`-periodic complex whose first map vanishes, this computes the additive
Herbrand quotient of a single endomorphism `ψ` of a finite module whose support has dimension at
most one: the length of the cokernel of `ψ` minus the length of its kernel is the sum, over the
nonclosed points `q` of the support, of the order of vanishing of the residue-field determinant
of the automorphism `ψ_q`.

## Main results

* `AlgebraicGeometry.neg_periodicLength_eq_finsum_ordFrac_periodicDeterminant` is the formula.
* `AlgebraicGeometry.length_quotient_sub_length_ker_eq_finsum_ordOfResidueUnit` is its
  specialization to the Herbrand quotient of an endomorphism.

## Implementation notes

The witnesses needed to form each determinant — one-dimensionality of the residue ring at the
prime, finite length of the localization, and the two exactness assertions — are consequences of
the hypotheses rather than extra assumptions, so they appear as existentials in the conclusion;
the sum is a `finsum` over the subtype of minimal points. The proof reduces to the
two-point-support case and composes the five-sequence computation there.

In the Herbrand-quotient formula the index set is the subtype of nonclosed points of the support,
which in dimension at most one is the source's list `q₁, …, qₜ`; the bijectivity of each
localized map is likewise a witness in the conclusion rather than an assumption. The support
dimension is allowed to drop to zero, where the index set is empty and the module has finite
length.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
* [Stacks Project, Tag 02QE](https://stacks.math.columbia.edu/tag/02QE)
-/

@[expose] public section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- **Stacks Project, Tag 02QD.** Let `R` be a Noetherian local ring and `(M, φ, ψ)` a
`(2, 1)`-periodic complex with `M` finite, the cohomology of finite length and the support of `M`
of dimension one. Then minus the multiplicity of the complex is the sum, over the minimal points
of the support, of the orders of the periodic determinants of the localizations. -/
@[stacks 02QD]
theorem neg_periodicLength_eq_finsum_ordFrac_periodicDeterminant
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (hcoh : ∀ i : ZMod 2, IsFiniteLength R ((twoPeriodicComplex φ ψ hφψ hψφ).homology i))
    (hdim : Module.supportDim R M = 1) :
    ∃ hdim1 : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
        Ring.KrullDimLE 1 (R ⧸ q.1.asIdeal),
    ∃ hfin : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
        IsFiniteLength (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl M),
    ∃ hex₁ : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
        Function.Exact (LocalizedModule.map q.1.asIdeal.primeCompl φ)
          (LocalizedModule.map q.1.asIdeal.primeCompl ψ),
    ∃ hex₂ : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
        Function.Exact (LocalizedModule.map q.1.asIdeal.primeCompl ψ)
          (LocalizedModule.map q.1.asIdeal.primeCompl φ),
      -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
        ∑ᶠ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
          letI := hdim1 q
          Multiplicative.toAdd (WithZero.unzero
            (x := Ring.ordFrac (R ⧸ q.1.asIdeal)
              ((periodicDeterminant (LocalizedModule.map q.1.asIdeal.primeCompl φ)
                (LocalizedModule.map q.1.asIdeal.primeCompl ψ)
                (hex₁ q) (hex₂ q) (hfin q) : q.1.asIdeal.ResidueField)))
            (((periodicDeterminant (LocalizedModule.map q.1.asIdeal.primeCompl φ)
                (LocalizedModule.map q.1.asIdeal.primeCompl ψ)
                (hex₁ q) (hex₂ q) (hfin q)).isUnit.map
              (Ring.ordFrac (R ⧸ q.1.asIdeal))).ne_zero)) := by
  classical
  have hne : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
      q.1 ≠ IsLocalRing.closedPoint R := by
    intro q
    have hset := minimal_support_eq_nonclosed (R := R) (M := M) hdim
    rw [Set.ext_iff] at hset
    exact ((hset q.1).mp q.2).2
  have hdim1 : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
      Ring.KrullDimLE 1 (R ⧸ q.1.asIdeal) := fun q ↦
    Ring.krullDimLE_iff.mpr
      (ringKrullDim_quotient_eq_one_of_supportDim_eq_one hdim q.2.1 (hne q)).le
  have hfinq : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
      IsFiniteLength (Localization.AtPrime q.1.asIdeal)
        (LocalizedModule q.1.asIdeal.primeCompl M) := fun q ↦
    Module.length_ne_top_iff.mp (localized_length_ne_top q.1 q.2)
  have hH0 : IsFiniteLength R (↥(LinearMap.ker φ) ⧸
      (LinearMap.range ψ).comap (LinearMap.ker φ).subtype) := by
    have hh := homology_length_eq_ker_quotient φ ψ hφψ hψφ (0 : ZMod 2) (Or.inl rfl)
    rw [ite_eq_left rfl] at hh
    rw [← Module.length_ne_top_iff, ← hh, Module.length_ne_top_iff]
    exact hcoh 0
  have hH1 : IsFiniteLength R (↥(LinearMap.ker ψ) ⧸
      (LinearMap.range φ).comap (LinearMap.ker ψ).subtype) := by
    have hh := homology_length_eq_ker_quotient φ ψ hφψ hψφ (1 : ZMod 2) (Or.inr rfl)
    rw [ite_eq_right (by decide : ¬((1 : ZMod 2) = 0))] at hh
    rw [← Module.length_ne_top_iff, ← hh, Module.length_ne_top_iff]
    exact hcoh 1
  have hpid : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
      q.1.asIdeal ≠ IsLocalRing.maximalIdeal R := fun q h ↦ hne q (PrimeSpectrum.ext h)
  have hex₂ : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
      Function.Exact (LocalizedModule.map q.1.asIdeal.primeCompl ψ)
        (LocalizedModule.map q.1.asIdeal.primeCompl φ) := fun q ↦
    exact_localizedModule_map_of_isFiniteLength_homology φ ψ hφψ q.1.asIdeal (hpid q) hH0
  have hex₁ : ∀ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
      Function.Exact (LocalizedModule.map q.1.asIdeal.primeCompl φ)
        (LocalizedModule.map q.1.asIdeal.primeCompl ψ) := fun q ↦
    exact_localizedModule_map_of_isFiniteLength_homology ψ φ hψφ q.1.asIdeal (hpid q) hH1
  have hbase : ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (φ' ψ' : Module.End R N) (hφψ' : φ' * ψ' = 0) (hψφ' : ψ' * φ' = 0) (p : PrimeSpectrum R),
      HasFiniteLengthHomology (twoPeriodicComplex φ' ψ' hφψ' hψφ') →
      Module.support R N ⊆ {IsLocalRing.closedPoint R, p} →
      p ≠ IsLocalRing.closedPoint R → p ∈ Module.support R M →
      -periodicLength (twoPeriodicComplex φ' ψ' hφψ' hψφ') =
        periodicDeterminantOrder φ' ψ' p := by
    intro N _ _ _ φ' ψ' hφψ' hψφ' p hfin' hsupp' hpne hpM
    have hdimp := ringKrullDim_quotient_eq_one_of_supportDim_eq_one hdim hpM hpne
    have hKD : Ring.KrullDimLE 1 (R ⧸ p.asIdeal) := Ring.krullDimLE_iff.mpr hdimp.le
    have hMq := isFiniteLength_localizedModule_of_support_subset_pair p hpne hsupp'
    have hpid' : p.asIdeal ≠ IsLocalRing.maximalIdeal R := fun h ↦ hpne (PrimeSpectrum.ext h)
    have hK0 : IsFiniteLength R (↥(LinearMap.ker φ') ⧸
        (LinearMap.range ψ').comap (LinearMap.ker φ').subtype) := by
      have hh := homology_length_eq_ker_quotient φ' ψ' hφψ' hψφ' (0 : ZMod 2) (Or.inl rfl)
      rw [ite_eq_left rfl] at hh
      rw [← Module.length_ne_top_iff, ← hh, Module.length_ne_top_iff]
      exact hfin' 0
    have hK1 : IsFiniteLength R (↥(LinearMap.ker ψ') ⧸
        (LinearMap.range φ').comap (LinearMap.ker ψ').subtype) := by
      have hh := homology_length_eq_ker_quotient φ' ψ' hφψ' hψφ' (1 : ZMod 2) (Or.inr rfl)
      rw [ite_eq_right (by decide : ¬((1 : ZMod 2) = 0))] at hh
      rw [← Module.length_ne_top_iff, ← hh, Module.length_ne_top_iff]
      exact hfin' 1
    have he2 := exact_localizedModule_map_of_isFiniteLength_homology φ' ψ' hφψ' p.asIdeal
      hpid' hK0
    have he1 := exact_localizedModule_map_of_isFiniteLength_homology ψ' φ' hψφ' p.asIdeal
      hpid' hK1
    obtain ⟨b, a, x, t, y, s, xt, st, wφ, wψ, z, hy, hs, hwφ, hwψ, hxf, htf, hyf, hsf,
      hwφf, hwψf, hzf, hXK, hTK, hSX, hYT, hZφ, hZψ, hfinφ, hfinψ, hfinX, hfinT, hfinZ⟩ :=
      exists_sequences_of_support_subset_pair φ' ψ' hφψ' hψφ' p hpne hsupp' hfin'
    rw [periodicDeterminantOrder_eq φ' ψ' p hKD hMq he1 he2]
    exact neg_periodicLength_eq_toAdd_unzero_ordFrac_periodicDeterminant_of_sequences
      φ' ψ' hφψ' hψφ' p.asIdeal hdimp hMq he1 he2 x t y s xt st wφ wψ z hy hs hwφ hwψ
      rfl rfl rfl rfl rfl rfl rfl hxf htf hyf hsf hwφf hwψf hzf hXK hTK hSX hYT hZφ hZψ
      hfinφ hfinψ hfinX hfinT hfinZ
  refine ⟨hdim1, hfinq, hex₁, hex₂, ?_⟩
  have key := neg_periodicLength_eq_finsum_nonclosed_of_twoPoint hdim hbase M φ ψ hφψ hψφ
    hcoh subset_rfl
  rw [← finsum_minimal_support_eq_finsum_nonclosed hdim] at key
  rw [key]
  exact finsum_congr fun q ↦
    periodicDeterminantOrder_eq φ ψ q.1 (hdim1 q) (hfinq q) (hex₁ q) (hex₂ q)

/-- Two elements of `ℤᵐ⁰` inverse to each other have opposite orders. -/
private lemma toAdd_unzero_eq_neg_of_eq_inv {x y : WithZero (Multiplicative ℤ)}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : x = y⁻¹) :
    Multiplicative.toAdd (WithZero.unzero hx) =
      -Multiplicative.toAdd (WithZero.unzero hy) := by
  have key : WithZero.unzero hx * WithZero.unzero hy = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
      WithZero.coe_one, h, inv_mul_cancel₀ hy]
  have hsum := congrArg Multiplicative.toAdd key
  rw [toAdd_mul, toAdd_one] at hsum
  omega

/-- The order of vanishing of the inverse of a residue-field unit is minus its order. -/
private lemma ordOfResidueUnit_inv {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : PrimeSpectrum R) [p.asIdeal.IsPrime] [Ring.KrullDimLE 1 (R ⧸ p.asIdeal)]
    (u : (p.asIdeal.ResidueField)ˣ) :
    ordOfResidueUnit p u⁻¹ = -ordOfResidueUnit p u :=
  toAdd_unzero_eq_neg_of_eq_inv _ _ (by rw [Units.val_inv_eq_inv_val, map_inv₀])

/-- The periodic determinant of a vanishing first map and a bijective second map is the inverse
of the determinant of the automorphism that the second map defines. -/
private lemma periodicDeterminant_eq_inv_determinantAutomorphism {A : Type u} {N : Type v}
    [CommRing A] [IsLocalRing A] [AddCommGroup N] [Module A N]
    (f g : N →ₗ[A] N) (hf : f = 0) (hg : Function.Bijective g)
    (h₁ : Function.Exact f g) (h₂ : Function.Exact g f) (hN : IsFiniteLength A N) :
    periodicDeterminant f g h₁ h₂ hN =
      (determinantAutomorphism (LinearEquiv.ofBijective g hg) hN)⁻¹ := by
  subst hf
  exact periodicDeterminant_zero_equiv (LinearEquiv.ofBijective g hg) hN

/-- An element of `WithBot ℕ∞` bounded by one is either one or nonpositive. -/
private lemma eq_one_or_le_zero {n : WithBot ℕ∞} (h : n ≤ 1) : n = 1 ∨ n ≤ 0 := by
  by_cases h0 : n ≤ 0
  · exact .inr h0
  · exact .inl (le_antisymm h ((ENat.WithBot.add_one_le_iff (n := 0)).2 (lt_of_not_ge h0)))

/-- Over a local ring, a module whose support has dimension at most zero is supported only at
the closed point. -/
private lemma eq_closedPoint_of_supportDim_le_zero {R : Type u} {M : Type v} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] (hM : Module.supportDim R M ≤ 0)
    (q : PrimeSpectrum R) (hq : q ∈ Module.support R M) : q = IsLocalRing.closedPoint R := by
  by_contra hne
  have hle : q ≤ IsLocalRing.closedPoint R :=
    IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  exact (not_lt_of_ge hM) (Order.krullDim_pos_iff.mpr
    ⟨⟨q, hq⟩, ⟨IsLocalRing.closedPoint R, Module.mem_support_mono hle hq⟩,
      lt_of_le_of_ne hle (fun he => hne (congrArg Subtype.val he))⟩)

/-- A finite module over a Noetherian local ring whose support has dimension at most zero has
finite length. -/
private lemma isFiniteLength_of_supportDim_le_zero {R : Type u} {M : Type v} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.supportDim R M ≤ 0) : IsFiniteLength R M := by
  rcases subsingleton_or_nontrivial M with _ | _
  · exact IsFiniteLength.of_subsingleton
  · refine isFiniteLength_of_support (Set.eq_singleton_iff_unique_mem.mpr
      ⟨IsLocalRing.closedPoint_mem_support R M, ?_⟩)
    exact fun q hq => eq_closedPoint_of_supportDim_le_zero hM q hq

/-- **Stacks Project, Tag 02QE.** Let `R` be a Noetherian local ring, `M` a finite `R`-module
whose support has dimension at most one, and `ψ : M → M` an `R`-linear map whose kernel and
cokernel have finite length. Then the length of the cokernel minus the length of the kernel is
the sum, over the nonclosed points `q` of the support of `M`, of the order of vanishing along
`R ⧸ q` of the residue-field determinant of the automorphism `ψ_q` of `M_q`. -/
@[stacks 02QE]
theorem length_quotient_sub_length_ker_eq_finsum_ordOfResidueUnit
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (ψ : Module.End R M)
    (hker : IsFiniteLength R (LinearMap.ker ψ))
    (hcoker : IsFiniteLength R (M ⧸ LinearMap.range ψ))
    (hdim : Module.supportDim R M ≤ 1) :
    ∃ hdim1 : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        Ring.KrullDimLE 1 (R ⧸ q.1.asIdeal),
    ∃ hfin : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        IsFiniteLength (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl M),
    ∃ hbij : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        Function.Bijective (LocalizedModule.map q.1.asIdeal.primeCompl ψ),
      ((Module.length R (M ⧸ LinearMap.range ψ)).toNat : ℤ) -
          ((Module.length R (LinearMap.ker ψ)).toNat : ℤ) =
        ∑ᶠ q : {q : PrimeSpectrum R //
            q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
          @ordOfResidueUnit R _ _ q.1 q.1.isPrime (hdim1 q)
            (determinantAutomorphism
              (LinearEquiv.ofBijective
                (LocalizedModule.map q.1.asIdeal.primeCompl ψ) (hbij q)) (hfin q)) := by
  classical
  have hmap0 : ∀ q : PrimeSpectrum R,
      LocalizedModule.map q.asIdeal.primeCompl (0 : Module.End R M) = 0 := fun q => map_zero _
  rcases eq_one_or_le_zero hdim with hone | hzero
  · have hi : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
    have hcoh : ∀ i : ZMod 2, IsFiniteLength R
        ((twoPeriodicComplex (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ)).homology i) := by
      intro i
      rcases hi i with rfl | rfl
      · rw [← Module.length_ne_top_iff, length_homology_zero_eq_length_quotient,
          Module.length_ne_top_iff]
        exact hcoker
      · rw [← Module.length_ne_top_iff, length_homology_one_eq_length_ker,
          Module.length_ne_top_iff]
        exact hker
    obtain ⟨hdimT, hfinT, hexT₁, hexT₂, hformula⟩ :=
      neg_periodicLength_eq_finsum_ordFrac_periodicDeterminant
        (0 : Module.End R M) ψ (zero_mul ψ) (mul_zero ψ) hcoh hone
    have hset : ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q ↔
        (q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R) :=
      fun q => Set.ext_iff.mp (minimal_support_eq_nonclosed hone) q
    have hdimS : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        Ring.KrullDimLE 1 (R ⧸ q.1.asIdeal) := fun q => hdimT ⟨q.1, (hset q.1).mpr q.2⟩
    have hfinS : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        IsFiniteLength (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl M) :=
      fun q => hfinT ⟨q.1, (hset q.1).mpr q.2⟩
    have hexS₁ : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        Function.Exact (LocalizedModule.map q.1.asIdeal.primeCompl (0 : Module.End R M))
          (LocalizedModule.map q.1.asIdeal.primeCompl ψ) :=
      fun q => hexT₁ ⟨q.1, (hset q.1).mpr q.2⟩
    have hexS₂ : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        Function.Exact (LocalizedModule.map q.1.asIdeal.primeCompl ψ)
          (LocalizedModule.map q.1.asIdeal.primeCompl (0 : Module.End R M)) :=
      fun q => hexT₂ ⟨q.1, (hset q.1).mpr q.2⟩
    have hbij : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        Function.Bijective (LocalizedModule.map q.1.asIdeal.primeCompl ψ) := by
      intro q
      refine ⟨LinearMap.ker_eq_bot.mp ?_, LinearMap.range_eq_top.mp ?_⟩
      · rw [LinearMap.exact_iff.mp (hexS₁ q), hmap0 q.1, LinearMap.range_zero]
      · rw [← LinearMap.exact_iff.mp (hexS₂ q), hmap0 q.1, LinearMap.ker_zero]
    refine ⟨hdimS, hfinS, hbij, ?_⟩
    have h1 : -periodicLength (twoPeriodicComplex (0 : Module.End R M) ψ
          (zero_mul ψ) (mul_zero ψ)) =
        ∑ᶠ q : {q : PrimeSpectrum R // Minimal (· ∈ Module.support R M) q},
          periodicDeterminantOrder (0 : Module.End R M) ψ q.1 :=
      hformula.trans (finsum_congr fun q =>
        (periodicDeterminantOrder_eq (0 : Module.End R M) ψ q.1
          (hdimT q) (hfinT q) (hexT₁ q) (hexT₂ q)).symm)
    have h2 : -periodicLength (twoPeriodicComplex (0 : Module.End R M) ψ
          (zero_mul ψ) (mul_zero ψ)) =
        ∑ᶠ q : {q : PrimeSpectrum R //
            q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
          periodicDeterminantOrder (0 : Module.End R M) ψ q.1 :=
      h1.trans (finsum_minimal_support_eq_finsum_nonclosed hone
        (fun p => periodicDeterminantOrder (0 : Module.End R M) ψ p))
    have hterm : ∀ q : {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R},
        periodicDeterminantOrder (0 : Module.End R M) ψ q.1 =
          -(@ordOfResidueUnit R _ _ q.1 q.1.isPrime (hdimS q)
            (determinantAutomorphism
              (LinearEquiv.ofBijective
                (LocalizedModule.map q.1.asIdeal.primeCompl ψ) (hbij q)) (hfinS q))) := by
      intro q
      rw [periodicDeterminantOrder_eq (0 : Module.End R M) ψ q.1
        (hdimS q) (hfinS q) (hexS₁ q) (hexS₂ q),
        periodicDeterminant_eq_inv_determinantAutomorphism _ _ (hmap0 q.1) (hbij q)]
      exact ordOfResidueUnit_inv _ _
    rw [finsum_congr hterm, finsum_neg_distrib] at h2
    rw [← periodicLength_zero_eq_length_quotient_sub_length_ker ψ]
    exact neg_inj.mp h2
  · have hempty : IsEmpty {q : PrimeSpectrum R //
        q ∈ Module.support R M ∧ q ≠ IsLocalRing.closedPoint R} :=
      ⟨fun q => q.2.2 (eq_closedPoint_of_supportDim_le_zero hzero q.1 q.2.1)⟩
    refine ⟨fun q => isEmptyElim q, fun q => isEmptyElim q, fun q => isEmptyElim q, ?_⟩
    rw [finsum_of_isEmpty, ← periodicLength_zero_eq_length_quotient_sub_length_ker ψ]
    have hMfin : IsFiniteLength R M := isFiniteLength_of_supportDim_le_zero hzero
    exact periodicLength_eq_zero_of_iso _ hMfin (CategoryTheory.Iso.refl _)

end AlgebraicGeometry

end
