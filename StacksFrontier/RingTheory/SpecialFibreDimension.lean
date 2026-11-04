module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.RingTheory.DimensionFormulaMinimalPrimes
public import StacksFrontier.RingTheory.QuasiFinite.GenericFiniteness
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# The special fibre of a generically finite algebra over a local domain

Let `(A, 𝔪)` be a Noetherian local domain of dimension at least one and let `C` be an
`A`-algebra of finite type whose primes lying over `(0)` are exactly its minimal primes. Then
the special fibre `C ⧸ 𝔪C` has dimension at most `dim(A) - 1`.

The generic condition forces the fibre of `Spec(C) → Spec(A)` over the generic point to be the
finite set of minimal primes of `C`, so that `A` becomes finite over `C` after inverting a
single nonzero element; hence `C` is algebraic over `A` and every residue field extension at a
minimal prime of `C` has transcendence degree zero. The dimension formula then bounds the
height of a prime of `C` over `𝔪` by `dim(A)`, and a chain inside the special fibre gains one
step when it is continued down to a minimal prime, which does not lie over `𝔪`.

## Main results

* `Algebra.isAlgebraic_of_primesOver_bot_eq_minimalPrimes`: such an algebra is algebraic over
  its base.
* `ringKrullDim_quotient_map_maximalIdeal_add_one_le`: the dimension bound on the special
  fibre.
* `Algebra.relativeDimensionAt_add_one_le_ringKrullDim`: the same bound for the relative
  dimension at a prime lying over the maximal ideal, which is the local form read off the
  special fibre of `Spec(C) → Spec(A)` at that prime.

## Implementation notes

The generic condition is stated as an equivalence `r ∈ minimalPrimes C ↔ r ∩ A = (0)` for
prime `r`, which is the source's "the points lying over the generic point are the generic
points of the irreducible components". Both directions are used: one supplies the finiteness
feeding generic finiteness, the other supplies algebraicity at each minimal prime and the fact
that a minimal prime does not lie over `𝔪`.

The dimension bound is written as `dim(C ⧸ 𝔪C) + 1 ≤ dim(A)` in `WithBot ℕ∞`, the codomain of
`ringKrullDim`; the subtraction in the source's `dim ≤ dim(A) - 1` is not available there. The
dimension formula is used in the form
`height_add_trdeg_residue_le_of_forall_minimalPrimes`, which needs no integrality of `C`.

## References

* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [Stacks Project, Tag 02ML](https://stacks.math.columbia.edu/tag/02ML)
-/

@[expose] public section

universe u v

namespace Stacks.SpecialFibreDimension

/-- An algebra which becomes module-finite over the base after inverting a single nonzero
element of a domain is algebraic over that base. -/
private theorem isAlgebraic_of_away_map_finite
    {A : Type u} [CommRing A] [IsDomain A] {C : Type v} [CommRing C] [Algebra A C]
    {g : A} (hg : g ≠ 0)
    (hfin : (IsLocalization.Away.map (Localization.Away g)
      (Localization.Away (algebraMap A C g)) (algebraMap A C) g).Finite) :
    Algebra.IsAlgebraic A C := by
  classical
  let Ag := Localization.Away g
  let Cg := Localization.Away (algebraMap A C g)
  let _ : Algebra Ag Cg := (IsLocalization.Away.map Ag Cg (algebraMap A C) g).toAlgebra
  have : Module.Finite Ag Cg := hfin
  have htow : IsScalarTower A Ag Cg := IsScalarTower.of_algebraMap_eq fun a => by
    show (algebraMap A Cg) a =
      (IsLocalization.Away.map Ag Cg (algebraMap A C) g) ((algebraMap A Ag) a)
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
    exact IsScalarTower.algebraMap_apply A C Cg a
  have : IsDomain Ag :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers g) Ag
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg))
  have : Algebra.IsAlgebraic A Ag := IsLocalization.isAlgebraic Ag (Submonoid.powers g)
  have : Algebra.IsAlgebraic A Cg := Algebra.IsAlgebraic.trans A Ag Cg
  refine ⟨fun c => ?_⟩
  obtain ⟨P, hP0, hP⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) ((algebraMap C Cg) c)
  have hker : (algebraMap C Cg) (Polynomial.aeval c P) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq A C Cg]
    simpa [Polynomial.aeval_def] using hP
  obtain ⟨⟨m, k, hk⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A C g)) Cg _).mp hker
  refine ⟨Polynomial.C (g ^ k) * P, mul_ne_zero ?_ hP0, ?_⟩
  · simpa using pow_ne_zero k hg
  · have hmv : m = (algebraMap A C) (g ^ k) := by rw [← hk, map_pow]
    simp only [map_mul, Polynomial.aeval_C]
    rw [← hmv] at *
    simpa using hm

/-- A finite-type algebra over a Noetherian domain whose primes lying over `(0)` are exactly
its minimal primes is algebraic over the base. -/
theorem _root_.Algebra.isAlgebraic_of_primesOver_bot_eq_minimalPrimes
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {C : Type u} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (hgen : ∀ r : Ideal C, r.IsPrime → (r ∈ minimalPrimes C ↔ Ideal.under A r = ⊥)) :
    Algebra.IsAlgebraic A C := by
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  have hbot : (⊥ : Ideal A) ∈ minimalPrimes A := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact rfl
  have hfin : ((⊥ : Ideal A).primesOver C).Finite := by
    refine (minimalPrimes.finite_of_isNoetherianRing C).subset ?_
    rintro r ⟨hrp, hrl⟩
    exact (hgen r hrp).mpr (Ideal.LiesOver.over (p := (⊥ : Ideal A)) (P := r)).symm
  obtain ⟨g, hg, hmap⟩ :=
    Algebra.exists_localization_away_map_finite_of_mem_minimalPrimes_of_finite_primesOver
      hbot hfin
  exact isAlgebraic_of_away_map_finite (by simpa using hg)
    (hmap (Localization.Away g) (Localization.Away (algebraMap A C g)))

/-- At a minimal prime lying over `(0)` of an algebra which is algebraic over its base, the
residue field extension has transcendence degree zero. -/
private theorem trdeg_quotient_under_eq_zero
    {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]
    (halg : Algebra.IsAlgebraic A C) (r : Ideal C) [r.IsPrime]
    (hr : Ideal.under A r = ⊥) :
    Algebra.trdeg (A ⧸ Ideal.under A r) (C ⧸ r) = 0 := by
  have hinj : Function.Injective (Ideal.Quotient.mk (Ideal.under A r)) := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker]
    exact hr
  have : Algebra.IsAlgebraic (A ⧸ Ideal.under A r) (C ⧸ r) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP0, hP⟩ := halg.1 c
    refine ⟨P.map (Ideal.Quotient.mk (Ideal.under A r)), ?_, ?_⟩
    · simpa [Polynomial.map_eq_zero_iff hinj] using hP0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map,
        Ideal.algebraMap_quotient_under_comp_mk (R := A) r, ← Polynomial.hom_eval₂]
      simpa [Polynomial.aeval_def] using congrArg (Ideal.Quotient.mk r) hP
  exact trdeg_eq_zero

/-- A prime of `C` contains the extension of the maximal ideal of a local ring `A` iff it lies
over the maximal ideal. -/
private theorem map_maximalIdeal_le_iff_under_eq
    {A : Type u} [CommRing A] [IsLocalRing A] {C : Type u} [CommRing C] [Algebra A C]
    (q : Ideal C) [q.IsPrime] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A C) ≤ q ↔
      Ideal.under A q = IsLocalRing.maximalIdeal A :=
  ⟨fun h => ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
    (Ideal.IsPrime.ne_top (Ideal.comap_isPrime (algebraMap A C) q))
    (Ideal.map_le_iff_le_comap.mp h)).symm,
   fun h => Ideal.map_le_iff_le_comap.mpr h.ge⟩

/-- **The dimension of the special fibre.** Let `(A, 𝔪)` be a Noetherian local domain of
dimension at least one and let `C` be an `A`-algebra of finite type whose primes lying over
`(0)` are exactly its minimal primes. Then `dim(C ⧸ 𝔪C) + 1 ≤ dim(A)`. -/
theorem _root_.ringKrullDim_quotient_map_maximalIdeal_add_one_le
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {C : Type u} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (hdim : 1 ≤ ringKrullDim A)
    (hgen : ∀ r : Ideal C, r.IsPrime → (r ∈ minimalPrimes C ↔ Ideal.under A r = ⊥)) :
    ringKrullDim (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C)) + 1
      ≤ ringKrullDim A := by
  classical
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  set J : Ideal C := (IsLocalRing.maximalIdeal A).map (algebraMap A C) with hJdef
  have halg : Algebra.IsAlgebraic A C :=
    Algebra.isAlgebraic_of_primesOver_bot_eq_minimalPrimes hgen
  have hmh : 1 ≤ (IsLocalRing.maximalIdeal A).height := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hdim
    exact_mod_cast hdim
  have hmne : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_eq_zero_iff_eq_bot.mpr rfl] at hmh
    simp at hmh
  have key : ∀ qb : PrimeSpectrum (C ⧸ J),
      Order.height qb + 1 ≤ (IsLocalRing.maximalIdeal A).height := by
    intro qb
    set q : Ideal C := Ideal.comap (Ideal.Quotient.mk J) qb.asIdeal with hqdef
    have hqp : q.IsPrime := Ideal.comap_isPrime _ _
    have hJq : J ≤ q := fun x hx => by
      show Ideal.Quotient.mk J x ∈ qb.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Ideal.zero_mem _
    have hmapq : q.map (Ideal.Quotient.mk J) = qb.asIdeal :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    have hunder : Ideal.under A q = IsLocalRing.maximalIdeal A :=
      (map_maximalIdeal_le_iff_under_eq q).mp hJq
    have : q.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hunder.symm⟩
    have hform := height_add_trdeg_residue_le_of_forall_minimalPrimes
      (R := A) (S := C) (IsLocalRing.maximalIdeal A) q 0
      (fun r hrp hrmin _ => by
        have h0 : Ideal.under A r = ⊥ := (hgen r hrp).mp hrmin
        rw [Ideal.underResidueTrdeg_eq_toNat_trdeg_quotient (R := A) r,
          trdeg_quotient_under_eq_zero halg r h0]
        simp)
    have hqle : q.height ≤ (IsLocalRing.maximalIdeal A).height := by
      simpa using le_trans le_self_add hform
    refine le_trans ?_ hqle
    refine ENat.add_le_of_forall_natCast_le fun n hn => ?_
    have hqbh : Order.height qb =
        Order.height (⟨⟨q, hqp⟩, hJq⟩ : ↑(PrimeSpectrum.zeroLocus (J : Set C))) := by
      rw [← Ideal.height_map_quotientMk_eq_orderHeight J q hJq, hmapq,
        PrimeSpectrum.height_eq_orderHeight]
    rw [hqbh] at hn
    obtain ⟨s, hslast, hslen⟩ := Order.exists_series_of_le_height _ hn
    let s' : LTSeries (PrimeSpectrum C) :=
      s.map (fun x => x.1) (fun _ _ h => h)
    have hJhead : J ≤ s'.head.asIdeal := by
      have := s.head.2
      rw [PrimeSpectrum.mem_zeroLocus] at this
      exact this
    obtain ⟨p, hp, hple⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := s'.head.asIdeal) bot_le
    have hpp : p.IsPrime := hp.isPrime
    have hplt : (⟨p, hpp⟩ : PrimeSpectrum C) < s'.head := by
      refine lt_of_le_of_ne hple fun h => hmne (le_bot_iff.mp ?_)
      have h0 : Ideal.under A p = ⊥ := (hgen p hpp).mp hp
      have hJp : J ≤ p := by
        have hh : p = s'.head.asIdeal := congrArg PrimeSpectrum.asIdeal h
        exact hh ▸ hJhead
      rw [← h0]
      exact Ideal.map_le_iff_le_comap.mp hJp
    have hs'last : s'.last = (⟨q, hqp⟩ : PrimeSpectrum C) := by
      show ((s.last : ↑(PrimeSpectrum.zeroLocus (J : Set C))) : PrimeSpectrum C) = _
      rw [hslast]
    calc ((n : ℕ∞) + 1)
        = (((s'.cons ⟨p, hpp⟩ hplt).length : ℕ) : ℕ∞) := by
          rw [RelSeries.cons_length, show s'.length = n from hslen]
          push_cast
          ring
      _ ≤ Order.height (s'.cons ⟨p, hpp⟩ hplt).last := Order.length_le_height_last
      _ = q.height := by
          rw [RelSeries.last_cons, hs'last, ← PrimeSpectrum.height_eq_orderHeight]
  rcases isEmpty_or_nonempty (PrimeSpectrum (C ⧸ J)) with _ | _
  · rw [ringKrullDim, Order.krullDim_eq_iSup_height]
    simp
  · rw [ringKrullDim, Order.krullDim_eq_iSup_height_of_nonempty,
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← WithBot.coe_one, ← WithBot.coe_add,
      WithBot.coe_le_coe, ENat.iSup_add]
    exact iSup_le key

/-- **The relative dimension over the closed point.** Under the hypotheses of
`ringKrullDim_quotient_map_maximalIdeal_add_one_le`, the relative dimension of `C` over `A` at
a prime lying over the maximal ideal is at most `dim(A) - 1`. -/
theorem _root_.Algebra.relativeDimensionAt_add_one_le_ringKrullDim
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {C : Type u} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (hdim : 1 ≤ ringKrullDim A)
    (hgen : ∀ r : Ideal C, r.IsPrime → (r ∈ minimalPrimes C ↔ Ideal.under A r = ⊥))
    (𝔮 : Ideal C) [h𝔮p : 𝔮.IsPrime]
    (h𝔮 : Ideal.under A 𝔮 = IsLocalRing.maximalIdeal A) :
    Algebra.relativeDimensionAt A 𝔮 + 1 ≤ ringKrullDim A := by
  have hset : (PrimeSpectrum.comap (algebraMap A C) ⁻¹'
        {PrimeSpectrum.comap (algebraMap A C) (⟨𝔮, h𝔮p⟩ : PrimeSpectrum C)}) =
      PrimeSpectrum.zeroLocus
        (((IsLocalRing.maximalIdeal A).map (algebraMap A C) : Ideal C) : Set C) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe]
    rw [map_maximalIdeal_le_iff_under_eq, PrimeSpectrum.ext_iff]
    change Ideal.under A x.asIdeal = Ideal.under A 𝔮 ↔ _
    rw [h𝔮]
  have hle : Algebra.relativeDimensionAt A 𝔮
      ≤ ringKrullDim (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C)) := by
    rw [← topologicalKrullDim_zeroLocus ((IsLocalRing.maximalIdeal A).map (algebraMap A C)),
      ← hset]
    exact topologicalKrullDimAt_le_topologicalKrullDim _
  calc Algebra.relativeDimensionAt A 𝔮 + 1
      ≤ ringKrullDim (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C)) + 1 := by gcongr
    _ ≤ ringKrullDim A :=
        ringKrullDim_quotient_map_maximalIdeal_add_one_le (C := C) hdim hgen

end Stacks.SpecialFibreDimension

end
