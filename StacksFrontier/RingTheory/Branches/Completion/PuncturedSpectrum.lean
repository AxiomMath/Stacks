module

public import StacksFrontier.RingTheory.Branches.Completion.HenselizationToCompletion

@[expose] public section

/-!
# Punctured spectra of the completion and of the henselization

Let `A` be a Noetherian local ring with completion `Â` and henselization `Aʰ`. The punctured
spectrum of `Â` is disconnected if and only if that of `Aʰ` is.

## Main results

* `not_isConnected_puncturedSpectrum_adicCompletion_iff_henselization`: the punctured spectrum
  of `Â` is disconnected if and only if that of `Aʰ` is.

## References

* [The Stacks Project, Tag 0C2C](https://stacks.math.columbia.edu/tag/0C2C)
-/

universe u v w x y

open Topology
open IsLocalRing
open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits

/-- Two ideals with zero product whose common zero locus is the closed point annihilate each
other's conormal modules up to a power of the maximal ideal. -/
private theorem exists_maximalIdeal_pow_smul_cotangent_eq_bot_of_mul_eq_bot
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hmul : I * J = ⊥)
    (hclosed : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal → J ≤ p.asIdeal →
      p.asIdeal = maximalIdeal R) :
    ∃ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R I.Cotangent) = ⊥ := by
  have hI : I ≤ Module.annihilator R I.Cotangent := by
    intro x hx
    exact Module.mem_annihilator.mpr (Ideal.Cotangent.smul_eq_zero_of_mem hx)
  have hJ : J ≤ Module.annihilator R I.Cotangent := by
    intro x hx
    apply Module.mem_annihilator.mpr
    intro z
    obtain ⟨z, rfl⟩ := I.toCotangent_surjective z
    rw [← map_smul, Ideal.toCotangent_eq_zero]
    have hz : x * (z : R) = 0 := by
      have := Ideal.mul_mem_mul z.property hx
      rw [hmul, Ideal.mem_bot] at this
      simpa only [mul_comm] using this
    change x * (z : R) ∈ I ^ 2
    rw [hz]
    exact Ideal.zero_mem _
  have hrad : maximalIdeal R ≤ (Module.annihilator R I.Cotangent).radical := by
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro p ⟨hap, hp⟩
    exact (hclosed ⟨p, hp⟩ (hI.trans hap) (hJ.trans hap)).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (maximalIdeal R).fg_of_isNoetherianRing
  refine ⟨n, le_antisymm ?_ bot_le⟩
  rw [Submodule.smul_le]
  intro x hx z _
  exact (Module.mem_annihilator.mp (hn hx)) z

/-- A disconnection of the punctured spectrum of a Noetherian local ring is cut out by two
ideals with zero product meeting only at the closed point. -/
theorem exists_ideals_of_not_isPreconnected_puncturedSpectrum
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : ¬ _root_.IsPreconnected {p : PrimeSpectrum R | p.asIdeal ≠ maximalIdeal R}) :
    ∃ I J : Ideal R, I * J = ⊥ ∧
      (∀ p : PrimeSpectrum R, I ≤ p.asIdeal → J ≤ p.asIdeal →
        p.asIdeal = maximalIdeal R) ∧
      (∃ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R ∧ I ≤ p.asIdeal) ∧
      (∃ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R ∧ J ≤ p.asIdeal) := by
  classical
  rw [isPreconnected_closed_iff] at h
  push Not at h
  obtain ⟨U, V, hU, hV, hcover, ⟨p, hp, hpU⟩, ⟨q, hq, hqV⟩, hdisj⟩ := h
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal U).mp hU
  obtain ⟨J, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal V).mp hV
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top p.isPrime.ne_top hpU
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top q.isPrime.ne_top hqV
  have hnil : I * J ≤ nilradical R := by
    apply (PrimeSpectrum.zeroLocus_eq_univ_iff _).mp
    rw [PrimeSpectrum.zeroLocus_mul]
    apply Set.eq_univ_of_forall
    intro r
    by_cases hr : r.asIdeal = maximalIdeal R
    · exact Or.inl (by change I ≤ r.asIdeal; rw [hr]; exact le_maximalIdeal hI)
    · exact hcover hr
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnil
    (I * J).fg_of_isNoetherianRing
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hpow (K : Ideal R) (r : PrimeSpectrum R) : K ^ n ≤ r.asIdeal ↔ K ≤ r.asIdeal :=
    Ideal.IsPrime.pow_le_iff hn0
  refine ⟨I ^ n, J ^ n, ?_, ?_, ⟨p, hp, (hpow I p).mpr hpU⟩, ⟨q, hq, (hpow J q).mpr hqV⟩⟩
  · exact le_antisymm (by simpa only [mul_pow, Ideal.zero_eq_bot] using hn) bot_le
  · intro r hrI hrJ
    by_contra hr
    exact (Set.not_nonempty_iff_eq_empty.mpr hdisj)
      ⟨r, hr, (hpow I r).mp hrI, (hpow J r).mp hrJ⟩

private theorem comap_eq_maximalIdeal_iff
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hm : (maximalIdeal R).map f = maximalIdeal S) (p : PrimeSpectrum S) :
    p.asIdeal.comap f = maximalIdeal R ↔ p.asIdeal = maximalIdeal S := by
  constructor
  · intro hp
    apply le_antisymm (le_maximalIdeal p.isPrime.ne_top)
    rw [← hm, Ideal.map_le_iff_le_comap, hp]
  · rintro hp
    rw [hp, maximalIdeal_comap]

/-- The punctured spectrum of the completion of a Noetherian local ring is disconnected if and
only if the punctured spectrum of its henselization is disconnected. -/
@[stacks 0C2C]
theorem not_isConnected_puncturedSpectrum_adicCompletion_iff_henselization
    (A : Type u) (Ah : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    (¬ _root_.IsConnected {p : PrimeSpectrum Ahat | p.asIdeal ≠ maximalIdeal Ahat}) ↔
      ¬ _root_.IsConnected {p : PrimeSpectrum Ah | p.asIdeal ≠ maximalIdeal Ah} := by
  classical
  dsimp only
  let Ahat := AdicCompletion (maximalIdeal A) A
  obtain ⟨f⟩ := exists_algHom_adicCompletion_of_isHenselization A Ah
  have : IsLocalHom f.toRingHom := isLocalHom_of_isHenselization_algHom f
  have : HenselianLocalRing Ah := IsHenselization.henselian (R := A) (L := ResidueField A)
  have hm : (maximalIdeal Ah).map f.toRingHom = maximalIdeal Ahat := by
    rw [← IsHenselization.map_maximalIdeal (R := A) (L := ResidueField A) (Rh := Ah),
      Ideal.map_map]
    exact (congrArg (fun g : A →+* Ahat => (maximalIdeal A).map g)
      f.comp_algebraMap).trans (AdicCompletion.maximalIdeal_eq_map_of_fg
        (maximalIdeal A).fg_of_isNoetherianRing).symm
  have hsurj : Function.Surjective (PrimeSpectrum.comap f.toRingHom) := by
    have hf := flat_of_isHenselization_algHom f
    let : Algebra Ah Ahat := f.toRingHom.toAlgebra
    have : Module.Flat Ah Ahat := hf
    have : Module.FaithfullyFlat Ah Ahat := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hpunct (p : PrimeSpectrum Ahat) :
      (PrimeSpectrum.comap f.toRingHom p).asIdeal ≠ maximalIdeal Ah ↔
        p.asIdeal ≠ maximalIdeal Ahat :=
    not_congr (comap_eq_maximalIdeal_iff f.toRingHom hm p)
  have himage : PrimeSpectrum.comap f.toRingHom ''
      {p : PrimeSpectrum Ahat | p.asIdeal ≠ maximalIdeal Ahat} =
      {p : PrimeSpectrum Ah | p.asIdeal ≠ maximalIdeal Ah} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (hpunct q).mpr hq
    · intro hp
      obtain ⟨q, rfl⟩ := hsurj p
      exact ⟨q, (hpunct q).mp hp, rfl⟩
  apply not_congr
  constructor
  · intro h
    rw [← himage]
    exact h.image _ (PrimeSpectrum.continuous_comap f.toRingHom).continuousOn
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← Set.image_nonempty, himage]
      exact h.nonempty
    · by_contra hn
      obtain ⟨I, J, hmul, hclosed, hI, hJ⟩ :=
        exists_ideals_of_not_isPreconnected_puncturedSpectrum Ahat hn
      have hext (I J : Ideal Ahat) (hmul : I * J = ⊥)
          (hclosed : ∀ p : PrimeSpectrum Ahat, I ≤ p.asIdeal → J ≤ p.asIdeal →
            p.asIdeal = maximalIdeal Ahat)
          (hI : ∃ p : PrimeSpectrum Ahat, p.asIdeal ≠ maximalIdeal Ahat ∧ I ≤ p.asIdeal) :
          ∃ Ih : Ideal Ah, Ih.map f.toRingHom = I := by
        obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_smul_cotangent_eq_bot_of_mul_eq_bot
          I J hmul hclosed
        obtain ⟨D, hD, hAD, hfinite, he⟩ := exists_finiteType_completion_quotient A I n hn
        obtain ⟨p, _, hp⟩ := hI
        exact exists_ideal_map_eq_of_algebraization A Ah f I
          (ne_top_of_le_ne_top p.isPrime.ne_top hp) D hD hAD hfinite he
      obtain ⟨Ih, hIh⟩ := hext I J hmul hclosed hI
      obtain ⟨Jh, hJh⟩ := hext J I (by rwa [mul_comm])
        (fun p hpJ hpI => hclosed p hpI hpJ) hJ
      have hcover : {p : PrimeSpectrum Ah | p.asIdeal ≠ maximalIdeal Ah} ⊆
          PrimeSpectrum.zeroLocus (Ih : Set Ah) ∪ PrimeSpectrum.zeroLocus (Jh : Set Ah) := by
        intro p _
        obtain ⟨q, rfl⟩ := hsurj p
        have hq : I ≤ q.asIdeal ∨ J ≤ q.asIdeal :=
          q.isPrime.mul_le.mp (by rw [hmul]; exact bot_le)
        exact hq.imp
          (fun hi => Ideal.map_le_iff_le_comap.mp (hIh.le.trans hi))
          (fun hj => Ideal.map_le_iff_le_comap.mp (hJh.le.trans hj))
      have hmeet (K : Ideal Ahat) (Kh : Ideal Ah) (hKh : Kh.map f.toRingHom = K)
          (hK : ∃ p : PrimeSpectrum Ahat, p.asIdeal ≠ maximalIdeal Ahat ∧ K ≤ p.asIdeal) :
          ({p : PrimeSpectrum Ah | p.asIdeal ≠ maximalIdeal Ah} ∩
            PrimeSpectrum.zeroLocus (Kh : Set Ah)).Nonempty := by
        obtain ⟨p, hp, hpK⟩ := hK
        exact ⟨PrimeSpectrum.comap f.toRingHom p, (hpunct p).mpr hp,
          Ideal.map_le_iff_le_comap.mp (hKh.le.trans hpK)⟩
      obtain ⟨p, hp, hpI, hpJ⟩ := isPreconnected_closed_iff.mp h.isPreconnected
        _ _ (PrimeSpectrum.isClosed_zeroLocus _) (PrimeSpectrum.isClosed_zeroLocus _)
        hcover (hmeet I Ih hIh hI) (hmeet J Jh hJh hJ)
      obtain ⟨q, rfl⟩ := hsurj p
      apply (hpunct q).mp hp
      exact hclosed q
        (hIh ▸ Ideal.map_le_iff_le_comap.mpr hpI)
        (hJh ▸ Ideal.map_le_iff_le_comap.mpr hpJ)

end
