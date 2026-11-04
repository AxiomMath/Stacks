module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Length

/-!
# Krull dimension at most one from an algebra realising the punctured spectrum

Let `A` be a Noetherian local ring with maximal ideal `m` and let `B` be a Noetherian
`A`-algebra such that

* the image of `Spec B → Spec A` is exactly the punctured spectrum `Spec A \ {m}`, and
* for every `g ∈ m` and every `b : B` some power of `g` carries `b` into the image of `A`.

Then `A` has Krull dimension at most one. This is the algebraic content of the hard direction of
Stacks tag 0BCR: the second hypothesis is what affineness of the punctured spectrum supplies,
because the basic open `D(g)` of `Spec A` attached to `g ∈ m` is contained in the punctured
spectrum, so the sections of the punctured spectrum localise at `g` to `A_g`.

## Main results

* `Stacks.PuncturedSpectrum.krullDimLE_one_of_isPuncturedSpectrumAlgebra` is the criterion.

## Implementation notes

The argument is the non-cohomological proof of Stacks 0BCR. Pick `f ∈ m` avoiding the finitely
many associated primes of `B`, so that `f` is a non-zero-divisor on `B`. Write `R ⊆ B` for the
image of `A` and `Q = B ⧸ R`. Then

* `{b : B | f • b ∈ R}` embeds into `R` by multiplication by `f`, hence is a finitely generated
  `A`-module, hence so is the `f`-torsion of `Q`;
* the `f`-torsion of `Q` is annihilated by a power of `m`, hence has finite length;
* `f` acts locally nilpotently on `Q`, so `Q ⧸ f • Q` has finite length by
  `Stacks.PuncturedSpectrum.length_quotient_range_lsmul_le`;
* consequently `B ⧸ f B` is a finite `A`-module, so `Spec (B ⧸ f B) → Spec A` is a closed map and
  its image `(Spec A \ {m}) ∩ V(f)` is closed.

A nonempty closed subset of `Spec A` contains the closed point, so that image is empty, `V(f)`
is the single point `m`, and Krull's principal ideal theorem bounds the height of `m` by one.

No reduction to the reduced case is needed, and in particular the affineness of thickenings
(Stacks tag 06AD) is not used: choosing `f` to avoid the associated primes of `B` rather than the
minimal primes of `A` is what replaces it.
-/

@[expose] public section

universe u v

namespace Stacks.PuncturedSpectrum

open scoped nonZeroDivisors

section Uniform

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {Q : Type v} [AddCommGroup Q] [Module A Q]

omit [IsNoetherianRing A] in
/-- If a scalar kills each element of a finitely generated submodule to some power, one power of
it annihilates the whole submodule. -/
private lemma exists_pow_mem_annihilator (N : Submodule A Q) (hN : N.FG) (g : A)
    (h : ∀ q ∈ N, ∃ k : ℕ, g ^ k • q = 0) : ∃ K : ℕ, g ^ K ∈ N.annihilator := by
  classical
  obtain ⟨s, hs⟩ := hN
  have h' : ∀ q : Q, ∃ k : ℕ, q ∈ N → g ^ k • q = 0 := by
    intro q
    by_cases hq : q ∈ N
    · obtain ⟨k, hk⟩ := h q hq
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun hc => absurd hc hq⟩
  choose k hk using h'
  refine ⟨s.sup k, ?_⟩
  rw [Submodule.mem_annihilator]
  have hsub : (s : Set Q) ⊆ (LinearMap.ker (LinearMap.lsmul A Q (g ^ s.sup k)) : Set Q) := by
    intro x hx
    have hxN : x ∈ N := hs ▸ Submodule.subset_span hx
    have hle : k x ≤ s.sup k := Finset.le_sup hx
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have : g ^ s.sup k • x = g ^ d • (g ^ k x • x) := by
      rw [← mul_smul, ← pow_add, hd, Nat.add_comm]
    simp [LinearMap.mem_ker, this, hk x hxN]
  intro q hq
  rw [← hs] at hq
  exact Submodule.span_le.mpr hsub hq

end Uniform

section Algebra

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing B]

/-- The image of `A` in `B`, as an `A`-submodule. -/
abbrev baseRange : Submodule A B := LinearMap.range (Algebra.linearMap A B)

omit [IsLocalRing A] [IsNoetherianRing A] [IsNoetherianRing B] in
private lemma baseRange_fg : (baseRange A B).FG := by
  refine ⟨{1}, ?_⟩
  ext b
  simp only [Finset.coe_singleton, Submodule.mem_span_singleton, LinearMap.mem_range,
    Algebra.linearMap_apply, Algebra.smul_def, mul_one]

omit [IsNoetherianRing A] in
/-- Some element of the maximal ideal of `A` becomes a non-zero-divisor in `B`, provided every
prime of `B` lies over a prime different from the closed point. -/
private lemma exists_mem_maximalIdeal_nonZeroDivisor
    (hrange : ∀ q : Ideal B, q.IsPrime →
      q.comap (algebraMap A B) ≠ IsLocalRing.maximalIdeal A) :
    ∃ f ∈ IsLocalRing.maximalIdeal A, algebraMap A B f ∈ B⁰ := by
  classical
  have hTfin : ((fun q : Ideal B => q.comap (algebraMap A B)) '' associatedPrimes B B).Finite :=
    (associatedPrimes.finite (A := B) (M := B)).image _
  have hTprime : ∀ I ∈ (fun q : Ideal B => q.comap (algebraMap A B)) '' associatedPrimes B B,
      I.IsPrime := by
    rintro I ⟨q, hq, rfl⟩
    have := hq.1
    exact Ideal.comap_isPrime _ _
  have hTne : ∀ I ∈ (fun q : Ideal B => q.comap (algebraMap A B)) '' associatedPrimes B B,
      ¬ IsLocalRing.maximalIdeal A ≤ I := by
    rintro I ⟨q, hq, rfl⟩ hle
    have hqp := hq.1
    have hcp : (q.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _
    exact hrange q hqp (le_antisymm (IsLocalRing.le_maximalIdeal hcp.ne_top) hle)
  have hnotsub : ¬ ((IsLocalRing.maximalIdeal A : Set A) ⊆
      ⋃ I ∈ (fun q : Ideal B => q.comap (algebraMap A B)) '' associatedPrimes B B,
        (I : Set A)) := by
    have key := Ideal.subset_union_prime_finite hTfin (f := id) ⊥ ⊤
      (fun I hI _ _ => hTprime I hI) (I := IsLocalRing.maximalIdeal A)
    simp only [id_eq] at key
    rw [key]
    rintro ⟨I, hI, hle⟩
    exact hTne I hI hle
  obtain ⟨f, hfm, hf⟩ := Set.not_subset.mp hnotsub
  refine ⟨f, hfm, ?_⟩
  by_contra hcon
  have hmem : algebraMap A B f ∈ (B⁰ : Set B)ᶜ := hcon
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmem
  obtain ⟨q, hq, hfq⟩ := hmem
  exact hf (Set.mem_biUnion (Set.mem_image_of_mem _ hq) hfq)

variable {A B}

omit [IsLocalRing A] [IsNoetherianRing A] [IsNoetherianRing B] in
/-- The `f`-torsion of `B ⧸ A` is the image of `{b | f • b ∈ A}`. -/
private lemma ker_lsmul_eq_map (f : A) :
    LinearMap.ker (LinearMap.lsmul A (B ⧸ baseRange A B) f) =
      Submodule.map (baseRange A B).mkQ
        (Submodule.comap (LinearMap.lsmul A B f) (baseRange A B)) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨b, rfl⟩ := (baseRange A B).mkQ_surjective q
    refine ⟨b, ?_, rfl⟩
    have : (baseRange A B).mkQ (f • b) = 0 := by
      rw [LinearMap.map_smul]
      exact hq
    simpa [Submodule.mem_comap] using (Submodule.Quotient.mk_eq_zero _).mp this
  · rintro q ⟨b, hb, rfl⟩
    have : f • b ∈ baseRange A B := hb
    simp only [LinearMap.mem_ker, LinearMap.lsmul_apply, ← LinearMap.map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr this

omit [IsLocalRing A] [IsNoetherianRing B] in
/-- The `f`-torsion of `B ⧸ A` is a finitely generated `A`-module when `f` is a non-zero-divisor
on `B`. -/
private lemma finite_ker_lsmul {f : A} (hf : algebraMap A B f ∈ B⁰) :
    Module.Finite A ↥(LinearMap.ker (LinearMap.lsmul A (B ⧸ baseRange A B) f)) := by
  have hR : IsNoetherian A ↥(baseRange A B) :=
    isNoetherian_of_fg_of_noetherian _ (baseRange_fg A B)
  have hres : ∀ x ∈ Submodule.comap (LinearMap.lsmul A B f) (baseRange A B),
      LinearMap.lsmul A B f x ∈ baseRange A B := fun _ hx => hx
  have hinj : Function.Injective ((LinearMap.lsmul A B f).restrict hres) := by
    intro x y hxy
    have h : f • (x : B) = f • (y : B) := congrArg Subtype.val hxy
    rw [Algebra.smul_def, Algebra.smul_def] at h
    exact Subtype.ext ((mul_cancel_left_mem_nonZeroDivisors hf).mp h)
  have hB' : IsNoetherian A ↥(Submodule.comap (LinearMap.lsmul A B f) (baseRange A B)) :=
    isNoetherian_of_injective _ hinj
  have hB'fg : (Submodule.comap (LinearMap.lsmul A B f) (baseRange A B)).FG :=
    Submodule.fg_top _ |>.mp (IsNoetherian.noetherian ⊤)
  rw [ker_lsmul_eq_map]
  exact Module.Finite.iff_fg.mpr (hB'fg.map _)

/-- If a power of `g` carries each `b : B` into `A`, then `g` is locally nilpotent on `B ⧸ A`. -/
private lemma exists_pow_smul_mkQ_eq_zero {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {g : A}
    (htors : ∀ b : B, ∃ k : ℕ, g ^ k • b ∈ baseRange A B) (q : B ⧸ baseRange A B) :
    ∃ k : ℕ, g ^ k • q = 0 := by
  obtain ⟨b, rfl⟩ := (baseRange A B).mkQ_surjective q
  obtain ⟨k, hk⟩ := htors b
  refine ⟨k, ?_⟩
  rw [← LinearMap.map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hk

omit [IsNoetherianRing B] in
/-- The `f`-torsion of `B ⧸ A` has finite length. -/
private lemma length_ker_lsmul_ne_top {f : A} (hf : algebraMap A B f ∈ B⁰)
    (htors : ∀ g ∈ IsLocalRing.maximalIdeal A, ∀ b : B,
      ∃ k : ℕ, g ^ k • b ∈ baseRange A B) :
    Module.length A ↥(LinearMap.ker (LinearMap.lsmul A (B ⧸ baseRange A B) f)) ≠ ⊤ := by
  have hfin := finite_ker_lsmul (B := B) hf
  set N := LinearMap.ker (LinearMap.lsmul A (B ⧸ baseRange A B) f) with hN
  have hNfg : N.FG := Module.Finite.iff_fg.mp hfin
  have hkill : ∀ g ∈ IsLocalRing.maximalIdeal A, ∀ q ∈ N, ∃ k : ℕ, g ^ k • q = 0 := by
    intro g hg q _
    exact exists_pow_smul_mkQ_eq_zero (htors g hg) q
  by_cases hI : N.annihilator = ⊤
  · have hsub : Subsingleton ↥N := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx : (1 : A) • (x : B ⧸ baseRange A B) = 0 :=
        Submodule.mem_annihilator.mp (hI ▸ Submodule.mem_top) _ x.2
      have hy : (1 : A) • (y : B ⧸ baseRange A B) = 0 :=
        Submodule.mem_annihilator.mp (hI ▸ Submodule.mem_top) _ y.2
      rw [one_smul] at hx hy
      rw [hx, hy]
    simp
  · have hIle : N.annihilator ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hI
    have hmin : IsLocalRing.maximalIdeal A ∈ N.annihilator.minimalPrimes := by
      refine ⟨⟨inferInstance, hIle⟩, fun b hb _ x hx => ?_⟩
      obtain ⟨K, hK⟩ := exists_pow_mem_annihilator N hNfg x (hkill x hx)
      exact hb.1.mem_of_pow_mem K (hb.2 hK)
    have _ : IsArtinianRing (A ⧸ N.annihilator) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
    obtain ⟨n, hn⟩ :=
      IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (R := A) N.annihilator
    refine length_ne_top_of_maximalIdeal_pow_smul_eq_zero A ↥N (n := max n 1)
      (by omega) fun a ha x => ?_
    have ha' : a ∈ N.annihilator :=
      hn (Ideal.pow_le_pow_right (le_max_left n 1) ha)
    exact Subtype.ext (Submodule.mem_annihilator.mp ha' _ x.2)

end Algebra

section Main

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing B]

omit [IsNoetherianRing B] in
/-- `B ⧸ f B` is a finite `A`-module. -/
private lemma finite_quotient_span {f : A} (hf : algebraMap A B f ∈ B⁰)
    (htors : ∀ g ∈ IsLocalRing.maximalIdeal A, ∀ b : B,
      ∃ k : ℕ, g ^ k • b ∈ baseRange A B) (hfm : f ∈ IsLocalRing.maximalIdeal A) :
    Module.Finite A (B ⧸ Ideal.span {algebraMap A B f}) := by
  set J : Ideal B := Ideal.span {algebraMap A B f} with hJ
  set R := baseRange A B with hR
  set π : B →ₗ[A] B ⧸ J := (Ideal.Quotient.mkₐ A J).toLinearMap with hπ
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hfzero : ∀ y : B ⧸ J, f • y = 0 := by
    intro y
    obtain ⟨b, rfl⟩ := hπsurj y
    have : f • b ∈ J := by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have h2 : π (f • b) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr this
    rwa [LinearMap.map_smul] at h2
  set N : Submodule A (B ⧸ J) := Submodule.map π R with hNdef
  have hNfin : Module.Finite A ↥N := Module.Finite.iff_fg.mpr ((baseRange_fg A B).map _)
  -- the quotient of `B ⧸ J` by `N` is a quotient of `Q ⧸ f • Q`
  have hρ : R ≤ LinearMap.ker (N.mkQ ∘ₗ π) := by
    intro b hb
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hb, rfl⟩
  have hρ' : LinearMap.range (LinearMap.lsmul A (B ⧸ R) f) ≤
      LinearMap.ker (R.liftQ (N.mkQ ∘ₗ π) hρ) := by
    rintro q ⟨q', rfl⟩
    obtain ⟨b, rfl⟩ := R.mkQ_surjective q'
    have hfb : π (f • b) = 0 := by rw [LinearMap.map_smul]; exact hfzero (π b)
    have hsm : (LinearMap.lsmul A (B ⧸ R) f) (R.mkQ b) = R.mkQ (f • b) :=
      (LinearMap.map_smul R.mkQ f b).symm
    rw [LinearMap.mem_ker, hsm, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.coe_comp, Function.comp_apply, hfb, map_zero]
  have hsurj : Function.Surjective
      ((LinearMap.range (LinearMap.lsmul A (B ⧸ R) f)).liftQ
        (R.liftQ (N.mkQ ∘ₗ π) hρ) hρ') := by
    intro y
    obtain ⟨z, rfl⟩ := N.mkQ_surjective y
    obtain ⟨b, rfl⟩ := hπsurj z
    exact ⟨(LinearMap.range (LinearMap.lsmul A (B ⧸ R) f)).mkQ (R.mkQ b), rfl⟩
  have hQfin : Module.Finite A ((B ⧸ R) ⧸ LinearMap.range (LinearMap.lsmul A (B ⧸ R) f)) := by
    have hlen := length_quotient_range_lsmul_le (Q := B ⧸ R) f ?_
    · have hne : Module.length A ((B ⧸ R) ⧸ LinearMap.range (LinearMap.lsmul A (B ⧸ R) f)) ≠ ⊤ :=
        ne_top_of_le_ne_top (length_ker_lsmul_ne_top hf htors) hlen
      have := (isFiniteLength_iff_isNoetherian_isArtinian).mp (Module.length_ne_top_iff.mp hne)
      exact Module.finite_def.mpr (this.1.noetherian ⊤)
    · exact exists_pow_smul_mkQ_eq_zero (htors f hfm)
  have _ : Module.Finite A ((B ⧸ J) ⧸ N) := Module.Finite.of_surjective _ hsurj
  exact Module.Finite.of_submodule_quotient N

/-- **Krull dimension at most one.** If `B` is a Noetherian `A`-algebra whose spectrum maps onto
the punctured spectrum of the Noetherian local ring `A`, and if every element of `B` is carried
into `A` by a power of any given element of the maximal ideal, then `A` has Krull dimension at
most one. -/
theorem krullDimLE_one_of_isPuncturedSpectrumAlgebra
    (hrange : Set.range (PrimeSpectrum.comap (algebraMap A B)) =
      {p : PrimeSpectrum A | p ≠ IsLocalRing.closedPoint A})
    (htors : ∀ g ∈ IsLocalRing.maximalIdeal A, ∀ b : B,
      ∃ k : ℕ, g ^ k • b ∈ baseRange A B) :
    Ring.KrullDimLE 1 A := by
  classical
  obtain ⟨f, hfm, hf⟩ := exists_mem_maximalIdeal_nonZeroDivisor A B (by
    intro q hq hcon
    have h1 : (⟨q.comap (algebraMap A B), Ideal.comap_isPrime _ _⟩ : PrimeSpectrum A) ∈
        Set.range (PrimeSpectrum.comap (algebraMap A B)) := ⟨⟨q, hq⟩, rfl⟩
    rw [hrange] at h1
    exact h1 (PrimeSpectrum.ext hcon))
  have hfin := finite_quotient_span A B hf htors hfm
  -- the image of `Spec (B ⧸ f B)` in `Spec A` is closed
  have hint : (algebraMap A (B ⧸ Ideal.span {algebraMap A B f})).IsIntegral :=
    fun x => IsIntegral.of_finite A x
  have hclosed : IsClosed
      (Set.range (PrimeSpectrum.comap (algebraMap A (B ⧸ Ideal.span {algebraMap A B f})))) := by
    have := PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint Set.univ isClosed_univ
    rwa [Set.image_univ] at this
  -- and it equals the punctured spectrum intersected with `V(f)`
  have himg : Set.range (PrimeSpectrum.comap (algebraMap A (B ⧸ Ideal.span {algebraMap A B f})))
      = {p : PrimeSpectrum A | p ≠ IsLocalRing.closedPoint A} ∩
        PrimeSpectrum.zeroLocus {f} := by
    have hcomp : (algebraMap A (B ⧸ Ideal.span {algebraMap A B f})) =
        (Ideal.Quotient.mk (Ideal.span {algebraMap A B f})).comp (algebraMap A B) := rfl
    rw [hcomp, PrimeSpectrum.comap_comp, Set.range_comp,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have hz : PrimeSpectrum.zeroLocus
        ((Ideal.span {algebraMap A B f} : Ideal B) : Set B) =
        PrimeSpectrum.comap (algebraMap A B) ⁻¹' PrimeSpectrum.zeroLocus ({f} : Set A) := by
      rw [PrimeSpectrum.preimage_comap_zeroLocus]
      simp only [Set.image_singleton]
      rw [PrimeSpectrum.zeroLocus_span]
    rw [hz, Set.image_preimage_eq_inter_range, hrange, Set.inter_comm]
  -- a nonempty closed subset of `Spec A` contains the closed point
  have hempty : {p : PrimeSpectrum A | p ≠ IsLocalRing.closedPoint A} ∩
      PrimeSpectrum.zeroLocus ({f} : Set A) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    rw [← himg] at hp
    have hcl : closure {p} ⊆
        {q : PrimeSpectrum A | q ≠ IsLocalRing.closedPoint A} ∩
          PrimeSpectrum.zeroLocus ({f} : Set A) := by
      rw [← himg]
      exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hp)
    have hmem : IsLocalRing.closedPoint A ∈ closure ({p} : Set (PrimeSpectrum A)) := by
      rw [PrimeSpectrum.closure_singleton]
      exact fun x hx => IsLocalRing.le_maximalIdeal p.isPrime.ne_top hx
    exact (hcl hmem).1 rfl
  -- hence `V(f) = {m}`, and Krull's principal ideal theorem finishes
  have hzl : PrimeSpectrum.zeroLocus ({f} : Set A) ⊆ {IsLocalRing.closedPoint A} := by
    intro p hp
    by_contra hne
    exact Set.eq_empty_iff_forall_notMem.mp hempty p ⟨hne, hp⟩
  have hmin : IsLocalRing.maximalIdeal A ∈ (Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨inferInstance, by simpa using hfm⟩, fun b hb hbm => ?_⟩
    have hbp : b.IsPrime := hb.1
    have : (⟨b, hbp⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus ({f} : Set A) := by
      simpa using hb.2 (Ideal.subset_span rfl)
    have := hzl this
    simp only [Set.mem_singleton_iff] at this
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal this).symm
  have hheight : (IsLocalRing.maximalIdeal A).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing (Ideal.span {f}) hmin
  rw [Ring.krullDimLE_iff, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hheight

end Main

end Stacks.PuncturedSpectrum
