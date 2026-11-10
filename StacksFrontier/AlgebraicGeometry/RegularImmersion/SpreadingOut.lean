module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.FGKernel
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Koszul.FlatQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Spreading out a nonzerodivisor on the fibre

Let `A → B` be flat and of finite presentation, let `q` be a prime of `B` with `p = A ∩ q`, and let
`h ∈ q`.  If `h` is a nonzerodivisor on the fibre `B_q/pB_q`, then there is a `g ∉ q` such that
`h` is a nonzerodivisor in `B_g` and `B_g/hB_g` is flat over `A` — that is, `V(h) ⊂ Spec(B_g)` is
a relative effective Cartier divisor over `Spec(A)`.  No Noetherian hypothesis is needed.

## Main results

* `Stacks.RingTheory.SpreadingOut.isSMulRegular_and_flat_quotient_atPrime`: `h` is a
  nonzerodivisor in `B_q` and `B_q/hB_q` is flat over `A`.
* `Stacks.RingTheory.SpreadingOut.exists_notMem_flat_quotient_away`: `B_g/hB_g` is flat over `A`
  for some `g ∉ q`.
* `Stacks.RingTheory.SpreadingOut.exists_notMem_forall_flat_quotient_away_of_fg`: the same for a
  finite family of finitely generated ideals at once, with a single `g`.
* `Stacks.RingTheory.SpreadingOut.exists_notMem_isSMulRegular_and_flat_quotient_away_of_fg_ker`:
  the spreading out, assuming `ker(h · : B → B)` finitely generated.
* `Stacks.RingTheory.SpreadingOut.exists_notMem_isSMulRegular_and_flat_quotient_away`: the
  spreading out, unconditionally.
* `Stacks.RingTheory.SpreadingOut.injective_lTensor_mulLeft_of_flat_quotient` and
  `Stacks.RingTheory.SpreadingOut.isSMulRegular_tmul_of_flat_quotient`: a relative effective
  Cartier divisor is stable under base change.

## References

* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 046Z](https://stacks.math.columbia.edu/tag/046Z)
* [Stacks Project, Tag 00MF](https://stacks.math.columbia.edu/tag/00MF)
* [Stacks Project, Tag 00RC](https://stacks.math.columbia.edu/tag/00RC)
* [Stacks Project, Tag 061L](https://stacks.math.columbia.edu/tag/061L)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.RingTheory.SpreadingOut

/-- The two spellings of the fibre of a flat local homomorphism `A_p → T` agree:
`𝔪_p T = p T`. -/
theorem map_maximalIdeal_eq_map_of_isLocalization
    {A P T : Type*} [CommRing A] [CommRing P] [CommRing T]
    [Algebra A P] [Algebra A T] [Algebra P T] [IsScalarTower A P T]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime P p] [IsLocalRing P] :
    (IsLocalRing.maximalIdeal P).map (algebraMap P T) = p.map (algebraMap A T) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p P, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A P T]

/-- Let `A → B` be flat and of finite presentation, let `q` be a prime of `B` and let
`p = A ∩ q`.  If `h ∈ B` is a nonzerodivisor on the fibre `B_q/pB_q`, then `h` is a
nonzerodivisor on `B_q` and `B_q/hB_q` is flat over `A`. -/
theorem isSMulRegular_and_flat_quotient_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (h : B)
    (hfib : IsSMulRegular
      (Localization.AtPrime q ⧸
        (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)))
      (algebraMap B (Localization.AtPrime q) h)) :
    IsSMulRegular (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) h) ∧
      Module.Flat A
        (Localization.AtPrime q ⧸ Ideal.span {algebraMap B (Localization.AtPrime q) h}) := by
  classical
  let T := Localization.AtPrime q
  let p := q.comap (algebraMap A B)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : q.LiesOver p := ⟨rfl⟩
  let P := Localization.AtPrime p
  let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap P T) :=
    Localization.isLocalHom_localRingHom p q (algebraMap A B) rfl
  have : Module.Flat P T :=
    (Module.flat_iff_of_isLocalization P p.primeCompl T).mpr inferInstance
  have hess : (algebraMap P T).EssentiallyOfFinitePresentation :=
    Koszul.essentiallyOfFinitePresentation_localization (S := B) p.primeCompl q.primeCompl
      (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have he (J : Ideal T) : J • (⊤ : Submodule T T) = J :=
    (Ideal.smul_eq_mul J ⊤).trans (Ideal.mul_top J)
  have hmax : (IsLocalRing.maximalIdeal P).map (algebraMap P T) = p.map (algebraMap A T) :=
    map_maximalIdeal_eq_map_of_isLocalization p
  obtain ⟨h1, h2⟩ :=
    Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal
      (R := P) (S := T) (M := T) hess (f := algebraMap B T h) (by rw [he, hmax]; exact hfib)
  refine ⟨h1, ?_⟩
  rw [he] at h2
  exact Module.Flat.trans A P _

/-- The image in `B ⧸ I` of the complement of a prime `q` lying under `Q` is the complement
of `Q`. -/
private lemma algebraMapSubmonoid_primeCompl_eq {B : Type*} [CommRing B] (I : Ideal B)
    (q : Ideal B) [q.IsPrime] (Q : Ideal (B ⧸ I)) [Q.IsPrime]
    (hQc : Q.comap (algebraMap B (B ⧸ I)) = q) :
    Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl = Q.primeCompl := by
  have key : ∀ b : B, algebraMap B (B ⧸ I) b ∈ Q ↔ b ∈ q := fun b => by rw [← hQc]; exact Iff.rfl
  ext c
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact fun hmem => hb ((key b).mp hmem)
  · intro hc
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨b, fun hmem => hc ((key b).mpr hmem), rfl⟩

/-- Over the base, flatness of a localization of `C` away from `g` follows from flatness of the
localizations of `C` at all primes of the basic open `D(g)`. -/
private lemma flat_localization_away_of_forall {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] (g : C)
    (hflat : ∀ Q : PrimeSpectrum C, g ∉ Q.asIdeal →
      Module.Flat A (LocalizedModule.AtPrime Q.asIdeal C)) :
    Module.Flat A (Localization.Away g) := by
  have key : ∀ (P : Ideal (Localization.Away g)) [P.IsPrime],
      g ∉ P.comap (algebraMap C (Localization.Away g)) := fun P _ hg =>
    (‹P.IsPrime›.ne_top) (Ideal.eq_top_of_isUnit_mem _ hg
      (IsLocalization.Away.algebraMap_isUnit g))
  refine Module.flat_of_isLocalized_maximal (Localization.Away g) (Localization.Away g)
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap _ _) fun P _ => ?_
  have := hflat ⟨P.comap (algebraMap C (Localization.Away g)), inferInstance⟩ (key P)
  exact Module.Flat.of_linearEquiv ((IsLocalizedModule.iso
    (P.comap (algebraMap C (Localization.Away g))).primeCompl
    (Algebra.linearMap C (Localization.AtPrime P))).symm.restrictScalars A)

/-- The quotient of a `B`-algebra `S` by the extension of an ideal `I` of `B` is an algebra over
`B ⧸ I`, and the scalars of any base `A` of `B` factor through it. -/
private instance isScalarTower_quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal B) (S : Type*) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S] :
    IsScalarTower A (B ⧸ I) (S ⧸ I.map (algebraMap B S)) :=
  .of_algebraMap_eq fun a => by
    change Ideal.Quotient.mk _ (algebraMap A S a) = _
    rw [IsScalarTower.algebraMap_apply A B S]
    rfl

/-- The flat locus of `B/IB` over `A` contains a basic open neighbourhood of `q`, for any
finitely generated ideal `I ⊆ q`. -/
theorem exists_notMem_forall_flat_atPrime_quotient_of_fg
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (I : Ideal B) (hI : I.FG) (hIq : I ≤ q)
    (hflat : Module.Flat A
      (Localization.AtPrime q ⧸ I.map (algebraMap B (Localization.AtPrime q)))) :
    ∃ g ∉ q, ∀ Q' : PrimeSpectrum (B ⧸ I),
      algebraMap B (B ⧸ I) g ∉ Q'.asIdeal →
        Module.Flat A (LocalizedModule.AtPrime Q'.asIdeal (B ⧸ I)) := by
  classical
  have hsurj : Function.Surjective (algebraMap B (B ⧸ I)) := Ideal.Quotient.mk_surjective
  have hker : Ideal.comap (algebraMap B (B ⧸ I)) ⊥ = I := Ideal.mk_ker
  set Q : Ideal (B ⧸ I) := q.map (algebraMap B (B ⧸ I)) with hQ
  have hQp : Q.IsPrime := Ideal.map_isPrime_of_surjective hsurj (Ideal.mk_ker.trans_le hIq)
  have hQc : Q.comap (algebraMap B (B ⧸ I)) = q := by
    rw [hQ, Ideal.comap_map_of_surjective _ hsurj, hker, sup_eq_left.mpr hIq]
  have : Algebra.FinitePresentation A (B ⧸ I) := Algebra.FinitePresentation.quotient hI
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl = Q.primeCompl :=
    algebraMapSubmonoid_primeCompl_eq I q Q hQc
  have : IsLocalization Q.primeCompl (Localization.AtPrime q ⧸
      I.map (algebraMap B (Localization.AtPrime q))) := hsub ▸ inferInstance
  have hQflat : Module.Flat A (LocalizedModule.AtPrime Q (B ⧸ I)) :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.iso Q.primeCompl
      (Algebra.linearMap (B ⧸ I) (Localization.AtPrime q ⧸
        I.map (algebraMap B (Localization.AtPrime q))))).restrictScalars A)
  obtain ⟨c, hcQ, hcU⟩ := Stacks.Flatness.FibreExactnessLocus.exists_basicOpen_subset_of_isOpen
    (U := {Q' : PrimeSpectrum (B ⧸ I) |
      Module.Flat A (LocalizedModule.AtPrime Q'.asIdeal (B ⧸ I))})
    Module.isOpen_setOf_flat_localizedModule_atPrime (q := ⟨Q, hQp⟩) hQflat
  obtain ⟨g, rfl⟩ := hsurj c
  exact ⟨g, fun hgq => hcQ (Ideal.mem_map_of_mem _ hgq),
    fun Q' hQ' => hcU ((PrimeSpectrum.mem_basicOpen _ _).mpr hQ')⟩

/-- The flat locus of `B/hB` over `A` contains a basic open neighbourhood of `q`. -/
private lemma exists_notMem_forall_flat_atPrime_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (h : B) (hq : h ∈ q)
    (hflat : Module.Flat A
      (Localization.AtPrime q ⧸ Ideal.span {algebraMap B (Localization.AtPrime q) h})) :
    ∃ g ∉ q, ∀ Q' : PrimeSpectrum (B ⧸ Ideal.span {h}),
      algebraMap B (B ⧸ Ideal.span {h}) g ∉ Q'.asIdeal →
        Module.Flat A (LocalizedModule.AtPrime Q'.asIdeal (B ⧸ Ideal.span {h})) := by
  refine exists_notMem_forall_flat_atPrime_quotient_of_fg q (Ideal.span {h})
    (Submodule.fg_span_singleton h) (Ideal.span_le.mpr (by simpa using hq)) ?_
  rwa [Ideal.map_span, Set.image_singleton]

/-- Flatness of `B_g/IB_g` over `A` from flatness of `B/IB` at every point of `D(g)`. -/
theorem flat_quotient_away_of_forall_of_fg
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (g : B)
    (hcU : ∀ Q' : PrimeSpectrum (B ⧸ I),
      algebraMap B (B ⧸ I) g ∉ Q'.asIdeal →
        Module.Flat A (LocalizedModule.AtPrime Q'.asIdeal (B ⧸ I))) :
    Module.Flat A (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g))) := by
  classical
  have haway : Module.Flat A (Localization.Away (algebraMap B (B ⧸ I) g)) :=
    flat_localization_away_of_forall _ fun Q' hQ' => hcU Q' hQ'
  have : IsLocalization (Submonoid.powers (algebraMap B (B ⧸ I) g))
      (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g))) :=
      by rw [← Algebra.algebraMapSubmonoid_powers (S := B ⧸ I) g]; infer_instance
  have hL : Module.Flat A
      (LocalizedModule (Submonoid.powers (algebraMap B (B ⧸ I) g)) (B ⧸ I)) :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.iso _
      (Algebra.linearMap (B ⧸ I)
        (Localization.Away (algebraMap B (B ⧸ I) g)))).restrictScalars A)
  exact Module.Flat.of_linearEquiv ((IsLocalizedModule.iso
    (Submonoid.powers (algebraMap B (B ⧸ I) g))
    (Algebra.linearMap (B ⧸ I)
      (Localization.Away g ⧸
        I.map (algebraMap B (Localization.Away g))))).symm.restrictScalars A)

/-- Flatness of `B_g/hB_g` over `A` from flatness of `B/hB` at every point of `D(g)`. -/
private lemma flat_quotient_away_of_forall
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (h g : B)
    (hcU : ∀ Q' : PrimeSpectrum (B ⧸ Ideal.span {h}),
      algebraMap B (B ⧸ Ideal.span {h}) g ∉ Q'.asIdeal →
        Module.Flat A (LocalizedModule.AtPrime Q'.asIdeal (B ⧸ Ideal.span {h}))) :
    Module.Flat A
      (Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) h}) := by
  have := flat_quotient_away_of_forall_of_fg (A := A) (Ideal.span {h}) g hcU
  rwa [Ideal.map_span, Set.image_singleton] at this

/-- If `A → B` is of finite presentation and `B_q/hB_q` is flat over `A`, then `B_g/hB_g` is flat
over `A` for some `g ∉ q`. -/
theorem exists_notMem_flat_quotient_away
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (h : B) (hq : h ∈ q)
    (hflat : Module.Flat A
      (Localization.AtPrime q ⧸ Ideal.span {algebraMap B (Localization.AtPrime q) h})) :
    ∃ g ∉ q, Module.Flat A
      (Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) h}) := by
  obtain ⟨g, hgq, hcU⟩ := exists_notMem_forall_flat_atPrime_quotient q h hq hflat
  exact ⟨g, hgq, flat_quotient_away_of_forall h g hcU⟩

/-- If `A → B` is of finite presentation and `B_q/I_kB_q` is flat over `A` for each member of a
finite family of finitely generated ideals `I_k ⊆ q`, then there is a single `g ∉ q` with
`B_g/I_kB_g` flat over `A` for every `k`. -/
theorem exists_notMem_forall_flat_quotient_away_of_fg
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] {ι : Type*} (s : Finset ι) (I : ι → Ideal B)
    (hI : ∀ k ∈ s, (I k).FG) (hIq : ∀ k ∈ s, I k ≤ q)
    (hflat : ∀ k ∈ s, Module.Flat A
      (Localization.AtPrime q ⧸ (I k).map (algebraMap B (Localization.AtPrime q)))) :
    ∃ g ∉ q, ∀ k ∈ s, Module.Flat A
      (Localization.Away g ⧸ (I k).map (algebraMap B (Localization.Away g))) := by
  classical
  have hex : ∀ k ∈ s, ∃ g ∉ q, ∀ Q' : PrimeSpectrum (B ⧸ I k),
      algebraMap B (B ⧸ I k) g ∉ Q'.asIdeal →
        Module.Flat A (LocalizedModule.AtPrime Q'.asIdeal (B ⧸ I k)) :=
    fun k hk => exists_notMem_forall_flat_atPrime_quotient_of_fg q (I k) (hI k hk) (hIq k hk)
      (hflat k hk)
  choose! g hgq hgflat using hex
  refine ⟨∏ k ∈ s, g k, fun hmem => (q.primeCompl.prod_mem fun k hk => hgq k hk) hmem,
    fun k hk => ?_⟩
  refine flat_quotient_away_of_forall_of_fg (I k) _ fun Q' hQ' => ?_
  refine hgflat k hk Q' fun hmem => hQ' ?_
  rw [← Finset.prod_erase_mul s _ hk, map_mul]
  exact Ideal.mul_mem_left _ _ hmem

/-- If every element of `B` killed by `h` is killed by an element of a submonoid `S`, then every
element of `B_g` killed by `h` is killed by (the image of) an element of `S`. -/
private lemma exists_mem_smul_eq_zero_away {B : Type*} [CommRing B] (S : Submonoid B) (h g : B)
    (hS : ∀ k : B, h * k = 0 → ∃ u ∈ S, u * k = 0) (z : Localization.Away g)
    (hz : algebraMap B (Localization.Away g) h * z = 0) :
    ∃ u ∈ S, algebraMap B (Localization.Away g) u * z = 0 := by
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (Submonoid.powers g) z
  have h1 : algebraMap B (Localization.Away g) (h * b) = 0 := by
    rw [map_mul, ← hbs, ← mul_assoc, hz, zero_mul]
  obtain ⟨⟨t, j, rfl⟩, hteq⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp h1
  obtain ⟨u, hu, hu0⟩ := hS (g ^ j * b) (by
    rw [← mul_assoc, mul_comm h (g ^ j), mul_assoc]; exact hteq)
  refine ⟨u, hu, (IsLocalization.map_units (Localization.Away g) s).mul_right_cancel ?_⟩
  have hgj : IsUnit (algebraMap B (Localization.Away g) (g ^ j)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow j
  have h3 : algebraMap B (Localization.Away g) (u * b) = 0 :=
    hgj.mul_left_cancel (by rw [← map_mul, mul_left_comm, hu0, map_zero, mul_zero])
  rw [zero_mul, mul_assoc, hbs, ← map_mul, h3]

/-- If some power of `g` annihilates every element of `B` killed by `h`, then `h` is a
nonzerodivisor in `B_g`. -/
private lemma isSMulRegular_away_of_smul_ker {B : Type*} [CommRing B] (h g : B)
    (hg : ∀ k : B, h * k = 0 → ∃ n : ℕ, g ^ n * k = 0) :
    IsSMulRegular (Localization.Away g) (algebraMap B (Localization.Away g) h) := by
  have key : ∀ z : Localization.Away g,
      algebraMap B (Localization.Away g) h * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨_, ⟨n, rfl⟩, h0⟩ := exists_mem_smul_eq_zero_away (Submonoid.powers g) h g
      (fun k hk => let ⟨n, hn⟩ := hg k hk; ⟨g ^ n, ⟨n, rfl⟩, hn⟩) z hz
    have hu : IsUnit (algebraMap B (Localization.Away g) (g ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n
    exact hu.mul_left_cancel (by rw [h0, mul_zero])
  exact fun x y hxy => sub_eq_zero.mp
    (key _ (by rw [mul_sub, sub_eq_zero]; simpa [smul_eq_mul] using hxy))

/-- If `h` is a nonzerodivisor in `B_q`, then every element of `B` killed by `h` is killed by an
element outside `q`. -/
private lemma exists_notMem_smul_eq_zero {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime]
    (h : B)
    (hreg : IsSMulRegular (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) h))
    (k : B) (hhk : h * k = 0) : ∃ u ∈ q.primeCompl, u * k = 0 := by
  have h0 : algebraMap B (Localization.AtPrime q) k = 0 :=
    hreg (by simp only [smul_eq_mul, mul_zero, ← map_mul, hhk, map_zero])
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h0
  exact ⟨u, u.2, hu⟩

/-- If `h` kills the elements of a finitely generated kernel and each element killed by `h` is
killed by an element of a submonoid `S`, then a single element of `S` kills all of them. -/
private lemma exists_mem_forall_mul_eq_zero_of_fg_ker {R : Type*} [CommRing R] (S : Submonoid R)
    (h : R) (hfg : (LinearMap.ker (LinearMap.lsmul R R h)).FG)
    (hkill : ∀ x : R, h * x = 0 → ∃ u ∈ S, u * x = 0) :
    ∃ u ∈ S, ∀ x : R, h * x = 0 → u * x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hgen : ∀ x ∈ (s : Set R), ∃ u ∈ S, u * x = 0 := by
    intro x hx
    refine hkill x ?_
    have : x ∈ LinearMap.ker (LinearMap.lsmul R R h) := by
      rw [← hs]; exact Submodule.subset_span hx
    simpa [LinearMap.mem_ker] using this
  choose! u hu hu0 using hgen
  refine ⟨∏ k ∈ s, u k, S.prod_mem fun k hk => hu k hk, ?_⟩
  have hker : LinearMap.ker (LinearMap.lsmul R R h) ≤
      LinearMap.ker (LinearMap.lsmul R R (∏ k ∈ s, u k)) := by
    rw [← hs, Submodule.span_le]
    intro k hk
    have : (∏ l ∈ s, u l) = (∏ l ∈ s.erase k, u l) * u k := by
      rw [Finset.prod_erase_mul _ _ hk]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul, this]
    rw [mul_assoc, hu0 k hk, mul_zero]
  intro k hk
  have : k ∈ LinearMap.ker (LinearMap.lsmul R R h) := by
    simpa [LinearMap.mem_ker, smul_eq_mul] using hk
  simpa [LinearMap.mem_ker, smul_eq_mul] using hker this

/-- If the kernel of multiplication by `h` is a finitely generated `B`-module and `h` is a
nonzerodivisor in `B_q`, then some `g ∉ q` annihilates that kernel. -/
private lemma exists_notMem_smul_ker {B : Type*} [CommRing B] (q : Ideal B) [q.IsPrime] (h : B)
    (hfg : (LinearMap.ker (LinearMap.lsmul B B h)).FG)
    (hreg : IsSMulRegular (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) h)) :
    ∃ g ∉ q, ∀ k : B, h * k = 0 → g * k = 0 :=
  exists_mem_forall_mul_eq_zero_of_fg_ker q.primeCompl h hfg (exists_notMem_smul_eq_zero q h hreg)

/-- Let `A → B` be flat and of finite presentation, let `q` be a prime of `B`, let `p = A ∩ q`
and let `h ∈ q`.  If `h` is a nonzerodivisor on the fibre `B_q/pB_q` and `ker(h · : B → B)` is a
finitely generated `B`-module, then there is a `g ∉ q` such that `h` is a nonzerodivisor in `B_g`
and `B_g/hB_g` is flat over `A`; that is, `V(h) ⊂ Spec(B_g)` is a relative effective Cartier
divisor over `Spec(A)`. -/
@[sga "2 XII 2.6" "special case"]
theorem exists_notMem_isSMulRegular_and_flat_quotient_away_of_fg_ker
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (h : B) (hq : h ∈ q)
    (hfg : (LinearMap.ker (LinearMap.lsmul B B h)).FG)
    (hfib : IsSMulRegular
      (Localization.AtPrime q ⧸
        (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)))
      (algebraMap B (Localization.AtPrime q) h)) :
    ∃ g ∉ q,
      IsSMulRegular (Localization.Away g) (algebraMap B (Localization.Away g) h) ∧
        Module.Flat A
          (Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) h}) := by
  obtain ⟨hreg, hflat⟩ := isSMulRegular_and_flat_quotient_atPrime q h hfib
  obtain ⟨g₁, hg₁, hcU⟩ := exists_notMem_forall_flat_atPrime_quotient q h hq hflat
  obtain ⟨g₂, hg₂, hkill⟩ := exists_notMem_smul_ker q h hfg hreg
  refine ⟨g₁ * g₂, fun hmem => (‹q.IsPrime›.mem_or_mem hmem).elim hg₁ hg₂, ?_, ?_⟩
  · exact isSMulRegular_away_of_smul_ker h (g₁ * g₂)
      fun k hk => ⟨1, by rw [pow_one, mul_assoc, hkill k hk, mul_zero]⟩
  · exact flat_quotient_away_of_forall h (g₁ * g₂) fun Q' hQ' => hcU Q'
      fun hmem => hQ' (by rw [map_mul]; exact Ideal.mul_mem_right _ _ hmem)

/-- Suppose `B_{g₁}/hB_{g₁}` is flat over `A` and `h` is a nonzerodivisor in `B_q`.  Then there
is a `u ∉ q` such that every element of `B` killed by `h` is killed by a power of `g₁ u`. -/
private lemma exists_notMem_pow_smul_ker
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (h g₁ : B)
    (hflat : Module.Flat A
      (Localization.Away g₁ ⧸ Ideal.span {algebraMap B (Localization.Away g₁) h}))
    (hreg : IsSMulRegular (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) h)) :
    ∃ u ∉ q, ∀ k : B, h * k = 0 → ∃ n : ℕ, (g₁ * u) ^ n * k = 0 := by
  have : Module.Flat A (Localization.Away g₁) := Module.Flat.trans A B _
  have : Algebra.FinitePresentation B (Localization.Away g₁) :=
    IsLocalization.Away.finitePresentation g₁
  have : Algebra.FinitePresentation A (Localization.Away g₁) :=
    Algebra.FinitePresentation.trans A B _
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0⟩ := exists_mem_forall_mul_eq_zero_of_fg_ker
    (Algebra.algebraMapSubmonoid (Localization.Away g₁) q.primeCompl)
    (algebraMap B (Localization.Away g₁) h)
    (fg_ker_lsmul_of_flat_quotient (A := A) (algebraMap B (Localization.Away g₁) h) hflat)
    fun x hx => by
      obtain ⟨u, hu, h0⟩ := exists_mem_smul_eq_zero_away q.primeCompl h g₁
        (exists_notMem_smul_eq_zero q h hreg) x hx
      exact ⟨_, ⟨u, hu, rfl⟩, h0⟩
  refine ⟨v, hv, fun k hk => ?_⟩
  have h3 : algebraMap B (Localization.Away g₁) (v * k) = 0 :=
    (map_mul ..).trans (hv0 _ (by rw [← map_mul, hk, map_zero]))
  obtain ⟨⟨t', m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g₁) _ _).mp h3
  have hm' : g₁ ^ m * (v * k) = 0 := hm
  refine ⟨m + 1, ?_⟩
  rw [show (g₁ * v) ^ (m + 1) * k = (g₁ * v ^ m) * (g₁ ^ m * (v * k)) by ring, hm', mul_zero]

/-- Let `A → B` be flat and of finite presentation, let `q` be a prime of `B`, let `p = A ∩ q` and
let `h ∈ q`. If `h` is a nonzerodivisor on the fibre `B_q/pB_q`, then there is a `g ∉ q` such that
`h` is a nonzerodivisor in `B_g` and `B_g/hB_g` is flat over `A`; that is, `V(h) ⊂ Spec(B_g)` is a
relative effective Cartier divisor over `Spec(A)`. -/
theorem exists_notMem_isSMulRegular_and_flat_quotient_away
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (h : B) (hq : h ∈ q)
    (hfib : IsSMulRegular
      (Localization.AtPrime q ⧸
        (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)))
      (algebraMap B (Localization.AtPrime q) h)) :
    ∃ g ∉ q,
      IsSMulRegular (Localization.Away g) (algebraMap B (Localization.Away g) h) ∧
        Module.Flat A
          (Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) h}) := by
  obtain ⟨hreg, hflatq⟩ := isSMulRegular_and_flat_quotient_atPrime q h hfib
  obtain ⟨g₁, hg₁, hcU⟩ := exists_notMem_forall_flat_atPrime_quotient q h hq hflatq
  obtain ⟨u, huq, hu⟩ :=
    exists_notMem_pow_smul_ker q h g₁ (flat_quotient_away_of_forall h g₁ hcU) hreg
  refine ⟨g₁ * u, fun hmem => (‹q.IsPrime›.mem_or_mem hmem).elim hg₁ huq,
    isSMulRegular_away_of_smul_ker h (g₁ * u) hu, ?_⟩
  exact flat_quotient_away_of_forall h (g₁ * u) fun Q' hQ' => hcU Q'
    fun hmem => hQ' (by rw [map_mul]; exact Ideal.mul_mem_right _ _ hmem)

/-! ### Base change -/

/-- If `h ∈ B` is a nonzerodivisor and `B/hB` is flat over `A`, then the short exact sequence
`0 → B →[h] B → B/hB → 0` of `A`-modules stays exact after `X ⊗_A -` for every `A`-module `X`. -/
@[ega "0 6.1.2" "special case", sga "1 IV 1.1" "(i), special case"]
theorem injective_lTensor_mulLeft_of_flat_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (h : B)
    (hreg : IsSMulRegular B h) (hflat : Module.Flat A (B ⧸ Ideal.span {h}))
    (X : Type*) [AddCommGroup X] [Module A X] :
    Function.Injective (LinearMap.lTensor X (LinearMap.mulLeft A h)) := by
  have := hflat
  refine LinearMap.lTensor_injective_of_exact_of_flat (R := A) (M := B) (N := B)
    (P := B ⧸ Ideal.span {h}) (Ideal.Quotient.mkₐ A (Ideal.span {h})).toLinearMap
    Ideal.Quotient.mk_surjective (LinearMap.mulLeft A h) hreg (fun y => ?_) X
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor <;> rintro ⟨c, hc⟩ <;>
    exact ⟨c, by simpa [LinearMap.mulLeft_apply, mul_comm] using hc⟩

/-- If `h ∈ B` is a nonzerodivisor and `B/hB` is flat over `A`, then the image of `h` in
`A' ⊗_A B` is a nonzerodivisor for every `A`-algebra `A'`. -/
theorem isSMulRegular_tmul_of_flat_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (h : B)
    (hreg : IsSMulRegular B h) (hflat : Module.Flat A (B ⧸ Ideal.span {h}))
    (A' : Type*) [CommRing A'] [Algebra A A'] :
    IsSMulRegular (A' ⊗[A] B) ((1 : A') ⊗ₜ[A] h) := by
  have hinj := injective_lTensor_mulLeft_of_flat_quotient h hreg hflat A'
  have key : ∀ x : A' ⊗[A] B,
      LinearMap.lTensor A' (LinearMap.mulLeft A h) x = ((1 : A') ⊗ₜ[A] h) * x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, hx, hy, mul_add]
  exact fun x y hxy => hinj (by rw [key, key]; simpa [smul_eq_mul] using hxy)

end Stacks.RingTheory.SpreadingOut

end
