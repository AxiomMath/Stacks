module

public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian
public import StacksFrontier.RingTheory.Localization.AwayToAtPrime
public import StacksFrontier.RingTheory.Sequence.Regular.Basic

/-!
# A regular sequence with flat quotient spreads out from a local ring

Let `S` be a Noetherian ring of finite type over a Noetherian ring `R` and let `q` be a prime
of `S`. A sequence in the local ring `S_q` which is regular and whose quotient is flat over `R`
is, after multiplying by one unit of `S_q`, the image of a sequence over a principal
localization `S_g` which is regular there and has flat quotient over `R`.

## Main results

* `SpreadingOut.exists_common_numerators`: finitely many elements of `S_q` become, after
  multiplying by a single element of `S` outside `q`, images of elements of `S`.
* `SpreadingOut.regular_sequence_localize_away_dvd_of_atPrime`: a sequence regular over `S_q`
  is regular over `S_g` for some `g ∉ q` divisible by a prescribed element outside `q`.
* `SpreadingOut.exists_away_flat_quotient`: a quotient of `S_q` flat over `R` stays flat over
  `R` at every prime of a basic open neighbourhood of `q`.
* `SpreadingOut.exists_away_regular_representation`: the combination of the three, producing the
  sequence over `S_g` together with its regularity and the flatness of its quotient.

## Implementation notes

The local and principal localizations are the concrete rings `Localization.AtPrime q` and
`Localization.Away g`, and the comparison between them is
`localizationAwayToAtPrime`. A sequence is a `List` for the regularity API of
`RingTheory.Sequence` and a function out of `Fin n` for the consumers that index terms; the two
are converted by `List.ofFn`.

Clearing denominators produces the sequence only up to the common denominator, so the conclusion
of `SpreadingOut.exists_away_regular_representation` is about `v⁻¹ • (numerators)` for a unit
`v`; regularity and the ideal generated are both unchanged by a unit, which is what makes this
harmless.
-/

@[expose] public noncomputable section

open RingTheory.Sequence

universe u

namespace SpreadingOut

/-- Finitely many elements of the local ring `S_q` admit a common denominator: there is a
`g ∈ S` outside `q` and elements `a i` of `S` with `a i = g * f i` in `S_q`. -/
theorem exists_common_numerators {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    {r : ℕ} (f : Fin r → Localization.AtPrime q) :
    ∃ (g : S) (_hg : g ∉ q) (a : Fin r → S),
      ∀ i, algebraMap S (Localization.AtPrime q) (a i) =
        algebraMap S (Localization.AtPrime q) g * f i := by
  classical
  have hrep (i : Fin r) : ∃ (a : S) (s : q.primeCompl),
      IsLocalization.mk' (Localization.AtPrime q) a s = f i := by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective q.primeCompl (f i)
    exact ⟨a, s, h⟩
  choose a s hs using hrep
  let g : S := ∏ i : Fin r, (s i : S)
  have hg : g ∉ q := show g ∈ q.primeCompl from Submonoid.prod_mem _ fun i _ => (s i).property
  let b (i : Fin r) : S := a i * ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i, (s j : S)
  refine ⟨g, hg, b, fun i => ?_⟩
  have hprod : g = (s i : S) *
      ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i, (s j : S) :=
    (Finset.mul_prod_erase Finset.univ (fun j => (s j : S)) (Finset.mem_univ i)).symm
  rw [← hs i, hprod]
  have hcancel : algebraMap S (Localization.AtPrime q) (s i : S) *
      IsLocalization.mk' (Localization.AtPrime q) (a i) (s i) =
      algebraMap S (Localization.AtPrime q) (a i) := by
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left]
  calc
    algebraMap S (Localization.AtPrime q) (b i) =
        algebraMap S (Localization.AtPrime q) (a i) *
          algebraMap S (Localization.AtPrime q)
            (∏ j ∈ (Finset.univ : Finset (Fin r)).erase i, (s j : S)) := map_mul _ _ _
    _ = (algebraMap S (Localization.AtPrime q) (s i : S) *
          algebraMap S (Localization.AtPrime q)
            (∏ j ∈ (Finset.univ : Finset (Fin r)).erase i, (s j : S))) *
          IsLocalization.mk' (Localization.AtPrime q) (a i) (s i) := by
          rw [mul_assoc, mul_comm _ (IsLocalization.mk' _ _ _), ← mul_assoc, hcancel]
    _ = algebraMap S (Localization.AtPrime q)
          ((s i : S) * ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i, (s j : S)) *
          IsLocalization.mk' (Localization.AtPrime q) (a i) (s i) := by rw [map_mul]

/-- Multiplying every generator by a unit does not change the ideal they span. -/
private theorem span_range_mul_unit {A : Type*} [CommRing A] {n : ℕ} {c : A} (hc : IsUnit c)
    (x : Fin n → A) : Ideal.span (Set.range fun i => c * x i) = Ideal.span (Set.range x) := by
  rw [← Ideal.ofList_ofFn, ← Ideal.ofList_ofFn x, ← Ideal.ofList_map_mul_unit hc (List.ofFn x),
    List.map_ofFn]
  rfl

/-- Multiplying every term of a regular sequence by a unit gives a regular sequence. -/
private theorem isRegular_ofFn_mul_unit {A : Type*} [CommRing A] {n : ℕ} {c : A} (hc : IsUnit c)
    {x : Fin n → A} (h : IsRegular A (List.ofFn x)) :
    IsRegular A (List.ofFn fun i => c * x i) := by
  simpa only [List.map_ofFn, Function.comp_def] using h.map_mul_unit hc

/-- The numerators produced by `SpreadingOut.exists_common_numerators` generate, in the local
ring, the same ideal as the original elements: their common denominator is a unit there. -/
theorem span_numerators_eq {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    {r : ℕ} (f : Fin r → Localization.AtPrime q) (a : S) (b : Fin r → S) (ha : a ∉ q)
    (hb : ∀ i, algebraMap S (Localization.AtPrime q) (b i) =
      algebraMap S (Localization.AtPrime q) a * f i) :
    (Ideal.span (Set.range b)).map (algebraMap S (Localization.AtPrime q)) =
      Ideal.span (Set.range f) := by
  have ha' : a ∈ q.primeCompl := ha
  have hu : IsUnit (algebraMap S (Localization.AtPrime q) a) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨a, ha'⟩ : q.primeCompl)
  rw [Ideal.map_span, ← Set.range_comp, Function.comp_def, funext hb, span_range_mul_unit hu]

section RegularSpread

variable {S : Type*} [CommRing S] [IsNoetherianRing S]

/-- A sequence regular on the localization of `S` at a prime `p` is regular on a principal
localization of `S` away from an element outside `p` which, moreover, may be taken divisible by
any prescribed element outside `p`. -/
theorem regular_sequence_localize_away_dvd_of_atPrime (p : Ideal S) [p.IsPrime] (xs : List S)
    (hp : IsRegular (LocalizedModule p.primeCompl S)
      (xs.map (algebraMap S (Localization.AtPrime p))))
    (a : S) (ha : a ∉ p) :
    ∃ g : S, g ∉ p ∧ a ∣ g ∧
      IsRegular (LocalizedModule (Submonoid.powers g) S)
        (xs.map (algebraMap S (Localization.Away g))) := by
  obtain ⟨g₀, hg₀, hker₀, _⟩ := L_choose_g p xs hp
  let g := a * g₀
  have hg : g ∈ p.primeCompl := mul_mem ha hg₀
  have hker : ∀ i (hi : i < xs.length),
      Subsingleton (LocalizedModule (Submonoid.powers g)
        (LinearMap.ker (LinearMap.lsmul S
          (S ⧸ (Ideal.ofList (xs.take i) • ⊤ : Submodule S S)) xs[i]))) := by
    intro i hi
    have hsub := hker₀ i hi
    rw [LocalizedModule.subsingleton_iff] at hsub ⊢
    intro m
    obtain ⟨r, ⟨k, rfl⟩, hr⟩ := hsub m
    refine ⟨g ^ k, ⟨k, rfl⟩, ?_⟩
    change g ^ k • m = 0
    rw [show g = g₀ * a by simp [g, mul_comm], mul_pow, mul_smul,
      smul_comm (g₀ ^ k) (a ^ k) m, hr, smul_zero]
  have htop :
      (⊤ : Submodule (Localization.Away g) (LocalizedModule (Submonoid.powers g) S)) ≠
        Ideal.ofList (xs.map (algebraMap S (Localization.Away g))) • ⊤ := by
    rw [ne_comm, ne_eq, ← Submodule.Quotient.subsingleton_iff]
    intro hsubg
    have hQg : Subsingleton
        (LocalizedModule (Submonoid.powers g)
          (S ⧸ (Ideal.ofList xs • ⊤ : Submodule S S))) := by
      obtain ⟨e⟩ := nonempty_localizedModule_quotient_ofList_equiv
        (M := S) xs (Submonoid.powers g)
      exact (Equiv.subsingleton_congr e.toEquiv).mpr hsubg
    have hQp : Subsingleton
        (LocalizedModule p.primeCompl (S ⧸ (Ideal.ofList xs • ⊤ : Submodule S S))) := by
      rw [LocalizedModule.subsingleton_iff] at hQg ⊢
      intro m
      obtain ⟨r, hrmem, hr⟩ := hQg m
      exact ⟨r, (Submonoid.powers_le.mpr hg) hrmem, hr⟩
    obtain ⟨e⟩ := nonempty_localizedModule_quotient_ofList_equiv (M := S) xs p.primeCompl
    have hsubp := (Equiv.subsingleton_congr e.toEquiv).mp hQp
    have hp' := hp.top_ne_smul
    rw [ne_comm, ne_eq, ← Submodule.Quotient.subsingleton_iff] at hp'
    exact hp' hsubp
  refine ⟨g, hg, ⟨g₀, rfl⟩, ?_, htop⟩
  rw [isWeaklyRegular_map_algebraMap_iff (Localization.Away g)]
  exact L_weaklyRegular_of_kernels_away g xs hker

/-- The localization of a ring at `T` is its localized module as a module over itself. -/
private def localizedModuleEquiv {S : Type*} [CommRing S] (T : Submonoid S) :
    LocalizedModule T S ≃ₗ[Localization T] Localization T :=
  LinearEquiv.extendScalarsOfIsLocalization T (Localization T)
    (IsLocalizedModule.linearEquiv T
      (LocalizedModule.mkLinearMap T S) (Algebra.linearMap S (Localization T)))

/-- Regularity of a sequence on `S_T`, viewed as a localized module or as a ring. -/
private theorem isRegular_localizedModule_iff {S : Type*} [CommRing S] (T : Submonoid S) {n : ℕ}
    (f : Fin n → S) :
    IsRegular (LocalizedModule T S) ((List.ofFn f).map (algebraMap S (Localization T))) ↔
      IsRegular (Localization T) (List.ofFn fun i => algebraMap S (Localization T) (f i)) := by
  rw [List.map_ofFn]
  exact (localizedModuleEquiv T).isRegular_congr _

/-- The `Fin`-indexed form of `SpreadingOut.regular_sequence_localize_away_dvd_of_atPrime`,
stated for the localizations themselves rather than for `LocalizedModule`. -/
theorem exists_away_regular_of_atPrime_regular (p : Ideal S) [p.IsPrime]
    {n : ℕ} (f : Fin n → S) (a : S) (ha : a ∉ p)
    (hreg : IsRegular (Localization.AtPrime p)
      (List.ofFn fun i => algebraMap S (Localization.AtPrime p) (f i))) :
    ∃ g : S, g ∉ p ∧ a ∣ g ∧ IsRegular (Localization.Away g)
      (List.ofFn fun i => algebraMap S (Localization.Away g) (f i)) := by
  obtain ⟨g, hg, hag, hr⟩ := regular_sequence_localize_away_dvd_of_atPrime p (List.ofFn f)
    ((isRegular_localizedModule_iff p.primeCompl f).2 hreg) a ha
  exact ⟨g, hg, hag, (isRegular_localizedModule_iff (Submonoid.powers g) f).1 hr⟩

end RegularSpread

/-- Localizing a quotient of a ring by an ideal is the quotient of the localization by the
extended ideal. -/
theorem localized_quotient_ring_equiv {S : Type*} [CommRing S] (T : Submonoid S) (I : Ideal S) :
    Nonempty ((LocalizedModule T (S ⧸ I)) ≃ₗ[S]
      (Localization T ⧸ I.map (algebraMap S (Localization T)))) := by
  let e := localizedModuleEquiv T
  have hmap : (I.localized T).map e.toLinearMap =
      (I.map (algebraMap S (Localization T)) :
        Submodule (Localization T) (Localization T)) := by
    rw [Submodule.localized, Submodule.localized'_eq_span, Submodule.map_span]
    change Submodule.span (Localization T)
      (e '' ((LocalizedModule.mkLinearMap T S) '' (I : Set S))) =
        Submodule.span (Localization T) ((algebraMap S (Localization T)) '' (I : Set S))
    congr 1
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (IsLocalizedModule.linearEquiv_apply T
        (LocalizedModule.mkLinearMap T S) (Algebra.linearMap S (Localization T)) x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(LocalizedModule.mkLinearMap T S) x, ⟨x, hx, rfl⟩,
        IsLocalizedModule.linearEquiv_apply T
          (LocalizedModule.mkLinearMap T S) (Algebra.linearMap S (Localization T)) x⟩
  let eQ := Submodule.Quotient.equiv (I.localized T)
    (I.map (algebraMap S (Localization T))) e hmap
  exact ⟨((localizedQuotientEquiv T I).symm.trans eQ).restrictScalars S⟩

/-- If the quotient of the local ring `S_q` by an ideal is flat over `R`, then the localization
of `S ⧸ I` at every prime of a basic open neighbourhood of `q` is flat over `R`. -/
theorem exists_away_flat_quotient {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] (I : Ideal S)
    (hflat : Module.Flat R
      (Localization.AtPrime q ⧸ I.map (algebraMap S (Localization.AtPrime q)))) :
    ∃ g : S, g ∉ q ∧
      ∀ p ∈ PrimeSpectrum.basicOpen g,
        Module.Flat R (LocalizedModule.AtPrime p.asIdeal (S ⧸ I)) := by
  let M := S ⧸ I
  let e : LocalizedModule.AtPrime q M ≃ₗ[S]
      (Localization.AtPrime q ⧸ I.map (algebraMap S (Localization.AtPrime q))) :=
    (localized_quotient_ring_equiv q.primeCompl I).some
  have hq : Module.Flat R (LocalizedModule.AtPrime q M) :=
    (Module.Flat.equiv_iff (e.restrictScalars R)).mpr hflat
  let U : Set (PrimeSpectrum S) := {p | Module.Flat R (LocalizedModule.AtPrime p.asIdeal M)}
  have ho : IsOpen U :=
    Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing
      (R := R) (S := S) (M := M)
  have hmem : (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) ∈ U := hq
  rw [PrimeSpectrum.eq_biUnion_of_isOpen ho] at hmem
  obtain ⟨g, hgU, hqg⟩ := Set.mem_iUnion₂.mp hmem
  exact ⟨g, (PrimeSpectrum.mem_basicOpen g ⟨q, ‹q.IsPrime›⟩).mp hqg, hgU⟩

/-- A sequence in the local ring `S_q` which is regular and whose quotient is flat over `R`
comes from a sequence over a principal localization `S_g`, up to a unit of `S_q`, which is
regular there and whose quotient is again flat over `R`. -/
theorem exists_away_regular_representation {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] {r : ℕ} (f : Fin r → Localization.AtPrime q)
    (hf : IsRegular (Localization.AtPrime q) (List.ofFn f))
    (hflat : Module.Flat R (Localization.AtPrime q ⧸ Ideal.span (Set.range f))) :
    ∃ (g : S) (hg : g ∉ q) (f' : Fin r → Localization.Away g),
      (∀ i, localizationAwayToAtPrime g q hg (f' i) = f i) ∧
      IsRegular (Localization.Away g) (List.ofFn f') ∧
      Module.Flat R (Localization.Away g ⧸ Ideal.span (Set.range f')) := by
  classical
  obtain ⟨a, ha, b, hb⟩ := exists_common_numerators q f
  have ha' : a ∈ q.primeCompl := ha
  have hu : IsUnit (algebraMap S (Localization.AtPrime q) a) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨a, ha'⟩ : q.primeCompl)
  have hregb : IsRegular (Localization.AtPrime q)
      (List.ofFn fun i => algebraMap S (Localization.AtPrime q) (b i)) := by
    rw [funext hb]
    exact isRegular_ofFn_mul_unit hu hf
  let I : Ideal S := Ideal.span (Set.range b)
  have hIq : I.map (algebraMap S (Localization.AtPrime q)) = Ideal.span (Set.range f) :=
    span_numerators_eq q f a b ha hb
  obtain ⟨c, hc, hU⟩ := exists_away_flat_quotient q I (by rwa [hIq])
  have hac : a * c ∉ q := (q.primeCompl).mul_mem ha hc
  obtain ⟨g, hg, hgc, hregg⟩ := exists_away_regular_of_atPrime_regular q b (a * c) hac hregb
  have hag : a ∣ g := dvd_trans (dvd_mul_right a c) hgc
  have hcg : c ∣ g := dvd_trans (dvd_mul_left c a) hgc
  have hunit : IsUnit (algebraMap S (Localization.Away g) a) := by
    obtain ⟨d, hd⟩ := hag
    refine isUnit_of_mul_isUnit_left (y := algebraMap S (Localization.Away g) d) ?_
    rw [← map_mul, ← hd]
    exact IsLocalization.Away.algebraMap_isUnit g
  let v : (Localization.Away g)ˣ := hunit.unit
  have hv : (v : Localization.Away g) = algebraMap S (Localization.Away g) a := hunit.unit_spec
  let f' (i : Fin r) : Localization.Away g :=
    (↑(v⁻¹) : Localization.Away g) * algebraMap S (Localization.Away g) (b i)
  refine ⟨g, hg, f', ?_, ?_, ?_⟩
  · intro i
    apply hu.mul_left_cancel
    have hmap : (localizationAwayToAtPrime g q hg)
        (algebraMap S (Localization.Away g) a * f' i) =
        algebraMap S (Localization.AtPrime q) (b i) := by
      change (localizationAwayToAtPrime g q hg)
        (algebraMap S (Localization.Away g) a *
          ((↑(v⁻¹) : Localization.Away g) * algebraMap S (Localization.Away g) (b i))) = _
      rw [← hv, ← mul_assoc, Units.mul_inv, one_mul]
      simp only [localizationAwayToAtPrime, IsLocalization.map_eq, RingHom.id_apply]
    have hstr : localizationAwayToAtPrime g q hg (algebraMap S (Localization.Away g) a) =
        algebraMap S (Localization.AtPrime q) a := by
      simp only [localizationAwayToAtPrime, IsLocalization.map_eq, RingHom.id_apply]
    calc
      algebraMap S (Localization.AtPrime q) a * localizationAwayToAtPrime g q hg (f' i)
          = (localizationAwayToAtPrime g q hg)
              (algebraMap S (Localization.Away g) a * f' i) := by
                rw [← hstr]
                exact ((localizationAwayToAtPrime g q hg).map_mul _ _).symm
      _ = algebraMap S (Localization.AtPrime q) (b i) := hmap
      _ = algebraMap S (Localization.AtPrime q) a * f i := hb i
  · exact isRegular_ofFn_mul_unit (Units.isUnit v⁻¹) hregg
  · have hflatg : Module.Flat R (LocalizedModule.Away g (S ⧸ I)) := by
      apply Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime g
      intro p hp
      refine hU p ((PrimeSpectrum.mem_basicOpen c p).mpr fun hcp => ?_)
      obtain ⟨d, hd⟩ := hcg
      exact (PrimeSpectrum.mem_basicOpen g p).mp hp (hd ▸ p.asIdeal.mul_mem_right d hcp)
    let eg : LocalizedModule.Away g (S ⧸ I) ≃ₗ[S]
        (Localization.Away g ⧸ I.map (algebraMap S (Localization.Away g))) :=
      (localized_quotient_ring_equiv (Submonoid.powers g) I).some
    have hflatIg : Module.Flat R
        (Localization.Away g ⧸ I.map (algebraMap S (Localization.Away g))) :=
      (Module.Flat.equiv_iff (eg.restrictScalars R)).mp hflatg
    have hIf : I.map (algebraMap S (Localization.Away g)) = Ideal.span (Set.range f') := by
      change (Ideal.span (Set.range b)).map (algebraMap S (Localization.Away g)) = _
      rw [Ideal.map_span, ← Set.range_comp]
      exact (span_range_mul_unit (Units.isUnit v⁻¹) _).symm
    rwa [← hIf]

end SpreadingOut

end
