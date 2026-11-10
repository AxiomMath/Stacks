module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Two principal opens of the spectrum of a UFD

Stacks Tag 0BDA says that the Picard group of an open subscheme `U` of `Spec R` — and of an open
subscheme of affine space over `R` — is trivial when `R` is a unique factorization domain. Its
proof reduces, by prime avoidance, to a pair of elements `f, g` of `R` with
`D(f) ∪ D(g) ⊆ U` whose common prime factors all vanish identically on `U`, and then rests
entirely on two elementary facts about such a pair:

* the sequence `0 → R → R_f × R_g → R_{fg}` is exact, so a function given compatibly on `D(f)`
  and on `D(g)` is already a function on all of `Spec R`; and
* the map `R_f^* × R_g^* → R_{fg}^*`, `(u, v) ↦ u ⬝ v`, is surjective, so a transition unit on
  `D(f) ∩ D(g)` splits, and an invertible module trivialized on each of `D(f)` and `D(g)` is
  trivial on `D(f) ∪ D(g)`.

This file carries those two facts and the prime-factor combinatorics they need, together with
two statements about the structure sheaf of `Spec R`: sections over `D(f) ∪ D(g)` are exactly the
elements of `R`, and restriction from `D(h)` to `D(h) ∩ (D(f) ∪ D(g))` is bijective whenever every
prime factor shared by `f` and `g` divides `h`. The tag itself is
`Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum` and
`Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace`.

## Main results

Prime-factor combinatorics in a UFD:

* `Stacks.PicardUFD.dvd_pow_of_dvd_mul_of_disjoint_factors`: for `f` and `g` with no common
  normalized prime factor, `f ^ m ∣ b * g ^ n` forces `f ^ m ∣ b`.
* `Stacks.PicardUFD.isUnit_away_of_normalizedFactors_subset`: an element all of whose normalized
  prime factors divide `f` becomes a unit in `R_f`.
* `Stacks.PicardUFD.normalizedFactors_mem_of_away_unit` and
  `Stacks.PicardUFD.factorization_split_of_away_unit`: a numerator that becomes a unit in
  `R_{fg}` has all its prime factors among those of `f` and of `g`, hence factors as a product of
  an element supported on `f`, one supported on `g`, and a unit.
* `Stacks.PicardUFD.fraction_mem_of_two_away_localizations` and
  `Stacks.PicardUFD.fraction_mem_away_of_common_factors`: a fraction regular after inverting
  either of two elements with disjoint (resp. with `h`-divisible common) prime factors is already
  regular (resp. regular after inverting `h`).

The two facts about the pair:

* `Stacks.PicardUFD.away_intersection`: exactness of `0 → R → R_f × R_g → R_{fg}`.
* `Stacks.PicardUFD.away_product_unit_splits`: surjectivity of `R_f^* × R_g^* → R_{fg}^*`.
* `Stacks.PicardUFD.localization_intersection` and
  `Stacks.PicardUFD.localization_units_split`: the same two statements for arbitrary models of
  the three localizations.

On `Spec R`:

* `Stacks.PicardUFD.algebraMap_bijective_two_basicOpens`:
  `R → 𝒪(D(f) ∪ D(g))` is bijective when `f` and `g` have no common prime factor.
* `Stacks.PicardUFD.restriction_bijective_two_basicOpens`: restriction
  `𝒪(D(h)) → 𝒪(D(h) ∩ (D(f) ∪ D(g)))` is bijective when every prime factor of `f` dividing `g`
  divides `h`.
* `Stacks.PicardUFD.functions_bijective_open_two_basicOpens`: on an open `U` containing
  `D(f) ∪ D(g)`, every function on `V ∩ (D(f) ∪ D(g))` extends uniquely to `V`, for every open
  `V` of `U`; `Stacks.PicardUFD.functions_bijective_of_basis` checks such a bijectivity on a
  basis.
* `Stacks.PicardUFD.exists_two_basicOpens_common_factors`: the prime-avoidance step — every
  nonempty open of `Spec R` contains `D(f) ∪ D(g)` for a pair `f, g` whose common prime factors
  vanish identically on it.

## Implementation notes

The two localization facts are proved first for Mathlib's model `Localization.Away`, where
`Localization.awayLift` names the comparison maps, and then transported to an arbitrary
`IsLocalization.Away` algebra by `IsLocalization.algEquiv`; the transported forms take the two
comparison maps as `AlgHom`s, which is how the restriction maps of the structure sheaf present
themselves.

Sections of the structure sheaf over a principal open are compared through the fraction field
rather than through `Localization.Away` directly: `Stacks.PicardUFD.awayToFractionRing` is the
canonical injection `𝒪(D(h)) → Frac R`, and both statements about the structure sheaf are proved
by identifying sections with their images there. This avoids transporting along
`IsLocalization.algEquiv` inside a sheaf condition, where the resulting `eqToHom`s do not
cancel.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.PicardUFD

/-! ### Prime-factor combinatorics in a unique factorization domain -/

/-- If two elements of a UFD have no common normalized prime factors, every power of the first
which divides a product of the second with another element already divides that other element. -/
theorem dvd_pow_of_dvd_mul_of_disjoint_factors
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] {f g b : R} {m n : ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hdisj : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f,
      p ∉ UniqueFactorizationMonoid.normalizedFactors g)
    (h : f ^ m ∣ b * g ^ n) : f ^ m ∣ b := by
  classical
  by_cases hb : b = 0
  · simp [hb]
  have hfg : f ^ m ≠ 0 := pow_ne_zero _ hf
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg
  have hmul : b * g ^ n ≠ 0 := mul_ne_zero hb hgn
  apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hfg hb).2
  rw [UniqueFactorizationMonoid.normalizedFactors_pow]
  apply Multiset.le_iff_count.mpr
  intro p
  have hc :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hfg hmul).1 h
  have hc' := (Multiset.le_iff_count.mp hc) p
  have hc'' : m * Multiset.count p (UniqueFactorizationMonoid.normalizedFactors f) ≤
      Multiset.count p (UniqueFactorizationMonoid.normalizedFactors b) +
        n * Multiset.count p (UniqueFactorizationMonoid.normalizedFactors g) := by
    simpa [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_mul hb hgn, Multiset.count_nsmul,
      Multiset.count_add] using hc'
  by_cases hp : p ∈ UniqueFactorizationMonoid.normalizedFactors f
  · simpa [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
      Multiset.count_eq_zero.mpr (hdisj p hp)] using hc''
  · have hpf : Multiset.count p (UniqueFactorizationMonoid.normalizedFactors f) = 0 :=
      Multiset.count_eq_zero.mpr (by simpa using hp)
    simp [Multiset.count_nsmul, hpf]

/-- A fraction which is regular after inverting either of two elements with disjoint prime factors
is already regular. -/
theorem fraction_mem_of_two_away_localizations
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [Field K] [Algebra R K]
    [IsFractionRing R K] {f g : R} {z : K}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hdisj : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f,
      p ∉ UniqueFactorizationMonoid.normalizedFactors g)
    (hfz : ∃ (m : ℕ) (a : R), z * (algebraMap R K f) ^ m = algebraMap R K a)
    (hgz : ∃ (n : ℕ) (b : R), z * (algebraMap R K g) ^ n = algebraMap R K b) :
    ∃ c : R, z = algebraMap R K c := by
  classical
  obtain ⟨m, a, hfa⟩ := hfz
  obtain ⟨n, b, hgb⟩ := hgz
  have heq : algebraMap R K (a * g ^ n) = algebraMap R K (b * f ^ m) := by
    calc
      algebraMap R K (a * g ^ n) =
          (z * (algebraMap R K f) ^ m) * (algebraMap R K g) ^ n := by
            rw [hfa, map_mul, map_pow]
      _ = (z * (algebraMap R K g) ^ n) * (algebraMap R K f) ^ m := by ring
      _ = algebraMap R K (b * f ^ m) := by rw [hgb, map_mul, map_pow]
  have hmul : a * g ^ n = b * f ^ m := (IsFractionRing.injective R K) heq
  have hpow : (algebraMap R K f) ^ m ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf)
  obtain ⟨c, hc⟩ := dvd_pow_of_dvd_mul_of_disjoint_factors hf hg hdisj
    (⟨b, by simpa [mul_comm] using hmul⟩ : f ^ m ∣ a * g ^ n)
  refine ⟨c, mul_right_cancel₀ hpow ?_⟩
  rw [hfa, hc, map_mul, map_pow, mul_comm]

/-- A numerator which becomes a unit after inverting a product can only have prime factors coming
from one of the two inverted elements. -/
theorem normalizedFactors_mem_of_away_unit
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] {f g a : R} (hf : f ≠ 0) (hg : g ≠ 0)
    (hunit : IsUnit (algebraMap R (Localization.Away (f * g)) a))
    {p : R} (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors a) :
    p ∈ UniqueFactorizationMonoid.normalizedFactors f ∨
      p ∈ UniqueFactorizationMonoid.normalizedFactors g := by
  classical
  obtain ⟨m, hm, hdiv⟩ :=
    (IsLocalization.algebraMap_isUnit_iff (Submonoid.powers (f * g))).mp hunit
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m (f * g)).mp hm
  rw [← hn] at hdiv
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hpow : (f * g) ^ n ≠ 0 := pow_ne_zero _ hfg
  have ha : a ≠ 0 := by
    rintro rfl
    exact hpow (zero_dvd_iff.mp hdiv)
  have hle := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
    ha hpow).mp hdiv
  have hcount := (Multiset.le_iff_count.mp hle) p
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_mul hf hg,
    Multiset.count_nsmul, Multiset.count_add] at hcount
  by_contra! hpfg
  rw [Multiset.count_eq_zero.mpr hpfg.1, Multiset.count_eq_zero.mpr hpfg.2] at hcount
  exact (Multiset.count_pos.mpr hp).ne' (by simpa using hcount)

/-- An element whose localization at a product is a unit splits as a product of an element
supported on the first factor, one supported on the second, and a unit. -/
theorem factorization_split_of_away_unit
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] {f g a : R} (hf : f ≠ 0) (hg : g ≠ 0)
    (hunit : IsUnit (algebraMap R (Localization.Away (f * g)) a)) :
    ∃ u : Rˣ, ∃ af ag : R,
      a = af * ag * u ∧
      (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors af,
        p ∈ UniqueFactorizationMonoid.normalizedFactors f) ∧
      (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors ag,
        p ∈ UniqueFactorizationMonoid.normalizedFactors g) := by
  classical
  obtain ⟨u, hu, haf, hag⟩ :=
    (IsLocalization.algebraMap_isUnit_iff (Submonoid.powers (f * g))).mp hunit
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff u (f * g)).mp hu
  rw [← hn] at hag
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have ha : a ≠ 0 := by
    rintro rfl
    exact (pow_ne_zero n hfg) (by simpa using hag)
  let F := UniqueFactorizationMonoid.normalizedFactors a
  let Ff := F.filter fun p => p ∈ UniqueFactorizationMonoid.normalizedFactors f
  let Fg := F.filter fun p => p ∉ UniqueFactorizationMonoid.normalizedFactors f
  have hparts : Ff + Fg = F := by
    dsimp [Ff, Fg]
    exact Multiset.filter_add_not _ _
  have hprod : Ff.prod * Fg.prod = F.prod := by
    rw [← Multiset.prod_add, hparts]
  have hirr_f : ∀ p ∈ Ff, Irreducible p := fun p hp =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.mem_filter.mp hp).1).irreducible
  have hirr_g : ∀ p ∈ Fg, Irreducible p := fun p hp =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.mem_filter.mp hp).1).irreducible
  obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.prod_normalizedFactors ha
  refine ⟨v, Ff.prod, Fg.prod, ?_, ?_, ?_⟩
  · rw [hprod]
    exact hv.symm
  · intro p hp
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq Ff hirr_f] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨hqF, hqf⟩ := Multiset.mem_filter.mp hq
    rw [UniqueFactorizationMonoid.normalize_normalized_factor q hqF]
    exact hqf
  · intro p hp
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq Fg hirr_g] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨hqF, hqnotf⟩ := Multiset.mem_filter.mp hq
    rw [UniqueFactorizationMonoid.normalize_normalized_factor q hqF]
    exact (normalizedFactors_mem_of_away_unit hf hg hunit hqF).resolve_left hqnotf

/-- If every normalized prime factor of an element divides `f`, then that element becomes a unit
after inverting `f`. -/
theorem isUnit_away_of_normalizedFactors_subset
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] {f a : R} (ha : a ≠ 0)
    (hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors a,
      p ∈ UniqueFactorizationMonoid.normalizedFactors f) :
    IsUnit (algebraMap R (Localization.Away f) a) := by
  classical
  have hprod : IsUnit (algebraMap R (Localization.Away f)
      (UniqueFactorizationMonoid.normalizedFactors a).prod) := by
    have haux : ∀ s : Multiset R, (∀ p ∈ s,
        p ∈ UniqueFactorizationMonoid.normalizedFactors f) →
        IsUnit (algebraMap R (Localization.Away f) s.prod) := by
      intro s hs
      induction s using Multiset.induction with
      | empty => simp
      | cons p s ih =>
        rw [Multiset.prod_cons, map_mul]
        have hp := hs p (by simp)
        have hpdiv := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
        have hup : IsUnit (algebraMap R (Localization.Away f) p) :=
          isUnit_of_dvd_unit (map_dvd (algebraMap R (Localization.Away f)) hpdiv)
            (IsLocalization.Away.algebraMap_isUnit f)
        exact hup.mul (ih fun q hq => hs q (by simp [hq]))
    exact haux _ hfac
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors ha
  rw [← hu, map_mul]
  exact hprod.mul (u.isUnit.map _)

/-! ### The two facts about a pair of principal opens -/

/-- Localizing at a nonzero element of a domain is injective on the base ring. -/
private theorem injective_algebraMap_away
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] {h : R} (hh : h ≠ 0)
    [IsLocalization.Away h S] : Function.Injective (algebraMap R S) :=
  IsLocalization.injective (M := Submonoid.powers h) _ (by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hh))

/-- The first factor becomes a unit after inverting a product. -/
private theorem isUnit_away_mul_left {R : Type*} [CommRing R] (f g : R) :
    IsUnit (algebraMap R (Localization.Away (f * g)) f) :=
  isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g)) (IsLocalization.Away.algebraMap_isUnit _)

/-- The second factor becomes a unit after inverting a product. -/
private theorem isUnit_away_mul_right {R : Type*} [CommRing R] (f g : R) :
    IsUnit (algebraMap R (Localization.Away (f * g)) g) :=
  isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left g f)) (IsLocalization.Away.algebraMap_isUnit _)

/-- The comparison map out of `Localization.Away h` is the transport of an algebra map between
other models of the localizations. -/
private theorem awayLift_eq_comp_algEquiv
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A] (h m : R)
    [IsLocalization.Away h S] (hu : IsUnit (algebraMap R (Localization.Away m) h))
    (ef : S ≃ₐ[R] Localization.Away h) (ea : A ≃ₐ[R] Localization.Away m) (φ : S →ₐ[R] A) :
    Localization.awayLift (algebraMap R (Localization.Away m)) h hu =
      ea.toRingHom.comp (φ.toRingHom.comp ef.symm.toRingHom) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers h)
  ext r
  simp [Localization.awayLift]

/-- Every unit on the intersection of two principal opens is a product of units pulled back from
the two opens, when the inverted elements have disjoint prime factors. This is surjectivity of
`R_f^* × R_g^* → R_{fg}^*`. -/
theorem away_product_unit_splits
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] {f g : R} (hf : f ≠ 0) (hg : g ≠ 0)
    (w : (Localization.Away (f * g))ˣ) :
    ∃ (uf : (Localization.Away f)ˣ) (ug : (Localization.Away g)ˣ),
      let B := Localization.Away (f * g)
      letI : IsDomain B := IsLocalization.Away.isDomain B (mul_ne_zero hf hg)
      letI : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
      letI : IsDomain (Localization.Away g) := IsLocalization.Away.isDomain _ hg
      let ufg : IsUnit (algebraMap R B (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
      Localization.awayLift (algebraMap R B) f
          (isUnit_of_dvd_unit
            (map_dvd (algebraMap R B) (dvd_mul_right f g)) ufg) (uf : _) *
        Localization.awayLift (algebraMap R B) g
          (isUnit_of_dvd_unit
            (map_dvd (algebraMap R B) (dvd_mul_left g f)) ufg) (ug : _) = w := by
  classical
  let B := Localization.Away (f * g)
  let _ : IsDomain B := IsLocalization.Away.isDomain B (mul_ne_zero hf hg)
  let _ : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let _ : IsDomain (Localization.Away g) := IsLocalization.Away.isDomain _ hg
  let ufg : IsUnit (algebraMap R B (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  let ufB : IsUnit (algebraMap R B f) := isUnit_away_mul_left f g
  let ugB : IsUnit (algebraMap R B g) := isUnit_away_mul_right f g
  let φ : Localization.Away f →+* B := Localization.awayLift (algebraMap R B) f ufB
  let ψ : Localization.Away g →+* B := Localization.awayLift (algebraMap R B) g ugB
  let s := IsLocalization.Away.sec (f * g) (w : B)
  have hs : (w : B) * algebraMap R B ((f * g) ^ s.2) = algebraMap R B s.1 :=
    IsLocalization.Away.sec_spec (f * g) (w : B)
  have hsa : IsUnit (algebraMap R B s.1) := by
    rw [← hs]
    exact w.isUnit.mul (by rw [map_pow]; exact IsUnit.pow s.2 ufg)
  obtain ⟨v, af, ag, hav, haf, hag⟩ := factorization_split_of_away_unit hf hg hsa
  have hsa_ne : s.1 ≠ 0 := fun h => hsa.ne_zero (by simp [h])
  have haf_ne : af ≠ 0 := fun h => hsa_ne (by simp [hav, h])
  have hag_ne : ag ≠ 0 := fun h => hsa_ne (by simp [hav, h])
  have huaf : IsUnit (algebraMap R (Localization.Away f) af) :=
    isUnit_away_of_normalizedFactors_subset haf_ne haf
  have huag : IsUnit (algebraMap R (Localization.Away g) ag) :=
    isUnit_away_of_normalizedFactors_subset hag_ne hag
  let hfPow : IsUnit (algebraMap R (Localization.Away f) (f ^ s.2)) := by
    rw [map_pow]
    exact IsUnit.pow s.2 (IsLocalization.Away.algebraMap_isUnit f)
  let hgPow : IsUnit (algebraMap R (Localization.Away g) (g ^ s.2)) := by
    rw [map_pow]
    exact IsUnit.pow s.2 (IsLocalization.Away.algebraMap_isUnit g)
  let uvf : IsUnit (algebraMap R (Localization.Away f) (v : R)) :=
    IsUnit.map (algebraMap R (Localization.Away f)) v.isUnit
  let uf : (Localization.Away f)ˣ := huaf.unit * uvf.unit * hfPow.unit⁻¹
  let ug : (Localization.Away g)ˣ := huag.unit * hgPow.unit⁻¹
  refine ⟨uf, ug, ?_⟩
  have hden : IsUnit (algebraMap R B ((f * g) ^ s.2)) := by
    rw [map_pow]
    exact IsUnit.pow s.2 ufg
  apply mul_right_cancel₀ hden.ne_zero
  let mφ := Units.map φ.toMonoidHom
  let mψ := Units.map ψ.toMonoidHom
  let A := mφ huaf.unit
  let V := mφ uvf.unit
  let G := mψ huag.unit
  have hφaf : (A : B) = algebraMap R B af := by
    change φ (huaf.unit : Localization.Away f) = _
    simp [φ, Localization.awayLift]
  have hφv : (V : B) = algebraMap R B (v : R) := by
    change φ (uvf.unit : Localization.Away f) = _
    simp [φ, Localization.awayLift]
  have hψag : (G : B) = algebraMap R B ag := by
    change ψ (huag.unit : Localization.Away g) = _
    simp [ψ, Localization.awayLift]
  have hφpow : mφ hfPow.unit = ufB.unit ^ s.2 := by
    apply Units.ext
    change φ (hfPow.unit : Localization.Away f) = _
    simp [φ, Localization.awayLift, map_pow]
  have hψpow : mψ hgPow.unit = ugB.unit ^ s.2 := by
    apply Units.ext
    change ψ (hgPow.unit : Localization.Away g) = _
    simp [ψ, Localization.awayLift, map_pow]
  have hφuf : mφ uf = A * V * (ufB.unit ^ s.2)⁻¹ := by
    change mφ (huaf.unit * uvf.unit * hfPow.unit⁻¹) = _
    rw [map_mul, map_mul, map_inv, hφpow]
  have hψug : mψ ug = G * (ugB.unit ^ s.2)⁻¹ := by
    change mψ (huag.unit * hgPow.unit⁻¹) = _
    rw [map_mul, map_inv, hψpow]
  have hunit_eq : (mφ uf * mψ ug) * (ufB.unit * ugB.unit) ^ s.2 = A * G * V := by
    rw [hφuf, hψug, mul_pow]
    calc
      _ = A * V * G * ((ufB.unit ^ s.2)⁻¹ * ufB.unit ^ s.2) *
          ((ugB.unit ^ s.2)⁻¹ * ugB.unit ^ s.2) := by ac_rfl
      _ = A * V * G := by simp
      _ = A * G * V := by ac_rfl
  have hden_val : algebraMap R B ((f * g) ^ s.2) =
      ((ufB.unit * ugB.unit) ^ s.2 : B) := by
    rw [map_pow, map_mul, ufB.unit_spec, ugB.unit_spec]
  have hleft : (φ (uf : Localization.Away f) * ψ (ug : Localization.Away g)) *
      algebraMap R B ((f * g) ^ s.2) = algebraMap R B (af * ag * (v : R)) := by
    calc
      _ = ((mφ uf * mψ ug) * (ufB.unit * ugB.unit) ^ s.2 : B) := by
        simp [mφ, mψ, hden_val]
      _ = (A * G * V : B) := congrArg (fun z : Bˣ => (z : B)) hunit_eq
      _ = algebraMap R B (af * ag * (v : R)) := by
        rw [map_mul, map_mul]
        simp [hφaf, hψag, hφv]
  rw [hleft, ← hav, ← hs]

/-- If `x * f ^ n` is the image of `f ^ n * c` in a localization at `f`, then `x` is the image
of `c`. -/
private theorem eq_algebraMap_of_mul_pow_eq
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] {f : R}
    [IsLocalization.Away f S] {x : S} {n : ℕ} {a c : R}
    (hxa : x * algebraMap R S (f ^ n) = algebraMap R S a)
    (hc : a = f ^ n * c) : algebraMap R S c = x := by
  have hne : algebraMap R S (f ^ n) ≠ 0 := by
    rw [map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit f).pow _).ne_zero
  exact (mul_left_cancel₀ hne (by rw [mul_comm, hxa, hc, map_mul])).symm

/-- The equalizer of the two localization maps at a pair of elements with disjoint prime factors
is the original domain: the sequence `0 → R → R_f × R_g → R_{fg}` is exact. -/
theorem away_intersection
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (hdisj : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f,
      p ∉ UniqueFactorizationMonoid.normalizedFactors g)
    (x : Localization.Away f) (y : Localization.Away g)
    (hxy : Localization.awayLift (algebraMap R (Localization.Away (f * g))) f
        (isUnit_of_dvd_unit
          (map_dvd (algebraMap R (Localization.Away (f * g))) (dvd_mul_right f g))
          (IsLocalization.Away.algebraMap_isUnit (f * g))) x =
      Localization.awayLift (algebraMap R (Localization.Away (f * g))) g
        (isUnit_of_dvd_unit
          (map_dvd (algebraMap R (Localization.Away (f * g))) (dvd_mul_left g f))
          (IsLocalization.Away.algebraMap_isUnit (f * g))) y) :
    ∃ a : R, algebraMap R (Localization.Away f) a = x ∧
      algebraMap R (Localization.Away g) a = y := by
  classical
  let B := Localization.Away (f * g)
  let _ : IsDomain B := IsLocalization.Away.isDomain B (mul_ne_zero hf hg)
  let _ : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let _ : IsDomain (Localization.Away g) := IsLocalization.Away.isDomain _ hg
  let φ : Localization.Away f →+* B :=
    Localization.awayLift (algebraMap R B) f (isUnit_away_mul_left f g)
  let ψ : Localization.Away g →+* B :=
    Localization.awayLift (algebraMap R B) g (isUnit_away_mul_right f g)
  have hxy' : φ x = ψ y := hxy
  let sx := IsLocalization.Away.sec f x
  let sy := IsLocalization.Away.sec g y
  have hxsec : x * algebraMap R (Localization.Away f) (f ^ sx.2) =
      algebraMap R (Localization.Away f) sx.1 := IsLocalization.Away.sec_spec f x
  have hysec : y * algebraMap R (Localization.Away g) (g ^ sy.2) =
      algebraMap R (Localization.Away g) sy.1 := IsLocalization.Away.sec_spec g y
  have hxB : φ x * algebraMap R B (f ^ sx.2) = algebraMap R B sx.1 := by
    simpa [φ, Localization.awayLift] using congrArg φ hxsec
  have hyB : ψ y * algebraMap R B (g ^ sy.2) = algebraMap R B sy.1 := by
    simpa [ψ, Localization.awayLift] using congrArg ψ hysec
  have hcrossB : algebraMap R B (sx.1 * g ^ sy.2) =
      algebraMap R B (sy.1 * f ^ sx.2) := by
    calc
      algebraMap R B (sx.1 * g ^ sy.2) =
          (φ x * algebraMap R B (f ^ sx.2)) * algebraMap R B (g ^ sy.2) := by
            rw [hxB]
            simp [map_mul]
      _ = (ψ y * algebraMap R B (g ^ sy.2)) * algebraMap R B (f ^ sx.2) := by
        rw [hxy']
        ring
      _ = algebraMap R B (sy.1 * f ^ sx.2) := by rw [hyB]; simp [map_mul]
  have hcross : sx.1 * g ^ sy.2 = sy.1 * f ^ sx.2 :=
    injective_algebraMap_away (mul_ne_zero hf hg) hcrossB
  obtain ⟨c, hc⟩ : f ^ sx.2 ∣ sx.1 := dvd_pow_of_dvd_mul_of_disjoint_factors hf hg hdisj
    ⟨sy.1, by rw [hcross]; ring⟩
  have hbc : sy.1 = g ^ sy.2 * c :=
    (mul_left_cancel₀ (pow_ne_zero sx.2 hf)
      (by linear_combination hcross - g ^ sy.2 * hc)).symm
  exact ⟨c, eq_algebraMap_of_mul_pow_eq hxsec hc, eq_algebraMap_of_mul_pow_eq hysec hbc⟩

/-- `Stacks.PicardUFD.away_intersection` for arbitrary models of the three localizations, with
the two comparison maps given as algebra maps. -/
theorem localization_intersection
    {R S T A : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] [Algebra R A]
    (f g : R) [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) A]
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hdisj : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f,
      p ∉ UniqueFactorizationMonoid.normalizedFactors g)
    (φ : S →ₐ[R] A) (ψ : T →ₐ[R] A) (x : S) (y : T) (hxy : φ x = ψ y) :
    ∃ a : R, algebraMap R S a = x ∧ algebraMap R T a = y := by
  let ef := IsLocalization.algEquiv (Submonoid.powers f) S (Localization.Away f)
  let eg := IsLocalization.algEquiv (Submonoid.powers g) T (Localization.Away g)
  let ea := IsLocalization.algEquiv (Submonoid.powers (f * g)) A (Localization.Away (f * g))
  have heφ := awayLift_eq_comp_algEquiv f (f * g) (isUnit_away_mul_left f g) ef ea φ
  have heψ := awayLift_eq_comp_algEquiv g (f * g) (isUnit_away_mul_right f g) eg ea ψ
  obtain ⟨a, ha, hb⟩ := away_intersection f g hf hg hdisj (ef x) (eg y) (by
    rw [heφ, heψ]
    simpa using congrArg ea hxy)
  exact ⟨a, ef.injective (by simpa using ha), eg.injective (by simpa using hb)⟩

/-- `Stacks.PicardUFD.away_product_unit_splits` for arbitrary models of the three localizations,
with the two comparison maps given as algebra maps. -/
theorem localization_units_split
    {R S T A : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] [Algebra R A]
    (f g : R) [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) A] (hf : f ≠ 0) (hg : g ≠ 0)
    (φ : S →ₐ[R] A) (ψ : T →ₐ[R] A) (w : Aˣ) :
    ∃ (u : Sˣ) (v : Tˣ), φ (u : S) * ψ (v : T) = w := by
  let ef := IsLocalization.algEquiv (Submonoid.powers f) S (Localization.Away f)
  let eg := IsLocalization.algEquiv (Submonoid.powers g) T (Localization.Away g)
  let ea := IsLocalization.algEquiv (Submonoid.powers (f * g)) A (Localization.Away (f * g))
  have heφ := awayLift_eq_comp_algEquiv f (f * g) (isUnit_away_mul_left f g) ef ea φ
  have heψ := awayLift_eq_comp_algEquiv g (f * g) (isUnit_away_mul_right f g) eg ea ψ
  obtain ⟨u, v, huv⟩ := away_product_unit_splits hf hg
    (Units.map ea.toRingHom.toMonoidHom w)
  refine ⟨Units.map ef.symm.toRingHom.toMonoidHom u,
    Units.map eg.symm.toRingHom.toMonoidHom v, ea.injective ?_⟩
  change Localization.awayLift (algebraMap R (Localization.Away (f * g))) f
      (isUnit_away_mul_left f g) (u : _) *
    Localization.awayLift (algebraMap R (Localization.Away (f * g))) g
      (isUnit_away_mul_right f g) (v : _) = ea (w : A) at huv
  rw [heφ, heψ] at huv
  change ea (φ (ef.symm (u : Localization.Away f))) *
    ea (ψ (eg.symm (v : Localization.Away g))) = ea (w : A) at huv
  change ea (φ (ef.symm (u : Localization.Away f)) *
    ψ (eg.symm (v : Localization.Away g))) = ea (w : A)
  rw [map_mul]
  exact huv

/-! ### Sections of the structure sheaf of `Spec R` -/

/-- Sections of the structure sheaf over `D(f) ∪ D(g)` are exactly the elements of `R`, when `f`
and `g` have no common prime factor. -/
theorem algebraMap_bijective_two_basicOpens
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (hdisj : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f,
      p ∉ UniqueFactorizationMonoid.normalizedFactors g) :
    Function.Bijective (algebraMap R ((Spec.structureSheaf R).obj.obj
      (.op (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g)))) := by
  let O := (Spec.structureSheaf R).obj
  let U := PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g
  let i : PrimeSpectrum.basicOpen f ⟶ U := homOfLE le_sup_left
  let j : PrimeSpectrum.basicOpen g ⟶ U := homOfLE le_sup_right
  let k : PrimeSpectrum.basicOpen (f * g) ⟶ PrimeSpectrum.basicOpen f :=
    homOfLE (by rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left)
  let l : PrimeSpectrum.basicOpen (f * g) ⟶ PrimeSpectrum.basicOpen g :=
    homOfLE (by rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_right)
  let φ : O.obj (.op (PrimeSpectrum.basicOpen f)) →ₐ[R]
      O.obj (.op (PrimeSpectrum.basicOpen (f * g))) :=
    { __ := (O.map k.op).hom, commutes' := fun _ => rfl }
  let ψ : O.obj (.op (PrimeSpectrum.basicOpen g)) →ₐ[R]
      O.obj (.op (PrimeSpectrum.basicOpen (f * g))) :=
    { __ := (O.map l.op).hom, commutes' := fun _ => rfl }
  constructor
  · exact fun a b hab =>
      injective_algebraMap_away (S := O.obj (.op (PrimeSpectrum.basicOpen f))) hf
        (congrArg (O.map i.op) hab)
  · intro s
    have hs : φ (O.map i.op s) = ψ (O.map j.op s) := by
      change (O.map i.op ≫ O.map k.op) s = (O.map j.op ≫ O.map l.op) s
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    obtain ⟨a, ha, hb⟩ := localization_intersection f g hf hg hdisj φ ψ
      (O.map i.op s) (O.map j.op s) hs
    exact ⟨a, (Spec.structureSheaf R).eq_of_locally_eq₂ i j le_rfl _ _ ha hb⟩

/-- The canonical injection of the sections of the structure sheaf over a nonempty principal open
into the fraction field. -/
noncomputable def awayToFractionRing
    {R K S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (h : R) (hh : h ≠ 0) [IsLocalization.Away h S] : S →ₐ[R] K :=
  { __ := IsLocalization.lift (M := Submonoid.powers h) (S := S)
      (g := algebraMap R K) (fun y => by
        apply isUnit_iff_ne_zero.mpr
        rw [← map_zero (algebraMap R K)]
        apply (IsFractionRing.injective R K).ne
        obtain ⟨n, hn⟩ := y.property
        simpa [← hn] using pow_ne_zero n hh)
    commutes' := by intro r; simp }

/-- `Stacks.PicardUFD.awayToFractionRing` is injective. -/
theorem awayToFractionRing_injective
    {R K S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (h : R) (hh : h ≠ 0) [IsLocalization.Away h S] :
    Function.Injective (awayToFractionRing (S := S) (K := K) h hh) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  exact fun x y => (injective_algebraMap_away hh).eq_iff.trans
    (IsFractionRing.injective R K).eq_iff.symm

/-- `Stacks.PicardUFD.awayToFractionRing` commutes with every `R`-algebra map between two
localizations at nonzero elements. -/
theorem awayToFractionRing_comp
    {R K S T : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T] [Field K] [Algebra R K] [IsFractionRing R K]
    (h k : R) (hh : h ≠ 0) (hk : k ≠ 0)
    [IsLocalization.Away h S] [IsLocalization.Away k T] (φ : S →ₐ[R] T) (s : S) :
    awayToFractionRing k hk (φ s) = awayToFractionRing (K := K) h hh s := by
  have he : ((awayToFractionRing (K := K) k hk).comp φ).toRingHom =
      (awayToFractionRing (S := S) (K := K) h hh).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    ext r
    simp
  exact DFunLike.congr_fun he s

/-- The denominator of a fraction divides every element of the base ring which makes it
integral. -/
theorem den_dvd_of_integral_multiple
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K] (z : K) (a b : R)
    (h : z * algebraMap R K b = algebraMap R K a) :
    (IsFractionRing.den R z : R) ∣ b := by
  have hd : z * algebraMap R K (IsFractionRing.den R z) =
      algebraMap R K (IsFractionRing.num R z) :=
    IsFractionRing.num_mul_den_eq_num_iff_eq.mpr rfl
  have he : IsFractionRing.num R z * b = a * (IsFractionRing.den R z : R) := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ← hd, ← h]
    ring
  apply (IsFractionRing.num_den_reduced R z).symm.dvd_of_dvd_mul_left
  rw [he]
  exact dvd_mul_left _ _

/-- A fraction regular after inverting either of `h * f` and `h * g`, where every prime factor of
`f` which divides `g` already divides `h`, is regular after inverting `h`. -/
theorem fraction_mem_away_of_common_factors
    {R K : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    (f g h : R) (hf : f ≠ 0) (hh : h ≠ 0)
    (hfg : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f, p ∣ g → p ∣ h)
    (z : K)
    (hzf : ∃ a : R, ∃ m : ℕ, z * algebraMap R K ((h * f) ^ m) = algebraMap R K a)
    (hzg : ∃ a : R, ∃ m : ℕ, z * algebraMap R K ((h * g) ^ m) = algebraMap R K a)
    (θ : Localization.Away h →ₐ[R] K) :
    ∃ c : Localization.Away h, θ c = z := by
  have hd0 : (IsFractionRing.den R z : R) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R z).property
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (IsFractionRing.den R z : R),
      p ∈ UniqueFactorizationMonoid.normalizedFactors h := by
    intro p hp
    have hpp := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    have hpd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
    obtain ⟨a, m, ham⟩ := hzf
    obtain ⟨b, n, hbn⟩ := hzg
    have hpf := hpp.dvd_of_dvd_pow (hpd.trans (den_dvd_of_integral_multiple z a _ ham))
    have hpg := hpp.dvd_of_dvd_pow (hpd.trans (den_dvd_of_integral_multiple z b _ hbn))
    have hph : p ∣ h := by
      rcases hpp.dvd_or_dvd hpf with hph | hpf
      · exact hph
      rcases hpp.dvd_or_dvd hpg with hph | hpg
      · exact hph
      apply hfg p _ hpg
      exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hf).mpr
        ⟨hpp.irreducible, UniqueFactorizationMonoid.normalize_normalized_factor p hp, hpf⟩
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hh).mpr
      ⟨hpp.irreducible, UniqueFactorizationMonoid.normalize_normalized_factor p hp, hph⟩
  have hd := isUnit_away_of_normalizedFactors_subset hd0 hfac
  refine ⟨algebraMap R (Localization.Away h) (IsFractionRing.num R z) * (hd.unit⁻¹ : _), ?_⟩
  apply (IsFractionRing.num_mul_den_eq_num_iff_eq (A := R)).mp
  have hdθ : θ (hd.unit : Localization.Away h) =
      algebraMap R K (IsFractionRing.den R z) := by
    rw [hd.unit_spec, θ.commutes]
  rw [map_mul, θ.commutes, ← hdθ, mul_assoc, ← map_mul]
  simp

/-- Restriction of sections of the structure sheaf between two principal opens is compatible with
the injections into the fraction field. -/
theorem awayToFractionRing_restriction
    (R : CommRingCat.{u}) [IsDomain R] (h k : R) (hh : h ≠ 0) (hk : k ≠ 0)
    (i : PrimeSpectrum.basicOpen k ⟶ PrimeSpectrum.basicOpen h)
    (s : ((Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen h)))) :
    awayToFractionRing
        (S := (Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen k)))
        (K := FractionRing R) k hk ((Spec.structureSheaf R).obj.map i.op s) =
      awayToFractionRing
        (S := (Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen h)))
        (K := FractionRing R) h hh s :=
  awayToFractionRing_comp
    (S := (Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen h)))
    (T := (Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen k))) h k hh hk
    { __ := ((Spec.structureSheaf R).obj.map i.op).hom, commutes' := fun _ => rfl } s

/-- Restriction of sections of the structure sheaf from `D(h)` to
`D(h) ∩ (D(f) ∪ D(g))` is bijective, provided every prime factor of `f` which divides `g`
divides `h`. This is the statement that a function on the two-open cover extends uniquely across
the points of `D(h)` outside it. -/
theorem restriction_bijective_two_basicOpens
    (R : CommRingCat.{u}) [IsDomain R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
    (f g h : R) (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hfg : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f, p ∣ g → p ∣ h) :
    Function.Bijective ((Spec.structureSheaf R).obj.map
      (homOfLE inf_le_left : PrimeSpectrum.basicOpen h ⊓
        (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g) ⟶
          PrimeSpectrum.basicOpen h).op) := by
  let O := (Spec.structureSheaf R).obj
  let P := PrimeSpectrum.basicOpen h ⊓ (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g)
  let A := PrimeSpectrum.basicOpen (h * f)
  let B := PrimeSpectrum.basicOpen (h * g)
  let C := PrimeSpectrum.basicOpen ((h * f) * (h * g))
  let iA : A ⟶ P := homOfLE (by
    dsimp [A, P]; rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_inf_left _ le_sup_left)
  let iB : B ⟶ P := homOfLE (by
    dsimp [B, P]; rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_inf_left _ le_sup_right)
  let jA : C ⟶ A := homOfLE (PrimeSpectrum.basicOpen_mul_le_left _ _)
  let jB : C ⟶ B := homOfLE (PrimeSpectrum.basicOpen_mul_le_right _ _)
  let kA : A ⟶ PrimeSpectrum.basicOpen h := homOfLE (PrimeSpectrum.basicOpen_mul_le_left _ _)
  let kB : B ⟶ PrimeSpectrum.basicOpen h := homOfLE (PrimeSpectrum.basicOpen_mul_le_left _ _)
  have hA := mul_ne_zero hh hf
  have hB := mul_ne_zero hh hg
  have hC := mul_ne_zero hA hB
  let θA := awayToFractionRing (S := O.obj (.op A)) (K := FractionRing R) (h * f) hA
  let θB := awayToFractionRing (S := O.obj (.op B)) (K := FractionRing R) (h * g) hB
  let θh := awayToFractionRing (S := O.obj (.op (PrimeSpectrum.basicOpen h)))
    (K := FractionRing R) h hh
  have hres : ∀ {Q : Opens (PrimeSpectrum R)} (i : Q ⟶ P) (k : Q ⟶ PrimeSpectrum.basicOpen h)
      (s : O.obj (.op (PrimeSpectrum.basicOpen h))),
      O.map i.op (O.map (homOfLE inf_le_left : P ⟶ PrimeSpectrum.basicOpen h).op s) =
        O.map k.op s := fun i k s => by
    change (O.map (homOfLE inf_le_left : P ⟶ PrimeSpectrum.basicOpen h).op ≫ O.map i.op) s = _
    rw [← Functor.map_comp]
    rfl
  constructor
  · intro a b hab
    apply awayToFractionRing_injective
      (S := O.obj (.op (PrimeSpectrum.basicOpen h))) (K := FractionRing R) h hh
    rw [← awayToFractionRing_restriction R h (h * f) hh hA kA a,
      ← awayToFractionRing_restriction R h (h * f) hh hA kA b]
    congr 1
    rw [← hres iA kA a, ← hres iA kA b, hab]
  · intro s
    let x := O.map iA.op s
    let y := O.map iB.op s
    have hxy : θA x = θB y := by
      rw [← awayToFractionRing_restriction R _ _ hA hC jA x,
        ← awayToFractionRing_restriction R _ _ hB hC jB y]
      congr 1
    have hx (k : R) (A' : Type u) [CommRing A'] [Algebra R A']
        [IsLocalization.Away k A'] (θ : A' →ₐ[R] FractionRing R) (a : A') :
        ∃ b : R, ∃ n : ℕ, θ a * algebraMap R (FractionRing R) (k ^ n) =
          algebraMap R (FractionRing R) b :=
      ⟨(IsLocalization.Away.sec k a).1, (IsLocalization.Away.sec k a).2, by
        simpa using congrArg θ (IsLocalization.Away.sec_spec k a)⟩
    obtain ⟨c, hc⟩ := fraction_mem_away_of_common_factors f g h hf hh hfg (θA x)
      (hx _ _ θA x) (hxy ▸ hx _ _ θB y) (awayToFractionRing h hh)
    let e := IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h)
      (O.obj (.op (PrimeSpectrum.basicOpen h)))
    have hch : θh (e c) = θA x :=
      (awayToFractionRing_comp h h hh hh e.toAlgHom c).trans hc
    refine ⟨e c, ?_⟩
    apply (Spec R).sheaf.eq_of_locally_eq₂ iA iB
      (by dsimp [P, A, B]; simp only [PrimeSpectrum.basicOpen_mul, inf_sup_left]; exact le_rfl)
    · have he : O.map kA.op (e c) = x := by
        apply awayToFractionRing_injective
          (S := O.obj (.op (PrimeSpectrum.basicOpen (h * f)))) (K := FractionRing R) (h * f) hA
        rw [awayToFractionRing_restriction R h (h * f) hh hA kA]
        exact hch
      exact (hres iA kA _).trans he
    · have he : O.map kB.op (e c) = y := by
        apply awayToFractionRing_injective
          (S := O.obj (.op (PrimeSpectrum.basicOpen (h * g)))) (K := FractionRing R) (h * g) hB
        rw [awayToFractionRing_restriction R h (h * g) hh hB kB]
        exact hch.trans hxy
      exact (hres iB kB _).trans he

/-- Bijectivity of restriction from an open `V` of a scheme to its intersection with a fixed open
`W` may be checked on a basis of opens. -/
theorem functions_bijective_of_basis
    {X : Scheme.{u}} (W : X.Opens) {ι : Type*} (B : ι → X.Opens)
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, Function.Bijective
      (X.presheaf.map (homOfLE (W.ι.image_preimage_le (B i))).op)) :
    ∀ V : X.Opens, Function.Bijective
      (X.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op) := by
  let E : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let η := (Scheme.Modules.restrictAdjunction W.ι).unit.app E
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨E.presheaf, E.isSheaf⟩
  let G : TopCat.Sheaf AddCommGrpCat X :=
    ⟨((Scheme.Modules.pushforward W.ι).obj (E.restrict W.ι)).presheaf,
      ((Scheme.Modules.pushforward W.ι).obj (E.restrict W.ι)).isSheaf⟩
  let ψ : F ⟶ G := ⟨η.mapPresheaf⟩
  have hp : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB (fun i => by
    change IsIso (η.app (B i))
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (h i))
  have he : IsIso η := (isIso_iff_of_reflects_iso η (Scheme.Modules.toPresheaf X)).mp
    (inferInstanceAs (IsIso ((TopCat.Sheaf.forget _ _).map ψ)))
  intro V
  have hi : IsIso (η.app V) := inferInstance
  rw [Scheme.Modules.restrictAdjunction_unit_app_app] at hi
  exact (ConcreteCategory.isIso_iff_bijective
    (E.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op)).mp hi

/-- On an open `U` of `Spec R` containing `D(f) ∪ D(g)`, with every prime factor shared by `f`
and `g` vanishing identically on `U`, every function on `V ∩ (D(f) ∪ D(g))` extends uniquely to
`V`, for every open `V` of `U`: the structure sheaf of `U` is the pushforward of its
restriction to the two-open cover. -/
theorem functions_bijective_open_two_basicOpens
    (R : CommRingCat.{u}) [IsDomain R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
    (f g : R) (hf : f ≠ 0) (hg : g ≠ 0) (U : (Spec R).Opens)
    (hfU : PrimeSpectrum.basicOpen f ≤ U) (hgU : PrimeSpectrum.basicOpen g ≤ U)
    (hfg : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f, p ∣ g →
      U ≤ PrimeSpectrum.basicOpen p) :
    let W : U.toScheme.Opens := U.ι ⁻¹ᵁ (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g)
    ∀ V : U.toScheme.Opens, Function.Bijective
      (U.toScheme.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op) := by
  let P : (Spec R).Opens := PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ P
  let B : {h : R // PrimeSpectrum.basicOpen h ≤ U} → U.toScheme.Opens :=
    fun h => U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen h.val
  have hBasis : Opens.IsBasis (Set.range B) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro V x hx
    have hx' : x.val ∈ U.ι ''ᵁ V := (U.mem_ι_image_iff).mpr hx
    obtain ⟨T, ⟨h, rfl⟩, hxh, hT⟩ :=
      Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hx'
    let hU : PrimeSpectrum.basicOpen h ≤ U := hT.trans (U.ι_image_le V)
    refine ⟨B ⟨h, hU⟩, ⟨⟨h, hU⟩, rfl⟩, hxh, ?_⟩
    have ht := U.ι.preimage_mono hT
    simpa [B] using ht
  apply functions_bijective_of_basis W B hBasis
  intro i
  have hBi : U.ι ''ᵁ B i = PrimeSpectrum.basicOpen i.val :=
    (U.ι.image_preimage_eq_opensRange_inf (PrimeSpectrum.basicOpen i.val)).trans
      (by simp only [Scheme.Opens.opensRange_ι]; exact inf_eq_right.mpr i.property)
  have hW : U.ι ''ᵁ W = P :=
    (U.ι.image_preimage_eq_opensRange_inf P).trans
      (by simp only [Scheme.Opens.opensRange_ι]; exact inf_eq_right.mpr (sup_le hfU hgU))
  have hI : U.ι ''ᵁ (W.ι ''ᵁ W.ι ⁻¹ᵁ B i) = PrimeSpectrum.basicOpen i.val ⊓ P := by
    have h1 : W.ι ''ᵁ W.ι ⁻¹ᵁ B i = W ⊓ B i :=
      (W.ι.image_preimage_eq_opensRange_inf (B i)).trans
        (by simp only [Scheme.Opens.opensRange_ι])
    have he : U.ι ''ᵁ (W ⊓ B i) = (U.ι ''ᵁ W) ⊓ (U.ι ''ᵁ B i) :=
      Opens.ext (Set.image_inter U.ι.isOpenEmbedding.injective)
    rw [h1, he, hBi, hW]
    exact inf_comm _ _
  have hl : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f, p ∣ g → p ∣ i.val := by
    intro p hp hpg
    have hpp := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    have hprime := (Ideal.span_singleton_prime hpp.ne_zero).mpr hpp
    have hm := (PrimeSpectrum.basicOpen_le_basicOpen_iff i.val p).mp
      (i.property.trans (hfg p hp hpg))
    rw [hprime.radical] at hm
    exact Ideal.mem_span_singleton.mp hm
  have hb : Function.Bijective ((Spec.structureSheaf R).obj.map
      (homOfLE inf_le_left :
        PrimeSpectrum.basicOpen i.val ⊓ P ⟶ PrimeSpectrum.basicOpen i.val).op) := by
    by_cases hh : i.val = 0
    · have he : PrimeSpectrum.basicOpen i.val ⊓ P = PrimeSpectrum.basicOpen i.val := by
        rw [hh, PrimeSpectrum.basicOpen_zero]
        exact bot_inf_eq _
      have hi : (homOfLE inf_le_left : PrimeSpectrum.basicOpen i.val ⊓ P ⟶
          PrimeSpectrum.basicOpen i.val) = eqToHom he := Subsingleton.elim _ _
      rw [hi]
      exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    · exact restriction_bijective_two_basicOpens R f g i.val hf hg hh hl
  have H (A D : (Spec R).Opens) (hAD : A ≤ D)
      (hA : A = PrimeSpectrum.basicOpen i.val ⊓ P) (hD : D = PrimeSpectrum.basicOpen i.val) :
      Function.Bijective ((Spec.structureSheaf R).obj.map (homOfLE hAD).op) := by
    subst A D
    exact hb
  exact H _ _ _ hI hBi

/-! ### The prime-avoidance choice of the pair -/

/-- Given a nonzero element `f` of an ideal `I` of a UFD, there is a nonzero `g ∈ I` such that
every prime factor of `f` dividing `g` generates an ideal containing `I`. This is the prime
avoidance step: the common prime factors of `f` and `g` cut out closed sets containing the zero
locus of `I`. -/
theorem exists_pair_mem_ideal_common_factors
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] (I : Ideal R) (f : R) (hf : f ∈ I) (hf0 : f ≠ 0) :
    ∃ g ∈ I, g ≠ 0 ∧ ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f,
      p ∣ g → I ≤ Ideal.span {p} := by
  classical
  let S : Finset R := insert 0 ((UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter
    (fun p => ¬ I ≤ Ideal.span {p}))
  have hprime : ∀ p ∈ S, (Ideal.span {p}).IsPrime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa using (Ideal.isPrime_bot : (⊥ : Ideal R).IsPrime)
    · have hp' := (Finset.mem_filter.mp hp).1
      have hpp := UniqueFactorizationMonoid.prime_of_normalized_factor p
        (Multiset.mem_toFinset.mp hp')
      exact (Ideal.span_singleton_prime hpp.ne_zero).mpr hpp
  have hnot : ∀ p ∈ S, ¬ I ≤ Ideal.span {p} := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact fun h => hf0 (by simpa using h hf)
    · exact (Finset.mem_filter.mp hp).2
  have havoid : ¬ (I : Set R) ⊆ ⋃ p ∈ (S : Set R), (Ideal.span {p} : Set R) := by
    intro h
    obtain ⟨p, hp, hI⟩ := (Ideal.subset_union_prime (s := S)
      (f := fun p => Ideal.span {p}) (0 : R) 0 (fun p hp _ _ => hprime p hp)).mp h
    exact hnot p hp hI
  obtain ⟨g, hg, hgn⟩ := Set.not_subset.mp havoid
  have hgn' : ∀ p ∈ S, g ∉ Ideal.span {p} := by
    simpa only [Set.mem_iUnion, Finset.mem_coe, SetLike.mem_coe, not_exists] using hgn
  refine ⟨g, hg, ?_, ?_⟩
  · intro hg0
    exact hgn' 0 (Finset.mem_insert_self _ _) (by simp [hg0])
  · intro p hp hpg
    by_contra h
    exact hgn' p (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hp, h⟩)) (Ideal.mem_span_singleton.mpr hpg)

/-- Every nonempty open of the spectrum of a UFD contains the union of two principal opens
`D(f) ∪ D(g)` for nonzero `f` and `g` whose common prime factors vanish identically on it. This
is the opening move of Stacks Tag 0BDA. -/
theorem exists_two_basicOpens_common_factors
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] (U : Opens (PrimeSpectrum R)) (hU : Nonempty U) :
    ∃ f g : R, f ≠ 0 ∧ g ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ U ∧
      PrimeSpectrum.basicOpen g ≤ U ∧
      ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors f, p ∣ g →
        U ≤ PrimeSpectrum.basicOpen p := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp U.isOpen.isClosed_compl
  obtain ⟨x⟩ := hU
  have hx : ¬ I ≤ x.val.asIdeal := by
    intro h
    have hx' : x.val ∈ PrimeSpectrum.zeroLocus (I : Set R) := h
    rw [← hI] at hx'
    exact hx' x.property
  obtain ⟨f, hf, hfx⟩ := Set.not_subset.mp hx
  have hf0 : f ≠ 0 := fun h => hfx (h.symm ▸ x.val.asIdeal.zero_mem)
  have hbasic : ∀ a ∈ I, PrimeSpectrum.basicOpen a ≤ U := by
    intro a ha y hy
    by_contra hyU
    have hyI : y ∈ PrimeSpectrum.zeroLocus (I : Set R) := by rwa [← hI]
    exact hy (hyI ha)
  obtain ⟨g, hg, hg0, hfg⟩ := exists_pair_mem_ideal_common_factors I f hf hf0
  refine ⟨f, g, hf0, hg0, hbasic f hf, hbasic g hg, ?_⟩
  intro p hp hpg x hxU hpx
  have hxI : x ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun a ha =>
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpx) (hfg p hp hpg ha)
  rw [← hI] at hxI
  exact hxI hxU

end Stacks.PicardUFD
