module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import StacksFrontier.RingTheory.Spectrum.Prime.BijectiveOfBijectiveComap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The spectrum of a quotient as the set of primes above an ideal

`Spec (R ⧸ I)` is the closed subset `V(I)` of `Spec R`: contraction along the quotient map
identifies the primes of `R ⧸ I` with the primes of `R` containing `I`. This file records that
identification as an `Equiv`, checks that it is natural for a ring map carrying `I` into `I'`, and
uses the naturality to rewrite the spectral hypothesis of
`RingHom.bijective_of_bijective_comap_of_forall_exists_sub_mem` as a statement about the primes of
the two *ambient* rings.

Also recorded is the elementary fact that makes a fibre into a `V(·)`: over a *maximal* ideal `m`
of `A`, a prime `q` of an `A`-algebra `A'` contracts to `m` exactly when it contains the extension
`m A'`, since the contraction of a prime is a proper ideal containing `m` and `m` is maximal. So
the set-theoretic fibre of `Spec A' → Spec A` over a closed point is `V(m A') = V(√(m A'))`, which
is `Spec (A' ⧸ √(m A'))`, the spectrum of a quotient by a *radical* ideal.

## Main definitions

* `PrimeSpectrum.quotientEquivSubtype`: `Spec (A ⧸ I) ≃ {p : Spec A // I ≤ p}`.
* `PrimeSpectrum.comapRestrict`: contraction along a ring map, restricted to the primes above a
  pair of compatible ideals.

## Main results

* `PrimeSpectrum.bijective_comap_quotientMap_iff`: the spectral map of `A ⧸ I → A' ⧸ I'` is
  bijective exactly when `comapRestrict` is.
* `RingHom.bijective_quotientMap_of_bijective_comapRestrict`: the recognition criterion of
  `StacksFrontier.RingTheory.Spectrum.Prime.BijectiveOfBijectiveComap` with all four of its
  hypotheses phrased in the ambient rings.
* `Ideal.map_le_iff_comap_eq_of_isMaximal` and `PrimeSpectrum.comap_eq_iff_radical_map_le`: the
  fibre over a closed point is the zero locus of the extended maximal ideal, and of its radical.
-/

@[expose] public section

/-- **A prime of `A'` contracts to a maximal ideal `m` of `A` exactly when it contains the
extension `m A'`.** -/
theorem Ideal.map_le_iff_comap_eq_of_isMaximal {A A' : Type*} [CommRing A] [CommRing A']
    (ψ : A →+* A') {m : Ideal A} (hm : m.IsMaximal) (q : Ideal A') [q.IsPrime] :
    m.map ψ ≤ q ↔ q.comap ψ = m := by
  rw [Ideal.map_le_iff_le_comap]
  refine ⟨fun h => (hm.eq_of_le ?_ h).symm, fun h => h.ge⟩
  exact fun htop => (‹q.IsPrime›).ne_top (by simpa [Ideal.comap_eq_top_iff] using htop)

namespace PrimeSpectrum

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- **The primes of `A ⧸ I` are the primes of `A` containing `I`.** Contraction along the quotient
map is a bijection onto them, with inverse the extension of ideals. -/
def quotientEquivSubtype (I : Ideal A) :
    PrimeSpectrum (A ⧸ I) ≃ {p : PrimeSpectrum A // I ≤ p.asIdeal} where
  toFun q := ⟨comap (Ideal.Quotient.mk I) q, fun x hx => by
    change Ideal.Quotient.mk I x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.asIdeal.zero_mem⟩
  invFun p := ⟨p.1.asIdeal.map (Ideal.Quotient.mk I),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact p.2)⟩
  left_inv q := PrimeSpectrum.ext
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.asIdeal)
  right_inv p := Subtype.ext (PrimeSpectrum.ext (by
    rw [comap_asIdeal, Ideal.comap_map_quotientMk]
    exact sup_eq_right.mpr p.2))

/-- The prime of `A` underlying `quotientEquivSubtype I q` is the contraction of `q` along the
quotient map. -/
@[simp]
theorem quotientEquivSubtype_apply_coe (I : Ideal A) (q : PrimeSpectrum (A ⧸ I)) :
    ((quotientEquivSubtype I q : {p : PrimeSpectrum A // I ≤ p.asIdeal}) :
      PrimeSpectrum A) = comap (Ideal.Quotient.mk I) q :=
  rfl

/-- **Contraction along `φ`, restricted to the primes above `I'` and `I`.** -/
def comapRestrict (φ : A →+* A') {I : Ideal A} {I' : Ideal A'} (hI : I ≤ I'.comap φ) :
    {q : PrimeSpectrum A' // I' ≤ q.asIdeal} → {p : PrimeSpectrum A // I ≤ p.asIdeal} :=
  fun q => ⟨comap φ q.1, hI.trans (Ideal.comap_mono q.2)⟩

/-- The prime of `A` underlying `comapRestrict φ hI q` is the contraction of `q` along `φ`. -/
@[simp]
theorem comapRestrict_coe (φ : A →+* A') {I : Ideal A} {I' : Ideal A'} (hI : I ≤ I'.comap φ)
    (q : {q : PrimeSpectrum A' // I' ≤ q.asIdeal}) :
    ((comapRestrict φ hI q : {p : PrimeSpectrum A // I ≤ p.asIdeal}) : PrimeSpectrum A) =
      comap φ q.1 :=
  rfl

/-- **The identification of the spectra of the quotients with the zero loci is natural**: the
spectral map of `A ⧸ I → A' ⧸ I'` is contraction along `φ` restricted to the two zero loci. -/
theorem quotientEquivSubtype_comap_quotientMap (φ : A →+* A') {I : Ideal A} {I' : Ideal A'}
    (hI : I ≤ I'.comap φ) (q : PrimeSpectrum (A' ⧸ I')) :
    quotientEquivSubtype I (comap (Ideal.quotientMap I' φ hI) q) =
      comapRestrict φ hI (quotientEquivSubtype I' q) := by
  refine Subtype.ext (PrimeSpectrum.ext ?_)
  change Ideal.comap (Ideal.Quotient.mk I) (Ideal.comap (Ideal.quotientMap I' φ hI) q.asIdeal) =
    Ideal.comap φ (Ideal.comap (Ideal.Quotient.mk I') q.asIdeal)
  rw [Ideal.comap_comap, Ideal.comap_comap, Ideal.quotientMap_comp_mk]

/-- **The spectral map of `A ⧸ I → A' ⧸ I'` is bijective exactly when contraction along `φ` is a
bijection from the primes above `I'` to the primes above `I`.** -/
theorem bijective_comap_quotientMap_iff (φ : A →+* A') {I : Ideal A} {I' : Ideal A'}
    (hI : I ≤ I'.comap φ) :
    Function.Bijective (comap (Ideal.quotientMap I' φ hI)) ↔
      Function.Bijective (comapRestrict φ hI) := by
  have hcomm : comapRestrict φ hI =
      (quotientEquivSubtype I) ∘ (comap (Ideal.quotientMap I' φ hI)) ∘
        (quotientEquivSubtype I').symm := by
    refine funext fun q => ?_
    simp only [Function.comp_apply]
    rw [quotientEquivSubtype_comap_quotientMap φ hI, Equiv.apply_symm_apply]
  rw [hcomm, Equiv.comp_bijective, Equiv.bijective_comp]

/-- **The fibre of `Spec A' → Spec A` over a closed point `m` is the zero locus of the radical of
the extended ideal `m A'`.** -/
@[ega "I 1.2.2" "special case"]
theorem comap_eq_iff_radical_map_le (ψ : A →+* A') {p : PrimeSpectrum A}
    (hp : p.asIdeal.IsMaximal) (q : PrimeSpectrum A') :
    comap ψ q = p ↔ (p.asIdeal.map ψ).radical ≤ q.asIdeal := by
  rw [PrimeSpectrum.ext_iff, comap_asIdeal, q.isPrime.radical_le_iff]
  exact (Ideal.map_le_iff_comap_eq_of_isMaximal ψ hp q.asIdeal).symm

end PrimeSpectrum

namespace RingHom

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- A prime of `A ⧸ I` is maximal as soon as its contraction to `A` is. -/
theorem isMaximal_of_isMaximal_comap_quotientMk {I : Ideal A} (q : PrimeSpectrum (A ⧸ I))
    (h : (Ideal.comap (Ideal.Quotient.mk I) q.asIdeal).IsMaximal) : q.asIdeal.IsMaximal := by
  have hmap : Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) q.asIdeal) =
      q.asIdeal :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.asIdeal
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective h with htop | hmax
  · exact absurd (hmap.symm.trans htop) q.isPrime.ne_top
  · exact hmap ▸ hmax

/-- **The recognition criterion of
`RingHom.bijective_of_bijective_comap_of_forall_exists_sub_mem`, phrased in the ambient rings.**

Let `φ : A → A'` be a ring map and let `I ⊆ A`, `I' ⊆ A'` be radical ideals with `I A' ⊆ I'`. If
the primes of `A` above `I` are finitely many maximal ideals, contraction along `φ` is a bijection
from the primes above `I'` to the primes above `I`, and every element of `A'` agrees with an
element of the image of `φ` modulo each prime above `I'`, then `A ⧸ I → A' ⧸ I'` is bijective.

Geometrically: `V(I') → V(I)` is a bijection of finite sets of closed points inducing surjections
on residue fields, and the two closed subschemes are reduced, so the map between them is an
isomorphism. -/
theorem bijective_quotientMap_of_bijective_comapRestrict (φ : A →+* A') {I : Ideal A}
    {I' : Ideal A'} (hI : I ≤ I'.comap φ) (hIrad : I.IsRadical) (hI'rad : I'.IsRadical)
    (hfin : _root_.Finite {p : PrimeSpectrum A // I ≤ p.asIdeal})
    (hmax : ∀ p : PrimeSpectrum A, I ≤ p.asIdeal → p.asIdeal.IsMaximal)
    (hfib : Function.Bijective (PrimeSpectrum.comapRestrict φ hI))
    (hsub : ∀ q : PrimeSpectrum A', I' ≤ q.asIdeal → ∀ y : A', ∃ x : A, y - φ x ∈ q.asIdeal) :
    Function.Bijective (Ideal.quotientMap I' φ hI) := by
  have _ : IsReduced (A ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hIrad
  have _ : IsReduced (A' ⧸ I') := (Ideal.isRadical_iff_quotient_reduced I').mp hI'rad
  have _ : _root_.Finite (PrimeSpectrum (A ⧸ I)) :=
    @Finite.of_equiv _ _ hfin (PrimeSpectrum.quotientEquivSubtype I).symm
  refine bijective_of_bijective_comap_of_forall_exists_sub_mem _ (fun p => ?_)
    ((PrimeSpectrum.bijective_comap_quotientMap_iff φ hI).mpr hfib) (fun q y => ?_)
  · exact isMaximal_of_isMaximal_comap_quotientMk p
      (hmax _ (PrimeSpectrum.quotientEquivSubtype I p).2)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hsub _ (PrimeSpectrum.quotientEquivSubtype I' q).2 a
    refine ⟨Ideal.Quotient.mk I x, ?_⟩
    rw [Ideal.quotientMap_mk, ← map_sub]
    exact hx

end RingHom

end
