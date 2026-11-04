module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Recognising a bijective ring map from its spectrum and its residue rings

A ring map `f : R →+* S` between *reduced* rings whose spectra are *finite sets of maximal
ideals* is bijective as soon as it is bijective on spectra and surjective onto every residue
ring `S ⧸ q`. In other words, for such rings the pair (the map of spectra, the induced maps of
residue fields) determines the ring map, and recognises it as an isomorphism.

Both reducedness hypotheses are used, and they are used for opposite halves of the conclusion:
reducedness of `R` makes `f` injective, because the kernel of `f` is contained in every prime of
`R` as soon as every prime of `R` is the contraction of a prime of `S`; reducedness of `S` makes
`f` surjective, because an element of `S` can be matched modulo each prime of `S` separately —
the Chinese remainder theorem applies to the contracted ideals, which are pairwise comaximal
because they are distinct maximal ideals — and the resulting error lies in every prime of `S`.

## Main results

* `RingHom.injective_of_surjective_comap`: **injectivity**, from reducedness of the source and
  surjectivity on spectra alone.
* `RingHom.surjective_of_bijective_comap_of_forall_exists_sub_mem`: **surjectivity.**
* `RingHom.bijective_of_bijective_comap_of_forall_exists_sub_mem`: **the two together.**
* `RingHom.bijective_of_bijective_comap_of_forall_surjective_quotientMap`: the same, with the
  hypothesis on residue rings phrased as surjectivity of the induced maps
  `R ⧸ f⁻¹ q → S ⧸ q`, which is how an isomorphism of residue fields supplies it.

## Implementation notes

Surjectivity needs less than "both spectra are finite sets of maximal ideals": only the primes
of `R` are required to be maximal, and only `Spec R` is required to be finite. Both transfer to
`S` through the bijection of spectra where they are needed, and maximality of the primes of `S`
is not used at all. Likewise only *surjectivity* of the maps of residue rings is used, not
bijectivity: injectivity is automatic, since `R ⧸ f⁻¹ q` is then a field.

The hypothesis on residue rings is taken in the elementary form "every element of `S` agrees
with an element of the image modulo `q`", which is what the Chinese remainder step consumes;
`RingHom.exists_sub_mem_of_surjective_quotientMap` converts the quotient-map form into it.
-/

@[expose] public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An element of a reduced ring lying in every prime ideal is zero. -/
private theorem eq_zero_of_forall_mem_asIdeal [IsReduced R] {x : R}
    (h : ∀ p : PrimeSpectrum R, x ∈ p.asIdeal) : x = 0 :=
  IsReduced.eq_zero x <| mem_nilradical.mp <| by
    rw [PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
    exact h

/-- **A ring map out of a reduced ring which is surjective on spectra is injective.** Its kernel
is contained in every prime of `R`, because every prime of `R` is the contraction of a prime of
`S`, hence in the nilradical of `R`, which vanishes. -/
theorem injective_of_surjective_comap [IsReduced R] (f : R →+* S)
    (hcomap : Function.Surjective (PrimeSpectrum.comap f)) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_mem_asIdeal fun p => ?_
  obtain ⟨q, rfl⟩ := hcomap p
  simp [hx]

/-- The elementary form of surjectivity onto a residue ring: if `R ⧸ f⁻¹ q → S ⧸ q` is
surjective then every element of `S` agrees modulo `q` with an element of the image of `f`. -/
theorem exists_sub_mem_of_surjective_quotientMap (f : R →+* S) (q : PrimeSpectrum S)
    (hq : Function.Surjective (Ideal.quotientMap q.asIdeal f (le_refl (q.asIdeal.comap f))))
    (y : S) : ∃ x : R, y - f x ∈ q.asIdeal := by
  obtain ⟨z, hz⟩ := hq (Ideal.Quotient.mk q.asIdeal y)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.quotientMap_mk] at hz
  exact ⟨x, (Submodule.Quotient.eq q.asIdeal).mp hz.symm⟩

/-- **A ring map into a reduced ring is surjective** as soon as it is bijective on spectra, the
spectrum of the source is a finite set of maximal ideals, and every element of the target agrees
modulo each prime with an element of the image.

The contractions of the primes of `S` are pairwise distinct maximal ideals of `R`, hence
pairwise comaximal, so the Chinese remainder theorem produces a single element of `R` realising
the chosen local solutions simultaneously; its image differs from the given element by something
lying in every prime of `S`, that is, by a nilpotent, that is, by zero. -/
theorem surjective_of_bijective_comap_of_forall_exists_sub_mem [IsReduced S]
    [_root_.Finite (PrimeSpectrum R)] (f : R →+* S)
    (hmax : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal)
    (hcomap : Function.Bijective (PrimeSpectrum.comap f))
    (hres : ∀ (q : PrimeSpectrum S) (y : S), ∃ x : R, y - f x ∈ q.asIdeal) :
    Function.Surjective f := by
  classical
  have : _root_.Finite (PrimeSpectrum S) := .of_injective _ hcomap.injective
  intro y
  choose x hx using fun q : PrimeSpectrum S => hres q y
  obtain ⟨r, hr⟩ :=
    Ideal.exists_forall_sub_mem_ideal (I := fun q : PrimeSpectrum S => q.asIdeal.comap f)
      (fun q₁ q₂ hne => Ideal.isCoprime_iff_sup_eq.mpr
        ((hmax (PrimeSpectrum.comap f q₁)).coprime_of_ne (hmax (PrimeSpectrum.comap f q₂))
          fun h => hne (hcomap.injective (PrimeSpectrum.ext h)))) x
  refine ⟨r, ?_⟩
  refine (sub_eq_zero.mp (eq_zero_of_forall_mem_asIdeal fun q => ?_)).symm
  have h2 := Ideal.mem_comap.mp (hr q)
  rw [map_sub] at h2
  simpa using sub_mem (hx q) h2

/-- **A ring map between reduced rings whose spectra are finite sets of maximal ideals, which is
bijective on spectra and surjective modulo every prime, is bijective.** -/
theorem bijective_of_bijective_comap_of_forall_exists_sub_mem [IsReduced R] [IsReduced S]
    [_root_.Finite (PrimeSpectrum R)] (f : R →+* S)
    (hmax : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal)
    (hcomap : Function.Bijective (PrimeSpectrum.comap f))
    (hres : ∀ (q : PrimeSpectrum S) (y : S), ∃ x : R, y - f x ∈ q.asIdeal) :
    Function.Bijective f :=
  ⟨injective_of_surjective_comap f hcomap.surjective,
    surjective_of_bijective_comap_of_forall_exists_sub_mem f hmax hcomap hres⟩

/-- **A ring map between reduced rings whose spectra are finite sets of maximal ideals, which is
bijective on spectra and induces surjections on all residue rings, is bijective.**

This is the form in which the hypotheses arise geometrically: a bijection of the two finite sets
of closed points together with isomorphisms of the residue fields at corresponding points. The
residue field at a prime `q` is the fraction field of `S ⧸ q`, and `S ⧸ q` is already a field
here, so an isomorphism of residue fields is the same thing as a surjection `R ⧸ f⁻¹ q → S ⧸ q`,
which is what the hypothesis asks for. -/
theorem bijective_of_bijective_comap_of_forall_surjective_quotientMap [IsReduced R] [IsReduced S]
    [_root_.Finite (PrimeSpectrum R)] (f : R →+* S)
    (hmax : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal)
    (hcomap : Function.Bijective (PrimeSpectrum.comap f))
    (hres : ∀ q : PrimeSpectrum S, Function.Surjective
      (Ideal.quotientMap q.asIdeal f (le_refl (q.asIdeal.comap f)))) :
    Function.Bijective f :=
  bijective_of_bijective_comap_of_forall_exists_sub_mem f hmax hcomap
    fun q => exists_sub_mem_of_surjective_quotientMap f q (hres q)

end RingHom

end
