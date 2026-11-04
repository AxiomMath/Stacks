module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Two constant sections of the affine line are separated by every flat scheme

Let `R` be a domain and let `r ≠ 0` in `R`. The two `R`-points `0` and `r` of the affine line
`A¹_R = Spec R[X]` agree on the closed subscheme cut out by `X - r`, which misses the generic
point of `Spec R`. So a scheme *flat* over `Spec R` on which the two induced morphisms to `A¹_R`
agree must be empty: flatness makes the structure morphism generalizing, so a point of the source
would produce a point over the generic point of `Spec R`, where the two sections are distinct.

This is the arithmetic content of the counterexample of **Stacks 07BG**, where the source takes
`R = ℤ` and `r = p`, and the two sections `x ↦ x` and `x ↦ x + p` of `A¹_ℤ`: their equaliser is
the fibre of `A¹_ℤ` over the prime `(p)`, and no scheme flat over `Spec ℤ` maps into it.

## Main results

* `AlgebraicGeometry.isEmpty_of_flat_of_eval_sections_eq`: a flat scheme over the spectrum of a
  domain on which the `0` and `r` evaluation sections of the polynomial ring agree is empty.

## Implementation notes

Flatness enters only through `AlgebraicGeometry.Flat.generalizingMap`, which lifts the
specialisation from the generic point `⊥` of `Spec R` to any point of the image. Over the
generic point the two sections differ because `X` lies in the prime
`(evalRingHom 0)⁻¹ ⊥ = (X)` while — `R` being a domain and `r` nonzero — it does not lie in
`(evalRingHom r)⁻¹ ⊥`.

## References

* [Stacks Project, Tag 07BG](https://stacks.math.columbia.edu/tag/07BG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A flat scheme over the spectrum of a domain separates the `0` and `r` sections of the
affine line.** If `r ≠ 0` in a domain `R` and `g : U ⟶ Spec R` is flat, then the two morphisms
`U ⟶ Spec R[X]` obtained from `g` by evaluating at `0` and at `r` are equal only when `U` is
empty.

Flatness makes `g` generalizing, so a point of `U` lies over a point which specialises from the
generic point of `Spec R` and may be moved there; at the generic point the two sections pull `X`
back to different primes. -/
theorem isEmpty_of_flat_of_eval_sections_eq
    {R : Type u} [CommRing R] [IsDomain R] (r : R) (hr : r ≠ 0)
    {U : Scheme.{u}} (g : U ⟶ Spec (.of R)) [Flat g]
    (h : g ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) =
      g ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom r))) : IsEmpty U := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y, hy, hgy⟩ := Flat.generalizingMap g
    ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum R) (g x)).mp bot_le)
  have hpoints := congrArg (fun f : U ⟶ Spec (.of (Polynomial R)) => f y) h
  simp only [Scheme.Hom.comp_apply, hgy] at hpoints
  change PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) ⊥ =
    PrimeSpectrum.comap (Polynomial.evalRingHom r) ⊥ at hpoints
  have hmem : Polynomial.X ∈
      (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) ⊥).asIdeal := by
    simp
  rw [hpoints] at hmem
  exact hr (by simpa using hmem)

end AlgebraicGeometry

end
