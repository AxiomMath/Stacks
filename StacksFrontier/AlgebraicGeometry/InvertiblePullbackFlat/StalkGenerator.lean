module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.AffineDescent
import StacksCore.Tactic.StacksAttribute

/-!
# The generator produced at a point, in the penultimate paragraph of Stacks Tag 0BD7

The affine step of Stacks Tag 0BD7 — proved in
`StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.AffineDescent` — is applied in the
source not to an affine chart but to `Spec(𝒪_{X,x}) → Spec(𝒪_{Y,y})`, and it is applied with the
exponents, the minimal primes and the ideal `I` all chosen inside the argument rather than
supplied. This file carries out that application: for a Noetherian normal local domain `R`, a
Noetherian domain `A` faithfully flat over `R`, and a unit `s` of `A ⊗_R K` (`K` the fraction
field of `R`), it produces nonzero `g, r ∈ R` and a unit `u` of `A` with `r s = g u` — that is,
`s = (g/r) u`, so that the meromorphic function `r/g` multiplies `s` into a generator. This is
the source's "there exists an element `g ∈ R(Y)^*` such that `φ^*(g) s` generates `ℒ_x`".

Two further obligations of that paragraph are discharged here.

The hypothesis `(𝔭 A).IsPrime` carried as an instance argument throughout `AffineDescent.lean` —
the source's "by assumption `𝔮ᵢ = 𝔭ᵢ A` is a prime" — is derived from flatness together with
integrality of the fibre over `𝔭`. The fibre ring of `Spec A → Spec R` over `𝔭` is `A' / 𝔭 A'`
for `A'` the localization of `A` at the image of `R ∖ 𝔭`, so "the fibre is integral" is exactly
`(𝔭 A').IsPrime`; the content is that `𝔭 A` is recovered from `𝔭 A'` by contraction, which needs
every element of `R ∖ 𝔭` to be a nonzerodivisor modulo `𝔭 A`. That in turn is flatness: in `R`
one has `𝔭 ⊓ (r) = (r) 𝔭` for `r ∉ 𝔭`, extension of ideals along a flat algebra commutes with
intersection (`Ideal.map_inf_of_flat`, Tag 0BBY), and a nonzerodivisor of `R` stays a
nonzerodivisor on a flat module.

The source's "well defined up to multiplication by an element of `𝒪_{Y,y}^*`" is
`Module.FaithfullyFlat.associated_of_algebraMap_eq_isUnit_mul`: two elements of `R` whose images
in `A` differ by a unit of `A` differ by a unit of `R`, because faithfully flat extension of
ideals is injective. It is what makes the generator found at one point of a fibre agree with the
one found at another.

## Main results

* `Ideal.mem_map_of_mul_mem_map_of_flat`: for `𝔭` prime and `r ∉ 𝔭` a nonzerodivisor, the image
  of `r` is a nonzerodivisor modulo `𝔭 A` when `A` is flat over `R`.
* `Ideal.isPrime_map_of_flat_of_isPrime_map_localization`: `𝔭 A` is prime as soon as `A` is flat
  over `R` and the fibre over `𝔭` is integral.
* `Ideal.isPrime_map_of_flat_of_isDomain_fiber`: the same, with the hypothesis stated on
  Mathlib's fibre ring `Ideal.Fiber 𝔭 A = κ(𝔭) ⊗_R A` instead of on a localization.
* `Module.FaithfullyFlat.associated_of_algebraMap_eq_isUnit_mul`: the uniqueness of the generator
  up to a unit of `R`.
* `Ideal.exists_isUnit_mul_eq_of_isUnit`: the conclusion of the penultimate paragraph of Tag
  0BD7 at a point, `r s = g u` with `u` a unit of `A` and `g, r ∈ R` nonzero.
* `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber`: the same conclusion with the primality
  hypothesis replaced by "every fibre ring of `R → A` is a domain".
* `Ideal.fiberBotRingEquivOfIsLocalization`: the ring `B` of the two results above — the
  source's `A ⊗_R K` — *is* the fibre ring of `R → A` over the generic point `⊥` of `Spec R`.

## Implementation notes

`Ideal.exists_isUnit_mul_eq_of_isUnit` keeps the hypothesis `𝔭 A` prime for *all* primes `𝔭` of
`R` rather than only for the minimal primes over the particular element `r r'` that the proof
produces: the element is chosen inside the proof, so a hypothesis naming it could not be
discharged by a caller. `Ideal.isPrime_map_of_flat_of_isPrime_map_localization` discharges it
prime by prime.

The ring `A ⊗_R K` of the source appears here as an arbitrary localization of `A` at the image of
the nonzero elements of `R`, which is what `IsLocalization.tensorRight` makes of the tensor
product; `IsLocalization.exists_mul_eq_algebraMap_of_isUnit` records that reduction.

`Ideal.fiberBotRingEquivOfIsLocalization` identifies that ring with `Ideal.Fiber ⊥ A`, so both
of the remaining obligations of this paragraph are statements about the *same* family of rings
`Ideal.Fiber 𝔭 A`: that each is a domain (the primality hypothesis, at every `𝔭`) and that the
germ of the meromorphic section is a unit (at `𝔭 = ⊥`, where assumption (5) of Tag 0BD7 lives).

`Ideal.Fiber` is `κ(𝔭) ⊗_R A` and carries its `Algebra A` structure through
`Algebra.TensorProduct.rightAlgebra`, which is not a global instance; the two proofs below that
mention that algebra structure therefore introduce it locally, by `let` in the `Prop`-valued one
and by `letI` in the `def`.

`Ideal.fiberBotRingEquivOfIsLocalization` is *not* proved by exhibiting the tensor product as a
quotient of a localization: `IsLocalization.tensorRight` already states that `κ(⊥) ⊗_R A` **is**
the localization of `A` at the image of the nonzero elements of `R`, so the equivalence is
`IsLocalization.algEquiv` between two localizations at one submonoid.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0BBY](https://stacks.math.columbia.edu/tag/0BBY)
-/

@[expose] public section

universe u

namespace Ideal

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A nonzerodivisor `r` of `R` outside a prime `𝔭` has image a nonzerodivisor modulo `𝔭 A`, for
`A` flat over `R`. In `R` one has `𝔭 ⊓ (r) = (r) 𝔭`, because `r b ∈ 𝔭` and `r ∉ 𝔭` force
`b ∈ 𝔭`; extension along a flat algebra commutes with intersection (Stacks Tag 0BBY), so the
same identity holds for `𝔭 A` and `(r) A`, and `r` is a nonzerodivisor on the flat module `A`. -/
theorem mem_map_of_mul_mem_map_of_flat [Module.Flat R A] (p : Ideal R) [hp : p.IsPrime]
    {r : R} (hr : r ∈ nonZeroDivisors R) (hrp : r ∉ p) {x : A}
    (hx : algebraMap R A r * x ∈ p.map (algebraMap R A)) :
    x ∈ p.map (algebraMap R A) := by
  have hinf : p ⊓ Ideal.span {r} = Ideal.span {r} * p := by
    refine le_antisymm (fun a ha => ?_) (le_inf Ideal.mul_le_right Ideal.mul_le_left)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha.2
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self r)
      ((hp.mem_or_mem ha.1).resolve_left hrp)
  have hmap : p.map (algebraMap R A) ⊓ Ideal.span {algebraMap R A r} =
      Ideal.span {algebraMap R A r} * p.map (algebraMap R A) := by
    have hs : Ideal.span {algebraMap R A r} = (Ideal.span {r}).map (algebraMap R A) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hs, ← Ideal.map_inf_of_flat, ← Ideal.map_mul, hinf]
  have hmem : algebraMap R A r * x ∈
      Ideal.span {algebraMap R A r} * p.map (algebraMap R A) := by
    rw [← hmap]
    exact ⟨hx, Ideal.mem_span_singleton.mpr ⟨x, rfl⟩⟩
  obtain ⟨z, hz, hzx⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hreg : IsSMulRegular A r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have hsmul : r • x = r • z := by simpa [Algebra.smul_def] using hzx.symm
  exact hreg hsmul ▸ hz

/-- **The source's "by assumption `𝔮ᵢ = 𝔭ᵢ A` is a prime".** For `A` flat over a domain `R` and
`𝔭` a prime of `R`, the extension `𝔭 A` is prime as soon as the fibre of `Spec A → Spec R` over
`𝔭` is integral — that fibre is `A' / 𝔭 A'` for `A'` the localization of `A` at the image of
`R ∖ 𝔭`, so integrality of the fibre is the hypothesis `(𝔭 A').IsPrime` (which also makes the
fibre nonempty).

The ideal `𝔭 A` is the contraction of `𝔭 A'` along `A ⟶ A'`: a section of `𝔭 A'` pulled back to
`A` is killed by some element of `R ∖ 𝔭`, and those are nonzerodivisors modulo `𝔭 A` by
`Ideal.mem_map_of_mul_mem_map_of_flat`. A contraction of a prime is prime. -/
theorem isPrime_map_of_flat_of_isPrime_map_localization [Module.Flat R A] [IsDomain R]
    (p : Ideal R) [hp : p.IsPrime] (A' : Type u) [CommRing A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) A']
    (hfib : (p.map (algebraMap R A')).IsPrime) :
    (p.map (algebraMap R A)).IsPrime := by
  have hmap : p.map (algebraMap R A') = (p.map (algebraMap R A)).map (algebraMap A A') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hcomap : p.map (algebraMap R A) = (p.map (algebraMap R A')).comap (algebraMap A A') := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [Ideal.mem_comap, hmap]
      exact Ideal.mem_map_of_mem _ hx
    · rw [Ideal.mem_comap, hmap,
        IsLocalization.algebraMap_mem_map_algebraMap_iff
          (Algebra.algebraMapSubmonoid A p.primeCompl)] at hx
      obtain ⟨m, ⟨r, hrp, rfl⟩, hmx⟩ := hx
      exact mem_map_of_mul_mem_map_of_flat p
        (mem_nonZeroDivisors_of_ne_zero (ne_of_mem_of_not_mem p.zero_mem hrp).symm) hrp hmx
  rw [hcomap]
  have := hfib
  infer_instance

/-- **`𝔭 A` is prime as soon as the fibre ring over `𝔭` is a domain.** This is
`Ideal.isPrime_map_of_flat_of_isPrime_map_localization` with its hypothesis moved onto Mathlib's
fibre ring `Ideal.Fiber 𝔭 A = κ(𝔭) ⊗_R A`, which is the form in which the geometry supplies it:
`Spec (κ(𝔭) ⊗_R A)` *is* the fibre of `Spec A → Spec R` over `𝔭`
(`PrimeSpectrum.preimageHomeomorphFiber`), whereas the localization `A'` of the previous result
is only a presentation of it.

No new mathematics: `Ideal.Fiber.algEquivAux₁` already identifies `κ(𝔭) ⊗_R A` with
`A' ⧸ 𝔭 A'` for `A'` the localization of `A` at the image of `R ∖ 𝔭`, and
`Ideal.Quotient.isDomain_iff_prime` turns "domain" into "prime". The point of recording it is
that it names the one geometric input the penultimate paragraph of Stacks Tag 0BD7 still owes,
and names it as a property of a fibre rather than of a localization. -/
theorem isPrime_map_of_flat_of_isDomain_fiber [Module.Flat R A] [IsDomain R]
    (p : Ideal R) [p.IsPrime] (hdom : IsDomain (p.Fiber A)) :
    (p.map (algebraMap R A)).IsPrime := by
  let : Algebra A (p.Fiber A) := Algebra.TensorProduct.rightAlgebra
  have hq : IsDomain (Localization (Algebra.algebraMapSubmonoid A p.primeCompl) ⧸
      Ideal.map (algebraMap A (Localization (Algebra.algebraMapSubmonoid A p.primeCompl)))
        (Ideal.map (algebraMap R A) p)) :=
    ((Ideal.Fiber.algEquivAux₁ (S := A) p).toRingEquiv.toMulEquiv.symm).isDomain _
  have hp' : (Ideal.map (algebraMap R
      (Localization (Algebra.algebraMapSubmonoid A p.primeCompl))) p).IsPrime := by
    rw [IsScalarTower.algebraMap_eq R A
        (Localization (Algebra.algebraMapSubmonoid A p.primeCompl)), ← Ideal.map_map]
    exact (Ideal.Quotient.isDomain_iff_prime _).mp hq
  exact isPrime_map_of_flat_of_isPrime_map_localization p
    (Localization (Algebra.algebraMapSubmonoid A p.primeCompl)) hp'

end Ideal

namespace Module.FaithfullyFlat

/-- **The uniqueness in the penultimate paragraph of Stacks Tag 0BD7**, that the element `g` is
"well defined up to multiplication by an element of `𝒪_{Y, y}^*`". If two elements of `R` have
images in a faithfully flat `R`-algebra `A` differing by a unit of `A`, they differ by a unit of
`R`: the two principal ideals they generate have equal extensions to `A`, and extension of ideals
along a faithfully flat algebra is injective. -/
theorem associated_of_algebraMap_eq_isUnit_mul {R A : Type u} [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Algebra R A] [Module.FaithfullyFlat R A] {c d : R} {w : A}
    (hw : IsUnit w) (h : algebraMap R A c = w * algebraMap R A d) :
    Associated c d := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  refine Ideal.map_injective_of_faithfullyFlat (A := R) (B := A) ?_
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    (h ▸ associated_unit_mul_left (algebraMap R A d) w hw)

end Module.FaithfullyFlat

namespace Ideal

/-- **The conclusion of the penultimate paragraph of Stacks Tag 0BD7, at a point.** Let `R` be a
Noetherian normal local domain, let `A` be a Noetherian domain faithfully flat over `R` with
`𝔭 A` prime for every prime `𝔭` of `R`, and let `B` be a localization of `A` at the image of the
nonzero elements of `R` — the ring `A ⊗_R K` of the source. Then a unit `s` of `B` can be written
`s = (g/r) u` with `g, r ∈ R` nonzero and `u` a unit of `A`: the fraction `r/g` of elements of
`R` multiplies `s` into a generator.

This is the source's application of the affine step to `Spec(𝒪_{X, x}) → Spec(𝒪_{Y, y})`. The
unit `s` is written `a/r` with inverse `a'/r'` by
`IsLocalization.exists_mul_eq_algebraMap_of_isUnit`, and the affine step
`Ideal.exists_isUnit_mul_of_mul_eq_algebraMap` is applied to the minimal primes over `r r'`,
which are finitely many because `R` is Noetherian. -/
theorem exists_isUnit_mul_eq_of_isUnit {R A B : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Algebra R A] [Module.FaithfullyFlat R A] [CommRing B] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) B]
    (hprime : ∀ q : Ideal R, q.IsPrime → (q.map (algebraMap R A)).IsPrime)
    {s : B} (hs : IsUnit s) :
    ∃ (g r : R) (u : A), g ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
      algebraMap R B r * s = algebraMap R B g * algebraMap A B u := by
  classical
  obtain ⟨a, a', r, r', hr, hr', haa', hab⟩ :=
    IsLocalization.exists_mul_eq_algebraMap_of_isUnit (R := R) (A := A) (B := B) hs
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors R) ≤ nonZeroDivisors A :=
    IsLocalization.algebraMapSubmonoid_le_nonZeroDivisors (R := R) (A := A)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  have hRA : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  have hRB : Function.Injective (algebraMap R B) := by
    rw [IsScalarTower.algebraMap_eq R A B]
    exact hAB.comp hRA
  have hrB : algebraMap R B r ≠ 0 := (map_ne_zero_iff _ hRB).2 hr
  have ha : a ≠ 0 := fun hc =>
    mul_ne_zero hrB hs.ne_zero (hab.symm.trans (by rw [hc, map_zero]))
  have hf : r * r' ≠ 0 := mul_ne_zero hr hr'
  have ha' : a' ≠ 0 := fun hc =>
    (map_ne_zero_iff _ hRA).2 hf (haa'.symm.trans (by rw [hc, mul_zero]))
  have : Fintype ((Ideal.span {r * r'}).minimalPrimes) :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {r * r'})).fintype
  have hp1 : ∀ i : ((Ideal.span {r * r'}).minimalPrimes), (i : Ideal R).IsPrime :=
    fun i => i.2.isPrime
  have hp2 : ∀ i : ((Ideal.span {r * r'}).minimalPrimes),
      ((i : Ideal R).map (algebraMap R A)).IsPrime := fun i => hprime _ i.2.isPrime
  obtain ⟨e, g, u, hu, -, hug⟩ :=
    Ideal.exists_isUnit_mul_of_mul_eq_algebraMap (A := A) (f := r * r')
      (Finset.univ : Finset ((Ideal.span {r * r'}).minimalPrimes)) (fun i => (i : Ideal R))
      hf ha ha' (fun i _ => i.2) (fun q hq => ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩) haa'
  have hg : g ≠ 0 := fun hc => ha (hug.trans (by rw [hc, map_zero, mul_zero]))
  exact ⟨g, r, u, hg, hr, hu, by
    rw [← hab, hug, map_mul, ← IsScalarTower.algebraMap_apply, mul_comm]⟩

/-- **The penultimate paragraph of Stacks Tag 0BD7 with its primality hypothesis replaced by the
geometric one.** `Ideal.exists_isUnit_mul_eq_of_isUnit` asks for `𝔮 A` to be prime for every
prime `𝔮` of `R`; here that is deduced from "every fibre ring of `R → A` is a domain", which for
`R = 𝒪_{Y, y}` and `A = 𝒪_{X, x}` is the assertion that the fibres of
`Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}` are integral — the source's "by assumption `𝔮ᵢ = 𝔭ᵢ A` is a
prime", read off hypothesis (3) of the tag.

This does not discharge the hypothesis: identifying `Ideal.Fiber 𝔭 𝒪_{X, x}` with a localization
of the ring of an affine open of the integral fibre `X_{y'}`, for `y'` the point of `Y`
corresponding to `𝔭`, is still owed. -/
theorem exists_isUnit_mul_eq_of_isDomain_fiber {R A B : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Algebra R A] [Module.FaithfullyFlat R A] [CommRing B] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) B]
    (hfib : ∀ q : Ideal R, ∀ _ : q.IsPrime, IsDomain (q.Fiber A))
    {s : B} (hs : IsUnit s) :
    ∃ (g r : R) (u : A), g ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
      algebraMap R B r * s = algebraMap R B g * algebraMap A B u :=
  exists_isUnit_mul_eq_of_isUnit
    (fun q hq => have := hq; isPrime_map_of_flat_of_isDomain_fiber q (hfib q hq)) hs

/-- **The source's `A ⊗_R K` is the fibre ring over the generic point of `Spec R`.** For a domain
`R`, the nonzero elements are exactly the complement of the prime `⊥`, so a localization of `A`
at their image — the ring `B` of `Ideal.exists_isUnit_mul_eq_of_isUnit`, and the `A ⊗_R K` of
Stacks Tag 0BD7 — is `Ideal.Fiber ⊥ A = κ(⊥) ⊗_R A`.

For `R = 𝒪_{Y, y}` and `A = 𝒪_{X, x}` with `Y` integral, `⊥` is the generic point `ξ` of `Y`, so
this says that `B` is the coordinate ring of the fibre of `Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}` over
`ξ`: the obligation "the germ of the meromorphic section `s` is a unit of `B`" is an obligation
about the *generic fibre*, which is where assumption (5) of the tag lives. -/
noncomputable def fiberBotRingEquivOfIsLocalization {R A B : Type u} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [CommRing B] [Algebra A B]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) B] :
    (⊥ : Ideal R).Fiber A ≃+* B := by
  letI : Algebra A ((⊥ : Ideal R).Fiber A) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := (⊥ : Ideal R).ResidueField) (B := A)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      ((⊥ : Ideal R).Fiber A) :=
    IsLocalization.tensorRight ((⊥ : Ideal R).ResidueField) (nonZeroDivisors R)
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
    ((⊥ : Ideal R).Fiber A) B).toRingEquiv

end Ideal

end
