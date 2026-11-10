module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The local ring at a generalization is a localization of the local ring

Let `X` be a scheme and let `y ⤳ x` be a specialization of points, so that `y` is a
generalization of `x`. Then every open neighbourhood of `x` contains `y`, the local ring
`𝒪_{X,y}` receives the canonical comparison map `TopCat.Presheaf.stalkSpecializes` out of
`𝒪_{X,x}`, and the content of this file is that this map exhibits `𝒪_{X,y}` as the
localization of `𝒪_{X,x}` at a prime ideal — namely at the contraction of the maximal ideal
of `𝒪_{X,y}`.

Mathlib has `TopCat.Presheaf.stalkSpecializes` only as a morphism, together with its
compatibilities (`germ_stalkSpecializes`, `stalkSpecializes_comp`,
`Scheme.Hom.stalkSpecializes_stalkMap`). Nothing identifies it as a localization map, so a
consumer that needs to pass from a statement about `𝒪_{X,y}` to a statement about a prime of
`𝒪_{X,x}` — the shape of the arguments about associated points and the relative assassin
(Tags 02OJ, 05AT) — has no handle at all. That passage is what this file supplies.

## Main results

* `Stacks.StalkSpecialization.isPrime_map_of_le`: for primes `q ≤ p` of `R` and a
  localization `S` of `R` at `p`, the ideal `q S` is prime. This is the side condition
  needed to state the next result.
* `Stacks.StalkSpecialization.isLocalization_atPrime_map_of_le`: the commutative-algebra
  core. If `q ≤ p` are primes of `R`, `S` is a localization of `R` at `p` and `T` is a
  localization of `R` at `q`, compatibly, then `T` is a localization of `S` at the prime
  `q S`. This is the `AtPrime` form of `IsLocalization.isLocalization_of_submonoid_le`,
  which gives only that `T` is the localization of `S` at the *image* of `q.primeCompl`.
* `Stacks.StalkSpecialization.isLocalization_atPrime_of_eq`: `IsLocalization.AtPrime`
  transported along an equality of primes, which `rw` cannot do because the two sides carry
  different `Ideal.IsPrime` instance arguments.
* `Stacks.StalkSpecialization.isLocalization_atPrime_stalk_of_specializes`: for `y ⤳ x` in
  a scheme `X`, and any `Algebra (𝒪_{X,x}) (𝒪_{X,y})` whose structure map is
  `stalkSpecializes`, the ring `𝒪_{X,y}` is the localization of `𝒪_{X,x}` at the prime
  `(maximalIdeal 𝒪_{X,y}).under 𝒪_{X,x}`.
* `Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`: the same statement
  at the canonical algebra structure `(stalkSpecializes h).hom.toAlgebra`, so that no
  algebra instance has to be produced by the caller.

## Implementation notes

**The prime is named canonically, not through a chart.** The proof picks an affine open
neighbourhood `U` of `x` — which also contains `y`, by `Specializes.mem_open` — and
transports `IsAffineOpen.isLocalization_stalk` at the two points of `U`. The prime of
`𝒪_{X,x}` that comes out of that argument is `q Γ(X,U)·𝒪_{X,x}`, which depends on `U`. It
is converted to the chart-independent `(IsLocalRing.maximalIdeal 𝒪_{X,y}).under 𝒪_{X,x}` by
`IsLocalization.AtPrime.under_maximalIdeal`, so the statements carry no chart and no
existential.

**Why `q S` is reached through `isLocalization_of_is_exists_mul_mem`.**
`IsLocalization.isLocalization_of_submonoid_le` gives `T` as the localization of `S` at
`Submonoid.map (algebraMap R S) q.primeCompl`, which is strictly smaller than
`(q S).primeCompl`: an element of the latter is a fraction `a/s` with `s ∈ p.primeCompl`,
not an element of `R`. Multiplying by `algebraMap R S s` lands it in the image, which is
exactly the hypothesis of `IsLocalization.isLocalization_of_is_exists_mul_mem`.

**The algebra structure is a hypothesis, not a global instance.** Registering
`(stalkSpecializes h).hom.toAlgebra` as an instance would put an `Algebra` between the
stalks at every pair of specializing points of every scheme, which typeclass search cannot
be expected to survive. The general result therefore takes `[Algebra 𝒪_{X,x} 𝒪_{X,y}]`
together with the equation pinning its structure map, which is also the shape a caller who
already built the algebra from `IsLocalization.localizationAlgebraOfSubmonoidLe` can use
without transporting anything. `isLocalization_atPrime_stalkSpecializes` instantiates it at
the canonical choice.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.StalkSpecialization

variable {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [hq : q.IsPrime]

/-- The prime complement of a larger prime is disjoint from a smaller prime. -/
private theorem disjoint_primeCompl_of_le {I J : Ideal R} [I.IsPrime] (hJI : J ≤ I) :
    Disjoint (I.primeCompl : Set R) J :=
  Set.disjoint_left.mpr fun _ ha hJa => ha (hJI hJa)

/-- If `q ≤ p` are prime ideals of `R` and `S` is a localization of `R` at `p`, then the ideal
generated by the image of `q` in `S` is prime. -/
theorem isPrime_map_of_le (hqp : q ≤ p) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p] : (Ideal.map (algebraMap R S) q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q hq
    (disjoint_primeCompl_of_le hqp)

/-- **The localization of a localization, in `AtPrime` form.** Let `q ≤ p` be prime ideals of
`R`, let `S` be a localization of `R` at `p` and let `T` be a localization of `R` at `q`,
compatibly. Then `T` is the localization of `S` at the prime ideal `q S`.

`IsLocalization.isLocalization_of_submonoid_le` gives only that `T` is the localization of `S`
at the image of `q.primeCompl`; the content here is that inverting that image already inverts
all of `(q S).primeCompl`. -/
theorem isLocalization_atPrime_map_of_le (hqp : q ≤ p) (S T : Type*) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsLocalization.AtPrime S p] [IsLocalization.AtPrime T q]
    [Algebra S T] [IsScalarTower R S T] [(Ideal.map (algebraMap R S) q).IsPrime] :
    IsLocalization.AtPrime T (Ideal.map (algebraMap R S) q) := by
  have hunder : (Ideal.map (algebraMap R S) q).under R = q :=
    IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hq
      (disjoint_primeCompl_of_le hqp)
  have hnotmem : ∀ a : R, a ∉ q → algebraMap R S a ∉ Ideal.map (algebraMap R S) q :=
    fun a ha hmem => ha (hunder ▸ Ideal.mem_comap.mpr hmem)
  have hpq : p.primeCompl ≤ q.primeCompl :=
    Set.disjoint_left.mp (disjoint_primeCompl_of_le hqp)
  have : IsLocalization (Submonoid.map (algebraMap R S) q.primeCompl) T :=
    IsLocalization.isLocalization_of_submonoid_le S T p.primeCompl q.primeCompl hpq
  refine IsLocalization.isLocalization_of_is_exists_mul_mem T
    (Submonoid.map (algebraMap R S) q.primeCompl) _ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hnotmem a ha
  · intro z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj p.primeCompl (z : S)
    refine ⟨algebraMap R S s, a, ?_, by rw [← hs, mul_comm]⟩
    intro hmemq
    refine z.2 ?_
    have hmul : algebraMap R S s * (z : S) ∈ Ideal.map (algebraMap R S) q := by
      rw [mul_comm, hs]
      exact Ideal.mem_map_of_mem _ hmemq
    exact (‹(Ideal.map (algebraMap R S) q).IsPrime›.mem_or_mem hmul).resolve_left
      (hnotmem s (hpq s.2))

/-- `IsLocalization.AtPrime` transported along an equality of primes. The two sides carry
different `Ideal.IsPrime` instance arguments, so `rw` cannot do this: its motive is not type
correct. -/
theorem isLocalization_atPrime_of_eq {S : Type*} [CommRing S] [Algebra R S] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (hIJ : I = J) (h : IsLocalization.AtPrime S I) :
    IsLocalization.AtPrime S J := by
  subst hIJ
  exact h

/-- **The local ring at a generalization is a localization.** Let `y ⤳ x` be a specialization
of points of a scheme `X`, and let `𝒪_{X,y}` be an `𝒪_{X,x}`-algebra whose structure map is
the canonical comparison `TopCat.Presheaf.stalkSpecializes`. Then `𝒪_{X,y}` is the
localization of `𝒪_{X,x}` at the prime ideal obtained by contracting the maximal ideal of
`𝒪_{X,y}`. -/
theorem isLocalization_atPrime_stalk_of_specializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    [Algebra (X.presheaf.stalk x) (X.presheaf.stalk y)]
    (halg : algebraMap (X.presheaf.stalk x) (X.presheaf.stalk y) =
      (X.presheaf.stalkSpecializes h).hom) :
    IsLocalization.AtPrime (X.presheaf.stalk y)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  let xU : U := ⟨x, hxU⟩
  let yU : U := ⟨y, hyU⟩
  let S := X.presheaf.stalk x
  let T := X.presheaf.stalk y
  let pp : Ideal Γ(X, U) := (hU.primeIdealOf xU).asIdeal
  let qq : Ideal Γ(X, U) := (hU.primeIdealOf yU).asIdeal
  let : Algebra Γ(X, U) S := X.presheaf.algebra_section_stalk xU
  let : Algebra Γ(X, U) T := X.presheaf.algebra_section_stalk yU
  have : pp.IsPrime := (hU.primeIdealOf xU).isPrime
  have : qq.IsPrime := (hU.primeIdealOf yU).isPrime
  have : IsLocalization.AtPrime S pp := hU.isLocalization_stalk xU
  have : IsLocalization.AtPrime T qq := hU.isLocalization_stalk yU
  have hqp : qq ≤ pp := (PrimeSpectrum.le_iff_specializes _ _).mpr (by
    change (Scheme.homeoOfIso hU.isoSpec) yU ⤳ (Scheme.homeoOfIso hU.isoSpec) xU
    exact ((subtype_specializes_iff yU xU).mpr h).map (Scheme.homeoOfIso hU.isoSpec).continuous)
  have : IsScalarTower Γ(X, U) S T :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [halg]
      exact congrArg CommRingCat.Hom.hom
        (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU h).symm)
  have : (Ideal.map (algebraMap Γ(X, U) S) qq).IsPrime := isPrime_map_of_le hqp _
  have hloc : IsLocalization.AtPrime T (Ideal.map (algebraMap Γ(X, U) S) qq) :=
    isLocalization_atPrime_map_of_le hqp S T
  exact isLocalization_atPrime_of_eq
    (IsLocalization.AtPrime.under_maximalIdeal T (Ideal.map (algebraMap Γ(X, U) S) qq)).symm hloc

/-- **The local ring at a generalization is a localization**, at the canonical algebra
structure induced by `TopCat.Presheaf.stalkSpecializes`. -/
theorem isLocalization_atPrime_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk y)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) :=
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  isLocalization_atPrime_stalk_of_specializes h (RingHom.algebraMap_toAlgebra _)

end Stacks.StalkSpecialization

end
