module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureQuotientStalk
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseMilnorBoundary

/-!
# Fraction fields and orders of vanishing along the height-one correspondence

The local algebraic reciprocity behind Stacks 0GU9 is stated at a two-dimensional Noetherian
local domain `A`: its summand at a height-one prime `𝔮` is built from the localization `A_𝔮`,
takes its arguments in the canonical fraction field `FractionRing A`, and measures an order of
vanishing in the residue field `κ(𝔮)` of `𝔮`, which is the fraction field of `A ⧸ 𝔮`. The
geometric form of the same summand, built at the integral closed subscheme `W = closure {x}` of
`X` with `A = 𝒪_{W, x''}`, speaks instead of the local ring `𝒪_{W, x'}` at the intermediate point,
of the residue field `κ(x)` of the generic point, and of the order of vanishing `Ring.ord` of a
germ. This file supplies the four identifications relating the two vocabularies, each with the
compatibility a transport consumes.

Two of them identify a field with a canonically presented fraction field, and so come from the
uniqueness of fraction fields: a localization of a ring at a multiplicative set is determined up
to a unique isomorphism over that ring, so any two presentations of it agree compatibly with the
maps from the ring. The other two are about the order of vanishing: `Ring.ordFrac` is transported
by a compatible pair of ring isomorphisms, and on a ring element it is `Ring.ord` of that
element.

## Restatements of private results of the base

* `Stacks.Chow.ordFrac_ringEquiv` restates `ordFrac_eq_of_ringEquiv` of
  `StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order`, which is `private` and so cannot
  be named from another module. That file's only public export,
  `Stacks.Chow.ord_functionFieldRingEquivOfIso`, is for an isomorphism of *schemes* and does not
  apply to a bare pair of ring isomorphisms. The proof is the same, except that the `Ring.ord`
  half is taken from the public `Ring.ord_ringEquiv` of
  `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder` instead of from the
  second `private` lemma of that file.

## What is carried

No further input is assumed. The two order statements need a one-dimensional Noetherian domain,
which is what makes the order of vanishing of Stacks 02MD defined; the two fraction-field
statements need integrality of the scheme, respectively the height-one correspondence of
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint`, and nothing else.

Nothing here asserts Stacks 0GU9 or Stacks 0GUA, and nothing here identifies the two forms of a
summand of the displayed sum of Stacks 0GU9: the Milnor K-groups at the two fields are not
compared, and no chain group, differential or complex appears.

## Main definitions

* `Stacks.Chow.fractionRingStalkEquiv` — for an integral scheme `W` whose function field is
  identified with a field `K`, the canonical fraction field of the local ring at a point of `W` is
  `K`.
* `Stacks.Chow.pointClosureFractionRingEquiv` — the same at `W = closure {x}`, where `K` is the
  residue field `κ(x)`.
* `Stacks.Chow.stalkLocalizationAtPrimeEquiv` — the canonical localization of `𝒪_{W, x''}` at a
  height-one prime is the local ring at the corresponding intermediate point.

## Main results

* `Stacks.Chow.ordFrac_ringEquiv` — `Ring.ordFrac` is transported by an isomorphism of
  one-dimensional Noetherian domains together with a compatible isomorphism of their fraction
  fields.
* `Stacks.Chow.ordFrac_algebraMap_eq_ofAdd`,
  `Stacks.Chow.toAdd_unzero_ordFrac_algebraMap` — on the image of a nonzero ring element,
  `Ring.ordFrac` is `Ring.ord` of that element.
* `Stacks.Chow.residueUnitOrder_eq_ord` — **the phrasing bridge**: the integer order of a unit of
  `κ(𝔮)` coming from an element of `A ⧸ 𝔮` is `Ring.ord` of that element.
* `Stacks.Chow.fractionRingStalkEquiv_algebraMap`,
  `Stacks.Chow.pointClosureFractionRingEquiv_algebraMap`,
  `Stacks.Chow.stalkLocalizationAtPrimeEquiv_algebraMap` — each identification commutes with the
  maps from the local ring, so each may be used to transport a tame symbol.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-! ### The order of vanishing along an isomorphism of pairs -/

section OrdFrac

variable {R S K L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field L] [Algebra S L] [IsFractionRing S L]

/-- **`Ring.ordFrac` is transported by an isomorphism of pairs.** Let `e : R ≃+* S` be an
isomorphism of one-dimensional Noetherian domains and let `E : K ≃+* L` be an isomorphism of
their fraction fields carrying the image of `r` to the image of `e r` for every `r` in `R`. Then
`E` preserves the order of vanishing of Stacks 02MD.

Every element of `K` is a quotient of two nonzero elements of `R`, and `Ring.ordFrac` of such a
quotient is the quotient of the two values of `Ring.ord`, which `e` preserves by
`Ring.ord_ringEquiv`.

This restates the `private` lemma `ordFrac_eq_of_ringEquiv` of
`StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order`, which cannot be named from another
module; the only public export of that file is for an isomorphism of schemes. -/
theorem ordFrac_ringEquiv (e : R ≃+* S) (E : K ≃+* L)
    (h : ∀ r : R, E (algebraMap R K r) = algebraMap S L (e r)) (f : K) :
    Ring.ordFrac S (E f) = Ring.ordFrac R f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀]
  simp only [h]
  have hb' : e b ∈ nonZeroDivisors S := map_mem_nonZeroDivisors e e.injective hb
  by_cases ha : a = 0
  · simp [ha]
  have ha₀ : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr ha
  have ha' : e a ∈ nonZeroDivisors S := map_mem_nonZeroDivisors e e.injective ha₀
  rw [← IsFractionRing.mk'_mk_eq_div hb, ← IsFractionRing.mk'_mk_eq_div hb',
    Ring.ordFrac_eq_div S ⟨e a, ha'⟩ ⟨e b, hb'⟩, Ring.ordFrac_eq_div R ⟨a, ha₀⟩ ⟨b, hb⟩,
    Ring.ordMonoidWithZeroHom_eq_ord ha', Ring.ordMonoidWithZeroHom_eq_ord ha₀,
    Ring.ordMonoidWithZeroHom_eq_ord hb', Ring.ordMonoidWithZeroHom_eq_ord hb,
    ← Ring.ord_ringEquiv e a, ← Ring.ord_ringEquiv e b]

end OrdFrac

/-! ### The order of vanishing of a ring element, read in the fraction field -/

section OrdFracOfElement

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **`Ring.ordFrac` on the image of a nonzero ring element is `Ring.ord` of that element.** The
`ℕ∞`-valued order of a nonzero element of a one-dimensional Noetherian domain is finite, and
`Ring.ordFrac` extends the multiplicative order of nonzerodivisors. -/
theorem ordFrac_algebraMap_eq_ofAdd {r : R} (hr : r ≠ 0) :
    Ring.ordFrac R (algebraMap R K r) =
      ((Multiplicative.ofAdd (((Ring.ord R r).toNat : ℕ) : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
  have hnz : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hr
  have hn : Ring.ord R r = (((Ring.ord R r).toNat : ℕ) : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top hnz)).symm
  rw [Ring.ordFrac_eq_ord R hr, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn]

/-- Equal nonzero values of `Ring.ordFrac` have equal integer logarithms: the two witnesses of
nonvanishing play no part, since they prove the same proposition. -/
private theorem toAdd_unzero_congr {x y : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : x = y) :
    Multiplicative.toAdd (WithZero.unzero hx) = Multiplicative.toAdd (WithZero.unzero hy) := by
  subst h
  rfl

/-- **The integer order of vanishing of the image of a nonzero ring element is `Ring.ord` of that
element.** This is the shape in which the `ℤ`-valued orders of the development, which read
`Ring.ordFrac` through `WithZero.unzero`, meet the `ℕ∞`-valued `Ring.ord` of a germ. -/
theorem toAdd_unzero_ordFrac_algebraMap {r : R} (hr : r ≠ 0)
    (h : Ring.ordFrac R (algebraMap R K r) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = ((Ring.ord R r).toNat : ℤ) := by
  refine Eq.trans (toAdd_unzero_congr h
    (y := ((Multiplicative.ofAdd (((Ring.ord R r).toNat : ℕ) : ℤ) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ))) (by simp) (ordFrac_algebraMap_eq_ofAdd hr)) ?_
  rw [WithZero.unzero_coe]
  rfl

end OrdFracOfElement

/-! ### The order of a residue-field unit coming from a ring element -/

section ResidueUnitOrder

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

/-- **The phrasing bridge between the two orders of vanishing.**
`Stacks.Chow.residueUnitOrder` measures a unit `d` of the residue field `κ(𝔮)` of a height-one
prime `𝔮` by `Ring.ordFrac (A ⧸ 𝔮)`, the order of vanishing of Stacks 02MD on the fraction field
of `A ⧸ 𝔮`. Where `d` is the image of an element `r` of `A ⧸ 𝔮`, that integer is `Ring.ord` of
`r`, which is the quantity that
`Stacks.Chow.ord_quot_eq_ord_intermediatePointStalk` carries to the local ring of the closure of
the intermediate point.

This is the explicit comparison of the two phrasings: the summand of the local algebraic
reciprocity of Stacks 0EAX is written with the first, and the geometric divisor on the closure of
a point with the second. -/
theorem residueUnitOrder_eq_ord {q : {q : Ideal A // q.IsPrime ∧ q.height = 1}} [q.1.IsPrime]
    (hquot : Ring.KrullDimLE 1 (A ⧸ q.1)) (d : q.1.ResidueFieldˣ) (r : A ⧸ q.1) (hr : r ≠ 0)
    (hd : (d : q.1.ResidueField) = algebraMap (A ⧸ q.1) q.1.ResidueField r) :
    residueUnitOrder (q := q) hquot d = ((Ring.ord (A ⧸ q.1) r).toNat : ℤ) := by
  have hne : Ring.ordFrac (A ⧸ q.1) (algebraMap (A ⧸ q.1) q.1.ResidueField r) ≠ 0 := by
    rw [← hd]
    exact ((Units.isUnit d).map (Ring.ordFrac (A ⧸ q.1))).ne_zero
  exact Eq.trans (toAdd_unzero_congr _ hne (by rw [hd]))
    (toAdd_unzero_ordFrac_algebraMap (K := q.1.ResidueField) hr hne)

end ResidueUnitOrder

/-! ### The canonical fraction field of a local ring of an integral scheme -/

section FractionRingStalk

variable {W : Scheme.{u}} [IsIntegral W] {K : Type u} [Field K] (e : ↥W.functionField ≃+* K)

/-- **The canonical fraction field of a local ring of an integral scheme is its function field.**
Let `W` be an integral scheme whose function field is identified with a field `K` by `e`, and let
`z` be a point of `W`. The function field is a fraction field of `𝒪_{W, z}`
(`Stacks.Chow.isFractionRing_stalkAlgebraOfFunctionFieldEquiv`), and so is the canonical
`FractionRing 𝒪_{W, z}`; a localization of a ring is determined up to a unique isomorphism over
that ring, so the two agree. -/
def fractionRingStalkEquiv (z : W) : FractionRing ↥(W.presheaf.stalk z) ≃+* K :=
  let _ := stalkAlgebraOfFunctionFieldEquiv e z
  have _ := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  (IsLocalization.algEquiv (nonZeroDivisors ↥(W.presheaf.stalk z))
    (FractionRing ↥(W.presheaf.stalk z)) K).toRingEquiv

/-- **The identification of fraction fields is one over the local ring.** The image of a germ in
the canonical fraction field goes to its image in `K`, so the pair consisting of the identity of
`𝒪_{W, z}` and `Stacks.Chow.fractionRingStalkEquiv` is a compatible pair of ring isomorphisms and
may be used to transport the tame symbol of Stacks 02Q1. -/
theorem fractionRingStalkEquiv_algebraMap (z : W) (a : ↥(W.presheaf.stalk z)) :
    fractionRingStalkEquiv e z
        (algebraMap ↥(W.presheaf.stalk z) (FractionRing ↥(W.presheaf.stalk z)) a) =
      e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField a) := by
  let _ := stalkAlgebraOfFunctionFieldEquiv e z
  have _ := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  exact (IsLocalization.algEquiv (nonZeroDivisors ↥(W.presheaf.stalk z))
    (FractionRing ↥(W.presheaf.stalk z)) K).commutes a

end FractionRingStalk

section PointClosureFractionRing

variable {X : Scheme.{u}}

/-- **The canonical fraction field of a local ring of `closure {x}` is the residue field at
`x`.** For a point `x` of a scheme `X` and a point `z` of the integral closed subscheme
`W = closure {x}`, the canonical fraction field of `𝒪_{W, z}` is `κ(x)`: the function field of
`W` is `κ(x)` by `Stacks.Chow.pointClosureFunctionFieldEquiv`, which is Stacks 01RV, and the
function field is a fraction field of every local ring of `W`.

This is the identification under which a class in the degree-two Milnor K-group of `κ(x)`, which
is what a chain of Stacks 0GU9 carries at `x`, becomes a class over the canonical fraction field
of `𝒪_{W, x''}`, which is what the local algebraic reciprocity of Stacks 0EAX takes as input. -/
def pointClosureFractionRingEquiv (x : X) (z : (integralComponentAt x).subscheme) :
    FractionRing ↥((integralComponentAt x).subscheme.presheaf.stalk z) ≃+*
      ↥(X.residueField x) :=
  fractionRingStalkEquiv (pointClosureFunctionFieldEquiv x) z

/-- The identification of the canonical fraction field with `κ(x)` is one over the local ring:
the image of a germ in the canonical fraction field goes to the image of its rational function
under `Stacks.Chow.pointClosureFunctionFieldEquiv`. -/
theorem pointClosureFractionRingEquiv_algebraMap (x : X)
    (z : (integralComponentAt x).subscheme)
    (a : ↥((integralComponentAt x).subscheme.presheaf.stalk z)) :
    pointClosureFractionRingEquiv x z
        (algebraMap ↥((integralComponentAt x).subscheme.presheaf.stalk z)
          (FractionRing ↥((integralComponentAt x).subscheme.presheaf.stalk z)) a) =
      pointClosureFunctionFieldEquiv x
        (algebraMap ↥((integralComponentAt x).subscheme.presheaf.stalk z)
          ↥((integralComponentAt x).subscheme.functionField) a) :=
  fractionRingStalkEquiv_algebraMap (pointClosureFunctionFieldEquiv x) z a

end PointClosureFractionRing

/-! ### The canonical localization at a height-one prime -/

section StalkLocalization

variable {W : Scheme.{u}}

/-- **The canonical localization of `𝒪_{W, x''}` at a height-one prime is the local ring at the
corresponding intermediate point.** `Stacks.Chow.isLocalization_stalk_heightOnePrime` says that
`𝒪_{W, x'}` is *a* localization of `A = 𝒪_{W, x''}` at `𝔮`, through specialization from `x'` to
`x''`; the canonical `Localization.AtPrime 𝔮` is another, and a localization of a ring is
determined up to a unique isomorphism over that ring.

This is the identification under which the local summand of the reciprocity of Stacks 0EAX,
formed at `Localization.AtPrime 𝔮`, becomes a summand formed at the local ring of the
intermediate point, which is where the first differential of Stacks 0GU9 forms it. -/
def stalkLocalizationAtPrimeEquiv (x'' : W)
    (q : {q : Ideal ↥(W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    letI : q.1.IsPrime := q.2.1
    Localization.AtPrime q.1 ≃+*
      ↥(W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q)) :=
  letI : q.1.IsPrime := q.2.1
  letI : Algebra ↥(W.presheaf.stalk x'')
      ↥(W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q)) :=
    (W.presheaf.stalkSpecializes
      (specializes_intermediatePointOfHeightOnePrime x'' q)).hom.toAlgebra
  have _ := isLocalization_stalk_heightOnePrime x'' q
  (IsLocalization.algEquiv q.1.primeCompl (Localization.AtPrime q.1)
    ↥(W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q))).toRingEquiv

/-- **The identification of localizations is one over `𝒪_{W, x''}`.** The image of a germ at
`x''` in the canonical localization goes to its specialization to a germ at the intermediate
point, so the identification is the canonical one and may be used to transport the tame symbol of
Stacks 02Q1. -/
theorem stalkLocalizationAtPrimeEquiv_algebraMap (x'' : W)
    (q : {q : Ideal ↥(W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1})
    (a : ↥(W.presheaf.stalk x'')) :
    letI : q.1.IsPrime := q.2.1
    stalkLocalizationAtPrimeEquiv x'' q
        (algebraMap ↥(W.presheaf.stalk x'') (Localization.AtPrime q.1) a) =
      (W.presheaf.stalkSpecializes
        (specializes_intermediatePointOfHeightOnePrime x'' q)).hom a := by
  have _ : q.1.IsPrime := q.2.1
  let _ : Algebra ↥(W.presheaf.stalk x'')
      ↥(W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q)) :=
    (W.presheaf.stalkSpecializes
      (specializes_intermediatePointOfHeightOnePrime x'' q)).hom.toAlgebra
  have _ := isLocalization_stalk_heightOnePrime x'' q
  exact (IsLocalization.algEquiv q.1.primeCompl (Localization.AtPrime q.1)
    ↥(W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q))).commutes a

end StalkLocalization

end Stacks.Chow

end
