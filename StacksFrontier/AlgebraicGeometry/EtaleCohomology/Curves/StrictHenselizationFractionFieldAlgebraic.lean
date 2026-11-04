module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# The fraction field of a strict henselisation is algebraic over the function field

Let `A` be a normal local domain with fraction field `K`, let `κ ⊆ κ^sep` be a separable algebraic
closure of its residue field and let `A^sh` be a strict henselisation of `A` with respect to that
closure. Then `A^sh` is again a normal local domain, so it has a fraction field `K^sh`, and

`K^sh` is an algebraic extension of `K`.

A smooth curve over a field is integral and normal, so each of its local rings is a normal local
domain — a discrete valuation ring at a closed point, the function field itself at the generic
point — and the fraction field of the local ring of an integral scheme at any point is the
function field of that scheme. The last two statements below are therefore this fact for a curve,
phrased over `X.functionField` itself.

This is one of the two computations the proof of Stacks 03RJ makes on top of the strictly
henselian base case of Stacks 03Q9. The other — that the generic fibre
`Spec(𝒪^{sh}_{X,x̄} ⊗_A K)` of the strict henselisation *is* `Spec K^sh` — is independent of it,
and nothing here assumes it: the statements below are about the field `K^sh` directly, so the two
compose.

## Main results

* `AlgebraicGeometry.isAlgebraic_fractionField_of_isHenselization`: **the fraction field of a
  strict henselisation of a normal local domain is algebraic over the fraction field of the
  domain.**
* `AlgebraicGeometry.isAlgebraic_functionField_fractionField_of_isHenselization_stalk`: the same
  at a point of an integral normal scheme, where the fraction field of the local ring is the
  function field of the scheme.
* `AlgebraicGeometry.isAlgebraic_functionField_fractionField_of_isHenselization_stalk_of_smooth`:
  **the statement for a smooth curve**, the normality hypothesis discharged from smoothness over
  the field.

## Implementation notes

Both inputs are on hand. A strict henselisation is ind-étale over its base, and an ind-étale
algebra over a domain is algebraic over it, which is
`AlgebraicGeometry.isAlgebraic_of_isHenselization`; and a strict henselisation of a normal local
domain is a normal local domain, which is Stacks 06DI in the form
`AlgebraicGeometry.isDomain_and_isIntegrallyClosed_of_isHenselization`. A fraction field is
algebraic over its ring (`IsLocalization.isAlgebraic`), so `K^sh` is algebraic over `A` by
transitivity, and algebraicity over `A` upgrades to algebraicity over `K` by
`Algebra.IsAlgebraic.extendScalars` along the injection `A → K`. Normality of `A` is used only to
know that `A^sh` is a domain, which is what gives `K^sh` its meaning; the strict henselisation of
a non-normal local domain — the local ring of a node — need not be a domain at all.

**No `@[stacks]` attribute.** This is a component of the proof of Tag 03RJ, not one of the
assertions of a tag of its own.

## References

* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ): the theorem whose proof
  makes this computation.
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP): the strict henselisation
  as a filtered colimit of étale algebras, which is why it is algebraic over its base.
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI): normality of a local
  ring and of its strict henselisation are equivalent.
-/

@[expose] public section

open IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The fraction field of a strict henselisation of a normal local domain is algebraic over the
fraction field of that domain.**

Let `A` be a normal local domain with fraction field `K`, let `κ^sep` be a separable algebraic
closure of the residue field of `A` and let `Ash` be a strict henselisation of `A` with respect
to it. Then `Ash` is a normal local domain, and its fraction field `Ksh` is an algebraic
extension of `K`.

The strict henselisation is ind-étale over `A`, hence algebraic over `A`
(`AlgebraicGeometry.isAlgebraic_of_isHenselization`), and `Ksh` is algebraic over `Ash` because a
localisation is algebraic over the ring it localises; so `Ksh` is algebraic over `A`, and
algebraicity over `A` is algebraicity over `K` because `A → K` is injective. That `Ash` is a
domain at all — so that `Ksh` is its fraction field — is Stacks 06DI. -/
theorem isAlgebraic_fractionField_of_isHenselization
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (κsep : Type u) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A κsep Ash]
    (Ksh : Type u) [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra A Ksh] [IsScalarTower A Ash Ksh] [Algebra K Ksh] [IsScalarTower A K Ksh] :
    Algebra.IsAlgebraic K Ksh := by
  obtain ⟨hdom, -⟩ := isDomain_and_isIntegrallyClosed_of_isHenselization A Ash κsep
  have := hdom
  have : Algebra.IsAlgebraic A Ash := isAlgebraic_of_isHenselization A Ash κsep K
  have : Algebra.IsAlgebraic Ash Ksh := IsLocalization.isAlgebraic Ksh (nonZeroDivisors Ash)
  have : Algebra.IsAlgebraic A Ksh := Algebra.IsAlgebraic.trans A Ash Ksh
  exact Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective A K)

/-- **The fraction field of a strict henselisation of a local ring of an integral normal scheme is
algebraic over the function field of that scheme.**

The fraction field `K^sh` of the strict henselisation of `𝒪_{X,t}` is an algebraic extension of
the function field `K = k(X)`. A smooth curve over a field is integral and normal, so this
applies at every point of one; that specialisation is
`AlgebraicGeometry.isAlgebraic_functionField_fractionField_of_isHenselization_stalk_of_smooth`.

The local ring of an integral scheme at a point is a domain whose fraction field is the function
field of the scheme, and normality of the scheme makes that local ring integrally closed
(`AlgebraicGeometry.IsNormal.stalk_normal`); so this is
`AlgebraicGeometry.isAlgebraic_fractionField_of_isHenselization` at `A = 𝒪_{X,t}`. -/
theorem isAlgebraic_functionField_fractionField_of_isHenselization_stalk
    {X : Scheme.{u}} [IsIntegral X] [IsNormal X] (t : X)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField ↥(X.presheaf.stalk t)) κsep]
    [IsSepClosure (ResidueField ↥(X.presheaf.stalk t)) κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(X.presheaf.stalk t) Ash]
    [IsLocalRing.IsHenselization ↥(X.presheaf.stalk t) κsep Ash]
    (Ksh : Type u) [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra ↥(X.presheaf.stalk t) Ksh] [IsScalarTower ↥(X.presheaf.stalk t) Ash Ksh]
    [Algebra X.functionField Ksh]
    [IsScalarTower ↥(X.presheaf.stalk t) X.functionField Ksh] :
    Algebra.IsAlgebraic X.functionField Ksh :=
  have : IsIntegrallyClosed ↥(X.presheaf.stalk t) := IsNormal.stalk_normal t
  isAlgebraic_fractionField_of_isHenselization ↥(X.presheaf.stalk t) X.functionField κsep Ash Ksh

/-- **The fraction field of a strict henselisation of a local ring of a smooth curve is algebraic
over the function field of that curve.**

Only smoothness over the field is used, not the dimension: a smooth integral scheme over a field
is normal, because a field is a normal ring and normality ascends along a smooth morphism
(Stacks 033C, as `AlgebraicGeometry.isNormal_of_smooth`). A smooth curve over `k` is an integral
scheme smooth over `k`, so this is the statement for one, and it is
`AlgebraicGeometry.isAlgebraic_functionField_fractionField_of_isHenselization_stalk` with its
normality hypothesis discharged. -/
theorem isAlgebraic_functionField_fractionField_of_isHenselization_stalk_of_smooth
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (t : X)
    (κsep : Type u) [Field κsep] [Algebra (ResidueField ↥(X.presheaf.stalk t)) κsep]
    [IsSepClosure (ResidueField ↥(X.presheaf.stalk t)) κsep]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra ↥(X.presheaf.stalk t) Ash]
    [IsLocalRing.IsHenselization ↥(X.presheaf.stalk t) κsep Ash]
    (Ksh : Type u) [Field Ksh] [Algebra Ash Ksh] [IsFractionRing Ash Ksh]
    [Algebra ↥(X.presheaf.stalk t) Ksh] [IsScalarTower ↥(X.presheaf.stalk t) Ash Ksh]
    [Algebra X.functionField Ksh]
    [IsScalarTower ↥(X.presheaf.stalk t) X.functionField Ksh] :
    Algebra.IsAlgebraic X.functionField Ksh :=
  have : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_iff.mpr (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal X := isNormal_of_smooth f
  isAlgebraic_functionField_fractionField_of_isHenselization_stalk t κsep Ash Ksh

end AlgebraicGeometry

end
