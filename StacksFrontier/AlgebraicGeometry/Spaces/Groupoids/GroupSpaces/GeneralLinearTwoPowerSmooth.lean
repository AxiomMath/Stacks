module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOverField
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothAffineRationalPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `m`-th power of `GL₂` is smooth

The coordinate ring of `(GL₂)^m` over a commutative ring `k` is the polynomial ring on the `4m`
entries of `m` generic two-by-two matrices with the product of their determinants inverted, so
`(GL₂)^m` is the basic open `D(∏ det)` of affine `4m`-space over `k`. A basic open of affine
space is a smooth algebra over the base, so the structure morphism `(GL₂)^m → Spec k` is smooth
for an **arbitrary** base, in particular for an arbitrary field with no assumption on its
characteristic and no perfection assumption.

Over a field the product of the generic determinants is a nonzero polynomial — it specializes to
`1` at the `m`-tuple of identity matrices — so the coordinate ring is a domain: `(GL₂)^m` is an
integral, hence irreducible, scheme and a variety over `k`, and the `m`-tuple of identity
matrices is a rational point at which the structure morphism is smooth, so it is geometrically
integral. Over an infinite field the `k`-rational points are dense.

Read on the big fppf site over `Spec k`, this makes the object `(GL₂)^m` of the site a smooth
algebraic space over the base, so that the density statement of [Stacks, Tag 07W4] applies to it.

## Main definitions

* `AlgebraicGeometry.generalLinearTwoPowerIdentityPoint`: the `k`-rational point of `(GL₂)^m`
  given by the `m`-tuple of identity matrices.

## Main results

* `AlgebraicGeometry.smooth_Spec_map_generalLinearTwoPowerStructureMap`: **`(GL₂)^m` is smooth
  over `Spec k`**, for an arbitrary commutative base ring `k`.
* `AlgebraicGeometry.prod_genericTwoPowerDeterminant_ne_zero`: over a field the product of the
  `m` generic determinants is a nonzero polynomial.
* `AlgebraicGeometry.isDomain_generalLinearTwoPowerCoordinateRing`,
  `AlgebraicGeometry.irreducibleSpace_generalLinearTwoPowerScheme` and
  `AlgebraicGeometry.isIntegral_generalLinearTwoPowerScheme`: over a field `(GL₂)^m` is
  irreducible and integral.
* `AlgebraicGeometry.isVariety_generalLinearTwoPowerStructureMap` and
  `AlgebraicGeometry.geometricallyIntegral_generalLinearTwoPowerStructureMap`: over a field
  `(GL₂)^m` is a geometrically integral variety.
* `AlgebraicGeometry.dense_rationalPoints_generalLinearTwoPowerScheme`: over an infinite field
  the `k`-rational points of `(GL₂)^m` are dense.
* `AlgebraicGeometry.Space.isSmooth_generalLinearTwoPowerSiteObject`: the structure morphism of
  the site object `(GL₂)^m` is a smooth morphism of algebraic spaces over `Spec k`.
* `AlgebraicGeometry.Space.dense_rationalPoints_points_generalLinearTwoPower`: over an infinite
  field the `k`-rational points are dense in the point space of the algebraic space `(GL₂)^m`.
* `AlgebraicGeometry.Space.dense_setOf_class_finiteSeparable_generalLinearTwoPower`: over any
  field the points of `(GL₂)^m` represented by a finite separable extension of `k` are dense —
  Tag 07W4 applied to it.

## Implementation notes

Smoothness comes from
`AlgebraicGeometry.smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial` with the index
type `Fin m × Fin 2 × Fin 2` of the `4m` matrix entries and the product of the generic
determinants as the inverted element. Nothing about that product is used, so no hypothesis on `k`
appears; it is only for the statements over a field that the product has to be nonzero, which is
read off the evaluation homomorphism at the identity matrices through
`AlgebraicGeometry.isUnit_genericTwoPowerEval_prod`.

The rational point is `AlgebraicGeometry.generalLinearTwoPowerPoint` at the `m`-tuple of identity
matrices, upgraded to a homomorphism of `k`-algebras by
`AlgebraicGeometry.generalLinearTwoPowerPoint_comp_algebraMap`.

At the level of the site, smoothness of the morphism of algebraic spaces represented by the
structure morphism of the site object is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map` for the étale-local property
`AlgebraicGeometry.Smooth` of Tag 04R3: a representable morphism whose underlying morphism of
schemes is smooth satisfies the every-chart condition of Tag 03MJ. Density transfers from the
scheme to the point space of the represented algebraic space along the homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph` of clause (1) of Tag 03BX.

## References

* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 07W4](https://stacks.math.columbia.edu/tag/07W4)
* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

@[expose] public noncomputable section

open CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

section Base

variable (k : Type u) [CommRing k] (m : ℕ)

/-- **The coordinate ring of `(GL₂)^m` is a smooth `k`-algebra.** It is the polynomial ring on
the `4m` entries of `m` generic two-by-two matrices with one element inverted, that is a basic
open of affine `4m`-space over `k`. -/
theorem smooth_generalLinearTwoPowerCoordinateRing :
    Algebra.Smooth k (generalLinearTwoPowerCoordinateRing k m) :=
  smooth_of_isLocalization_away_mvPolynomial k
    (∏ i : Fin m, genericTwoPowerDeterminant k m i) (generalLinearTwoPowerCoordinateRing k m)

/-- **`(GL₂)^m` is smooth over `Spec k`.** Its coordinate ring is a localization of the
polynomial ring on the `4m` matrix entries away from the product of the `m` generic
determinants, so `(GL₂)^m` is a basic open of affine `4m`-space over `k`, and a basic open of
affine space is smooth over the base. No assumption on `k` is involved: in particular, for `k` a
field there is no assumption on the characteristic and no perfection assumption. -/
@[sga "3 XX 5.1" "special case"]
theorem smooth_Spec_map_generalLinearTwoPowerStructureMap :
    Smooth (Spec.map (generalLinearTwoPowerStructureMap k m)) :=
  smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial k
    (∏ i : Fin m, genericTwoPowerDeterminant k m i) (generalLinearTwoPowerCoordinateRing k m)

/-- The `k`-rational point of `(GL₂)^m` given by the `m`-tuple of identity matrices, as a
homomorphism of `k`-algebras from the coordinate ring to `k`. -/
def generalLinearTwoPowerIdentityPoint :
    generalLinearTwoPowerCoordinateRing k m →ₐ[k] k where
  __ := generalLinearTwoPowerPoint k m 1
  commutes' r := by
    simpa using RingHom.congr_fun (generalLinearTwoPowerPoint_comp_algebraMap k m 1) r

end Base

section Field

variable (k : Type u) [Field k] (m : ℕ)

/-- **Over a field the product of the `m` generic determinants is a nonzero polynomial.** It
specializes, at the `m`-tuple of identity matrices, to a unit of `k`. -/
theorem prod_genericTwoPowerDeterminant_ne_zero :
    (∏ i : Fin m, genericTwoPowerDeterminant k m i) ≠ 0 := by
  intro hzero
  have hunit := isUnit_genericTwoPowerEval_prod k m 1
  rw [hzero, map_zero] at hunit
  exact zero_ne_one (isUnit_zero_iff.mp hunit)

/-- **Over a field the coordinate ring of `(GL₂)^m` is a domain.** It is a localization of the
polynomial ring on the `4m` matrix entries away from a nonzero polynomial. -/
@[sga "3 XX 5.1" "special case"]
theorem isDomain_generalLinearTwoPowerCoordinateRing :
    IsDomain (generalLinearTwoPowerCoordinateRing k m) :=
  Localization.Away.isDomain (prod_genericTwoPowerDeterminant_ne_zero k m)

/-- **Over a field `(GL₂)^m` is irreducible.** Its coordinate ring is a domain, so the zero
ideal is prime and is contained in every prime. -/
theorem irreducibleSpace_generalLinearTwoPowerScheme :
    IrreducibleSpace (Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m))) :=
  letI := isDomain_generalLinearTwoPowerCoordinateRing k m
  inferInstanceAs
    (IrreducibleSpace (PrimeSpectrum (generalLinearTwoPowerCoordinateRing k m)))

/-- **Over a field `(GL₂)^m` is an integral scheme.** Its coordinate ring is a domain. -/
theorem isIntegral_generalLinearTwoPowerScheme :
    IsIntegral (Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m))) :=
  letI := isDomain_generalLinearTwoPowerCoordinateRing k m
  inferInstance

/-- **Over a field `(GL₂)^m` is a variety.** It is integral, and its structure morphism is a
morphism of affine schemes which is smooth, hence separated, quasi-compact and locally of finite
type. -/
@[sga "3 XX 5.1" "special case"]
theorem isVariety_generalLinearTwoPowerStructureMap :
    IsVariety k (Spec.map (generalLinearTwoPowerStructureMap k m)) :=
  letI := isDomain_generalLinearTwoPowerCoordinateRing k m
  letI := smooth_generalLinearTwoPowerCoordinateRing k m
  isVariety_Spec_map_algebraMap k (generalLinearTwoPowerCoordinateRing k m)

/-- **Over a field `(GL₂)^m` is geometrically integral.** It is a smooth variety with the
`m`-tuple of identity matrices as a rational point, so Tag 0CDW applies. -/
theorem geometricallyIntegral_generalLinearTwoPowerStructureMap :
    GeometricallyIntegral (Spec.map (generalLinearTwoPowerStructureMap k m)) :=
  letI := isDomain_generalLinearTwoPowerCoordinateRing k m
  letI := smooth_generalLinearTwoPowerCoordinateRing k m
  geometricallyIntegral_Spec_map_algebraMap_of_rationalPoint k
    (generalLinearTwoPowerCoordinateRing k m) (generalLinearTwoPowerIdentityPoint k m)

/-- **Over an infinite field the `k`-rational points of `(GL₂)^m` are dense.** A `k`-rational
point is a section of the structure morphism; such sections are exactly the `m`-tuples of
invertible matrices over `k`, and they are dense because a nonzero polynomial on affine
`4m`-space over an infinite field has a nonvanishing point. -/
theorem dense_rationalPoints_generalLinearTwoPowerScheme [Infinite k] :
    Dense {x : Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m)) |
      ∃ s : Spec (CommRingCat.of k) ⟶
          Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m)),
        s ≫ Spec.map (generalLinearTwoPowerStructureMap k m) = 𝟙 _ ∧ x ∈ Set.range s.base} :=
  dense_rationalPoints_Spec_of_isLocalization_away_mvPolynomial k
    (prod_genericTwoPowerDeterminant_ne_zero k m)
    (generalLinearTwoPowerCoordinateRing k m)

end Field

/-! ### On the big fppf site over the base -/

namespace Space

attribute [local instance] pointTopology

variable (k : Type u) [CommRing k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)

/-- The structure morphism of the site object `(GL₂)^m` to the terminal object of the big fppf
category over `Spec k`. -/
abbrev generalLinearTwoPowerSiteStructure :
    generalLinearTwoPowerSiteObject k B hk m ⟶
      (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
  Over.homMk (generalLinearTwoPowerSiteObject k B hk m).hom (by simp)

/-- **The structure morphism of the site object `(GL₂)^m` is a smooth morphism of algebraic
spaces over `Spec k`.** Smoothness of morphisms of schemes is étale local on the source and the
target, so a representable morphism whose underlying morphism of schemes is smooth satisfies the
every-chart condition of Tag 03MJ; and the morphism of schemes underlying the structure morphism
of the site object is `Spec` of the structure map of the coordinate ring. -/
@[sga "3 XX 5.1" "special case"]
theorem isSmooth_generalLinearTwoPowerSiteObject :
    IsSmooth B (Spec (CommRingCat.of k)) hk
      (yoneda.map (generalLinearTwoPowerSiteStructure k B hk m)) :=
  holdsOnEveryEtaleChart_yoneda_map B (Spec (CommRingCat.of k)) hk
    Smooth.isEtaleLocalOnSourceAndTarget (generalLinearTwoPowerSiteStructure k B hk m)
    (smooth_Spec_map_generalLinearTwoPowerStructureMap k m)

/-- **Over an infinite field the `k`-rational points of `(GL₂)^m` are dense in the point space
of the algebraic space it represents.** The points of a represented presheaf are homeomorphic to
the points of the representing scheme by clause (1) of Tag 03BX, so this is the scheme-level
density statement read through that homeomorphism. -/
theorem dense_rationalPoints_points_generalLinearTwoPower {k : Type u} [Field k] [Infinite k]
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ) :
    Dense (schemePointsHomeomorph B (Spec (CommRingCat.of k)) hk
        (generalLinearTwoPowerSiteObject k B hk m) ⁻¹'
      {x : Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m)) |
        ∃ s : Spec (CommRingCat.of k) ⟶
            Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m)),
          s ≫ Spec.map (generalLinearTwoPowerStructureMap k m) = 𝟙 _ ∧
            x ∈ Set.range s.base}) := by
  rw [(schemePointsHomeomorph B (Spec (CommRingCat.of k)) hk
    (generalLinearTwoPowerSiteObject k B hk m)).isOpenQuotientMap.dense_preimage_iff]
  exact dense_rationalPoints_generalLinearTwoPowerScheme k m

/-- **Over any field the points of `(GL₂)^m` represented by a finite separable extension of `k`
are dense**: Tag 07W4 for the smooth algebraic space `(GL₂)^m`. Over an infinite field
`AlgebraicGeometry.Space.dense_rationalPoints_points_generalLinearTwoPower` is stronger, but over
a finite field the `k`-rational points are a finite set and this is the statement that holds. -/
theorem dense_setOf_class_finiteSeparable_generalLinearTwoPower {k : Type u} [Field k]
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ) :
    Dense {x : points B (Spec (CommRingCat.of k)) hk
        (yoneda.obj (generalLinearTwoPowerSiteObject k B hk m)) |
      ∃ p : FieldValuedPoint B (Spec (CommRingCat.of k)) hk
          (yoneda.obj (generalLinearTwoPowerSiteObject k B hk m)),
        p.class B (Spec (CommRingCat.of k)) hk
            (yoneda.obj (generalLinearTwoPowerSiteObject k B hk m)) = x ∧
          ∃ alg : Algebra k p.carrier,
            letI := alg
            Module.Finite k p.carrier ∧ Algebra.IsSeparable k p.carrier ∧
              p.toBase = Spec.map (CommRingCat.ofHom (algebraMap k p.carrier))} :=
  dense_setOf_class_finiteSeparable_of_isSmooth k B hk
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk
      (generalLinearTwoPowerSiteObject k B hk m))
    (yoneda.map (generalLinearTwoPowerSiteStructure k B hk m))
    (isSmooth_generalLinearTwoPowerSiteObject k B hk m)

end Space

end AlgebraicGeometry

end
