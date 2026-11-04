module

public import StacksFrontier.Cotangent.ProductDecompositionSplittingElement
public import StacksFrontier.Cotangent.RestrictedCotangentDescent

/-!
# Tag 08SC over an arbitrary base

[Stacks, Tag 08SC] says that for ring maps `A → B` and `A → C` the canonical map

`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}`

of `CommAlgCat.cotangentComplexProductMap` is an isomorphism in `D(B × C)`. This file proves it,
over an arbitrary base.

The proof is the source's. Factor `A → B × C` through the polynomial ring,
`A → A[x] → B × C` with `x ↦ (1, 0)`. Over the base `A[x]` the lemma holds outright, by
`CommAlgCat.quasiIso_cotangentComplexProductMap_of_splittingElement`: inverting `x` kills the
`C` factor and inverting `1 - x` kills the `B` factor, so [Stacks, Tag 08QQ] applies twice. The
step from the base `A[x]` down to the base `A` is the comparison of the three distinguished
triangles of [Stacks, Tag 08SA] for `B × C`, for `B` and for `C`, which is
`CommAlgCat.quasiIso_cotangentExtendScalars_restrictedTopSquare` of
`StacksFrontier/Cotangent/RestrictedCotangentDescent.lean`, applied to each of the two projections:
each projection is flat, the sequences are short exact, the first vertical is an isomorphism by
cancellation of base change and the third is the statement over `A[x]`, so the five lemma
inverts the middle one.

## Main results

* `CommAlgCat.quasiIso_cotangentComplexProductMap_of_tower`: the canonical map is a
  quasi-isomorphism whenever the base `A` admits a polynomial extension `A → R` over which `B`
  and `C` are algebras carrying a splitting element. This is the shape in which the two halves of
  the argument meet.
* `CommAlgCat.quasiIso_cotangentComplexProductMap`: **[Stacks, Tag 08SC] at chain level**, over an
  arbitrary base: the canonical map is a quasi-isomorphism.
* `CommAlgCat.isIso_Q_map_cotangentComplexProductMap`: **[Stacks, Tag 08SC]**, as the statement
  that the canonical map is an isomorphism in `D(B × C)`.

## Implementation notes

The `A`-algebra structures on `B` and `C` are *equal* to the composites `A → A[x] → B` and
`A → A[x] → C`, two algebra structures with the same structure map being equal
(`Algebra.algebra_ext`), so the general statement may be read for the structures that restriction
of scalars along `A → A[x]` produces, which is the form
`CommAlgCat.restrictedBase` — and hence the whole of
`StacksFrontier/Cotangent/RestrictedCotangentDescent.lean` — is written for. This is the same device
`CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex` uses.

The three rings are taken in one universe, which is no restriction: three rings with maps between
them always live in a common universe.

## References

* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-- An algebra structure through which `A → R → B` factors is the restriction along `A → R`. -/
private theorem algebra_compHom_eq_of_isScalarTower (A R B : Type u) [CommRing A] [CommRing R]
    [CommRing B] [Algebra A R] [Algebra R B] [inst : Algebra A B] [IsScalarTower A R B] :
    Algebra.compHom B (algebraMap A R) = inst :=
  Algebra.algebra_ext _ _ fun a => (IsScalarTower.algebraMap_apply A R B a).symm

/-- The `A[x]`-algebra structure on `B` evaluating `x` at `b` is compatible with `A → B`. -/
private theorem isScalarTower_polynomial_aeval (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (b : B) :
    letI : Algebra (Polynomial A) B := (Polynomial.aeval b).toRingHom.toAlgebra
    IsScalarTower A (Polynomial A) B :=
  letI : Algebra (Polynomial A) B := (Polynomial.aeval b).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun a => (Polynomial.aeval_C b a).symm

/-- **The canonical map of [Stacks, Tag 08SC] is a quasi-isomorphism when the base is extended by
a polynomial algebra carrying a splitting element.** Let `A → R` be a polynomial algebra, let `B`
and `C` be `R`-algebras whose `A`-algebra structures factor through `R`, and let `x : R` have
image `1` in `B` and `0` in `C`. Then

`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}`

is a quasi-isomorphism.

Both components are handled by
`CommAlgCat.quasiIso_cotangentExtendScalars_restrictedTopSquare`, which descends them from the
base `R` to the base `A`; over `R` they are
`CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare` at `x` and
`CommAlgCat.quasiIso_cotangentExtendScalars_productSndSquare` at `1 - x`. The two projections of
`B × C` are flat (`RingHom.flat_fst`, `RingHom.flat_snd`), which is what makes the base change of
the sequence of [Stacks, Tag 08SA] along them exact. -/
theorem quasiIso_cotangentComplexProductMap_of_tower (A : Type u) [CommRing A]
    (R : Type u) [CommRing R] [Algebra A R] (hR : Algebra.IsPolynomialAlgebra A R)
    (B C : Type u) [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    [instB : Algebra A B] [instC : Algebra A C]
    [IsScalarTower A R B] [IsScalarTower A R C]
    (x : R) (hB : algebraMap R B x = 1) (hC : algebraMap R C x = 0) :
    QuasiIso (cotangentComplexProductMap.{u, u} A (CommAlgCat.of A B) (CommAlgCat.of A C)) := by
  have hiB := algebra_compHom_eq_of_isScalarTower A R B
  have hiC := algebra_compHom_eq_of_isScalarTower A R C
  subst hiB
  subst hiC
  let : Algebra A B := Algebra.compHom B (algebraMap A R)
  let : Algebra A C := Algebra.compHom C (algebraMap A R)
  have hxB : IsUnit (algebraMap R B x) := hB ▸ isUnit_one
  have hyB : algebraMap R B (1 - x) = 0 := by rw [map_sub, map_one, hB, sub_self]
  have hyC : algebraMap R C (1 - x) = 1 := by rw [map_sub, map_one, hC, sub_zero]
  have hyC' : IsUnit (algebraMap R C (1 - x)) := hyC ▸ isUnit_one
  let : Algebra (Localization.Away x) B :=
    IsLocalization.awayAlgebraOfIsUnit (Localization.Away x) hxB
  have : IsScalarTower R (Localization.Away x) B :=
    IsLocalization.isScalarTower_awayAlgebraOfIsUnit (Localization.Away x) hxB
  let : Algebra (Localization.Away (1 - x)) C :=
    IsLocalization.awayAlgebraOfIsUnit (Localization.Away (1 - x)) hyC'
  have : IsScalarTower R (Localization.Away (1 - x)) C :=
    IsLocalization.isScalarTower_awayAlgebraOfIsUnit (Localization.Away (1 - x)) hyC'
  refine quasiIso_cotangentComplexProductMap_of_components_counit.{u, u} A
    (CommAlgCat.of A B) (CommAlgCat.of A C) ?_ ?_
  · exact quasiIso_cotangentExtendScalars_restrictedTopSquare A R (AlgHom.fst R B C) hR
      (RingHom.flat_fst B C)
      (quasiIso_cotangentExtendScalars_productFstSquare (Localization.Away x)
        (CommAlgCat.of R B) (CommAlgCat.of R C) hB hC)
  · exact quasiIso_cotangentExtendScalars_restrictedTopSquare A R (AlgHom.snd R B C) hR
      (RingHom.flat_snd B C)
      (quasiIso_cotangentExtendScalars_productSndSquare (Localization.Away (1 - x))
        (CommAlgCat.of R B) (CommAlgCat.of R C) hyB hyC)

/-- **[Stacks, Tag 08SC] at chain level, over an arbitrary base.** For ring maps `A → B` and
`A → C` the canonical map

`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}`

of `CommAlgCat.cotangentComplexProductMap` is a quasi-isomorphism of complexes of
`B × C`-modules.

The base is extended to `A[x]`, over which `x ↦ (1, 0)` is a splitting element, and
`CommAlgCat.quasiIso_cotangentComplexProductMap_of_tower` applies: the `A[x]`-algebra structures
are `Polynomial.aeval 1` on `B` and `Polynomial.aeval 0` on `C`, whose composites with
`A → A[x]` are the given `A`-algebra structures. -/
theorem quasiIso_cotangentComplexProductMap (A : Type u) [CommRing A] (B C : CommAlgCat.{u} A) :
    QuasiIso (cotangentComplexProductMap.{u, u} A B C) := by
  let : Algebra (Polynomial A) (B : Type u) :=
    (Polynomial.aeval (1 : (B : Type u))).toRingHom.toAlgebra
  let : Algebra (Polynomial A) (C : Type u) :=
    (Polynomial.aeval (0 : (C : Type u))).toRingHom.toAlgebra
  have : IsScalarTower A (Polynomial A) (B : Type u) :=
    isScalarTower_polynomial_aeval A B 1
  have : IsScalarTower A (Polynomial A) (C : Type u) :=
    isScalarTower_polynomial_aeval A C 0
  refine quasiIso_cotangentComplexProductMap_of_tower A (Polynomial A)
    (Algebra.isPolynomialAlgebra_polynomial A) (B : Type u) (C : Type u) Polynomial.X ?_ ?_
  · rw [RingHom.algebraMap_toAlgebra]
    exact Polynomial.aeval_X (1 : (B : Type u))
  · rw [RingHom.algebraMap_toAlgebra]
    exact Polynomial.aeval_X (0 : (C : Type u))

/-- **Stacks Project, Tag 08SC.** Let `A → B` and `A → C` be ring maps. Then the canonical map

`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}`

is an isomorphism in `D(B × C)`.

The map is `CommAlgCat.cotangentComplexProductMap`, the pair of the functoriality maps of
[Stacks, Tag 08PN] for the two projections; it is a quasi-isomorphism by
`CommAlgCat.quasiIso_cotangentComplexProductMap`, and the localization `DerivedCategory.Q`
inverts exactly the quasi-isomorphisms. -/
@[stacks 08SC "the lemma: for ring maps `A → B` and `A → C` the canonical map \
  `L_{B×C/A} → L_{B/A} ⊕ L_{C/A}` -- the pair of the functoriality maps of the two projections, \
  `CommAlgCat.cotangentComplexProductMap` -- is an isomorphism in `D(B × C)`, over an arbitrary \
  base `A`. The chain-level form, that the map is a quasi-isomorphism, is \
  `CommAlgCat.quasiIso_cotangentComplexProductMap`"]
theorem isIso_Q_map_cotangentComplexProductMap (A : Type u) [CommRing A]
    (B C : CommAlgCat.{u} A) :
    IsIso (DerivedCategory.Q.map (cotangentComplexProductMap.{u, u} A B C)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (cotangentComplexProductMap.{u, u} A B C)).2
    (quasiIso_cotangentComplexProductMap A B C)

end CommAlgCat

end
