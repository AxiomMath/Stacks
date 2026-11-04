module

public import Mathlib.Algebra.Algebra.Prod
public import StacksFrontier.Cotangent.BaseChangeCompositionCounit
public import StacksFrontier.Cotangent.BaseChangeQuasiIsoUnconditional
public import StacksFrontier.Cotangent.ProductDecompositionCriterion
public import StacksFrontier.Cotangent.ProductDecompositionLocalization

/-!
# Tag 08SC over a base carrying a splitting element

[Stacks, Tag 08SC] says that for ring maps `A → B` and `A → C` the canonical map

`L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}`

of `CommAlgCat.cotangentComplexProductMap` is a quasi-isomorphism. Over a base `R` which carries
an element `x` of image `1` in `B` and image `0` in `C` this file proves it outright. The source's
proof reduces the general case to the base `A[x]`, where `x ↦ (1, 0)` provides exactly such an
element; `CommAlgCat.quasiIso_cotangentComplexProductMap_polynomialBase` is that case. The step
from the base `A[x]` down to the base `A` is **not** in this file; the implementation notes of
`StacksFrontier/Cotangent/ProductDecomposition.lean` record what it still wants.

The argument. By `CommAlgCat.quasiIso_cotangentComplexProductMap_of_components_counit` it is
enough to invert the two component maps

`L_{B×C/R} ⊗_{B×C} B ⟶ L_{B/R}` and `L_{B×C/R} ⊗_{B×C} C ⟶ L_{C/R}`,

each written in the adjoint shape which [Stacks, Tag 08QQ] inverts. The first is handled by the
splitting element `x`, the second by its mirror `1 - x`, whose image is the complementary
idempotent `(0, 1)`. Fix the first. Writing `R' = R[1/x]`, the first projection factors as a
composite of two squares

```
R  ---→  R'  ===  R'
|         |        |
B × C --→  B  ===  B
```

whose left half is the localization square of
`StacksFrontier/Cotangent/ProductDecompositionLocalization.lean` and whose right half has the
identity of `B` on top. Tag 08QQ applies to the outer square — `B` is the localization of `B × C`
at the idempotent `(1, 0)`, so the square is a pushout, and `R → R'` is flat — and to the right
half, where it is a pushout because `x` acts on `B` as `1` and is therefore already invertible
there. `CommAlgCat.quasiIso_squareCotangentComplexMap_counit_of_comp` turns those two instances
into the component statement for the left half, which is the first projection.

## Main results

* `CommAlgCat.quasiIso_squareCotangentComplexMap_away_of_isUnit`: the `D`-linear functoriality
  map `L_{D/R} ⟶ L_{D/R[1/x]}` of the square `(R → R[1/x], D → D)` is a quasi-isomorphism when
  `x` is already a unit in `D`. This is Tag 08QQ at a square whose top map is the identity, with
  the extension of scalars along that identity removed by
  `ModuleCat.quasiIso_of_quasiIso_extendScalars_id`.
* `CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare` and
  `CommAlgCat.quasiIso_cotangentExtendScalars_productSndSquare`: **the two components of the
  canonical map of Tag 08SC**, in the adjoint shape, for a base carrying a splitting element.
* `CommAlgCat.quasiIso_cotangentComplexProductMap_of_splittingElement`: **[Stacks, Tag 08SC] over
  a base carrying a splitting element.**
* `CommAlgCat.quasiIso_cotangentComplexProductMap_polynomialBase`: **[Stacks, Tag 08SC] over the
  base `A[x]`**, for `A`-algebras `B` and `C` read over `A[x]` through `x ↦ 1` and `x ↦ 0`.
* `Polynomial.aeval_prodMk`: the `A[x]`-algebra structure `x ↦ (b, c)` on a product is the
  product of the structures `x ↦ b` and `x ↦ c`, so that the product `A[x]`-algebra structure on
  `B × C` is the one Tag 08SC's proof uses.

## Implementation notes

The composite of the two squares above is *definitionally* the localization square of the first
projection: `CommAlgCat.AlgebraSquare.comp` composes the base maps and the algebra maps with
`RingHom.comp`, and composing with an identity on either side changes nothing up to the
structure eta of `RingHom`. Likewise `ModuleCat.restrictScalars` along the identity leaves a
complex alone, since `Module.compHom M (RingHom.id _)` is the module structure of `M` again. So
the hypothesis of `CommAlgCat.quasiIso_squareCotangentComplexMap_counit_of_comp` at these two
squares is definitionally what Tag 08QQ produces at the localization square of the projection,
and the two are crossed by `exact`, which elaborates at default transparency. No `rw` is asked to
build a motive mixing the spellings; that is what the implementation notes of
`StacksFrontier/Cotangent/BaseChangeComplexCounit.lean` and
`StacksFrontier/Cotangent/BaseChangeCompositionCounit.lean` warn against.

Nothing here mentions a polynomial ring until the last two results: the content is the splitting
element, and `A[x]` only supplies one.

## References

* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Polynomial

/-- **The product `A[x]`-algebra structure.** Sending `x` to a pair is the pair of the two
structures sending `x` to its components. For `[Stacks, Tag 08SC]` over the base `A[x]` this says
that the `A[x]`-algebra structure `x ↦ (1, 0)` on `B × C`, which the source's proof uses, is the
*product* of the structures `x ↦ 1` on `B` and `x ↦ 0` on `C` — so that the `A[x]`-algebra
`B × C` is the product of the `A[x]`-algebras `B` and `C`, as the statement of Tag 08SC needs. -/
theorem aeval_prodMk {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (b : B) (c : C) :
    Polynomial.aeval (R := A) ((b, c) : B × C) =
      (Polynomial.aeval (R := A) b).prod (Polynomial.aeval (R := A) c) :=
  Polynomial.algHom_ext (by simp)

end Polynomial

namespace CommAlgCat

variable {R : Type u} [CommRing R] {x : R} (R' : Type u) [CommRing R'] [Algebra R R']
  [IsLocalization.Away x R']

/-- **Tag 08QQ at a square whose top map is the identity.** If `x` is already a unit in `D` then
the `D`-linear functoriality map `L_{D/R} ⟶ L_{D/R[1/x]}` of [Stacks, Tag 08PN] for the square

```
R  ---→  R[1/x]
|          |
D  ===    D
```

is a quasi-isomorphism. The square is a pushout by `IsLocalization.isPushout_of_isUnit` and Tor
independent by `CommAlgCat.torIndependent_localization_away`, so [Stacks, Tag 08QQ] inverts the
*adjoint* map `L_{D/R} ⊗_D D ⟶ L_{D/R[1/x]}`; the counit is invertible because the identity is
surjective, and extension of scalars along the identity is then removed by
`ModuleCat.quasiIso_of_quasiIso_extendScalars_id`. -/
theorem quasiIso_squareCotangentComplexMap_away_of_isUnit (D : CommAlgCat.{u} R)
    [Algebra R' (D : Type u)] [IsScalarTower R R' (D : Type u)]
    (hx : IsUnit (algebraMap R (D : Type u) x)) :
    QuasiIso (squareCotangentComplexMap.{u, u, u}
      (algebraSquareOfAlgHom (B := D) (B' := CommAlgCat.of R' (D : Type u))
        (AlgHom.id R (D : Type u)))) := by
  have : Algebra.IsPushout R (D : Type u) R' (D : Type u) :=
    IsLocalization.isPushout_of_isUnit R' (D : Type u) hx
  have h := quasiIso_cotangentExtendScalarsComplexMap_unconditional
    (B := D) (B' := CommAlgCat.of R' (D : Type u)) (AlgHom.id R (D : Type u))
    (torIndependent_localization_away x R' (D : Type u))
    (bijective_baseChangeUnit_of_isPushout _ fun _ => rfl)
  rw [cotangentExtendScalarsComplexMap_eq_counit] at h
  have : IsIso (ModuleCat.extendRestrictScalarsAdjCounitComplex
      (AlgHom.id R (D : Type u)).toRingHom (ComplexShape.up ℤ)
      (cotangentComplex.{u, u} R' (CommAlgCat.of R' (D : Type u)))) :=
    ModuleCat.isIso_extendRestrictScalarsAdjCounitComplex _ _ (fun y => ⟨y, rfl⟩) _
  have h2 : QuasiIso (((ModuleCat.extendScalars (AlgHom.id R (D : Type u)).toRingHom
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (squareCotangentComplexMap.{u, u, u}
        (algebraSquareOfAlgHom (B := D) (B' := CommAlgCat.of R' (D : Type u))
          (AlgHom.id R (D : Type u))))) :=
    quasiIso_of_comp_right _ (ModuleCat.extendRestrictScalarsAdjCounitComplex
      (AlgHom.id R (D : Type u)).toRingHom (ComplexShape.up ℤ)
      (cotangentComplex.{u, u} R' (CommAlgCat.of R' (D : Type u)))) (hφφ' := h)
  exact ModuleCat.quasiIso_of_quasiIso_extendScalars_id _ h2

/-- The counit shape of Tag 08QQ for a quotient `E → D` of `R`-algebras which is a pushout along
`R → R[1/x]`, composed with the identity square `(R[1/x], D → D)` when `x` is a unit in `D`. -/
private theorem quasiIso_extendScalars_counit_of_isPushout_away (E D : CommAlgCat.{u} R)
    [Algebra R' (D : Type u)] [IsScalarTower R R' (D : Type u)]
    [Algebra (E : Type u) (D : Type u)] [IsScalarTower R (E : Type u) (D : Type u)]
    [Algebra.IsPushout R (E : Type u) R' (D : Type u)]
    (hx : IsUnit (algebraMap R (D : Type u) x)) :
    QuasiIso (((ModuleCat.extendScalars (algebraMap (E : Type u) (D : Type u))
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u}
            (⟨RingHom.id R, algebraMap (E : Type u) (D : Type u),
              fun r => (IsScalarTower.algebraMap_apply R (E : Type u) (D : Type u) r).symm⟩ :
              AlgebraSquare.{u, u, u} R R E D)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (algebraMap (E : Type u) (D : Type u))
          (ComplexShape.up ℤ) (cotangentComplex.{u, u} R D)) := by
  have h := quasiIso_cotangentExtendScalarsComplexMap_unconditional
    (B := E) (B' := CommAlgCat.of R' (D : Type u))
    (IsScalarTower.toAlgHom R (E : Type u) (D : Type u))
    (torIndependent_localization_away x R' (E : Type u))
    (bijective_baseChangeUnit_of_isPushout _ fun _ => rfl)
  rw [cotangentExtendScalarsComplexMap_eq_counit] at h
  exact quasiIso_squareCotangentComplexMap_counit_of_comp
    (⟨RingHom.id R, algebraMap (E : Type u) (D : Type u),
      fun r => (IsScalarTower.algebraMap_apply R (E : Type u) (D : Type u) r).symm⟩ :
      AlgebraSquare.{u, u, u} R R E D)
    (algebraSquareOfAlgHom (B := D) (B' := CommAlgCat.of R' (D : Type u))
      (AlgHom.id R (D : Type u))) h
    (quasiIso_squareCotangentComplexMap_away_of_isUnit R' D hx)

variable (B C : CommAlgCat.{u} R)

/-- **The first component of the canonical map of [Stacks, Tag 08SC], over a base carrying a
splitting element.** If `x : R` has image `1` in `B` and image `0` in `C` then the adjoint shape
`L_{B×C/R} ⊗_{B×C} B ⟶ L_{B/R}` of the functoriality map of the first projection is a
quasi-isomorphism.

The first projection is the composite of the localization square `(R → R[1/x], B × C → B)` and
the square `(R → R[1/x], B → B)`; [Stacks, Tag 08QQ] applies to both, by
`IsLocalization.isPushout_prod_fst` and `IsLocalization.isPushout_of_isUnit` respectively, and
`CommAlgCat.quasiIso_squareCotangentComplexMap_counit_of_comp` combines them. -/
theorem quasiIso_cotangentExtendScalars_productFstSquare
    [Algebra R' (B : Type u)] [IsScalarTower R R' (B : Type u)]
    (hB : algebraMap R (B : Type u) x = 1) (hC : algebraMap R (C : Type u) x = 0) :
    QuasiIso (((ModuleCat.extendScalars (productFstSquare.{u, u} R B C).map
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (productFstSquare.{u, u} R B C)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (productFstSquare.{u, u} R B C).map
          (ComplexShape.up ℤ) (cotangentComplex.{u, u} R B)) := by
  let : Algebra (B × C : Type u) (B : Type u) := (RingHom.fst _ _).toAlgebra
  have : IsScalarTower R (B × C : Type u) (B : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsPushout R (B × C : Type u) R' (B : Type u) :=
    IsLocalization.isPushout_prod_fst R' hB hC
  exact quasiIso_extendScalars_counit_of_isPushout_away R' (CommAlgCat.of R (B × C)) B
    (hB ▸ isUnit_one)

/-- **The second component of the canonical map of [Stacks, Tag 08SC], over a base carrying a
splitting element.** The mirror of
`CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare`: if `x : R` has image `0` in `B`
and image `1` in `C` then the adjoint shape `L_{B×C/R} ⊗_{B×C} C ⟶ L_{C/R}` of the functoriality
map of the second projection is a quasi-isomorphism. For the application it is used at the
element `1 - x`. -/
theorem quasiIso_cotangentExtendScalars_productSndSquare
    [Algebra R' (C : Type u)] [IsScalarTower R R' (C : Type u)]
    (hB : algebraMap R (B : Type u) x = 0) (hC : algebraMap R (C : Type u) x = 1) :
    QuasiIso (((ModuleCat.extendScalars (productSndSquare.{u, u} R B C).map
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (productSndSquare.{u, u} R B C)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (productSndSquare.{u, u} R B C).map
          (ComplexShape.up ℤ) (cotangentComplex.{u, u} R C)) := by
  let : Algebra (B × C : Type u) (C : Type u) := (RingHom.snd _ _).toAlgebra
  have : IsScalarTower R (B × C : Type u) (C : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsPushout R (B × C : Type u) R' (C : Type u) :=
    IsLocalization.isPushout_prod_snd R' hB hC
  exact quasiIso_extendScalars_counit_of_isPushout_away R' (CommAlgCat.of R (B × C)) C
    (hC ▸ isUnit_one)

section SplittingElement

variable {R : Type u} [CommRing R]

/-- **[Stacks, Tag 08SC] over a base carrying a splitting element.** Let `R → B` and `R → C` be
ring maps and let `x : R` have image `1` in `B` and image `0` in `C`. Then the canonical map

`L_{B×C/R} ⟶ L_{B/R} ⊕ L_{C/R}`

is a quasi-isomorphism.

The two components are `CommAlgCat.quasiIso_cotangentExtendScalars_productFstSquare` at `x` and
`CommAlgCat.quasiIso_cotangentExtendScalars_productSndSquare` at `1 - x`, whose image is `0` in
`B` and `1` in `C`; they are assembled by
`CommAlgCat.quasiIso_cotangentComplexProductMap_of_components_counit`. The two localizations
`R[1/x]` and `R[1/(1-x)]` are taken to be `Localization.Away`, and the `R[1/x]`-algebra structure
on `B` is `IsLocalization.awayAlgebraOfIsUnit`, `x` acting on `B` as the unit `1`.

This is **not** [Stacks, Tag 08SC], which is the statement over an arbitrary base; see the
implementation notes of `StacksFrontier/Cotangent/ProductDecomposition.lean`. -/
theorem quasiIso_cotangentComplexProductMap_of_splittingElement (B C : CommAlgCat.{u} R) (x : R)
    (hB : algebraMap R (B : Type u) x = 1) (hC : algebraMap R (C : Type u) x = 0) :
    QuasiIso (cotangentComplexProductMap.{u, u} R B C) := by
  have hxB : IsUnit (algebraMap R (B : Type u) x) := hB ▸ isUnit_one
  have hyB : algebraMap R (B : Type u) (1 - x) = 0 := by rw [map_sub, map_one, hB, sub_self]
  have hyC : algebraMap R (C : Type u) (1 - x) = 1 := by rw [map_sub, map_one, hC, sub_zero]
  have hyC' : IsUnit (algebraMap R (C : Type u) (1 - x)) := hyC ▸ isUnit_one
  let : Algebra (Localization.Away x) (B : Type u) :=
    IsLocalization.awayAlgebraOfIsUnit (Localization.Away x) hxB
  have : IsScalarTower R (Localization.Away x) (B : Type u) :=
    IsLocalization.isScalarTower_awayAlgebraOfIsUnit (Localization.Away x) hxB
  let : Algebra (Localization.Away (1 - x)) (C : Type u) :=
    IsLocalization.awayAlgebraOfIsUnit (Localization.Away (1 - x)) hyC'
  have : IsScalarTower R (Localization.Away (1 - x)) (C : Type u) :=
    IsLocalization.isScalarTower_awayAlgebraOfIsUnit (Localization.Away (1 - x)) hyC'
  exact quasiIso_cotangentComplexProductMap_of_components_counit.{u, u} R B C
    (quasiIso_cotangentExtendScalars_productFstSquare (Localization.Away x) B C hB hC)
    (quasiIso_cotangentExtendScalars_productSndSquare (Localization.Away (1 - x)) B C hyB hyC)

/-- **[Stacks, Tag 08SC] over the base `A[x]`.** For `A`-algebras `B` and `C`, read as
`A[x]`-algebras through `x ↦ 1` respectively `x ↦ 0`, the canonical map

`L_{B×C/A[x]} ⟶ L_{B/A[x]} ⊕ L_{C/A[x]}`

is a quasi-isomorphism. This is the base over which the source proves Tag 08SC before descending
to `A`: the element `x` of `A[x]` has image `1` in `B` and `0` in `C`, so its image in `B × C` is
the idempotent `(1, 0)` and
`CommAlgCat.quasiIso_cotangentComplexProductMap_of_splittingElement` applies. The product
`A[x]`-algebra structure on `B × C` is `Polynomial.aeval (1, 0)` by `Polynomial.aeval_prodMk`.

The descent from the base `A[x]` to the base `A`, which is what Tag 08SC asserts, is not proved;
the implementation notes of `StacksFrontier/Cotangent/ProductDecomposition.lean` say what it
wants. -/
theorem quasiIso_cotangentComplexProductMap_polynomialBase (A : Type u) [CommRing A]
    (B C : CommAlgCat.{u} A) :
    letI : Algebra (Polynomial A) (B : Type u) :=
      (Polynomial.aeval (1 : (B : Type u))).toRingHom.toAlgebra
    letI : Algebra (Polynomial A) (C : Type u) :=
      (Polynomial.aeval (0 : (C : Type u))).toRingHom.toAlgebra
    QuasiIso (cotangentComplexProductMap.{u, u} (Polynomial A)
      (CommAlgCat.of (Polynomial A) (B : Type u))
      (CommAlgCat.of (Polynomial A) (C : Type u))) := by
  let : Algebra (Polynomial A) (B : Type u) :=
    (Polynomial.aeval (1 : (B : Type u))).toRingHom.toAlgebra
  let : Algebra (Polynomial A) (C : Type u) :=
    (Polynomial.aeval (0 : (C : Type u))).toRingHom.toAlgebra
  refine quasiIso_cotangentComplexProductMap_of_splittingElement
    (CommAlgCat.of (Polynomial A) (B : Type u)) (CommAlgCat.of (Polynomial A) (C : Type u))
    Polynomial.X ?_ ?_
  · rw [RingHom.algebraMap_toAlgebra]
    exact Polynomial.aeval_X (1 : (B : Type u))
  · rw [RingHom.algebraMap_toAlgebra]
    exact Polynomial.aeval_X (0 : (C : Type u))

end SplittingElement

end CommAlgCat

end
