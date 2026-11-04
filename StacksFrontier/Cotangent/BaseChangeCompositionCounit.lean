module

public import StacksFrontier.Cotangent.BaseChangeComplexCounit
public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestriction

/-!
# Composing the base-change functoriality maps of cotangent complexes

Two commutative squares of ring maps compose horizontally
(`CommAlgCat.AlgebraSquare.comp`), and the `B`-linear functoriality map of [Stacks, Tag 08PN] is
functorial for that composition: `CommAlgCat.squareCotangentComplexMap_comp` of
`StacksFrontier/Cotangent/SheavesOfRings/AffineCotangentRestriction.lean` says so in each
cohomological degree. This file records the same law as an equality of maps of complexes, and
then the law for the *adjoint* shape of the functoriality map — the shape
`L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` which [Stacks, Tag 08QQ] inverts.

## Main results

* `CommAlgCat.squareCotangentComplexMap_comp'`: the composition law of [Stacks, Tag 08PN] as an
  equality of maps of complexes of `B`-modules.
* `CommAlgCat.squareCotangentComplexMap_comp_counit`: **the composition law for the adjoint
  shape.** The map `L_{B/A} ⊗_B B' ⟶ L_{B''/A''}` of the composite square is the map
  `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of the first square followed by the `B`-linear map
  `L_{B'/A'} ⟶ L_{B''/A''}` of the second.
* `CommAlgCat.quasiIso_squareCotangentComplexMap_counit_of_comp`: **the composition law used.**
  If the adjoint map of the composite square is a quasi-isomorphism, and the `B'`-linear map of
  the second square is, then the adjoint map of the first square is. This is how one instance of
  [Stacks, Tag 08QQ] over a larger base and one over the smaller one combine into a component
  statement over the smaller base.
The second hypothesis of that last result -- that the `B'`-linear map of the second square is a
quasi-isomorphism -- is what [Stacks, Tag 08QQ] gives at a square whose top map is the identity,
once extension of scalars along the identity is removed by
`ModuleCat.quasiIso_of_quasiIso_extendScalars_id` of
`StacksFrontier/Cotangent/BaseChangeComplexCounit.lean`.

## Implementation notes

The adjoint shape of the functoriality map is `ModuleCat.extendScalars` of the `B`-linear map
followed by the counit of `ModuleCat.extendScalars ⊣ ModuleCat.restrictScalars`, which is
`CommAlgCat.cotangentExtendScalarsComplexMap_eq_counit`. So the composition law for the adjoint
shape is the composition law for the `B`-linear map together with the naturality of the counit,
and that is exactly how it is proved: there is no comparison between
`ModuleCat.extendScalars (sq'.map.comp sq.map)` and the iterated extension of scalars, because
the adjoint map of the composite square is taken along `sq.map` alone, its target being read
over `B'` along `sq'.map`.

Restriction of scalars does not change the underlying module, so
`ModuleCat.restrictScalars (sq'.map.comp sq.map)` and
`ModuleCat.restrictScalars sq.map ⋙ ModuleCat.restrictScalars sq'.map` agree definitionally, and
no comparison between them appears either. They are not *syntactically* equal, however, so the
proof is a chain of `Eq.trans`, `CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq`
terms rather than a sequence of rewrites: a `rw` whose motive mixes the two spellings is rejected
as ill-typed at `implicit` transparency.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe u

namespace CommAlgCat

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'} {B'' : CommAlgCat.{u} A''}

/-- **The map of cotangent complexes induced by a composite of squares is the composite of the
induced maps**, as an equality of maps of complexes of `B`-modules. This is
`CommAlgCat.squareCotangentComplexMap_comp` in all cohomological degrees at once. -/
theorem squareCotangentComplexMap_comp' (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') :
    squareCotangentComplexMap.{u, u, u} (sq.comp sq') =
      squareCotangentComplexMap.{u, u, u} sq ≫
        ((ModuleCat.restrictScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} sq') :=
  HomologicalComplex.hom_ext _ _ (squareCotangentComplexMap_comp.{u} sq sq')

/-- **The composition law for the adjoint shape of the functoriality map of [Stacks, Tag 08PN].**
The map `L_{B/A} ⊗_B B' ⟶ L_{B''/A''}` attached to the composite square — extension of scalars
along `sq.map : B → B'` of the `B`-linear map of the composite, followed by the counit — is the
map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of the first square followed by the `B'`-linear map
`L_{B'/A'} ⟶ L_{B''/A''}` of the second.

This is the composition law that [Stacks, Tag 08SC] consumes: over the base `A[x]` the
component map `L_{B×C/A[x]} ⊗_{B×C} B ⟶ L_{B/A[x]}` of the canonical map is recognised, through
this law, as the map which [Stacks, Tag 08QQ] inverts at the localization square followed by the
inverse of the map which it inverts at the second localization square. -/
theorem squareCotangentComplexMap_comp_counit (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') :
    ((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (sq.comp sq')) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
          (((ModuleCat.restrictScalars sq'.map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A'' B'')) =
      (((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (squareCotangentComplexMap.{u, u, u} sq) ≫
          ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
            (cotangentComplex.{u, u} A' B')) ≫
        squareCotangentComplexMap.{u, u, u} sq' := by
  have hmap : ((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (squareCotangentComplexMap.{u, u, u} (sq.comp sq')) =
      ((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} sq) ≫
        ((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((ModuleCat.restrictScalars sq.map).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (squareCotangentComplexMap.{u, u, u} sq')) :=
    (congrArg (fun z => ((ModuleCat.extendScalars sq.map).mapHomologicalComplex
      (ComplexShape.up ℤ)).map z) (squareCotangentComplexMap_comp'.{u} sq sq')).trans
      (Functor.map_comp _ _ _)
  refine Eq.trans (eq_whisker hmap _) (Eq.trans (Category.assoc _ _ _) ?_)
  exact Eq.trans (whisker_eq _ (ModuleCat.extendRestrictScalarsAdjCounitComplex_naturality
    sq.map (ComplexShape.up ℤ) (squareCotangentComplexMap.{u, u, u} sq')))
    (Category.assoc _ _ _).symm

/-- **The composition law used.** Let `sq` and `sq'` be composable squares. If the adjoint map
`L_{B/A} ⊗_B B' ⟶ L_{B''/A''}` of the composite is a quasi-isomorphism, and the `B'`-linear map
`L_{B'/A'} ⟶ L_{B''/A''}` of the second square is one, then the adjoint map
`L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of the first square is one.

This is how [Stacks, Tag 08SC] over the base `A[x]` consumes its two instances of
[Stacks, Tag 08QQ]: at the square `(A[x] → A[x, x⁻¹], B × C → B)` -- the composite -- and at the
square `(A[x] → A[x, x⁻¹], B → B)` -- the second factor, whose top map is the identity. -/
theorem quasiIso_squareCotangentComplexMap_counit_of_comp (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'')
    (h : QuasiIso (((ModuleCat.extendScalars sq.map).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (squareCotangentComplexMap.{u, u, u} (sq.comp sq')) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
          (((ModuleCat.restrictScalars sq'.map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A'' B''))))
    (h' : QuasiIso (squareCotangentComplexMap.{u, u, u} sq')) :
    QuasiIso (((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} sq) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} A' B')) :=
  quasiIso_of_comp_right _ (squareCotangentComplexMap.{u, u, u} sq') (hφ := h')
    (hφφ' := Eq.mp (congrArg (fun φ => QuasiIso φ)
      (squareCotangentComplexMap_comp_counit.{u} sq sq')) h)

end CommAlgCat

end
