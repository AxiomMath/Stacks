module

public import StacksFrontier.Cotangent.ResolutionIndependence
public import StacksFrontier.Cotangent.StandardResolutionFunctoriality
public import StacksFrontier.Cotangent.StandardResolutionOverPolynomialBase

/-!
# The comparison of the two resolutions of Tag 08SA, with its morphism named

For a tower `A → B → C` the proof of [Stacks, Tag 08SA] uses the standard resolution `P_•` of `C`
over `B`, read over `A`. Its complex of differentials `Ω[P_•⁄A] ⊗[P_•] C`
(`CommAlgCat.restrictedCotangentComplex`) is the middle term of the short exact sequence whose
triangle Tag 08SA asserts, and it has to be identified with `L_{C/A}`, which is the complex of
the standard resolution `Q_•` of `C` over `A`.

The library's identification,
`CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex`, is a `Nonempty`
isomorphism of *objects* of `D(C)`: both complexes are derived lower shriek of `i^*Ω_{𝒪/A}` on
the site, and the comparison rests on a chosen projective resolution of the coefficient sheaf. It
names no arrow, and that is what blocks Tag 08SC: to compare triangles one needs the
identification to commute with the triangles' morphisms, and an isomorphism of objects cannot.

This file names the arrow. There is a canonical morphism of simplicial `A`-algebras over `C`

`Q_• = P_•(C/A) ⟶ P_•(C/B) = P_•`,

namely `CommAlgCat.standardResolutionSquareMap` of the square `(A → B, 𝟙_C)` — the square
`CommAlgCat.displaySquare₂` of the display of [Stacks, Tag 08QS] — and *both* simplicial algebras
are resolutions of `C` over `A` as soon as `B` is a polynomial algebra over `A`. Remark 08QI at
the arrow level, `CommAlgCat.quasiIso_alternatingFaceMapComplex_map_of_isResolution`, then says
that the induced map of the complexes `Ω[−⁄A] ⊗ C` is a quasi-isomorphism. So the comparison is a
named map, induced by a named morphism of resolutions, and it is manifestly functorial in `C`:
the square `(A → B, 𝟙_C)` and the morphism of resolutions are built from `C` by functorial
constructions.

## Main definitions

* `CommAlgCat.restrictedTowerSquare`: the square `(A → B, 𝟙_C)` of the tower, from `C` read over
  `A` to `C` read over `B`.
* `CommAlgCat.restrictedTopSquare` and `CommAlgCat.topSquareOfAlgHom`: the squares `(𝟙_A, f)` and
  `(𝟙_B, f)` attached to a `B`-algebra map `f : C → C'`.
* `CommAlgCat.restrictedResolutionComparisonApp`: the degreewise map `P_n(C/A) ⟶ P_n(C/B)`.
* `CommAlgCat.restrictedResolutionComparisonOver`: **the canonical morphism of resolutions
  `P_•(C/A) ⟶ P_•(C/B)`**, read as a morphism of the simplicial objects of `Over C` which
  `CommAlgCat.resolutionOver` attaches to the two augmentations.
* `CommAlgCat.restrictedCotangentComparisonMooreMap` and
  `CommAlgCat.restrictedCotangentComparison`: **the induced map
  `L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C`**, on the Moore complexes and on the cotangent complexes.

## Main results

* `CommAlgCat.quasiIso_restrictedResolutionComparison`: the comparison induces a
  quasi-isomorphism of the Moore complexes of `Ω[−⁄A] ⊗ C`, when `B` is a polynomial algebra over
  `A`. This is Tag 08PU for the two resolutions in play *with its arrow named*, which is what
  `CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex` does not give.
* `CommAlgCat.quasiIso_restrictedCotangentComparisonMooreMap` and
  `CommAlgCat.quasiIso_restrictedCotangentComparison`: the same, read as a map into
  `CommAlgCat.restrictedCotangentSimplicialModule`'s complex and into
  `CommAlgCat.restrictedCotangentComplex`. **The second is the named replacement for the
  `Nonempty` object isomorphism**: a quasi-isomorphism
  `L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C` of cochain complexes of `C`-modules.
* `CommAlgCat.standardResolutionSquareMap_restrictedTowerSquare_naturality`: **the comparison is
  natural in the top algebra.** For a `B`-algebra map `f : C → C'` the comparison commutes with
  the functoriality of the standard resolution in `f`. This is the axis the implementation notes
  of `StacksFrontier/Cotangent/ProductDecomposition.lean` record as the one Tag 08SC needs and
  `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality` does not give.

## Implementation notes

Restriction of scalars along `A → B` changes neither the underlying ring of an algebra nor the
underlying map of a morphism (`CommAlgCat.restrictScalars`), so the ring homomorphism
`CommAlgCat.standardResolutionSquareMap` produces in each degree is already a morphism into the
restricted resolution; its `A`-linearity is `CommAlgCat.standardResolutionSquareMap_algebraMap`,
the `A`-algebra structure of the restriction being `Algebra.compHom` along `A → B` by
definition. Naturality in the simplicial degree is
`CommAlgCat.standardResolutionSquareMap_naturality` and compatibility with the augmentations is
`CommAlgCat.standardResolutionSquareMap_augmentation_app`; both are stated for an arbitrary
square and an arbitrary simplicial operator, so nothing here is checked at a concrete simplicial
degree — evaluating the standard resolution at a simplex is what makes the unifier diverge.

## References

* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra B C]

/-- **The square `(A → B, 𝟙_C)` of the tower `A → B → C`**, from `C` read as an `A`-algebra to
`C` read as a `B`-algebra. This is `CommAlgCat.displaySquare₂` of the display of
[Stacks, Tag 08QS], written with the source algebra as `CommAlgCat.restrictedBase`, which is the
form the resolutions of Tag 08SA are indexed by. -/
noncomputable def restrictedTowerSquare :
    AlgebraSquare.{u, u, u} A B (restrictedBase A B C) (CommAlgCat.of B C) where
  base := algebraMap A B
  map := RingHom.id C
  map_algebraMap _ := rfl

/-- **The canonical map `P_n(C/A) ⟶ P_n(C/B)` in degree `n`**, the target read over `A`. It is
`CommAlgCat.standardResolutionSquareMap` of `CommAlgCat.restrictedTowerSquare`; restriction of
scalars changes neither the underlying ring nor the underlying map, so that ring homomorphism
already lands in the restricted resolution, and it is `A`-linear by
`CommAlgCat.standardResolutionSquareMap_algebraMap`, the `A`-algebra structure of the restriction
being `Algebra.compHom` along `A → B` by definition. -/
noncomputable def restrictedResolutionComparisonApp (n : SimplexCategoryᵒᵖ) :
    (standardResolution.{u, u} A (restrictedBase A B C)).left.obj n ⟶
      (restrictedResolution A B C).obj n :=
  letI : Algebra A ((standardResolutionOver B C).left.obj n : Type u) :=
    Algebra.compHom _ (algebraMap A B)
  CommAlgCat.ofHom
    { toRingHom := standardResolutionSquareMap.{u, u, u} (restrictedTowerSquare A B C) n
      commutes' := standardResolutionSquareMap_algebraMap (restrictedTowerSquare A B C) n }

/-- **The canonical morphism of resolutions `P_•(C/A) ⟶ P_•(C/B)`**, read as a morphism of the
simplicial objects of `Over C` which `CommAlgCat.resolutionOver` attaches to the two
augmentations. This is the shape Remark 08QI at the arrow level consumes; the underlying morphism
of simplicial `A`-algebras is `CommAlgCat.resolutionOverForget` of it.

Compatibility with the augmentations is
`CommAlgCat.standardResolutionSquareMap_augmentation_app` and naturality in the simplicial degree
is `CommAlgCat.standardResolutionSquareMap_naturality`, both stated for an arbitrary square and
an arbitrary simplicial operator. -/
noncomputable def restrictedResolutionComparisonOver :
    resolutionOver (standardResolution.{u, u} A (restrictedBase A B C)).hom ⟶
      resolutionOver (restrictedResolutionAug A B C) where
  app n := Over.homMk (restrictedResolutionComparisonApp A B C n)
    (CommAlgCat.hom_ext (AlgHom.ext fun p =>
      standardResolutionSquareMap_augmentation_app (restrictedTowerSquare A B C) n p))
  naturality _ _ g := Over.OverMorphism.ext (CommAlgCat.hom_ext (AlgHom.ext fun p =>
    standardResolutionSquareMap_naturality (restrictedTowerSquare A B C) g p))

/-- **Tag 08PU for the two resolutions of Tag 08SA, with its arrow named.** For `B` a polynomial
algebra over `A`, the map of Moore complexes `L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C` induced by the
canonical morphism of resolutions `P_•(C/A) ⟶ P_•(C/B)` is a quasi-isomorphism.

Both simplicial algebras are resolutions of `C` over `A`: the first by
`CommAlgCat.standardResolution_isResolution` and the second by
`CommAlgCat.standardResolution_isResolution_restrictScalars`, which is where polynomiality of `B`
is used. Remark 08QI at the arrow level,
`CommAlgCat.quasiIso_alternatingFaceMapComplex_map_of_isResolution`, then applies to the
morphism between them.

Unlike `CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex` this is a
statement about a *named* map, so it can be made to commute with the morphisms of a triangle. -/
theorem quasiIso_restrictedResolutionComparison (hB : Algebra.IsPolynomialAlgebra A B) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} C)).map
      (Functor.whiskerRight (restrictedResolutionComparisonOver A B C)
        (overDifferentialsFunctor (A := A) (B := restrictedBase A B C)))) :=
  quasiIso_alternatingFaceMapComplex_map_of_isResolution _ _
    (standardResolution_isResolution.{u, u} A (restrictedBase A B C))
    (standardResolution_isResolution_restrictScalars A B (CommAlgCat.of B C) hB)
    (restrictedResolutionComparisonOver A B C)

/-! ### The comparison on the cotangent complexes -/

/-- **The comparison, read into `CommAlgCat.restrictedCotangentSimplicialModule`.** The target of
`CommAlgCat.restrictedResolutionComparisonOver`'s induced map is the composite
`resolutionOver ⋙ overDifferentialsFunctor`, which is
`CommAlgCat.restrictedCotangentSimplicialModule` up to the identity isomorphism
`CommAlgCat.restrictedResolutionOverDifferentialsIso`; the two are built from the same formula. -/
noncomputable def restrictedCotangentComparisonMooreMap :
    (alternatingFaceMapComplex (ModuleCat.{u} C)).obj
        (cotangentSimplicialModule.{u, u} A (restrictedBase A B C)).object ⟶
      (alternatingFaceMapComplex (ModuleCat.{u} C)).obj
        (restrictedCotangentSimplicialModule.{u, u} A B C) :=
  (alternatingFaceMapComplex (ModuleCat.{u} C)).map
      (Functor.whiskerRight (restrictedResolutionComparisonOver A B C)
        (overDifferentialsFunctor (A := A) (B := restrictedBase A B C))) ≫
    ((alternatingFaceMapComplex (ModuleCat.{u} C)).mapIso
      (restrictedResolutionOverDifferentialsIso A B C)).hom

/-- The comparison is a quasi-isomorphism of the Moore complexes, read into
`CommAlgCat.restrictedCotangentSimplicialModule`. -/
theorem quasiIso_restrictedCotangentComparisonMooreMap (hB : Algebra.IsPolynomialAlgebra A B) :
    QuasiIso (restrictedCotangentComparisonMooreMap A B C) :=
  have := quasiIso_restrictedResolutionComparison A B C hB
  quasiIso_comp
    ((alternatingFaceMapComplex (ModuleCat.{u} C)).map
      (Functor.whiskerRight (restrictedResolutionComparisonOver A B C)
        (overDifferentialsFunctor (A := A) (B := restrictedBase A B C))))
    ((alternatingFaceMapComplex (ModuleCat.{u} C)).mapIso
      (restrictedResolutionOverDifferentialsIso A B C)).hom

/-- **The named comparison `L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C` of cochain complexes of `C`-modules.**
Both complexes are the reindexing along `ComplexShape.embeddingUpIntLE 0` of the Moore complexes
compared above, so the map is `HomologicalComplex.extendMap` of
`CommAlgCat.restrictedCotangentComparisonMooreMap`. -/
noncomputable def restrictedCotangentComparison :
    cotangentComplex.{u, u} A (restrictedBase A B C) ⟶ restrictedCotangentComplex.{u, u} A B C :=
  HomologicalComplex.extendMap (restrictedCotangentComparisonMooreMap A B C)
    (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- **Tag 08PU for the two resolutions of Tag 08SA, on the cotangent complexes and with its arrow
named.** For `B` a polynomial algebra over `A` the map
`L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C` is a quasi-isomorphism.

This is the statement `CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex`
makes about objects only. Having it about a named map is what lets the middle term of the short
exact sequence of Tag 08SA be identified with `L_{C/A}` *compatibly with the sequence's own
morphisms*, which is what comparing the triangles of [Stacks, Tag 08SC] needs. -/
theorem quasiIso_restrictedCotangentComparison (hB : Algebra.IsPolynomialAlgebra A B) :
    QuasiIso (restrictedCotangentComparison A B C) :=
  (HomologicalComplex.quasiIso_extendMap_iff _ _).2
    (quasiIso_restrictedCotangentComparisonMooreMap A B C hB)

/-! ### Naturality in the top algebra -/

section Naturality

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C C' : Type u} [CommRing C] [CommRing C'] [Algebra B C] [Algebra B C']

/-- The square `(𝟙_A, C → C')` attached to a `B`-algebra map `C → C'`, with both algebras read
over `A` through `B`. -/
noncomputable def restrictedTopSquare (f : C →ₐ[B] C') :
    AlgebraSquare.{u, u, u} A A (restrictedBase A B C) (restrictedBase A B C') where
  base := RingHom.id A
  map := f.toRingHom
  map_algebraMap a := f.commutes (algebraMap A B a)

/-- The square `(𝟙_B, C → C')` attached to a `B`-algebra map `C → C'`, over the base `B`. -/
def topSquareOfAlgHom (f : C →ₐ[B] C') :
    AlgebraSquare.{u, u, u} B B (CommAlgCat.of B C) (CommAlgCat.of B C') where
  base := RingHom.id B
  map := f.toRingHom
  map_algebraMap := f.commutes

/-- **The two squares of the tower commute with the top-algebra square.** For a `B`-algebra map
`f : C → C'` the horizontal composites `(A → B, 𝟙_C) ∘ (𝟙_B, f)` and `(𝟙_A, f) ∘ (A → B, 𝟙_{C'})`
are the same square `(A → B, f)`. Both base maps are `A → B` composed with an identity and both
algebra maps are `f` composed with an identity, so the two squares are definitionally equal; the
proof-valued field of `CommAlgCat.AlgebraSquare` is a `Prop`. -/
theorem restrictedTowerSquare_comp_topSquare (f : C →ₐ[B] C') :
    (restrictedTowerSquare A B C).comp (topSquareOfAlgHom f) =
      (restrictedTopSquare (A := A) f).comp (restrictedTowerSquare A B C') := rfl

/-- **The comparison of the two resolutions is natural in the top algebra.** For a `B`-algebra
map `f : C → C'` the square

```
P_n(C/A)  ---→  P_n(C/B)
   |               |
P_n(C'/A) ---→  P_n(C'/B)
```

commutes, the horizontal maps being `CommAlgCat.restrictedResolutionComparisonApp` and the
vertical ones the functoriality of the standard resolution in `f`.

This is the naturality axis the implementation notes of
`StacksFrontier/Cotangent/ProductDecomposition.lean` record as missing — naturality of the
comparison of [Stacks, Tag 08PU] **in the algebra `C`**. It holds because
`CommAlgCat.standardResolutionSquareMap` is functorial in the square
(`CommAlgCat.standardResolutionSquareMap_comp`) and the two composite squares agree. Nothing is
evaluated at a concrete simplicial degree: the statement is at an arbitrary `n`. -/
theorem standardResolutionSquareMap_restrictedTowerSquare_naturality (f : C →ₐ[B] C')
    (n : SimplexCategoryᵒᵖ) :
    (standardResolutionSquareMap.{u, u, u} (topSquareOfAlgHom f) n).comp
        (standardResolutionSquareMap.{u, u, u} (restrictedTowerSquare A B C) n) =
      (standardResolutionSquareMap.{u, u, u} (restrictedTowerSquare A B C') n).comp
        (standardResolutionSquareMap.{u, u, u} (restrictedTopSquare (A := A) f) n) := by
  rw [← standardResolutionSquareMap_comp, ← standardResolutionSquareMap_comp,
    restrictedTowerSquare_comp_topSquare]

end Naturality

end CommAlgCat

end
