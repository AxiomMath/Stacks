module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleQuasiIso
public import StacksFrontier.Cotangent.ExtendedMooreBaseChange
public import StacksFrontier.Cotangent.RestrictedComparisonDisplay
public import StacksFrontier.Cotangent.RestrictedCotangentShortComplexTop

/-!
# Descending the functoriality map of a tower from the middle ring to the base

Let `A → B → C` and `A → B → C'` be towers with `B` a polynomial algebra over `A`, and let
`f : C → C'` be a `B`-algebra map. [Stacks, Tag 08SA] gives, for each of `C` and `C'`, a short
exact sequence of complexes

`Ω[B⁄A] ⊗[B] C ⟶ Ω[P_•⁄A] ⊗[P_•] C ⟶ L_{C/B}`

(`CommAlgCat.restrictedCotangentComplexShortComplex`), and `f` induces a morphism from the first
to the second — `CommAlgCat.restrictedCotangentShortComplexTopMap`. This file base changes that
morphism along `f` and runs the five lemma on it. The outcome is:

**if the functoriality map `L_{C/B} ⊗_C C' ⟶ L_{C'/B}` over the middle ring `B` is a
quasi-isomorphism, so is the functoriality map `L_{C/A} ⊗_C C' ⟶ L_{C'/A}` over the base `A`.**

The first vertical is an isomorphism because base change cancels:
`C' ⊗_C (C ⊗_B Ω[B⁄A]) = C' ⊗_B Ω[B⁄A]`, with no hypothesis on `Ω[B⁄A]`. The third vertical is
the hypothesis. Both sequences are short exact — the source one after base change along `f`,
which is exact because `f` is assumed flat — so the five lemma
`DifferentialGradedModule.quasiIso_τ₂_of_shortExact` inverts the middle vertical. The middle
terms are then identified with `L_{C/A}` and `L_{C'/A}` by the named comparison
`CommAlgCat.restrictedCotangentComparison` of [Stacks, Tag 08PU], which is natural in the top
algebra.

This is the step from the base `A[x]` down to the base `A` in the source's proof of
[Stacks, Tag 08SC]: taking `B = A[x]`, `C = B₀ × C₀` and `C'` one of the two factors, the
hypothesis over the middle ring is Tag 08SC over `A[x]`, which
`StacksFrontier/Cotangent/ProductDecompositionSplittingElement.lean` proves.

## Main definitions

* `CommAlgCat.restrictedCotangentComparisonSimplicial`: the comparison of the two resolutions as
  a morphism of simplicial `C`-modules, of which
  `CommAlgCat.restrictedCotangentComparison` is the extended Moore complex.
* `CommAlgCat.restrictedCotangentComplexShortComplexTopMap`: the morphism of short complexes of
  complexes of `C`-modules induced by `f`.
* `CommAlgCat.restrictedCotangentComplexShortComplexTopAdjoint`: its adjoint, a morphism of short
  complexes of complexes of `C'`-modules.

## Main results

* `CommAlgCat.restrictedCotangentComparisonSimplicial_naturality`: **the comparison of the two
  resolutions is natural in the top algebra**, as a morphism of simplicial modules. On the pure
  differential both composites give `1 ⊗ d (w (u q))` for the two composite maps of standard
  resolutions, and those agree by
  `CommAlgCat.standardResolutionSquareMap_restrictedTowerSquare_naturality`.
* `CommAlgCat.quasiIso_cotangentExtendScalars_restrictedTopSquare`: **the descent.**

## Implementation notes

Everything is kept at the level of simplicial modules until the very end: the two commuting
squares of the morphism of short complexes of *complexes* are obtained from the simplicial ones by
`AlgebraicTopology.extendMooreMap_comp_left` and `AlgebraicTopology.extendMooreMap_comp_right`, and
likewise for the naturality square of the comparison. So the only place a formula on a pure
differential is checked is `CommAlgCat.restrictedCotangentComparisonSimplicial_naturality`, at an
arbitrary simplicial degree; evaluating the standard resolution at a concrete simplex is what
makes the unifier diverge here.

The comparison is written throughout as the extended Moore complex of
`CommAlgCat.restrictedCotangentComparisonSimplicial` rather than as
`CommAlgCat.restrictedCotangentComparison`, to which it is equal by
`CommAlgCat.restrictedCotangentComparison_eq`. The reason is that the source of the latter is
`L_{C/A}` read as a complex of `↑(CommAlgCat.restrictedBase A B C)`-modules while its target is a
complex of `C`-modules, two definitionally equal spellings of one category; a `rw` whose motive
mixes them is rejected, its target not being type-correct at `implicit` transparency, which is
what `rw` checks motives at. Written the other way every term is in the `C` spelling by
construction and the spellings are crossed exactly once, in
`CommAlgCat.restrictedCotangentComparison_eq`, by a `congrArg`. For the same reason the two
equalities of large composites are transported into `QuasiIso` by
`HomologicalComplex.quasiIso_of_eq`, whose two morphisms are variables and whose motive is
therefore always type-correct, rather than by `rw`; and the base change of the naturality square
is `ModuleCat.extendScalars_comp_counit_naturality`, stated for arbitrary morphisms of complexes
so that its own rewriting happens where there is nothing to trip over.

The three spellings of the pure differential `1 ⊗ d p` which meet in the naturality proof —
`CommAlgCat.overDifferentialsMk`, `CommAlgCat.cotangentTermDifferential` and
`CommAlgCat.restrictedCotangentDifferential` — are definitionally but not syntactically equal.
They are crossed in `CommAlgCat.restrictedCotangentComparisonSimplicial_D`, once, and the
statement of the naturality square is restated by a single `show` before any `rw` runs.

## References

* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct

universe u

namespace CommAlgCat

/-! ### The comparison of the two resolutions, as a map of simplicial modules -/

section Comparison

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra B C]

/-- **The comparison of the two resolutions of [Stacks, Tag 08SA], as a morphism of simplicial
`C`-modules** `L_{C/A} ⟶ Ω[P_•⁄A] ⊗[P_•] C`. Its extended Moore complex is
`CommAlgCat.restrictedCotangentComparison`. -/
noncomputable def restrictedCotangentComparisonSimplicial :
    (cotangentSimplicialModule.{u, u} A (restrictedBase A B C)).object ⟶
      restrictedCotangentSimplicialModule.{u, u} A B C :=
  Functor.whiskerRight (restrictedResolutionComparisonOver A B C)
      (overDifferentialsFunctor (A := A) (B := restrictedBase A B C)) ≫
    (restrictedResolutionOverDifferentialsIso A B C).hom

/-- **The comparison sends the pure differential `1 ⊗ d q` to `1 ⊗ d (u q)`**, for
`u : P_n(C/A) ⟶ P_n(C/B)` the canonical map of standard resolutions. -/
theorem restrictedCotangentComparisonSimplicial_D (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution.{u, u} A (restrictedBase A B C)).left.obj n) :
    (restrictedCotangentComparisonSimplicial A B C).app n
        (cotangentTermDifferential.{u, u} A (restrictedBase A B C) n q) =
      restrictedCotangentDifferential.{u, u} A B C n
        (standardResolutionSquareMap.{u, u, u} (restrictedTowerSquare A B C) n q) :=
  overDifferentialsFunctor_map_mk ((restrictedResolutionComparisonOver A B C).app n) q

/-- The Moore complex of `CommAlgCat.restrictedCotangentComparisonSimplicial` is
`CommAlgCat.restrictedCotangentComparisonMooreMap`. -/
theorem restrictedCotangentComparisonMooreMap_eq :
    restrictedCotangentComparisonMooreMap A B C =
      (alternatingFaceMapComplex (ModuleCat.{u} C)).map
        (restrictedCotangentComparisonSimplicial A B C) :=
  (Functor.map_comp (alternatingFaceMapComplex (ModuleCat.{u} C))
      (Functor.whiskerRight (restrictedResolutionComparisonOver A B C)
        (overDifferentialsFunctor (A := A) (B := restrictedBase A B C)))
      (restrictedResolutionOverDifferentialsIso A B C).hom).symm

/-- **`CommAlgCat.restrictedCotangentComparison` is the extended Moore complex of the simplicial
comparison.** This is the one place the two definitionally equal spellings of the category of
complexes of `C`-modules are crossed. -/
theorem restrictedCotangentComparison_eq :
    restrictedCotangentComparison A B C =
      (extendedMooreFunctor (ModuleCat.{u} C)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C) :=
  congrArg (fun φ => HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE (0 : ℤ)))
    (restrictedCotangentComparisonMooreMap_eq A B C)

end Comparison

/-! ### The comparison is natural in the top algebra -/

section Naturality

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C C' : Type u} [CommRing C] [CommRing C'] [Algebra B C] [Algebra B C']

/-- **The comparison of the two resolutions is natural in the top algebra.** For a `B`-algebra
map `f : C → C'` the square

```
L_{C/A}   ---→  Ω[P_•(C/A)⁄A] ⊗ C
  |                    |
L_{C'/A}  ---→  Ω[P_•(C'/A)⁄A] ⊗ C'
```

commutes, the horizontal maps being
`CommAlgCat.restrictedCotangentComparisonSimplicial` and the vertical ones the functoriality of
[Stacks, Tag 08PN] at the square `(𝟙_A, f)` and
`CommAlgCat.restrictedCotangentTopMap`. On the pure differential `1 ⊗ d q` both composites give
`1 ⊗ d` of the image of `q` under the two composite maps of standard resolutions, and those
agree by `CommAlgCat.standardResolutionSquareMap_restrictedTowerSquare_naturality`. -/
theorem restrictedCotangentComparisonSimplicial_naturality (f : C →ₐ[B] C') :
    restrictedCotangentComparisonSimplicial A B C ≫
        (restrictedCotangentShortComplexTopMap f).τ₂ =
      squareCotangentSimplicialMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f) ≫
        ((SimplicialObject.whiskering (ModuleCat.{u} C') (ModuleCat.{u} C)).obj
            (ModuleCat.restrictScalars f.toRingHom)).map
          (restrictedCotangentComparisonSimplicial A B C') := by
  refine NatTrans.ext (funext fun n => ?_)
  refine cotangentTerm_hom_ext.{u, u} A (restrictedBase A B C) n _ _ fun q => ?_
  show restrictedCotangentTopMap f n
      ((restrictedCotangentComparisonSimplicial A B C).app n
        (cotangentTermDifferential.{u, u} A (restrictedBase A B C) n q)) =
    (restrictedCotangentComparisonSimplicial A B C').app n
      (squareCotangentTermMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f) n
        (cotangentTermDifferential.{u, u} A (restrictedBase A B C) n q))
  rw [restrictedCotangentComparisonSimplicial_D, restrictedCotangentTopMap_D,
    squareCotangentTermMap_D, restrictedCotangentComparisonSimplicial_D]
  exact congrArg (restrictedCotangentDifferential.{u, u} A B C' n)
    (RingHom.congr_fun (standardResolutionSquareMap_restrictedTowerSquare_naturality f n) q)

end Naturality

/-! ### The morphism of short complexes of complexes -/

section ShortComplex

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  {C C' : Type u} [CommRing C] [CommRing C'] [Algebra B C] [Algebra B C']

/-- **The morphism of short complexes of complexes of `C`-modules** induced by a `B`-algebra map
`f : C → C'`: the extended Moore complex of
`CommAlgCat.restrictedCotangentShortComplexTopMap`. The two commuting squares are the simplicial
ones, carried over by `AlgebraicTopology.extendMooreMap_comp_left` and
`AlgebraicTopology.extendMooreMap_comp_right`. -/
noncomputable def restrictedCotangentComplexShortComplexTopMap (f : C →ₐ[B] C') :
    restrictedCotangentComplexShortComplex.{u, u} A B C ⟶
      (restrictedCotangentComplexShortComplex.{u, u} A B C').map
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)) where
  τ₁ := extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) (restrictedCotangentShortComplexTopMap f).τ₁
  τ₂ := extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) (restrictedCotangentShortComplexTopMap f).τ₂
  τ₃ := extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) (restrictedCotangentShortComplexTopMap f).τ₃
  comm₁₂ := by
    change extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (restrictedCotangentShortComplexTopMap f).τ₁ ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((extendedMooreFunctor (ModuleCat.{u} C')
              (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
            (restrictedCotangentShortComplex.{u, u} A B C').f) =
      (extendedMooreFunctor (ModuleCat.{u} C)
            (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
          (restrictedCotangentShortComplex.{u, u} A B C).f ≫
        extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (restrictedCotangentShortComplexTopMap f).τ₂
    rw [← extendMooreMap_comp_right, ← extendMooreMap_comp_left]
    exact congrArg _ (restrictedCotangentShortComplexTopMap f).comm₁₂
  comm₂₃ := by
    change extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (restrictedCotangentShortComplexTopMap f).τ₂ ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((extendedMooreFunctor (ModuleCat.{u} C')
              (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
            (restrictedCotangentShortComplex.{u, u} A B C').g) =
      (extendedMooreFunctor (ModuleCat.{u} C)
            (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
          (restrictedCotangentShortComplex.{u, u} A B C).g ≫
        extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (restrictedCotangentShortComplexTopMap f).τ₃
    rw [← extendMooreMap_comp_right, ← extendMooreMap_comp_left]
    exact congrArg _ (restrictedCotangentShortComplexTopMap f).comm₂₃

/-- **The adjoint morphism of short complexes of complexes of `C'`-modules.** -/
noncomputable def restrictedCotangentComplexShortComplexTopAdjoint (f : C →ₐ[B] C') :
    (restrictedCotangentComplexShortComplex.{u, u} A B C).map
        ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      restrictedCotangentComplexShortComplex.{u, u} A B C' :=
  ModuleCat.shortComplexExtendScalarsAdjoint f.toRingHom (ComplexShape.up ℤ)
    (restrictedCotangentComplexShortComplexTopMap A B f)

/-- The last component of the adjoint morphism is the functoriality map over the middle ring `B`,
in the shape [Stacks, Tag 08QQ] inverts. -/
theorem restrictedCotangentComplexShortComplexTopAdjoint_τ₃ (f : C →ₐ[B] C') :
    (restrictedCotangentComplexShortComplexTopAdjoint A B f).τ₃ =
      ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (topSquareOfAlgHom.{u} f)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} B (CommAlgCat.of B C')) :=
  rfl

/-- The middle component of the adjoint morphism. -/
theorem restrictedCotangentComplexShortComplexTopAdjoint_τ₂ (f : C →ₐ[B] C') :
    (restrictedCotangentComplexShortComplexTopAdjoint A B f).τ₂ =
      ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
            (ComplexShape.embeddingUpIntLE (0 : ℤ))
            (restrictedCotangentShortComplexTopMap f).τ₂) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
          (restrictedCotangentComplex.{u, u} A B C') :=
  rfl

/-- The first component of the adjoint morphism is an isomorphism: in every simplicial degree it
is the cancellation of base change. -/
theorem isIso_restrictedCotangentComplexShortComplexTopAdjoint_τ₁ (f : C →ₐ[B] C') :
    IsIso (restrictedCotangentComplexShortComplexTopAdjoint A B f).τ₁ :=
  ModuleCat.isIso_extendScalars_extendMooreMap_comp_counit f.toRingHom
    (restrictedCotangentShortComplexTopMap f).τ₁ (ComplexShape.embeddingUpIntLE (0 : ℤ))
    fun _ => isIso_extendScalars_baseDifferentialsTopMap_counit (A := A) f

end ShortComplex

/-! ### The descent -/

section Descent

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  {C C' : Type u} [CommRing C] [CommRing C'] [Algebra B C] [Algebra B C']

/-- **The functoriality map of a tower descends from the middle ring to the base.** Let
`A → B → C` and `A → B → C'` be towers with `B` a polynomial algebra over `A`, and let
`f : C → C'` be a `B`-algebra map which is flat. If the functoriality map
`L_{C/B} ⊗_C C' ⟶ L_{C'/B}` of [Stacks, Tag 08PN] over the middle ring is a quasi-isomorphism,
then so is the functoriality map `L_{C/A} ⊗_C C' ⟶ L_{C'/A}` over the base.

The proof is the five lemma on the two short exact sequences of [Stacks, Tag 08SA], base changed
along `f`: the hypothesis is the third vertical, the first is an isomorphism by cancellation of
base change, and the middle one is then identified with the functoriality map over `A` by the
comparison `CommAlgCat.restrictedCotangentComparison` of [Stacks, Tag 08PU], which is natural in
the top algebra. -/
theorem quasiIso_cotangentExtendScalars_restrictedTopSquare (f : C →ₐ[B] C')
    (hB : Algebra.IsPolynomialAlgebra A B) (hflat : f.toRingHom.Flat)
    (h₃ : QuasiIso (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (topSquareOfAlgHom.{u} f)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} B (CommAlgCat.of B C')))) :
    QuasiIso (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (squareCotangentComplexMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f)) ≫
      ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
        (cotangentComplex.{u, u} A (restrictedBase A B C'))) := by
  have hS := ModuleCat.shortExact_map_extendScalars_of_flat f.toRingHom (ComplexShape.up ℤ)
    hflat (restrictedCotangentComplexShortComplex_shortExact.{u, u} A B C)
  have hT := restrictedCotangentComplexShortComplex_shortExact.{u, u} A B C'
  have h1 : QuasiIso (restrictedCotangentComplexShortComplexTopAdjoint A B f).τ₁ :=
    have := isIso_restrictedCotangentComplexShortComplexTopAdjoint_τ₁ A B f
    quasiIso_of_isIso _
  have h3 : QuasiIso (restrictedCotangentComplexShortComplexTopAdjoint A B f).τ₃ := by
    rw [restrictedCotangentComplexShortComplexTopAdjoint_τ₃]
    exact h₃
  have h2 : QuasiIso (restrictedCotangentComplexShortComplexTopAdjoint A B f).τ₂ :=
    DifferentialGradedModule.quasiIso_τ₂_of_shortExact
      (restrictedCotangentComplexShortComplexTopAdjoint A B f) hS hT h1 h3
  have hqC : QuasiIso ((extendedMooreFunctor (ModuleCat.{u} C)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C)) := by
    rw [← restrictedCotangentComparison_eq]
    exact quasiIso_restrictedCotangentComparison A B C hB
  have hqC' : QuasiIso ((extendedMooreFunctor (ModuleCat.{u} C')
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C')) := by
    rw [← restrictedCotangentComparison_eq]
    exact quasiIso_restrictedCotangentComparison A B C' hB
  -- the naturality square, at the level of complexes
  have hsq : (extendedMooreFunctor (ModuleCat.{u} C)
            (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
          (restrictedCotangentComparisonSimplicial A B C) ≫
        extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (restrictedCotangentShortComplexTopMap f).τ₂ =
      extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (squareCotangentSimplicialMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f)) ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((extendedMooreFunctor (ModuleCat.{u} C')
              (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
            (restrictedCotangentComparisonSimplicial A B C')) :=
    (extendMooreMap_comp_left (ModuleCat.restrictScalars f.toRingHom)
        (ComplexShape.embeddingUpIntLE (0 : ℤ))
        (restrictedCotangentComparisonSimplicial A B C)
        (restrictedCotangentShortComplexTopMap f).τ₂).symm.trans
      ((congrArg (extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
            (ComplexShape.embeddingUpIntLE (0 : ℤ)))
          (restrictedCotangentComparisonSimplicial_naturality f)).trans
        (extendMooreMap_comp_right (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (squareCotangentSimplicialMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f))
          (restrictedCotangentComparisonSimplicial A B C')))
  -- the same square after base change, with the counit folded in
  have hsq2 := ModuleCat.extendScalars_comp_counit_naturality f.toRingHom
    (ComplexShape.up ℤ)
    ((extendedMooreFunctor (ModuleCat.{u} C)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C))
    (extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (restrictedCotangentShortComplexTopMap f).τ₂)
    (extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (squareCotangentSimplicialMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f)))
    ((extendedMooreFunctor (ModuleCat.{u} C')
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C')) hsq
  have : (ModuleCat.extendScalars.{u, u, u} f.toRingHom).PreservesHomology :=
    extendScalars_preservesHomology_of_flat.{u, u} f.toRingHom hflat
  have h2' : QuasiIso (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (restrictedCotangentShortComplexTopMap f).τ₂) ≫
      ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
        (restrictedCotangentComplex.{u, u} A B C')) := h2
  have hqL := HomologicalComplex.quasiIso_map_of_preservesHomology
    ((extendedMooreFunctor (ModuleCat.{u} C)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C))
    (ModuleCat.extendScalars f.toRingHom)
  have hcomp := HomologicalComplex.quasiIso_of_eq hsq2
    (quasiIso_comp _ _ (hφ := hqL) (hφ' := h2'))
  have hfin : QuasiIso (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (extendMooreMap (ModuleCat.restrictScalars f.toRingHom)
          (ComplexShape.embeddingUpIntLE (0 : ℤ))
          (squareCotangentSimplicialMap.{u, u, u} (restrictedTopSquare.{u} (A := A) f))) ≫
      ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
        (cotangentComplex.{u, u} A (restrictedBase A B C'))) :=
    quasiIso_of_comp_right _ ((extendedMooreFunctor (ModuleCat.{u} C')
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).map
        (restrictedCotangentComparisonSimplicial A B C')) (hφ := hqC') (hφφ' := hcomp)
  exact HomologicalComplex.quasiIso_of_eq
    (congrArg (fun z => ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map z ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex f.toRingHom (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} A (restrictedBase A B C')))
      (extendMooreMap_squareCotangentSimplicialMap
        (restrictedTopSquare.{u} (A := A) f))) hfin

end Descent

end CommAlgCat

end
