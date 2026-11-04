module

public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# The nine diagram of a tensor product, on the canonical maps

Let `R` be a ring and let `A`, `B` be `R`-algebras. [Stacks, Tag 09D9] is the diagram

```
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}      ⟶ E
            ‖                     ↑                ↑
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}      ⟶ L_{A ⊗_R B/A}
                                  ↑                ↑
                      L_{B/R} ⊗^L_B (A ⊗_R B) ═ L_{B/R} ⊗^L_B (A ⊗_R B)
```

in `D(A ⊗_R B)`. Its middle row is the fundamental triangle (Tag 08QS) of `R → A → A ⊗_R B`, its
middle column the fundamental triangle of `R → B → A ⊗_R B`, and `E` is an object making the top
row and the right column distinguished triangles.

`CommAlgCat.exists_tensorProduct_nine_diagram` of `StacksFrontier/Cotangent/TensorProduct.lean`
proves the octahedral step for two arbitrary distinguished triangles on these vertices, because
that file sits upstream of Proposition 08QX. This file sits downstream of it and builds the
diagram from the canonical maps: the middle row and the middle column are the triangles of
`CommAlgCat.productFundamentalTriangle_distinguished` (Proposition 08QX) for the two towers,
with the functoriality maps of Tag 08PN, and the two remaining arrows -- the first map of the top
row and the first map of the right column -- are shown to be the functoriality maps of Tag 08PN
for the squares `(R → B, A → A ⊗_R B)` and `(R → A, B → A ⊗_R B)`.

## Main definitions

* `CommAlgCat.tensorProductIncludeRight`: the inclusion `B ⟶ A ⊗_R B` as a map of `R`-algebras
  into the `A`-algebra `A ⊗_R B`.
* `CommAlgCat.cotangentTensorProductBaseChangeMapRight`: the canonical morphism
  `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`, the first map of the right column.
* `CommAlgCat.canonicalTensorProductNineDiagram`: a nine diagram whose middle row and middle
  column are the canonical fundamental triangles.

## Main results

* `CommAlgCat.fundamentalMor₁_comp_fundamentalMor₂_includeLeft` and
  `CommAlgCat.fundamentalMor₁_comp_fundamentalMor₂_includeRight`: the left and the lower squares
  of the diagram commute, with the canonical maps on all sides.
* `CommAlgCat.exists_canonical_tensorProduct_nine_diagram`: **Stacks 09D9** on the canonical
  maps, with nothing assumed.

## References

* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The inclusion `B ⟶ A ⊗_R B`, `b ↦ 1 ⊗ b`, as a morphism of `R`-algebras from `B` to
`A ⊗_R B` viewed as an `A`-algebra. -/
def tensorProductIncludeRight :
    ↥(CommAlgCat.of R B) →ₐ[R] ↥(CommAlgCat.of A (A ⊗[R] B)) :=
  Algebra.TensorProduct.includeRight

/-- **The first map of the right column of Equation 92.15.0.1.** The canonical morphism
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`: the functoriality map of Tag 08PN for the square
`R → B`, `R → A`, `B → A ⊗_R B`, `A → A ⊗_R B`, read through the identification of the derived
base change with the degreewise one. -/
def cotangentTensorProductBaseChangeMapRight :
    cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
      cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) :=
  (cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R B) (A ⊗[R] B)).hom ≫
    DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (tensorProductIncludeRight R A B))

/-! ### The left and the lower squares -/

/-- The square `(𝟙_R, A → A ⊗_R B)` followed by the square `(R → B, 𝟙_{A ⊗_R B})` is the square
`(R → B, A → A ⊗_R B)`. -/
theorem algebraSquareOfAlgHom_comp_displaySquare₂_includeLeft :
    (algebraSquareOfAlgHom (A := R) (A' := R) (B := CommAlgCat.of R A)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (IsScalarTower.toAlgHom R A (A ⊗[R] B))).comp
        (displaySquare₂ R B (A ⊗[R] B)) =
      algebraSquareOfAlgHom (tensorProductIncludeLeft R A B) :=
  rfl

/-- The square `(𝟙_R, B → A ⊗_R B)` followed by the square `(R → A, 𝟙_{A ⊗_R B})` is the square
`(R → A, B → A ⊗_R B)`. -/
theorem algebraSquareOfAlgHom_comp_displaySquare₂_includeRight :
    (algebraSquareOfAlgHom (A := R) (A' := R) (B := CommAlgCat.of R B)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (IsScalarTower.toAlgHom R B (A ⊗[R] B))).comp
        (displaySquare₂ R A (A ⊗[R] B)) =
      algebraSquareOfAlgHom (tensorProductIncludeRight R A B) :=
  rfl

/-- If the square of an `R`-algebra map `g : M → C` followed by the square `(R → S, 𝟙_C)` induces
the same map of cotangent complexes as the square of `g` over `S`, then the functoriality map of
`g` followed by the change of base ring `L_{C/R} ⟶ L_{C/S}` is the functoriality map of `g` over
`S`. -/
private theorem cotangentExtendScalarsComplexMap_comp_baseRingMap_of_square_eq
    {M C S : Type u} [CommRing M] [CommRing C] [CommRing S] [Algebra R M] [Algebra R C]
    [Algebra R S] [Algebra S C] [IsScalarTower R S C] (g : M →ₐ[R] C)
    (h : squareCotangentComplexMap.{u, u, u} ((algebraSquareOfAlgHom (A := R) (A' := R)
        (B := CommAlgCat.of R M) (B' := CommAlgCat.of R C) g).comp (displaySquare₂ R S C)) =
      squareCotangentComplexMap.{u, u, u} (algebraSquareOfAlgHom (A := R) (A' := S)
        (B := CommAlgCat.of R M) (B' := CommAlgCat.of S C) g)) :
    cotangentExtendScalarsComplexMap (A := R) (A' := R) (B := CommAlgCat.of R M)
        (B' := CommAlgCat.of R C) g ≫ cotangentComplexBaseRingMap R S C =
      cotangentExtendScalarsComplexMap (A := R) (A' := S) (B := CommAlgCat.of R M)
        (B' := CommAlgCat.of S C) g := by
  refine Eq.trans (eq_whisker (cotangentExtendScalarsComplexMap_eq_counit (A := R) (A' := R)
    (B := CommAlgCat.of R M) (B' := CommAlgCat.of R C) g) _) ?_
  refine Eq.trans (squareCotangentComplexMap_comp_counit.{u}
    (algebraSquareOfAlgHom (A := R) (A' := R) (B := CommAlgCat.of R M)
      (B' := CommAlgCat.of R C) g) (displaySquare₂ R S C)).symm ?_
  refine Eq.trans ?_ (cotangentExtendScalarsComplexMap_eq_counit (A := R) (A' := S)
    (B := CommAlgCat.of R M) (B' := CommAlgCat.of S C) g).symm
  exact congrArg (fun z => ((ModuleCat.extendScalars g.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map z ≫ ModuleCat.extendRestrictScalarsAdjCounitComplex g.toRingHom
        (ComplexShape.up ℤ) (cotangentComplex.{u, u} S (CommAlgCat.of S C)))
    h

/-- The chain-level left square: the functoriality map `L_{A/R} ⊗_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`
followed by the change of base ring `L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/B}` is the functoriality map
`L_{A/R} ⊗_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}` of the composite square. -/
theorem cotangentExtendScalarsComplexMap_comp_cotangentComplexBaseRingMap_includeLeft :
    cotangentExtendScalarsComplexMap (A := R) (A' := R) (B := CommAlgCat.of R A)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (IsScalarTower.toAlgHom R A (A ⊗[R] B)) ≫
        cotangentComplexBaseRingMap R B (A ⊗[R] B) =
      cotangentExtendScalarsComplexMap (tensorProductIncludeLeft R A B) :=
  cotangentExtendScalarsComplexMap_comp_baseRingMap_of_square_eq R _ rfl

/-- The chain-level lower square: the functoriality map `L_{B/R} ⊗_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`
followed by the change of base ring `L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/A}` is the functoriality map
`L_{B/R} ⊗_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}` of the composite square. -/
theorem cotangentExtendScalarsComplexMap_comp_cotangentComplexBaseRingMap_includeRight :
    cotangentExtendScalarsComplexMap (A := R) (A' := R) (B := CommAlgCat.of R B)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (IsScalarTower.toAlgHom R B (A ⊗[R] B)) ≫
        cotangentComplexBaseRingMap R A (A ⊗[R] B) =
      cotangentExtendScalarsComplexMap (tensorProductIncludeRight R A B) :=
  cotangentExtendScalarsComplexMap_comp_baseRingMap_of_square_eq R _ rfl

/-- **The left square of Equation 92.15.0.1 commutes.** The first map of the middle row,
`L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`, followed by the second map of the middle column,
`L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/B}`, is the canonical map `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}`
of the top row. -/
theorem fundamentalMor₁_comp_fundamentalMor₂_includeLeft :
    fundamentalMor₁ R A (A ⊗[R] B) ≫ fundamentalMor₂ R B (A ⊗[R] B) =
      cotangentTensorProductBaseChangeMap R A B :=
  (Category.assoc _ _ _).trans (whisker_eq _ ((DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map
      (cotangentExtendScalarsComplexMap_comp_cotangentComplexBaseRingMap_includeLeft R A B))))

/-- **The lower square of Equation 92.15.0.1 commutes.** The first map of the middle column,
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`, followed by the second map of the middle row,
`L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/A}`, is the canonical map `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`
of the right column. -/
theorem fundamentalMor₁_comp_fundamentalMor₂_includeRight :
    fundamentalMor₁ R B (A ⊗[R] B) ≫ fundamentalMor₂ R A (A ⊗[R] B) =
      cotangentTensorProductBaseChangeMapRight R A B :=
  (Category.assoc _ _ _).trans (whisker_eq _ ((DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map
      (cotangentExtendScalarsComplexMap_comp_cotangentComplexBaseRingMap_includeRight R A B))))

/-! ### The nine diagram -/

/-- **Stacks 09D9**, Equation 92.15.0.1, on the canonical maps. Let `A` and `B` be algebras over
a ring `R`. In `D(A ⊗_R B)` consider

```
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}      ⟶ E
            ‖                     ↑                ↑
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}      ⟶ L_{A ⊗_R B/A}
                                  ↑                ↑
                      L_{B/R} ⊗^L_B (A ⊗_R B) ═ L_{B/R} ⊗^L_B (A ⊗_R B)
```

The middle row is the fundamental triangle of `R → A → A ⊗_R B` and the middle column is the
fundamental triangle of `R → B → A ⊗_R B`. Both are distinguished, with the functoriality maps of
Tag 08PN (`CommAlgCat.fundamentalMor₁`, `CommAlgCat.fundamentalMor₂`) and the connecting maps
`CommAlgCat.productFundamentalMor₃`. The first map of the top row is the canonical map
`CommAlgCat.cotangentTensorProductBaseChangeMap`, and the first map of the right column is
`CommAlgCat.cotangentTensorProductBaseChangeMapRight`. The left and the lower squares commute.
There is an object `E` in the upper right corner that makes the top row and the right column
distinguished triangles, makes the upper right square commute, and has connecting maps that
recover those of the middle row and the middle column. -/
@[stacks 09D9 "the diagram 92.15.0.1 on the canonical maps, with nothing assumed: the middle \
  row and column are the fundamental triangles of Proposition 08QX for R → A → A ⊗_R B and \
  R → B → A ⊗_R B, with the functoriality maps of Tag 08PN and their own connecting maps; the \
  top-row and right-column first maps are the 08PN maps of the squares (R → B, A → A ⊗_R B) and \
  (R → A, B → A ⊗_R B); the left and lower squares commute; and an object E makes the top row \
  and the right column distinguished, with the upper right square commuting"]
theorem exists_canonical_tensorProduct_nine_diagram :
    Triangle.mk (fundamentalMor₁ R A (A ⊗[R] B)) (fundamentalMor₂ R A (A ⊗[R] B))
        (productFundamentalMor₃ R A (A ⊗[R] B)) ∈ distTriang _ ∧
    Triangle.mk (fundamentalMor₁ R B (A ⊗[R] B)) (fundamentalMor₂ R B (A ⊗[R] B))
        (productFundamentalMor₃ R B (A ⊗[R] B)) ∈ distTriang _ ∧
    fundamentalMor₁ R A (A ⊗[R] B) ≫ fundamentalMor₂ R B (A ⊗[R] B) =
      cotangentTensorProductBaseChangeMap R A B ∧
    fundamentalMor₁ R B (A ⊗[R] B) ≫ fundamentalMor₂ R A (A ⊗[R] B) =
      cotangentTensorProductBaseChangeMapRight R A B ∧
    ∃ (E : DerivedCategory (ModuleCat.{u} (A ⊗[R] B)))
      (a : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶ E)
      (b : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E)
      (e₁ : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))⟦(1 : ℤ)⟧)
      (e₂ : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧),
      Triangle.mk (cotangentTensorProductBaseChangeMap R A B) a e₁ ∈ distTriang _ ∧
      Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e₂ ∈ distTriang _ ∧
      fundamentalMor₂ R B (A ⊗[R] B) ≫ a = fundamentalMor₂ R A (A ⊗[R] B) ≫ b ∧
      b ≫ e₁ = productFundamentalMor₃ R A (A ⊗[R] B) ∧
      a ≫ e₂ = productFundamentalMor₃ R B (A ⊗[R] B) := by
  have h₁ := productFundamentalTriangle_distinguished R A (A ⊗[R] B)
  have h₂ := productFundamentalTriangle_distinguished R B (A ⊗[R] B)
  have hl := fundamentalMor₁_comp_fundamentalMor₂_includeLeft R A B
  have hr := fundamentalMor₁_comp_fundamentalMor₂_includeRight R A B
  obtain ⟨E, a, b, e₁, e₂, ht, hc, hsq, hd, he⟩ :=
    exists_tensorProduct_nine_diagram.{u, u} R A B h₁ h₂
  refine ⟨h₁, h₂, hl, hr, E, a, b, e₁, e₂, ?_, ?_, hsq, hd, he⟩
  · rw [← hl]; exact ht
  · rw [← hr]; exact hc

/-- **The nine diagram of Equation 92.15.0.1 on the canonical fundamental triangles.** Its middle
row and middle column are the triangles of Proposition 08QX for `R → A → A ⊗_R B` and
`R → B → A ⊗_R B`; see `CommAlgCat.canonicalTensorProductNineDiagram_mapA` and the lemmas after
it. -/
def canonicalTensorProductNineDiagram : TensorProductNineDiagram R A B :=
  (exists_tensorProductNineDiagram R A B
    (productFundamentalTriangle_distinguished R A (A ⊗[R] B))
    (productFundamentalTriangle_distinguished R B (A ⊗[R] B))).choose

/-- The six maps of the middle row and the middle column of
`CommAlgCat.canonicalTensorProductNineDiagram` are the canonical maps of the two fundamental
triangles of Proposition 08QX. -/
theorem canonicalTensorProductNineDiagram_spec :
    (canonicalTensorProductNineDiagram R A B).mapA = fundamentalMor₁ R A (A ⊗[R] B) ∧
      (canonicalTensorProductNineDiagram R A B).projA = fundamentalMor₂ R A (A ⊗[R] B) ∧
      (canonicalTensorProductNineDiagram R A B).shiftA = productFundamentalMor₃ R A (A ⊗[R] B) ∧
      (canonicalTensorProductNineDiagram R A B).mapB = fundamentalMor₁ R B (A ⊗[R] B) ∧
      (canonicalTensorProductNineDiagram R A B).projB = fundamentalMor₂ R B (A ⊗[R] B) ∧
      (canonicalTensorProductNineDiagram R A B).shiftB = productFundamentalMor₃ R B (A ⊗[R] B) :=
  (exists_tensorProductNineDiagram R A B
    (productFundamentalTriangle_distinguished R A (A ⊗[R] B))
    (productFundamentalTriangle_distinguished R B (A ⊗[R] B))).choose_spec

end CommAlgCat

end
