module

public import StacksFrontier.Cotangent.PolynomialRetraction
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# Lemma 08SI with the fundamental triangle supplied

`StacksFrontier.Cotangent.PolynomialRetraction` proves [Stacks, Tag 08SI] under the predicate
`CommAlgCat.HasFundamentalTriangleAt A B A`, the existence of a distinguished triangle on the
three vertices of the display of Tag 08QS for the tower `A → B → A`; that file is upstream of
Proposition 08QX. This file proves the predicate at every tower, from Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, and states Tag 08SI under exactly the source's
hypotheses.

## Main results

* `CommAlgCat.hasFundamentalTriangleAt`: `CommAlgCat.HasFundamentalTriangleAt A B C` holds for
  every tower `A → B → C`.
* `CommAlgCat.nonempty_cotangentComplex_retraction_iso_single_unconditional`: **[Stacks, Tag
  08SI]**, in the general form — `L_{A/B}` is isomorphic in `D(A)` to `I/I²` placed in
  cohomological degree `-1`.

## References

* [Stacks Project, Tag 08SI](https://stacks.math.columbia.edu/tag/08SI)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-- **Proposition 08QX at one tower.** For every tower `A → B → C` the three vertices of the
display of Tag 08QS fit into a distinguished triangle: this is
`CommAlgCat.productFundamentalTriangle_distinguished`. -/
theorem hasFundamentalTriangleAt (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    HasFundamentalTriangleAt A B C :=
  exists_distTriang_fundamentalVertex.{u} A B C

section Retraction

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra B A]
  [IsScalarTower A B A]

/-- **Stacks Project, Tag 08SI.** Let `B` be a polynomial algebra over `A` with an augmentation
`B → A`, and let `I` be its kernel. Then `L_{A/B}` is isomorphic in `D(A)` to `I/I²` placed in
cohomological degree `-1`.

This is `CommAlgCat.nonempty_cotangentComplex_retraction_iso_single` with the fundamental
triangle of the tower `A → B → A` supplied by `CommAlgCat.hasFundamentalTriangleAt`. -/
@[stacks 08SI "the lemma for a general base ring A and a general polynomial algebra B over it \
  with an augmentation B → A, of which the source's A = Z[x_1,...,x_n] -> B = Z sending every \
  x_i to 0 is the case A = Z; the source's ideal I = (x_1,...,x_n) is the kernel of the \
  augmentation, and I/I^2 is its conormal module. NOTHING is carried: the triangle the source's \
  proof invokes is Proposition 08QX for the tower A -> B -> A, \
  `CommAlgCat.productFundamentalTriangle_distinguished`, which holds for arbitrary ring maps — \
  the triangle of Tag 08SD needs the middle map injective, whereas the augmentation B → A is \
  surjective, so it is the proposition and not Tag 08SD that applies"]
theorem nonempty_cotangentComplex_retraction_iso_single_unconditional
    (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex B (CommAlgCat.of B A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} ↥(CommAlgCat.of B A)) (-1)).obj
        (ModuleCat.of ↥(CommAlgCat.of B A)
          (surjectionExtension B (CommAlgCat.of B A)
            (surjective_algebraMap_of_isScalarTower_self A B)).Cotangent)) :=
  nonempty_cotangentComplex_retraction_iso_single A B hB (hasFundamentalTriangleAt A B A)

end Retraction

end CommAlgCat

end
