module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Triangle.FundamentalDisplay

/-!
# The two displayed morphisms of the fundamental triangle

For ring maps `A → B → C`, Equation 92.7.0.1 of the Stacks Project displays the triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`. `StacksFrontier/Cotangent/Triangle/FundamentalDisplay.lean` names its three vertices.
This file constructs the first two displayed morphisms, **canonically and with no hypothesis on
the two ring maps**: they are the functoriality maps of Tag 08PN for the two commutative squares
of the tower, which is what makes them *the* morphisms of the display rather than some pair of
morphisms between the same objects.

## Main definitions

* `CommAlgCat.displaySquare₁` and `CommAlgCat.displaySquare₂`: the two commutative squares of
  ring maps attached to the tower, `(𝟙_A, B → C)` from `A → B` to `A → C` and `(A → B, 𝟙_C)`
  from `A → C` to `B → C`.
* `CommAlgCat.fundamentalMor₁`: **the first displayed morphism** `L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}`.
* `CommAlgCat.cotangentComplexBaseRingMap` and `CommAlgCat.fundamentalMor₂`: **the second
  displayed morphism** `L_{C/A} ⟶ L_{C/B}`, at chain level and in `D(C)`.

## Main results

* `CommAlgCat.cotangentComplexBaseRingMap_differential`: in each simplicial degree the second
  morphism carries the universal derivation to the universal derivation, `1 ⊗ d p ↦ 1 ⊗ d (u p)`.
  This is the formula that pins the map of Tag 08PN down, so the second displayed morphism is the
  canonical one and not merely some morphism `L_{C/A} ⟶ L_{C/B}`. The same formula for the first
  morphism is `CommAlgCat.cotangentExtendScalarsMooreMap_f_mk` at the square
  `CommAlgCat.displaySquare₁`, by `CommAlgCat.displaySquare₁_eq`.

## Where the rest of the display is

Equation 92.7.0.1 asserts that the three vertices and three morphisms form a **distinguished**
triangle in `D(C)`, which is Proposition 08QX. The third displayed morphism, the connecting
morphism `L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`, is not a functoriality map of anything, so it is not
built here: it comes with the triangle.

**For `B → C` injective** it is `CommAlgCat.fundamentalMor₃` of
`StacksFrontier/Cotangent/Triangle/DisplayedTriangle.lean`, and the display is a distinguished
triangle on it and the two morphisms built here, by
`CommAlgCat.fundamentalTriangle_distinguished` there, resting on
`CommAlgCat.cotangentTriangle_mor₁_eq_fundamentalMor₁` and
`CommAlgCat.fundamentalDisplayMor₂_eq_fundamentalMor₂` — the first two morphisms of the triangle
of Tag 08SD, read between the display's own vertices, *are* `CommAlgCat.fundamentalMor₁` and
`CommAlgCat.fundamentalMor₂`.

**For arbitrary `A → B → C`**, as Equation 92.7.0.1 and Proposition 08QX read them, it is
`CommAlgCat.productFundamentalMor₃` of `StacksFrontier/Cotangent/Triangle/ProductDescent.lean`,
obtained by the passage to `A → B → B × C` of [Stacks, Remark 08SD], and the display is a
distinguished triangle on the same two morphisms and it by
`CommAlgCat.productFundamentalTriangle_distinguished` there. Those two declarations carry
`@[stacks 08QS]` for the third displayed morphism and `@[stacks 08QX]` for the proposition, so
the registration of Equation 92.7.0.1 is the three vertices of
`StacksFrontier/Cotangent/Triangle/FundamentalDisplay.lean`, the two morphisms below and that third
morphism.

## Implementation notes

The second square has the identity of `C` for its horizontal map, and restriction of scalars
along the identity ring homomorphism is the identity functor definitionally, so
`CommAlgCat.squareCotangentComplexMap` already lands in `L_{C/B}` with no comparison isomorphism
interposed; that is why the second morphism needs no identification at all.

The first morphism is a map *out of the derived base change*, so it is assembled as the
functoriality map of Tag 08PN after extension of scalars,
`CommAlgCat.cotangentExtendScalarsComplexMap`, read through
`CommAlgCat.cotangentComplexDerivedBaseChangeTermwiseIso`, which identifies `L_{B/A} ⊗^𝐋_B C`
with the degreewise extension of scalars `C ⊗_B L_{B/A}` because the terms of `L_{B/A}` are
projective `B`-modules. This is the same assembly as
`CommAlgCat.cotangentTensorProductBaseChangeMap` of `StacksFrontier/Cotangent/TensorProduct.lean`,
which is the first morphism of the fundamental triangle of `R → A → A ⊗_R B`. The square
`CommAlgCat.displaySquare₁` is `CommAlgCat.algebraSquareOfAlgHom` of the algebra map `B → C`;
it is recorded here because it is the square whose functoriality map the first morphism is.

The three rings are taken in one universe, which is no restriction: three rings with maps
between them always lie in a common universe. The scalar structures are those of a tower
`A → B → C` of plain types, as the display of Tag 08QS reads them, as in
`StacksFrontier/Cotangent/Triangle/Fundamental.lean`.

## References

* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the displayed triangle.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is
  distinguished.
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN), the functoriality of the
  cotangent complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The commutative square `(𝟙_A, B → C)` of the tower `A → B → C`, from the algebra `A → B` to
the algebra `A → C`. Its functoriality map is the first displayed morphism, after extension of
scalars. -/
def displaySquare₁ : AlgebraSquare.{u, u, u} A A (CommAlgCat.of A B) (CommAlgCat.of A C) where
  base := RingHom.id A
  map := algebraMap B C
  map_algebraMap a := (IsScalarTower.algebraMap_apply A B C a).symm

/-- The first square of the tower is the square that the algebra map `B → C` determines, which is
the square whose functoriality map `CommAlgCat.fundamentalMor₁` is built from. -/
theorem displaySquare₁_eq :
    displaySquare₁ A B C =
      algebraSquareOfAlgHom (A := A) (A' := A) (B := CommAlgCat.of A B)
        (B' := CommAlgCat.of A C) (IsScalarTower.toAlgHom A B C) :=
  rfl

/-- The commutative square `(A → B, 𝟙_C)` of the tower `A → B → C`, from the algebra `A → C` to
the algebra `B → C`. Its functoriality map is the second displayed morphism. -/
def displaySquare₂ : AlgebraSquare.{u, u, u} A B (CommAlgCat.of A C) (CommAlgCat.of B C) where
  base := algebraMap A B
  map := RingHom.id C
  map_algebraMap a := IsScalarTower.algebraMap_apply A B C a

/-- **Stacks Project, Tag 08QS.**

The first displayed morphism `L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}` of the triangle, for arbitrary ring
maps `A → B → C`: the functoriality map of Tag 08PN for the square `(𝟙_A, B → C)` after
extension of scalars along `B → C`, read through the identification of the derived base change
`L_{B/A} ⊗^𝐋_B C` with the degreewise one `C ⊗_B L_{B/A}`. -/
@[stacks 08QS "the first displayed morphism `L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A}`, canonical and with no \
  hypothesis on the two ring maps: the functoriality map of Tag 08PN for the square (1_A, B → C) \
  after extension of scalars. It is the first morphism of the distinguished triangle of \
  Proposition 08QX, `CommAlgCat.productFundamentalTriangle_distinguished`, whose third morphism \
  is `CommAlgCat.productFundamentalMor₃`"]
def fundamentalMor₁ :
    fundamentalVertex₁.{u, u, u + 1, u + 1} A B C ⟶ fundamentalVertex₂.{u, u, u + 1} A C :=
  (cotangentComplexDerivedBaseChangeTermwiseIso A (CommAlgCat.of A B) C).hom ≫
    DerivedCategory.Q.map
      (cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := CommAlgCat.of A B)
        (B' := CommAlgCat.of A C) (IsScalarTower.toAlgHom A B C))

/-- The chain-level second displayed morphism `L_{C/A} ⟶ L_{C/B}`: the functoriality map of
Tag 08PN for the square `(A → B, 𝟙_C)`. Restriction of scalars along the identity of `C` is the
identity functor, so no comparison isomorphism intervenes. -/
def cotangentComplexBaseRingMap :
    cotangentComplex.{u, u} A (CommAlgCat.of A C) ⟶
      cotangentComplex.{u, u} B (CommAlgCat.of B C) :=
  squareCotangentComplexMap.{u, u, u} (displaySquare₂ A B C)

/-- **Stacks Project, Tag 08QS.**

The second displayed morphism `L_{C/A} ⟶ L_{C/B}` of the triangle, for arbitrary ring maps
`A → B → C`: the functoriality map of Tag 08PN for the square `(A → B, 𝟙_C)`, read in `D(C)`. -/
@[stacks 08QS "the second displayed morphism `L_{C/A} ⟶ L_{C/B}`, canonical and with no \
  hypothesis on the two ring maps: the functoriality map of Tag 08PN for the square (A → B, 1_C). \
  It is the second morphism of the distinguished triangle of Proposition 08QX, \
  `CommAlgCat.productFundamentalTriangle_distinguished`, whose third morphism is \
  `CommAlgCat.productFundamentalMor₃`"]
def fundamentalMor₂ :
    fundamentalVertex₂.{u, u, u + 1} A C ⟶ fundamentalVertex₃.{u, u, u + 1} B C :=
  DerivedCategory.Q.map (cotangentComplexBaseRingMap A B C)

/-- **The second displayed morphism is the canonical one.** In simplicial degree `n` it carries
the universal derivation `1 ⊗ d p` of the standard resolution of `C` over `A` to the universal
derivation `1 ⊗ d (u p)` of the standard resolution of `C` over `B`, `u` being the canonical map
of the two standard resolutions. This is the formula that pins down the map of Tag 08PN. -/
theorem cotangentComplexBaseRingMap_differential (n : ℕ)
    (p : (standardResolution.{u, u} A (CommAlgCat.of A C)).left.obj (op ⦋n⦌)) :
    (cotangentComplex_degreeIso.{u, u} B (CommAlgCat.of B C) n).hom
        ((cotangentComplexBaseRingMap A B C).f (-(n : ℤ))
          ((cotangentComplex_degreeIso.{u, u} A (CommAlgCat.of A C) n).inv
            (cotangentTermDifferential.{u, u} A (CommAlgCat.of A C) (op ⦋n⦌) p))) =
      cotangentTermDifferential.{u, u} B (CommAlgCat.of B C) (op ⦋n⦌)
        (standardResolutionSquareMap.{u, u, u} (displaySquare₂ A B C) (op ⦋n⦌) p) :=
  squareCotangentComplexMap_differential.{u, u, u} (displaySquare₂ A B C) n p

end CommAlgCat

end
