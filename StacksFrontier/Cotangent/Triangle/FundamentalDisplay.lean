module

public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex

/-!
# The objects of the fundamental triangle

For ring maps `A → B → C`, Equation 92.7.0.1 of the Stacks Project displays the triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`. This file names its three vertices as objects of `D(C)` and ties the first two to the
triangle of Tag 08SD. The three displayed morphisms between them, and the fact that the six data
form a distinguished triangle for arbitrary `A → B → C`, are built on top of this file; see the
implementation notes for where each of them lives.

## Main definitions

* `CommAlgCat.fundamentalVertex₁`, `CommAlgCat.fundamentalVertex₂`,
  `CommAlgCat.fundamentalVertex₃`: the three vertices `L_{B/A} ⊗^𝐋_B C`, `L_{C/A}` and `L_{C/B}`
  of the displayed triangle, as objects of `D(C)`.

## Main results

* `CommAlgCat.fundamentalVertex₂_eq_cotangentTriangle_obj₂` and
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_cotangentTriangle_obj₁`: for an injective map of
  `A`-algebras, the second and first vertices are the corresponding vertices of the distinguished
  triangle of Tag 08SD.

## Implementation notes

Only the vertices of the display are named here. The first two displayed morphisms, which exist
canonically for arbitrary `A → B → C`, are `CommAlgCat.fundamentalMor₁` and
`CommAlgCat.fundamentalMor₂` of `StacksFrontier/Cotangent/Triangle/DisplayMorphisms.lean`; the third,
`L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)⟦1⟧`, is `CommAlgCat.productFundamentalMor₃` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`. That the three vertices and those three
morphisms form a *distinguished* triangle for arbitrary `A → B → C` is Proposition 08QX, which is
`CommAlgCat.productFundamentalTriangle_distinguished` of the same file.

Naming the constituents of an equation is how this development carries an equation tag: Tag 08QT,
which displays the three morphisms of the threefold site, is carried by the declarations defining
that site, its functors, its structure sheaves and those morphisms, none of which asserts anything
about the display itself.

The third vertex reads `C` as a `B`-algebra, so the three rings are bound as plain types with a
scalar tower, as in `StacksFrontier.Cotangent.TensorProduct`, rather than as objects of `CommAlgCat`.

## References

* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the displayed triangle.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is distinguished.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v wB wC

namespace CommAlgCat

section Display

variable (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
  (C : Type (max u v)) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]

/-- **Stacks Project, Tag 08QS.**

The first vertex `L_{B/A} ⊗^𝐋_B C` of the displayed triangle, as an object of `D(C)`. -/
@[stacks 08QS "the first vertex of the displayed triangle, `L_{B/A} ⊗^𝐋_B C`. The display's three \
  morphisms are `CommAlgCat.fundamentalMor₁`, `CommAlgCat.fundamentalMor₂` and \
  `CommAlgCat.productFundamentalMor₃`, and that the six form a distinguished triangle is \
  Proposition 08QX, `CommAlgCat.productFundamentalTriangle_distinguished`"]
noncomputable abbrev fundamentalVertex₁ : DerivedCategory (ModuleCat.{max u v} C) :=
  cotangentComplexDerivedBaseChange.{u, v, wB, wC} A (CommAlgCat.of A B) C

/-- **Stacks Project, Tag 08QS.**

The second vertex `L_{C/A}` of the displayed triangle, as an object of `D(C)`. -/
@[stacks 08QS "the second vertex of the displayed triangle, `L_{C/A}`, the target of the first \
  displayed morphism `CommAlgCat.fundamentalMor₁` and the source of the second, \
  `CommAlgCat.fundamentalMor₂`"]
noncomputable abbrev fundamentalVertex₂ : DerivedCategory (ModuleCat.{max u v} C) :=
  cotangentComplexDerived.{u, v, wC} A (CommAlgCat.of A C)

/-- **Stacks Project, Tag 08QS.**

The third vertex `L_{C/B}` of the displayed triangle, as an object of `D(C)`. -/
@[stacks 08QS "the third vertex of the displayed triangle, `L_{C/B}`, the target of the second \
  displayed morphism `CommAlgCat.fundamentalMor₂` and the source of the third, \
  `CommAlgCat.productFundamentalMor₃`, which lands in `(L_{B/A} ⊗^𝐋_B C)[1]`"]
noncomputable abbrev fundamentalVertex₃ : DerivedCategory (ModuleCat.{max u v} C) :=
  cotangentComplexDerived.{max u v, max u v, wC} B (CommAlgCat.of B C)

end Display

section Comparison

variable (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A}
  [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
  [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)]

omit [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)] in
/-- The second vertex of the display is the second vertex of the triangle of Tag 08SD. -/
theorem fundamentalVertex₂_eq_cotangentTriangle_obj₂ (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    cotangentComplexDerived.{u, v, wC} A C = (cotangentTriangle A f hf).obj₂ :=
  (cotangentTriangle_obj₂ A f hf).symm

/-- The first vertex of the display, formed along the ring map underlying `f`, is isomorphic to
the first vertex of the triangle of Tag 08SD. -/
theorem nonempty_fundamentalVertex₁_iso_cotangentTriangle_obj₁ (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            f.hom.toRingHom).functor.obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, v} A B)) ≅
        (cotangentTriangle A f hf).obj₁) :=
  nonempty_derivedExtensionScalars_cotangentTriangle_obj₁_iso.{u, v, wB, wC} A f hf

end Comparison

end CommAlgCat

end
