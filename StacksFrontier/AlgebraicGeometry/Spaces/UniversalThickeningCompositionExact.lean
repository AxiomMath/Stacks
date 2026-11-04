module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSquareExact
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningCompositionComplex

/-!
# Exactness of the conormal sequence of a composition of universal first-order thickenings

Let `Z ⟶ Y ⟶ X` be morphisms of algebraic spaces over `S`, with universal first-order
thickenings `Z ⊂ Z'` and `Y ⊂ Y'` over `X`, and let `h : Z' ⟶ Y'` be the morphism of clause (1)
of Stacks 06BF (`AlgebraicGeometry.Space.universalThickeningCompMap`).  Clause (2) of Stacks 06BF
asserts that the conormal sequence

`i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`

is exact.  `StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningComposition.lean` carries the
epimorphism at the right and the vanishing of the composite; the exactness in the middle is the
instance of `AlgebraicGeometry.Space.exact_conormalMap_square` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSquareExact.lean`, and this file puts the
whole clause on one declaration.

## Main results

* `AlgebraicGeometry.Space.exact_and_epi_universalThickeningCompConormalMapSquare`: **Stacks 06BF,
  clause (2)**, exactness of the conormal sequence of the composition at both of its terms.
* `AlgebraicGeometry.Space.universalThickeningCompConormalSequence_f_eq` and `..._g_eq`: the two
  arrows of that short complex are, by definition, the arrows of
  `AlgebraicGeometry.Space.universalThickeningConormalMap_comp_conormalMap_eq_zero`.

## Implementation notes

The short complex of the main theorem is formed at the vanishing proof of
`AlgebraicGeometry.Space.exact_conormalMap_square`, not at the one of
`UniversalThickeningComposition.lean`.  The two proofs are of the same statement up to the
definitional unfolding of the abbreviations naming the fibre product `h⁻¹(Y)` and the copy of `Z`
in it, and their arrows agree by `rfl` (the two lemmas below); but the two files find the zero
morphisms of the category of modules along different instance paths, and the kernel does not
identify those paths within its budget.  Stating the theorem at one proof keeps every comparison
inside one file's instances.  The `rfl` comparisons of the arrows are checked with `conormalMap`
and `modulePullback` locally irreducible, for the whole file, since unfolding either is what
exhausts the budget.

## References

* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

-- Unfolding the inverse image of modules or the conormal map, neither of which any statement
-- below needs, is what exhausts the budget; see the implementation notes.
attribute [local irreducible] modulePullback conormalMap

/-- **Stacks 06BF, clause (2).**  Let `Z ⟶ Y ⟶ X` be morphisms of algebraic spaces, `Z ⊂ Z'`
and `Y ⊂ Y'` universal first-order thickenings over `X`, and `h : Z' ⟶ Y'` the morphism of
clause (1).  The conormal sequence

`i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`

is exact: exact at `𝒞_{Z/X}`, and its right-hand map is an epimorphism.  Here `𝒞_{Z/X}` is the
conormal module of `Z ⊂ Z'`, `𝒞_{Y/X}` that of `Y ⊂ Y'`, and `𝒞_{Z/Y}` that of the copy of `Z`
inside the universal first-order thickening `Y ×_{Y'} Z' = h⁻¹(Y)` of clause (1); the two maps
are those of Stacks 04CP, for the square of `Z ⊆ Z'` over `Y ⊆ Y'` with ambient morphism `h`
(pulled back to the copy of `Z`) and for the inclusion `h⁻¹(Y) ⟶ Z'`.  They are the arrows of
`AlgebraicGeometry.Space.universalThickeningConormalMap_comp_conormalMap_eq_zero`, by
`AlgebraicGeometry.Space.universalThickeningCompConormalSequence_f_eq` and `..._g_eq`.

Exactness in the middle is `AlgebraicGeometry.Space.exact_conormalMap_square` at that square;
the epimorphism is the surjectivity clause of Stacks 04CQ for the inclusion `h⁻¹(Y) ⟶ Z'`. -/
@[stacks 06BF "clause (2): the conormal sequence i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0 is exact"]
theorem exact_and_epi_universalThickeningCompConormalMapSquare :
    (ShortComplex.mk _ _ (conormalMap_square_comp_eq_zero B S hS
        (universalThickeningCompMap B S hS i hZ hY hfac)
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        (ObjectProperty.homMk i)
        (universalThickeningComp_subspace_square B S hS i hZ hY hfac))).Exact ∧
      Epi (ShortComplex.mk _ _ (conormalMap_square_comp_eq_zero B S hS
        (universalThickeningCompMap B S hS i hZ hY hfac)
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        (ObjectProperty.homMk i)
        (universalThickeningComp_subspace_square B S hS i hZ hY hfac))).g :=
  ⟨exact_conormalMap_square B S hS (universalThickeningCompMap B S hS i hZ hY hfac)
    ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
    ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
    (ObjectProperty.homMk i) (universalThickeningComp_subspace_square B S hS i hZ hY hfac),
    epi_conormalMap B S hS (squareFibreInclusion B S hS
      (universalThickeningCompMap B S hS i hZ hY hfac)
      ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩)
      ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩⟩

/-- The left-hand arrow of
`AlgebraicGeometry.Space.exact_and_epi_universalThickeningCompConormalMapSquare`
is that of `AlgebraicGeometry.Space.universalThickeningConormalMap_comp_conormalMap_eq_zero`. -/
theorem universalThickeningCompConormalSequence_f_eq :
    (ShortComplex.mk _ _ (conormalMap_square_comp_eq_zero B S hS
        (universalThickeningCompMap B S hS i hZ hY hfac)
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        (ObjectProperty.homMk i)
        (universalThickeningComp_subspace_square B S hS i hZ hY hfac))).f =
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).f := rfl

/-- The right-hand arrow of
`AlgebraicGeometry.Space.exact_and_epi_universalThickeningCompConormalMapSquare`
is that of `AlgebraicGeometry.Space.universalThickeningConormalMap_comp_conormalMap_eq_zero`. -/
theorem universalThickeningCompConormalSequence_g_eq :
    (ShortComplex.mk _ _ (conormalMap_square_comp_eq_zero B S hS
        (universalThickeningCompMap B S hS i hZ hY hfac)
        ⟨Y, (IsNthOrderThickening.isThickening B S hS hY.firstOrder).1⟩
        ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩
        (ObjectProperty.homMk i)
        (universalThickeningComp_subspace_square B S hS i hZ hY hfac))).g =
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).g := rfl

end AlgebraicGeometry.Space

end
