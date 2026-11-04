module

public import StacksFrontier.Cotangent.FibreProductStalk
public import StacksFrontier.Cotangent.HenselizationUnconditional

/-!
# Step 3 of the proof of Tag 09DM, with Proposition 08QX supplied

`CommAlgCat.nonempty_derivedBaseChangeObj_cotangentComplexDerived_iso_of_henselization` of
`StacksFrontier.Cotangent.FibreProductStalk` identifies the derived base change of
`L_{A ⊗_R B/R}` along a henselization `A ⊗_R B ⟶ C` with `L_{C/R}`, given two instances of
Proposition 08QX as parameters: the fundamental triangle of `R ⟶ A ⊗_R B ⟶ C`, and the family
`CommAlgCat.HasEtaleDiagonalTriangle` of triangles of the diagonal towers of the étale
`A ⊗_R B`-algebras.

Proposition 08QX holds for arbitrary ring maps, so Tag 08UN holds with nothing but the
henselization assumed, as
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional` of
`StacksFrontier.Cotangent.HenselizationUnconditional`; read at `A ⊗_R B`, that is the identification
below, with no parameter beyond the henselization.

## Main results

* `CommAlgCat.nonempty_derivedBaseChangeObj_cotangentComplexDerived_iso_of_isHenselization`:
  `L_{A ⊗_R B/R} ⊗^𝐋_{A ⊗_R B} C ≅ L_{C/R}` for a henselization `C` of the local ring `A ⊗_R B`.

## References

* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 08UN](https://stacks.math.columbia.edu/tag/08UN)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped TensorProduct

universe u v

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- **Step 3 of the source's proof of Stacks 09DM, with nothing carried.** If the local ring
`A ⊗_R B` has henselization `C`, with residue field extension `L`, then the derived base change
of `L_{A ⊗_R B/R}` along `A ⊗_R B ⟶ C` is `L_{C/R}`: this identifies the middle vertex of the
base-changed nine diagram with the cotangent complex of `C` over `R`.

This is Tag 08UN at `A ⊗_R B`, in the form
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional`,
which assumes nothing beyond the henselization. -/
public theorem nonempty_derivedBaseChangeObj_cotangentComplexDerived_iso_of_isHenselization
    (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [IsLocalRing (A ⊗[R] B)]
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField (A ⊗[R] B)) L]
    (C : Type u) [CommRing C] [IsLocalRing C] [Algebra (A ⊗[R] B) C]
    [IsLocalRing.IsHenselization (A ⊗[R] B) L C] [Algebra R C]
    [IsScalarTower R (A ⊗[R] B) C] :
    Nonempty (derivedBaseChangeObj C
        (cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))) ≅
      cotangentComplexDerived R (CommAlgCat.of R C)) :=
  nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization_unconditional R (A ⊗[R] B) L C

end CommAlgCat

end
