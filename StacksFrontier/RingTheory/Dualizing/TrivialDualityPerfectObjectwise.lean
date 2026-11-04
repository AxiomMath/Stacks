module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DiagonalModelHom

/-!
# Trivial duality for a perfect algebra, objectwise over the base

Let `f : R → A` be a homomorphism of commutative rings with `A` perfect as an `R`-module. Stacks
0BZE says that derived coextension of scalars `R Hom(A, -) : D(R) ⥤ D(A)` of Stacks 0A70 is the
derived tensor product `K ↦ K ⊗ᴸ_R R Hom(A, R)`. This file proves that identification **objectwise
and after restriction of scalars back to `R`**: for each object `K` of `D(R)` there is an
isomorphism

`R Hom_R(A, K) ≅ K ⊗ᴸ_R R Hom_R(A, R)`

of objects of `D(R)`, with no hypothesis beyond perfectness of `A`.

This is the half of Stacks 0BZE that the tree's bridges reach, and it is where perfectness is
actually spent. The K-flat route of
`StacksFrontier/RingTheory/Dualizing/TrivialDualityPerfectTensor.lean` carries an undischarged
hypothesis, pointwise invertibility of `Stacks0BZE.comparison` on the K-flat complexes. Here
nothing is carried: perfectness enters through the derived tensor--Hom diagonal of Stacks 0ATK,
exactly as the source spends it.

## What is proved and what is not

The statement is objectwise and lives in `D(R)`, where Stacks 0BZE asserts an isomorphism of
functors `D(R) ⥤ D(A)`. Two steps separate the two, and neither is available:

* The comparison `Dualizing.modelHomIsoRestrictScalarsDerivedHom` between the internal derived
  Hom of Stacks 0A63 and restricted derived coextension is produced at one object from a chosen
  K-injective representative, and its naturality is not asserted; so the chain of isomorphisms
  below is not natural in `K`.
* Even granted naturality, the resulting isomorphism of functors would live in `D(R)`. Lifting
  it to `D(A)` means showing that the canonical `D(A)`-morphism `Stacks0BZE.comparison` — the
  transpose under Stacks 0A70 of the tensored derived counit, built from a chain-level fraction —
  is the tensor--Hom diagonal of Stacks 0ATK, which is built from the coevaluation and the
  composition of the model internal Hom. Restriction of scalars is conservative but not full, so
  an isomorphism of restrictions does not descend.

## Main results

* `Dualizing.nonempty_restrictScalars_derivedHom_iso_derivedTensor_unitDual`: **Stacks 0BZE**,
  objectwise and after restriction of scalars.

## Implementation notes

Everything happens at the module universe equal to the ring universe. That is forced twice over:
`StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal`, which Stacks 0ATK proves invertible,
is defined only there, and so is the comparison of
`StacksFrontier/RingTheory/Dualizing/DerivedHomothety/DiagonalModelHom.lean`. The forms of
Stacks 0BZE in the reduction files are stated with an independent module universe above the
ring's, and specialise to this one.

The tensor factor is written as derived coextension evaluated at the complex `R` in degree zero,
which is the tensor unit of the monoidal category of cochain complexes; the right unitor of the
derived tensor product is therefore available at it, and that is the step turning
`R Hom(A, K ⊗ᴸ_R R)` into `R Hom(A, K)`.

## References

* [The Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE), the statement.
* [The Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK), the derived
  tensor--Hom diagonal, whose first case is perfectness of the internal-Hom source.
* [The Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63) for the internal
  derived Hom, [Tag 0A70](https://stacks.math.columbia.edu/tag/0A70) for derived coextension of
  scalars and [Tag 0657](https://stacks.math.columbia.edu/tag/0657) for perfectness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom.DerivedInternalHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **Stacks 0BZE, objectwise and after restriction of scalars.** Let `f : R → A` be a
homomorphism of commutative rings with `A` perfect as an `R`-module. For every object `K` of
`D(R)`, derived coextension of scalars `R Hom(A, K)` of Stacks 0A70, read in `D(R)` by
restriction of scalars along `f`, is the derived tensor product of `K` with `R Hom(A, R)` read in
the same way.

Perfectness is consumed, not recorded: it is the first case of the derived tensor--Hom diagonal
of Stacks 0ATK, applied with the diagonal's internal-Hom source the module `A` placed in degree
zero and read over `R`. The two vocabularies are reconciled by
`Dualizing.nonempty_modelHomIsoRestrictScalarsDerivedHom`, which identifies the internal derived
Hom of Stacks 0A63 out of that object with restricted derived coextension, and the tensor factor
`K ⊗ᴸ_R R` is cut down by the right unitor of the derived tensor product.

Stacks 0BZE asserts more: an isomorphism of functors `D(R) ⥤ D(A)`. Both of the missing steps —
naturality of the comparison in `K`, and the identification of `Stacks0BZE.comparison` with the
diagonal that would carry an isomorphism in `D(R)` up to `D(A)` — are discussed in this module's
documentation. For the form of Stacks 0BZE that asserts the isomorphism of functors and carries
those steps as hypotheses, see `Stacks0BZE.cardIso` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlat`; for the unconditional form, see
`Dualizing.exists_derivedHom_iso_derivedTensor` of
`StacksFrontier.RingTheory.Dualizing.DerivedHomPerfectTensor`. -/
@[stacks 0BZE "objectwise and after restriction of scalars to the base"]
theorem nonempty_restrictScalars_derivedHom_iso_derivedTensor_unitDual (f : R →+* A)
    (hperfect : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    Nonempty
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} f).obj K) ≅
        (Model.tensor R).obj
          (K, (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
            ((derivedHom.{u, u, u} f).obj
              (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
                  (ModuleCat.of R R)))))) := by
  set U := DerivedCategory.Q.obj
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) with hUdef
  set AR := (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) with hARdef
  have hAR : StacksDraft.Perfect.IsPerfect AR :=
    StacksDraft.Perfect.isPerfect_of_iso
      (((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of A A)) hperfect
  have hdiag := Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal K U AR 0
    (Or.inl hAR)
  obtain ⟨bK⟩ := nonempty_modelHomIsoRestrictScalarsDerivedHom f K
  obtain ⟨bU⟩ := nonempty_modelHomIsoRestrictScalarsDerivedHom f U
  exact ⟨bK.symm ≪≫
    (Model.hom R).mapIso (Iso.prod (Iso.refl (Opposite.op AR))
        ((Model.adjunction R).tensorRightUnitor.app K).symm) ≪≫
      (@asIso _ _ _ _ _ hdiag).symm ≪≫
      (Model.tensor R).mapIso (Iso.prod (Iso.refl K) bU)⟩

end Dualizing

end
