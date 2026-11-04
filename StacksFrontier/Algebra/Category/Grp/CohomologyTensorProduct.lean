module

public import StacksFrontier.AlgebraicGeometry.Spaces.AddCommGrpCatDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafMonoidalPreadditive
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatCohomologyTensor

/-!
# The Künneth map on the derived category of abelian groups

The derived category of abelian groups is monoidal under the derived tensor product
(`AddCommGrpCat.derivedMonoidal`), the tensor product being the one transported from the modules
over a universe-lifted copy of the integers.  This file supplies the Künneth map

`Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ L)`

there, for any two objects `K` and `L` of `D(Ab)`, by instantiating the construction of
`StacksFrontier/Homology/DerivedCategory/Monoidal/KFlatCohomologyTensor.lean` at the abelian groups.

## Main definitions

* `AddCommGrpCat.tensorHomology`: **the cohomology product of two cochain complexes of abelian
  groups**, `Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`, on the total tensor complex.
* `AddCommGrpCat.kFlatComparison`: the identification of the derived tensor product of two
  K-flat complexes of abelian groups with their total tensor complex.
* `AddCommGrpCat.cohomologyTensorProduct`: **the Künneth map on `D(Ab)`**, together with the
  cocycle formula that pins it down.

## Main results

* `AddCommGrpCat.homologyπ_tensorHomology`: the cohomology product of two complexes of abelian
  groups is the map induced by tensoring cocycles.
* `AddCommGrpCat.tensorHomology_naturality`: that product is natural in both complexes.
* `AddCommGrpCat.cohomologyTensorProduct_map_cocycles`: the cocycle formula for the Künneth map
  on `D(Ab)`, on the K-flat representatives it was built from.

## Implementation notes

**The tensor product here is the transported one**, `AddCommGrpCat.monoidalCategory`, and not
Mathlib's cartesian monoidal structure on abelian groups; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AddCommGrpCatDerivedMonoidal.lean`.  All four transported
structures have to be seated by hand, as they are `@[instance_reducible]` definitions rather than
instances.

The colimit-preservation hypothesis of the generic construction is discharged by instance
search: tensoring on the left with an abelian group preserves colimits because it is a left
adjoint, `AddCommGrpCat.monoidalClosed`.  The matching statement on the right comes from the
braiding inside the generic file.

Nothing is reproved on the abelian-group side: the cocycle construction, the cokernel argument
producing the product on cohomology and the transport along the chosen K-flat representatives all
live in the generic file, whose hypotheses are satisfied here.  In particular the agreement with
the module-level map `RingTheory.TorProducts.cohomologyTensorProduct` is not asserted as an
equation between the two — they are maps in two different derived categories — but both are
characterised by the same cocycle formula `[p] ⊗ [q] ↦ [p ⊗ q]`, which is the content of
`maps_cocycles` on either side.

## References

* [The Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal
  AddCommGrpCat.symmetricCategoryTransported
  AddCommGrpCat.monoidalClosed
  AddCommGrpCat.braidedCategoryCochainComplex

universe w v

namespace AddCommGrpCat

/-! ### The cohomology product of two cochain complexes of abelian groups -/

/-- **The cohomology product of two cochain complexes of abelian groups**,
`Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)`, where `P ⊗ Q` is the total tensor complex. -/
def tensorHomology (P Q : CochainComplex AddCommGrpCat.{v} ℤ) (i j : ℤ) :
    P.homology i ⊗ Q.homology j ⟶ (P ⊗ Q).homology (i + j) :=
  CochainComplex.KFlatMonoidal.tensorHomology P Q i j

/-- **The cohomology product of two complexes of abelian groups is the map induced by tensoring
cocycles**: the tensor of the classes of two cocycles is the class of their tensor. -/
lemma homologyπ_tensorHomology (P Q : CochainComplex AddCommGrpCat.{v} ℤ) (i j : ℤ) :
    (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ tensorHomology P Q i j =
      CochainComplex.KFlatMonoidal.tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) :=
  CochainComplex.KFlatMonoidal.homologyπ_tensorHomology P Q i j

/-- **The cohomology product of two complexes of abelian groups is natural in both
complexes.** -/
lemma tensorHomology_naturality {P P' Q Q' : CochainComplex AddCommGrpCat.{v} ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j : ℤ) :
    (HomologicalComplex.homologyMap f i ⊗ₘ HomologicalComplex.homologyMap g j) ≫
        tensorHomology P' Q' i j =
      tensorHomology P Q i j ≫ HomologicalComplex.homologyMap (f ⊗ₘ g) (i + j) :=
  CochainComplex.KFlatMonoidal.tensorHomology_naturality f g i j

/-! ### The Künneth map on `D(Ab)` -/

section Derived

variable [HasDerivedCategory.{w} AddCommGrpCat.{v}]

attribute [local instance] derivedMonoidal

/-- **For K-flat complexes of abelian groups the tensor product of `D(Ab)` is the image of the
total tensor complex.**  This is `CochainComplex.KFlatMonoidal.derivedTensorIso` with its
hypothesis discharged by `AddCommGrpCat.exists_kFlat_quasiIso`. -/
def kFlatComparison :
    CochainComplex.KFlatMonoidal.KFlatComparison AddCommGrpCat.{v} :=
  fun _ _ hP hQ ↦
    CochainComplex.KFlatMonoidal.derivedTensorIso AddCommGrpCat.{v} exists_kFlat_quasiIso hP hQ

/-- **The Künneth map on the derived category of abelian groups.**  For any two objects `K` and
`L` of `D(Ab)`, tensoring cocycles gives the canonical map

`Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ L)`,

and the result records K-flat representatives on which it is induced by
`CochainComplex.KFlatMonoidal.tensorCycles`, so the map comes with the formula
`[p] ⊗ [q] ↦ [p ⊗ q]` that determines it.

This is the module-level `RingTheory.TorProducts.cohomologyTensorProduct` transported to the
abelian groups: the construction is the generic one of
`CochainComplex.KFlatMonoidal.cohomologyTensorProduct`, whose inputs here are the monoidal
structure `AddCommGrpCat.monoidalCategory` transported along
`AddCommGrpCat.uliftIntEquivalence` and the unconditional supply of K-flat resolutions
`AddCommGrpCat.exists_kFlat_quasiIso` that the same equivalence provides. -/
def cohomologyTensorProduct (K L : DerivedCategory AddCommGrpCat.{v}) (i j : ℤ) :
    CochainComplex.KFlatMonoidal.CohomologyTensorProduct AddCommGrpCat.{v}
      kFlatComparison K L i j :=
  CochainComplex.KFlatMonoidal.cohomologyTensorProduct AddCommGrpCat.{v} kFlatComparison
    exists_kFlat_quasiIso K L i j

/-- **On the chosen K-flat representatives the Künneth map of `D(Ab)` sends the tensor of two
cohomology classes to the class of the tensor of their cocycle representatives.** -/
lemma cohomologyTensorProduct_map_cocycles
    (K L : DerivedCategory AddCommGrpCat.{v}) (i j : ℤ) :
    ∃ (P Q : CochainComplex AddCommGrpCat.{v} ℤ)
      (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor AddCommGrpCat.{v}) P)
      (hQ : CochainComplex.KFlatBifunctor.KFlat (curriedTensor AddCommGrpCat.{v}) Q)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L)
      (z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j)),
      z ≫ (P ⊗ Q).iCycles (i + j) =
          (P.iCycles i ⊗ₘ Q.iCycles j) ≫
            HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ∧
        (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
              ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} i).inv.app P ⊗ₘ
                (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} j).inv.app Q) ≫
              ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} i).map eP.hom ⊗ₘ
                (DerivedCategory.homologyFunctor AddCommGrpCat.{v} j).map eQ.hom) ≫
              (cohomologyTensorProduct K L i j).map ≫
              (DerivedCategory.homologyFunctor AddCommGrpCat.{v} (i + j)).map
                ((eP.inv ⊗ₘ eQ.inv) ≫ (kFlatComparison P Q hP hQ).hom) ≫
              (DerivedCategory.homologyFunctorFactors
                AddCommGrpCat.{v} (i + j)).hom.app (P ⊗ Q) =
            z ≫ (P ⊗ Q).homologyπ (i + j) :=
  (cohomologyTensorProduct K L i j).maps_cocycles

end Derived

end AddCommGrpCat

end
