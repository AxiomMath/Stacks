module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafDerivedTensor
public import StacksFrontier.Homology.KFlat.MonoidalResolutionTransport
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft

/-!
# K-flat resolutions of complexes of abelian groups, and the monoidal derived category `D(Ab)`

The abelian groups carry the tensor product transported from the modules over a universe-lifted
copy of the integers, `AddCommGrpCat.monoidalCategory`. This file supplies the three inputs that
the *unbounded* derived tensor product needs there, and assembles them: every cochain complex of
abelian groups receives a quasi-isomorphism from a K-flat one, the cochain complexes of abelian
groups are braided monoidal under the total tensor complex, and therefore `D(Ab)` is monoidal.

Unlike the abelian sheaves of
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafDerivedTensor.lean`, where the existence of
K-flat resolutions is left as the hypothesis `hres` of
`CochainComplex.KFlatMonoidal.derivedMonoidal`, here that hypothesis is *discharged*: the
monoidal equivalence `AddCommGrpCat.uliftIntEquivalence` presents abelian groups as modules over
a ring, where K-flat resolutions are unconditional. So
`AddCommGrpCat.derivedMonoidal` carries no hypothesis beyond the choice of a derived category.

## Main definitions

* `AddCommGrpCat.braidedCategoryCochainComplex`: **the cochain complexes of abelian groups are
  braided monoidal** under the total tensor complex, the braiding being the Koszul symmetry of
  `CochainComplex.braidedCategory`.
* `AddCommGrpCat.derivedMonoidal`: **the derived category of abelian groups is monoidal**, under
  the derived tensor product.

## Main results

* `AddCommGrpCat.exists_kFlat_quasiIso`: **every cochain complex of abelian groups receives a
  quasi-isomorphism from one which is K-flat for the tensor product of abelian groups.**

## Implementation notes

**The tensor product here is the transported one, and it is the only monoidal structure on
`AddCommGrpCat` in scope.** Mathlib's monoidal structure on abelian groups is the cartesian one,
whose unit is the trivial group, and it is not the structure any of this is about. It is not
reachable by instance search in this import closure — with the four transported structures below
left unseated, `MonoidalCategory AddCommGrpCat` fails to synthesize rather than resolving to the
cartesian product — so the statements of this file are unambiguous. The transported structures
are nevertheless seated by hand, as `AddCommGrpCat.monoidalCategory` and its companions are
`@[instance_reducible]` definitions rather than instances, for exactly that reason.

The three graded-object hypotheses of `CochainComplex.braidedCategory` —
`CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor`, `HasGoodTensorTensor₂₃` and
`HasTensor₄ObjExt` — are found by instance search only once `AddCommGrpCat.monoidalClosed` is in
scope: they ask that tensoring with a fixed abelian group commute with the antidiagonal
coproducts, which holds because it is a left adjoint. This is the same route the abelian sheaves
take through `Stacks.Cohomology.monoidalClosed_abelianSheaves`.

**The hypothesis of `AddCommGrpCat.derivedMonoidal` is satisfiable**, so the statement is not
vacuous: `HasDerivedCategory.standard` supplies `HasDerivedCategory.{v + 1} AddCommGrpCat.{v}`.
It is left as a hypothesis, in its own universe, because which derived category is meant is a
choice the consumer makes, as everywhere else in the library.

## References

* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal
  AddCommGrpCat.symmetricCategoryTransported
  AddCommGrpCat.monoidalClosed

universe w v

namespace AddCommGrpCat

/-- **Stacks 06Y4 for abelian groups.** Every cochain complex of abelian groups receives a
quasi-isomorphism from a complex which is K-flat for the tensor product of abelian groups.

This is the module-level statement
`CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso` over the universe-lifted integers,
transported along the monoidal equivalence `AddCommGrpCat.uliftIntEquivalence` by
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_monoidalEquivalence`. No resolution is
constructed on the abelian-group side.

It is the hypothesis `hres` of `CochainComplex.KFlatMonoidal.derivedMonoidal`, which is why
`AddCommGrpCat.derivedMonoidal` below is unconditional. -/
theorem exists_kFlat_quasiIso (G : CochainComplex AddCommGrpCat.{v} ℤ) :
    ∃ (P : CochainComplex AddCommGrpCat.{v} ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor AddCommGrpCat.{v}) P ∧ QuasiIso f :=
  CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_monoidalEquivalence
    (uliftIntEquivalence.{v})
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso (ULiftInt.{v})) G

/-- **The cochain complexes of abelian groups are braided monoidal** under the total tensor
complex, the braiding being the Koszul symmetry of `CochainComplex.braidedCategory`.

This is the second input `CochainComplex.KFlatMonoidal.derivedMonoidal` carries on top of the
existence of K-flat resolutions. Like `CochainComplex.braidedCategory` itself it is not an
instance: the cochain complexes of abelian groups have no monoidal structure in scope until one
is seated. The symmetric refinement needs no new name — with the instances of this file in scope
`CochainComplex.symmetricCategory AddCommGrpCat.{v}` elaborates directly. -/
@[instance_reducible] def braidedCategoryCochainComplex :
    BraidedCategory (CochainComplex AddCommGrpCat.{v} ℤ) :=
  CochainComplex.braidedCategory _

attribute [local instance] braidedCategoryCochainComplex

/-- **The derived category of abelian groups is monoidal**, under the derived tensor product.

This is `CochainComplex.KFlatMonoidal.derivedMonoidal` at the abelian groups, with its
hypothesis `hres` discharged by `AddCommGrpCat.exists_kFlat_quasiIso`. The tensor product is
obtained by localizing the K-flat complexes, so on K-flat complexes it is the total tensor
complex and no coherence diagram is checked.

Contrast `Stacks.Cohomology.derivedMonoidalAbelianSheaves`, which must carry `hres` as a
hypothesis because the abelian sheaves are not known to be equivalent to modules over a ring
compatibly with their tensor product. -/
@[instance_reducible] def derivedMonoidal [HasDerivedCategory.{w} AddCommGrpCat.{v}] :
    MonoidalCategory (DerivedCategory AddCommGrpCat.{v}) :=
  CochainComplex.KFlatMonoidal.derivedMonoidal _ exists_kFlat_quasiIso

end AddCommGrpCat

end
