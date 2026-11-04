module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafTensorComparison
public import StacksFrontier.Homology.DerivedCategory.Monoidal.BoundedBelowSubcategory

/-!
# The bounded below derived category of abelian sheaves

`Stacks.Cohomology.derivedMonoidalAbelianSheavesOfKFlat` makes the *unbounded* derived category
of abelian sheaves on a site monoidal, unconditionally.  The hypercohomology of abelian sheaves
is instead computed in `DerivedCategory.Plus`, and this file says exactly what is left to do
there: `CochainComplex.KFlatMonoidal.derivedPlusMonoidal` at the abelian sheaves.

**The unit half is unconditional** — `containsUnit_plus_abelianSheaves`, and
`Leray.containsUnit_plus_abelianSheaf` on a space.  **The stability half is not, and it is not a
formality.**  The derived tensor product is computed from K-flat representatives, so the
degreewise bound (`Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_of_isZero` is the
statement that bounded below complexes have a total complex at all) does not by itself bound the
derived tensor product below; what is needed is that a bounded below complex of abelian sheaves
admits a K-flat resolution which is itself bounded below, and that is the hypothesis `hGE` here.

That hypothesis is true for abelian sheaves, with `a' = a - 1`: an abelian sheaf is a quotient
of a sheafified direct sum of copies of `ℤ_U`, a subsheaf of a torsion-free abelian sheaf is
torsion-free, and a torsion-free abelian sheaf is flat, so abelian sheaves have flat dimension at
most one.  It is *not* true for a general monoidal abelian category — over `k[x]/(x²)` the
residue field lies in `D^{≥ 0}` and its derived self-tensor lies in no `D^{≥ n}` — so no general
lemma can supply it, and nothing in this library supplies it for abelian sheaves yet.  The
companion bound in the other direction needs none of this: the derived tensor product is right
t-exact, which is `Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor` on a ringed site.

## Main results

* `Stacks.Cohomology.containsUnit_plus_abelianSheaves`,
  `Stacks.Cohomology.Leray.containsUnit_plus_abelianSheaf`: **the unit of the derived tensor
  product of abelian sheaves is bounded below**, unconditionally.
* `Stacks.Cohomology.derivedPlusMonoidalAbelianSheaves`,
  `Stacks.Cohomology.Leray.derivedPlusMonoidalAbelianSheaf`: **the bounded below derived
  category of abelian sheaves is monoidal**, given bounded below K-flat resolutions.

## Implementation notes

`HasDerivedCategory` is data, so it is carried as an instance binder rather than seated here: a
second instance would be a second derived category.  It is already seated for
`Stacks.Cohomology.Leray.AbelianSheaf` by
`StacksFrontier/Topology/Sheaves/Cohomology/Leray/AbelianSheafSpectralSequence.lean`.

The monoidal structures are seated with `attribute [local instance]` exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafDerivedTensor.lean`, each link named rather
than left to a chain of `inferInstance`: the abelian-sheaf monoidal structure is reached from
`CategoryTheory.Sheaf.monoidalCategory` only through several steps, and leaving the chain to
search is what turns a one-second file into a heartbeat timeout reported against an unrelated
goal.

## References

* [The Stacks Project, Tag 06YI](https://stacks.math.columbia.edu/tag/06YI)
* [The Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonoidalClosed.FunctorCategory

universe u v

namespace Stacks.Cohomology

section Site

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{u}] [HasSheafify J RingCat.{u}]
  [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal
  AddCommGrpCat.symmetricCategoryTransported
  AddCommGrpCat.monoidalClosed MonoidalClosed.enrichedOrdinaryCategorySelf
  Sheaf.monoidalCategory Sheaf.symmetricCategory
  braidedCategoryCochainComplexAbelianSheaves

/-- **The unit of the derived tensor product of abelian sheaves on a site is bounded below.**
This is `CochainComplex.KFlatMonoidal.containsUnit_plus` at the abelian sheaves, where the
hypothesis on K-flat resolutions is `Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves`:
the unit is the image of the unit of the complexes, which is the constant sheaf `ℤ` placed in
degree `0`.  It is the half of `CategoryTheory.ObjectProperty.IsMonoidal` for the bounded below
objects that needs nothing further. -/
theorem containsUnit_plus_abelianSheaves
    [HasDerivedCategory.{v} (Sheaf J AddCommGrpCat.{u})] :
    letI := derivedMonoidalAbelianSheavesOfKFlat J
    (DerivedCategory.TStructure.t (C := Sheaf J AddCommGrpCat.{u})).plus.ContainsUnit :=
  CochainComplex.KFlatMonoidal.containsUnit_plus _
    (exists_kFlat_resolution_abelianSheaves J)

/-- **The bounded below derived category of abelian sheaves on a site is monoidal**, under the
derived tensor product of `Stacks.Cohomology.derivedMonoidalAbelianSheavesOfKFlat`, as soon as
every bounded below cochain complex of abelian sheaves receives a quasi-isomorphism from a
K-flat complex which is itself bounded below.

This is `CochainComplex.KFlatMonoidal.derivedPlusMonoidal` at the abelian sheaves.  The
unbounded structure needs no such hypothesis, `hGE` being the whole difference between
`DerivedCategory` and `DerivedCategory.Plus` for the derived tensor product. -/
@[instance_reducible] def derivedPlusMonoidalAbelianSheaves
    [HasDerivedCategory.{v} (Sheaf J AddCommGrpCat.{u})]
    (hGE : ∀ (a : ℤ) (G : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (f : P ⟶ G),
        P.IsStrictlyGE a' ∧
          CochainComplex.KFlatBifunctor.KFlat
            (curriedTensor (Sheaf J AddCommGrpCat.{u})) P ∧ QuasiIso f) :
    MonoidalCategory (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{u})) :=
  CochainComplex.KFlatMonoidal.derivedPlusMonoidal _
    (exists_kFlat_resolution_abelianSheaves J) hGE

end Site

namespace Leray

attribute [local instance] abelianSheafMonoidalCategory
  braidedCategoryCochainComplexAbelianSheaf

/-- **The derived category of abelian sheaves on a topological space is monoidal,
unconditionally.** This is `Stacks.Cohomology.derivedMonoidalAbelianSheavesOfKFlat` at the
open-cover topology, its hypothesis discharged by
`Stacks.Cohomology.Leray.exists_kFlat_resolution_abelianSheaf`.  It is the unbounded structure,
named here so that the bounded below statements below have something to restrict. -/
@[instance_reducible] def derivedMonoidalAbelianSheafOfKFlat (X : TopCat.{u})
    [HasDerivedCategory.{v} (AbelianSheaf X)] :
    MonoidalCategory (DerivedCategory (AbelianSheaf X)) :=
  CochainComplex.KFlatMonoidal.derivedMonoidal _ (exists_kFlat_resolution_abelianSheaf X)

/-- **The unit of the derived tensor product of abelian sheaves on a topological space is bounded
below.** This is `Stacks.Cohomology.containsUnit_plus_abelianSheaves` at the open-cover
topology. -/
theorem containsUnit_plus_abelianSheaf (X : TopCat.{u})
    [HasDerivedCategory.{v} (AbelianSheaf X)] :
    letI := derivedMonoidalAbelianSheafOfKFlat X
    (DerivedCategory.TStructure.t (C := AbelianSheaf X)).plus.ContainsUnit :=
  CochainComplex.KFlatMonoidal.containsUnit_plus _
    (exists_kFlat_resolution_abelianSheaf X)

/-- **The bounded below derived category of abelian sheaves on a topological space is monoidal**,
given bounded below K-flat resolutions.  This is
`Stacks.Cohomology.derivedPlusMonoidalAbelianSheaves` at the open-cover topology, and it is the
category the hypercohomology of abelian sheaves is computed in. -/
@[instance_reducible] def derivedPlusMonoidalAbelianSheaf (X : TopCat.{u})
    [HasDerivedCategory.{v} (AbelianSheaf X)]
    (hGE : ∀ (a : ℤ) (G : CochainComplex (AbelianSheaf X) ℤ), G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex (AbelianSheaf X) ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
        CochainComplex.KFlatBifunctor.KFlat (curriedTensor (AbelianSheaf X)) P ∧ QuasiIso f) :
    MonoidalCategory (DerivedCategory.Plus (AbelianSheaf X)) :=
  CochainComplex.KFlatMonoidal.derivedPlusMonoidal _
    (exists_kFlat_resolution_abelianSheaf X) hGE

end Leray

end Stacks.Cohomology

end
