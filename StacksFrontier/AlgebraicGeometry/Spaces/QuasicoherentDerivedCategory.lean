module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
import StacksCore.Tactic.StacksAttribute

/-!
# The derived category with quasi-coherent cohomology on an algebraic space

For an algebraic space `F` over a scheme `S` contained in a big fppf site `B`, the category
`D_QCoh(𝒪_F)` is the full subcategory of the unbounded derived category of `𝒪_F`-modules cut
out by quasi-coherence of every cohomology sheaf.  Here `𝒪_F`-modules are the sheaves of
modules on the small étale ringed site of `F`, that is
`AlgebraicGeometry.Space.Modules`, and quasi-coherence is the predicate
`SheafOfModules.IsQuasicoherentOnSite` already used for the abelian category `QCoh(𝒪_F)` of
Stacks 03G9.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` is `D_QCoh(𝒪_F)`.

## Implementation notes

`DerivedCategoryB.derivedCategoryB` selects the objects of a derived category all of whose
cohomology objects satisfy a given property, so `D_QCoh(𝒪_F)` is its full subcategory for the
quasi-coherence predicate.  Taking the property to be
`SheafOfModules.isQuasicoherentOnSite` rather than Mathlib's `SheafOfModules.IsQuasicoherent`
is what keeps the universe of the module sections independent of the universe `u` of the
schemes, exactly as for `AlgebraicGeometry.Space.QuasicoherentSheaves`; Mathlib's predicate
would force them to agree.

The two sheafification hypotheses are the standard conditions under which Mathlib equips the
`𝒪_F`-modules at the chosen module universe with their abelian structure, and hence with a
derived category.  They are hypotheses rather than instances because
`AlgebraicGeometry.Space.RingedSite` provides them only for the *slices* of the small étale
topology; at the module universe `u` of the structure rings the unsliced forms are available
from `AlgebraicGeometry.Space.SmallEtale`, but the definition is stated at a free module
universe and so must take them.

This is a definition only.  `D_QCoh(𝒪_F)` is *not* yet known here to be a triangulated
subcategory of `D(𝒪_F)`: that is `DerivedCategoryB.derivedCategoryB_isTriangulated` applied to
the quasi-coherence predicate, whose hypothesis is that quasi-coherence on the small étale
site of an algebraic space is a weak Serre class, and no
`CategoryTheory.ObjectProperty.IsWeakSerreClass` instance for
`SheafOfModules.isQuasicoherentOnSite` exists in the library.

## References

* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 071X.** The category `D_QCoh(𝒪_F)`: the full subcategory of the unbounded derived
category of `𝒪_F`-modules whose objects have quasi-coherent cohomology sheaves in every
degree. -/
@[stacks 071X]
noncomputable abbrev QuasicoherentDerivedCategory
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}] :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)))).FullSubcategory

end AlgebraicGeometry.Space

end
