module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor

/-!
# The tensor product of abelian sheaves on a small étale site

Let `X` be a scheme. Abelian sheaves on the small étale site of `X`, with values in
`AddCommGrpCat.{max (u + 1) v}` as everywhere in the étale development, form a monoidal category
for the tensor product over `ℤ`: `F ⊗ G` is the sheafification of the presheaf
`U ↦ F(U) ⊗_ℤ G(U)`. This file records that structure, which is the one the derived tensor
product of abelian étale sheaves is built from.

## Main definitions

* `AddCommGrpCat.braidedCategoryGeneral`, `AddCommGrpCat.monoidalClosedGeneral`: the braiding and
  the closed structure of the tensor product of abelian groups `AddCommGrpCat.monoidalCategory`,
  at an arbitrary universe.
* `Stacks.EtaleCohomology.etaleAbelianMonoidalCategory`: the monoidal structure on abelian
  sheaves on the small étale site, Mathlib's `CategoryTheory.Sheaf.monoidalCategory` for the
  tensor product of abelian groups.
* `Stacks.EtaleCohomology.etaleAbelianTensor`: its tensor product, as a bifunctor.

## Implementation notes

`AddCommGrpCat.monoidalCategory` is the transport of the monoidal structure of modules over a
copy of `ℤ` in the universe of the groups; its braiding and closed structure are transported the
same way. None of the three is a global instance (the cartesian monoidal structure of
`AddCommGrpCat` is the one Mathlib finds), so they are activated with
`attribute [local instance]` wherever they are used, and the monoidal structure on sheaves is an
`instance_reducible` definition activated the same way.

The localizing class of sheafification is monoidal because the small étale site has enough
points at the coefficient universe (`AlgebraicGeometry.Scheme.hasEnoughPoints_smallEtaleTopology`)
and the tensor product of abelian groups commutes with filtered colimits, Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w u v

namespace AddCommGrpCat

attribute [local instance] AddCommGrpCat.monoidalCategory

/-- The braiding of the tensor product of abelian groups, at an arbitrary universe, transported
from the modules over a copy of `ℤ` in that universe. -/
@[instance_reducible]
noncomputable def braidedCategoryGeneral : BraidedCategory AddCommGrpCat.{w} := by
  change BraidedCategory (Monoidal.Transported (AddCommGrpCat.uliftIntEquivalence.{w}))
  infer_instance

/-- The closed structure of the tensor product of abelian groups, at an arbitrary universe,
transported from the modules over a copy of `ℤ` in that universe. -/
@[instance_reducible]
noncomputable def monoidalClosedGeneral : MonoidalClosed AddCommGrpCat.{w} :=
  letI : (AddCommGrpCat.uliftIntEquivalence.{w}).inverse.Monoidal := by
    change (Monoidal.equivalenceTransported
      (AddCommGrpCat.uliftIntEquivalence.{w})).inverse.Monoidal
    infer_instance
  MonoidalClosed.ofEquiv (AddCommGrpCat.uliftIntEquivalence.{w}).inverse
    (AddCommGrpCat.uliftIntEquivalence.{w}).symm.toAdjunction

end AddCommGrpCat

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.braidedCategoryGeneral
  AddCommGrpCat.monoidalClosedGeneral

variable (X : Scheme.{u})

/-- Tensoring on the left by a fixed abelian group preserves all colimits, being a left
adjoint for the closed structure. -/
instance preservesColimits_tensorLeft_addCommGrpCat (A : AddCommGrpCat.{w}) :
    PreservesColimitsOfSize.{w, w} (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

/-- Tensoring on the right by a fixed abelian group preserves all colimits: it is tensoring on
the left, up to the braiding. -/
instance preservesColimits_tensorRight_addCommGrpCat (A : AddCommGrpCat.{w}) :
    PreservesColimitsOfSize.{w, w} (tensorRight A) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight A)

/-- **The localizing class of sheafification of abelian presheaves on the small étale site is
monoidal** for the tensor product over `ℤ`: the site has enough points at the coefficient
universe, and the tensor product of abelian groups commutes with filtered colimits. -/
theorem isMonoidal_W_smallEtale :
    (X.smallEtaleTopology.W (A := AddCommGrpCat.{max (u + 1) v})).IsMonoidal := by
  have : GrothendieckTopology.HasEnoughPoints.{max (u + 1) v} X.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology X
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty.{max (u + 1) v}
      X.smallEtaleTopology
  exact hP.isMonoidal_W AddCommGrpCat.{max (u + 1) v}

/-- **The monoidal structure on abelian sheaves on the small étale site**: the tensor product
of two sheaves is the sheafification of the presheaf of sectionwise tensor products over `ℤ`.
This is Mathlib's `CategoryTheory.Sheaf.monoidalCategory` for the tensor product of abelian
groups `AddCommGrpCat.monoidalCategory`. -/
@[instance_reducible]
noncomputable def etaleAbelianMonoidalCategory :
    MonoidalCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  letI := isMonoidal_W_smallEtale.{u, v} X
  Sheaf.monoidalCategory X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}

attribute [local instance] etaleAbelianMonoidalCategory

/-- The tensor product of abelian sheaves on the small étale site, as a bifunctor. -/
noncomputable abbrev etaleAbelianTensor :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  curriedTensor _

end Stacks.EtaleCohomology

end
