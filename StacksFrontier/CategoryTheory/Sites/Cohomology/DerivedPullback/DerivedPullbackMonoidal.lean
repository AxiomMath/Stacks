module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquareUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal

/-!
# Derived pullback along a flat morphism of ringed topoi is monoidal

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites, whose pullback of sheaves of modules `f^*` is exact and carries K-flat
complexes to K-flat complexes. Then `f^*` applied termwise induces a functor
`D(O_D) ⥤ D(O_C)` which is monoidal for the derived tensor products, and it is the derived
pullback `Lf^*` of Stacks 06YY.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.isLeftDerivedFunctor_pullbackToposMapDerived`: for `f^*` exact,
  `f^*` applied termwise is a left derived functor of degreewise pullback.

* `Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived`: `f^*` applied termwise, on derived
  categories.
* `Stacks.Sheaves.DerivedPullback.pullbackToposMapDerivedMonoidal`: its monoidal structure, for
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` on either side.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived`: the identification of
  `Lf^*` with it.

## Implementation notes

The monoidal structures on `Mod(O)` are seated as local instances at pinned universes, as in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory`: the sections universe of
`SheafOfModules.monoidalCategorySheafTensor` is the maximum of the two site universes, and the
graded tensor products the monoidal structure on complexes is built from are only found when
both are pinned. None of the structures defined here is an instance, so that no second monoidal
pairing is registered on categories that already carry one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor

/-- `Mod(O)` is monoidal for `sheafTensor`, at pinned universes, as in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory`. -/
@[instance_reducible] local instance monoidalCategoryMod
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor.{u, u} R

/-- `Mod(O)` is symmetric monoidal, at pinned universes. -/
@[instance_reducible] local instance symmetricCategoryMod
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    SymmetricCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  _root_.SheafOfModules.symmetricCategorySheafTensor.{u, u} R

attribute [local instance] CochainComplex.symmetricCategory

/-- `⊗_O` is bilinear on morphisms, at pinned universes. -/
local instance monoidalPreadditiveMod
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor.{u, u} R

/-- `Mod(O)` is monoidal closed, at pinned universes. -/
@[instance_reducible] local instance monoidalClosedMod
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalClosed (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  _root_.SheafOfModules.monoidalClosedSheafTensor.{u, u} R

/-- The graded tensor products of `O`-modules exist. -/
local instance hasTensorMod
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    ∀ A B : GradedObject ℤ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)),
      GradedObject.HasTensor A B :=
  fun _ _ => inferInstance

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- The pullback of sheaves of modules along a morphism of ringed topoi is additive, being a
left adjoint. -/
instance additive_pullbackTopos : f.pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos f)

/-- The pullback of sheaves of modules along a morphism of ringed topoi preserves colimits,
being a left adjoint. -/
instance preservesColimitsOfSize_pullbackTopos :
    PreservesColimitsOfSize.{0, 0} f.pullbackTopos :=
  Adjunction.leftAdjoint_preservesColimits
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos f)

variable [PreservesFiniteLimits f.pullbackTopos]

/-- **`f^*` applied termwise, on derived categories**, for `f^*` exact. -/
abbrev pullbackToposMapDerived :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  haveI : PreservesFiniteColimits f.pullbackTopos :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  f.pullbackTopos.mapDerivedCategory

/-- **`f^*` applied termwise is monoidal on derived categories**, for the derived tensor products
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` on either side: this is
`CategoryTheory.Functor.mapDerivedCategoryMonoidal` at the monoidal structure
`pullbackToposMonoidal` of `f^*`, given that `f^*` carries K-flat complexes to K-flat
complexes. -/
@[instance_reducible]
def pullbackToposMapDerivedMonoidal
    (hF : ∀ K : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor _) K →
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor _)
        ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    (pullbackToposMapDerived f).Monoidal :=
  letI := pullbackToposMonoidal f hmos
  haveI : PreservesFiniteColimits f.pullbackTopos :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  CategoryTheory.Functor.mapDerivedCategoryMonoidal f.pullbackTopos hF
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.O)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O)

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- `f^*` applied termwise is a left derived functor of degreewise pullback followed by
localization, `f^*` being exact. -/
instance isLeftDerivedFunctor_pullbackToposMapDerived :
    (pullbackToposMapDerived f).IsLeftDerivedFunctor
      (haveI : PreservesFiniteColimits f.pullbackTopos :=
        PreservesColimitsOfSize.preservesFiniteColimits _
      f.pullbackTopos.mapDerivedCategoryFactorsh).hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
  haveI : PreservesFiniteColimits f.pullbackTopos :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  Functor.isLeftDerivedFunctor_of_inverts _ _ _

/-- **The derived pullback along `f` is `f^*` applied termwise**, for `f^*` exact: both are left
derived functors of degreewise pullback followed by localization, so the canonical comparison
between them is invertible. -/
def derivedPullbackIsoMapDerived : derivedPullback f ≅ pullbackToposMapDerived f :=
  haveI : PreservesFiniteColimits f.pullbackTopos :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI := (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (derivedPullback f) ((pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh _)
    (HomotopyCategory.quasiIso _ _) (pullbackToposMapDerived f)
    f.pullbackTopos.mapDerivedCategoryFactorsh.hom).1 inferInstance
  (asIso ((derivedPullback f).leftDerivedLift
    ((pullbackOnHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh _)
    (HomotopyCategory.quasiIso _ _) (pullbackToposMapDerived f)
    f.pullbackTopos.mapDerivedCategoryFactorsh.hom)).symm

end Stacks.Sheaves.DerivedPullback

end
