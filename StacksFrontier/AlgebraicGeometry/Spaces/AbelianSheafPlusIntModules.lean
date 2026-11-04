module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafPlusMonoidal
public import StacksFrontier.Homology.KFlat.BifunctorBoundedBelowTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# Bounded below K-flat resolutions of abelian sheaves, from the modules over the constant sheaf

`Stacks.Cohomology.derivedPlusMonoidalAbelianSheaves` makes the bounded below derived category of
abelian sheaves monoidal given `hGE`: every complex of abelian sheaves vanishing in degrees below
`a` receives a quasi-isomorphism from a K-flat complex vanishing in degrees below some `a'`. This
file reduces that hypothesis to the same hypothesis for modules over the constant sheaf of
integers, along the equivalence `Stacks.Cohomology.intModulesEquivAbelianSheaves` between abelian
sheaves and modules over the constant sheaf `ℤ`.

## Main results

* `Stacks.Cohomology.exists_kFlat_resolution_isStrictlyGE_abelianSheaves`,
  `Stacks.Cohomology.Leray.exists_kFlat_resolution_isStrictlyGE_abelianSheaf`: **bounded below
  K-flat resolutions of complexes of abelian sheaves, from bounded below K-flat resolutions of
  complexes of modules over the constant sheaf of integers.**
* `Stacks.Cohomology.derivedPlusMonoidalAbelianSheavesOfIntModules`,
  `Stacks.Cohomology.Leray.derivedPlusMonoidalAbelianSheafOfIntModules`: **the bounded below
  derived category of abelian sheaves is monoidal**, given bounded below K-flat resolutions of
  complexes of modules over the constant sheaf of integers.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
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

/-- `- ⊗_ℤ -` is additive in its first variable, for the constant sheaf of rings `ℤ` on this
site: `Stacks.SheafOfModules.Tensor.sheafTensor_additive` with its universes given, which
instance search does not find unaided. -/
noncomputable local instance constIntSheafTensorAdditive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (constIntCommSheaf J)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} (constIntCommSheaf J)

/-- `M ⊗_ℤ -` is additive, for the constant sheaf of rings `ℤ` on this site:
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` with its universes given. -/
noncomputable local instance constIntSheafTensorObjAdditive
    (moduleSheaf : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (constIntCommSheaf J)).obj moduleSheaf).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (constIntCommSheaf J) moduleSheaf

/-- **Bounded below K-flat resolutions of complexes of abelian sheaves on a site, from bounded
below K-flat resolutions of complexes of modules over the constant sheaf of integers.** -/
theorem exists_kFlat_resolution_isStrictlyGE_abelianSheaves
    (hGE : ∀ (a : ℤ) (G : CochainComplex
        (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) ℤ),
      G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex
          (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) ℤ) (f : P ⟶ G),
        P.IsStrictlyGE a' ∧
          CochainComplex.KFlatBifunctor.KFlat
            (Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J)) P ∧ QuasiIso f)
    (a : ℤ) (G : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (hG : G.IsStrictlyGE a) :
    ∃ (a' : ℤ) (P : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (f : P ⟶ G),
      P.IsStrictlyGE a' ∧
        CochainComplex.KFlatBifunctor.KFlat
          (curriedTensor (Sheaf J AddCommGrpCat.{u})) P ∧ QuasiIso f :=
  CochainComplex.KFlatBifunctor.exists_kFlat_resolution_isStrictlyGE_of_equivalence
    (Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J))
    (curriedTensor (Sheaf J AddCommGrpCat.{u})) (intModulesEquivAbelianSheaves J)
    (abelianSheafTensorComparison J)
    (abelianSheafTensorComparison_naturality_left J)
    (abelianSheafTensorComparison_naturality_right J)
    hGE a G hG

/-- **The bounded below derived category of abelian sheaves on a site is monoidal**, given
bounded below K-flat resolutions of complexes of modules over the constant sheaf of integers.
The monoidal structure is that of `Stacks.Cohomology.derivedPlusMonoidalAbelianSheaves`. -/
@[instance_reducible] def derivedPlusMonoidalAbelianSheavesOfIntModules
    [HasDerivedCategory.{v} (Sheaf J AddCommGrpCat.{u})]
    (hGE : ∀ (a : ℤ) (G : CochainComplex
        (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) ℤ),
      G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex
          (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) ℤ) (f : P ⟶ G),
        P.IsStrictlyGE a' ∧
          CochainComplex.KFlatBifunctor.KFlat
            (Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J)) P ∧ QuasiIso f) :
    MonoidalCategory (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{u})) :=
  derivedPlusMonoidalAbelianSheaves J
    (exists_kFlat_resolution_isStrictlyGE_abelianSheaves J hGE)

end Site

namespace Leray

attribute [local instance] abelianSheafMonoidalCategory
  braidedCategoryCochainComplexAbelianSheaf

-- The instances of `Stacks.Topology.SheafTensorAdditiveOnOpens` take their sheaf of rings as
-- `TopCat.Sheaf CommRingCat X`; making `TopCat.Sheaf` reducible for instance search lets that
-- spelling unify with `Sheaf (Opens.grothendieckTopology X) CommRingCat`.
attribute [local instance_reducible] TopCat.Sheaf

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- **Bounded below K-flat resolutions of complexes of abelian sheaves on a topological space,
from bounded below K-flat resolutions of complexes of modules over the constant sheaf of
integers.** -/
theorem exists_kFlat_resolution_isStrictlyGE_abelianSheaf (X : TopCat.{u})
    (hGE : ∀ (a : ℤ) (G : CochainComplex
        (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u}
          (constIntCommSheaf (Opens.grothendieckTopology X))) ℤ),
      G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex
          (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u}
            (constIntCommSheaf (Opens.grothendieckTopology X))) ℤ) (f : P ⟶ G),
        P.IsStrictlyGE a' ∧
          CochainComplex.KFlatBifunctor.KFlat
            (Stacks.SheafOfModules.Tensor.sheafTensor
              (constIntCommSheaf (Opens.grothendieckTopology X))) P ∧ QuasiIso f)
    (a : ℤ) (G : CochainComplex (AbelianSheaf X) ℤ) (hG : G.IsStrictlyGE a) :
    ∃ (a' : ℤ) (P : CochainComplex (AbelianSheaf X) ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (AbelianSheaf X)) P ∧ QuasiIso f :=
  let := hasSheafify_ringCat.{u, u, u} (Opens.grothendieckTopology X)
  let := wEqualsLocallyBijective_ringCat.{u, u, u} (Opens.grothendieckTopology X)
  exists_kFlat_resolution_isStrictlyGE_abelianSheaves
    (Opens.grothendieckTopology X) hGE a G hG

/-- **The bounded below derived category of abelian sheaves on a topological space is
monoidal**, given bounded below K-flat resolutions of complexes of modules over the constant
sheaf of integers. -/
@[instance_reducible] def derivedPlusMonoidalAbelianSheafOfIntModules (X : TopCat.{u})
    [HasDerivedCategory.{v} (AbelianSheaf X)]
    (hGE : ∀ (a : ℤ) (G : CochainComplex
        (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u}
          (constIntCommSheaf (Opens.grothendieckTopology X))) ℤ),
      G.IsStrictlyGE a →
      ∃ (a' : ℤ) (P : CochainComplex
          (Stacks.SheafOfModules.DerivedMonoidal.Mod.{u}
            (constIntCommSheaf (Opens.grothendieckTopology X))) ℤ) (f : P ⟶ G),
        P.IsStrictlyGE a' ∧
          CochainComplex.KFlatBifunctor.KFlat
            (Stacks.SheafOfModules.Tensor.sheafTensor
              (constIntCommSheaf (Opens.grothendieckTopology X))) P ∧ QuasiIso f) :
    MonoidalCategory (DerivedCategory.Plus (AbelianSheaf X)) :=
  derivedPlusMonoidalAbelianSheaf X
    (exists_kFlat_resolution_isStrictlyGE_abelianSheaf X hGE)

end Leray

end Stacks.Cohomology

end
