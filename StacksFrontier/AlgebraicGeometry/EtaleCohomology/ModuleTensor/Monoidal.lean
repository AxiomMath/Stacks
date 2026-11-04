module

public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive

/-!
# The tensor product of étale sheaves of `Λ`-modules

Let `Λ` be a commutative ring and `X` a scheme. Sheaves of `Λ`-modules on the small étale site of
`X`, `Stacks.EtaleCohomology.EtaleModules Λ X`, with values in `ModuleCat.{max (u + 1) r} Λ`, form
a monoidal category for the tensor product over `Λ`: `F ⊗_Λ G` is the sheafification of the
presheaf `U ↦ F(U) ⊗_Λ G(U)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleMonoidalCategory`: the monoidal structure on
  `EtaleModules Λ X`, Mathlib's `CategoryTheory.Sheaf.monoidalCategory`.
* `Stacks.EtaleCohomology.etaleModuleTensor`: its tensor product, as a bifunctor.

## Implementation notes

The coefficients `ModuleCat.{max (u + 1) r} Λ` live in a universe above that of `Λ`, so the tensor
product of `Λ`-modules used is the large-universe structure `ModuleCat.liftedModuleMonoidal` of
`StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse` (sections `M ⊗[Λ] N`, unit
`ULift Λ`), with its symmetry and closed structure; it is a global instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u r

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- The forgetful functor of `Λ`-modules in a universe `v` in which `Λ` is small preserves
filtered colimits of size `v`. -/
instance preservesFilteredColimitsOfSize_forget_moduleCat_small {Λ' : Type r} [Ring Λ']
    [Small.{v} Λ'] :
    PreservesFilteredColimitsOfSize.{v, v} (forget (ModuleCat.{v} Λ')) := by
  have : PreservesColimitsOfSize.{v, v} (forget₂ (ModuleCat.{v} Λ') AddCommGrpCat.{v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{v, r, v, v} Λ'
  exact comp_preservesFilteredColimits (forget₂ (ModuleCat.{v} Λ') AddCommGrpCat.{v})
    (forget AddCommGrpCat.{v})

/- The next two are theorems rather than instances: the universe `u` occurs in their statements
only inside `max (u + 1) r`, from which instance search cannot recover it. -/

/-- Tensoring on the left by a fixed `Λ`-module in the coefficient universe preserves all colimits
of that size. -/
theorem preservesColimits_tensorLeft_etaleCoefficients (M : ModuleCat.{max (u + 1) r} Λ) :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

/-- Tensoring on the right by a fixed `Λ`-module in the coefficient universe preserves all
colimits of that size. -/
theorem preservesColimits_tensorRight_etaleCoefficients (M : ModuleCat.{max (u + 1) r} Λ) :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorRight M) :=
  have := preservesColimits_tensorLeft_etaleCoefficients.{u, r} Λ M
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

/-- **The localizing class of sheafification of `Λ`-module presheaves on the small étale site is
monoidal** for the tensor product over `Λ`. -/
theorem isMonoidal_W_smallEtale_module :
    (X.smallEtaleTopology.W (A := ModuleCat.{max (u + 1) r} Λ)).IsMonoidal := by
  have : GrothendieckTopology.HasEnoughPoints.{max (u + 1) r} X.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology X
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty.{max (u + 1) r}
      X.smallEtaleTopology
  have := preservesColimits_tensorLeft_etaleCoefficients.{u, r} Λ
  have := preservesColimits_tensorRight_etaleCoefficients.{u, r} Λ
  exact hP.isMonoidal_W (ModuleCat.{max (u + 1) r} Λ)

/-- **The monoidal structure on étale sheaves of `Λ`-modules**: the tensor product of two
sheaves is the sheafification of the presheaf of sectionwise tensor products over `Λ`. -/
@[instance_reducible]
noncomputable def etaleModuleMonoidalCategory : MonoidalCategory (EtaleModules.{u, r} Λ X) :=
  letI := isMonoidal_W_smallEtale_module.{u, r} Λ X
  Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)

/-- The braiding of the tensor product of étale sheaves of `Λ`-modules. -/
@[instance_reducible]
noncomputable def etaleModuleBraidedCategory :
    letI := etaleModuleMonoidalCategory.{u, r} Λ X
    BraidedCategory (EtaleModules.{u, r} Λ X) :=
  letI := isMonoidal_W_smallEtale_module.{u, r} Λ X
  Sheaf.braidedCategory X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

/-- The tensor product of étale sheaves of `Λ`-modules, as a bifunctor. -/
noncomputable abbrev etaleModuleTensor :
    EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ X :=
  curriedTensor _

/-- **The tensor product of étale sheaves of `Λ`-modules is additive in each variable.** -/
instance etaleModuleMonoidalPreadditive : MonoidalPreadditive (EtaleModules.{u, r} Λ X) :=
  letI := isMonoidal_W_smallEtale_module.{u, r} Λ X
  Sheaf.monoidalPreadditive X.smallEtaleTopology

/-- Étale sheaves of `Λ`-modules have all small colimits indexed by categories in `Type`. -/
instance etaleModules_hasColimitsOfSize_zero : HasColimitsOfSize.{0, 0} (EtaleModules.{u, r} Λ X) :=
  have : HasColimitsOfSize.{max (u + 1) r, max (u + 1) r} (EtaleModules.{u, r} Λ X) :=
    have := etaleModules_isGrothendieckAbelian.{u, r} Λ X
    IsGrothendieckAbelian.hasColimits _
  hasColimitsOfSizeShrink.{0, 0, max (u + 1) r, max (u + 1) r} _

/-- Coproducts of étale sheaves of `Λ`-modules indexed by a type in `Type` exist. -/
lemma hasColimitOfShape_discrete_small {ι : Type} (D : Discrete ι ⥤ EtaleModules.{u, r} Λ X) :
    HasColimit D :=
  ((etaleModules_hasColimitsOfSize_zero.{u, r} Λ X).has_colimits_of_shape
    (Discrete ι)).has_colimit D

/-- Every double complex of étale sheaves of `Λ`-modules has a total complex. -/
instance etaleModule_hasTotal
    (K : HomologicalComplex₂ (EtaleModules.{u, r} Λ X)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) :=
  fun _ ↦ hasColimitOfShape_discrete_small Λ X _

end Stacks.EtaleCohomology

end
