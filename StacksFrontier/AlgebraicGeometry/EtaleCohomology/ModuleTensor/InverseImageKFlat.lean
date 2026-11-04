module
import all StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.DeltaFunctor
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.AffineLifting
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.DeltaFunctor
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.InverseImageKFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.DerivedTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.InverseImageMonoidal

/-!
# Stalks and inverse images of étale sheaves of `Λ`-modules preserve K-flatness

For the tensor product over a commutative ring `Λ` of étale sheaves of `Λ`-modules
(`Stacks.EtaleCohomology.etaleModuleTensor`) and of `Λ`-modules, this file proves:

* the stalk functor at a point of the small étale site (relative to the coefficient universe)
  carries complexes K-flat for the tensor product of sheaves to complexes K-flat for the tensor
  product of `Λ`-modules ([Stacks, Tag 06YB]), in both variables;
* a complex of étale sheaves of `Λ`-modules all of whose stalks at the residue geometric points are
  K-flat is K-flat;
* consequently the inverse image `f⁻¹` along a morphism of schemes carries K-flat complexes to
  K-flat complexes ([Stacks, Tag 06YC]), in both variables.

## Implementation notes

The argument is the one for abelian étale sheaves
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.InverseImageKFlat`), whose two
halves are the generic statements of `StacksFrontier.Homology.KFlat.TransportKFlat`: the stalk
functor is monoidal (Mathlib) and every acyclic complex of `Λ`-modules is a retract of the stalk
of its (acyclic) skyscraper complex; K-flatness is detected at the residue geometric points,
which form a conservative family
(`isConservativeFamilyOfPoints_residueGeometricPoints_unconditional`); and the stalk of an
inverse image at a geometric point is the stalk at the image point
(`Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.OplaxMonoidal
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory isMonoidal_W_smallEtale_module

open CochainComplex.KFlatBifunctor

variable (Λ : Type r) [CommRing Λ]

/-- Tensoring on the left by a fixed `Λ`-module preserves filtered colimits of the coefficient
size. -/
theorem preservesFilteredColimitsOfSize_tensorLeft_etaleCoefficients
    (M : ModuleCat.{max (u + 1) r} Λ) :
    PreservesFilteredColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorLeft M) :=
  have := preservesColimits_tensorLeft_etaleCoefficients.{u, r} Λ M
  inferInstance

/-- Tensoring on the right by a fixed `Λ`-module preserves filtered colimits of the coefficient
size. -/
theorem preservesFilteredColimitsOfSize_tensorRight_etaleCoefficients
    (M : ModuleCat.{max (u + 1) r} Λ) :
    PreservesFilteredColimitsOfSize.{max (u + 1) r, max (u + 1) r} (tensorRight M) :=
  have := preservesColimits_tensorRight_etaleCoefficients.{u, r} Λ M
  inferInstance

section Stalk

variable {X : Scheme.{u}} (Φ : GrothendieckTopology.Point.{max (u + 1) r} X.smallEtaleTopology)

/-- The stalk functor of a point of the small étale site is monoidal on étale sheaves of
`Λ`-modules (Mathlib's `CategoryTheory.GrothendieckTopology.Point.instMonoidalSheafSheafFiber`). -/
noncomputable instance monoidal_sheafFiber_etaleModule :
    (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).Monoidal := by
  have : LocallySmall.{max (u + 1) r} X.Etale := inferInstance
  have : HasProducts.{max (u + 1) r} (ModuleCat.{max (u + 1) r} Λ) := inferInstance
  have : HasColimitsOfSize.{max (u + 1) r, max (u + 1) r} (ModuleCat.{max (u + 1) r} Λ) :=
    inferInstance
  have : (X.smallEtaleTopology.W (A := ModuleCat.{max (u + 1) r} Λ)).IsMonoidal :=
    isMonoidal_W_smallEtale_module Λ X
  have : HasWeakSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) := inferInstance
  have := preservesFilteredColimitsOfSize_tensorLeft_etaleCoefficients.{u, r} Λ
  have := preservesFilteredColimitsOfSize_tensorRight_etaleCoefficients.{u, r} Λ
  infer_instance

/-- The stalk functor of a point of the small étale site relative to the coefficient universe is
additive on étale sheaves of modules, being left exact. The coefficient ring `R` need not be
commutative. -/
instance additive_sheafFiber_etaleModule {R : Type r} [Ring R] :
    (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} R)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The skyscraper sheaf functor of a point of the small étale site is additive on `Λ`-modules,
being a right adjoint. -/
instance additive_skyscraperSheafFunctor_etaleModule :
    (Φ.skyscraperSheafFunctor (A := ModuleCat.{max (u + 1) r} Λ)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- An acyclic complex of `Λ`-modules is a retract of the stalk of its skyscraper complex, which
is acyclic. -/
theorem exists_retract_sheafFiber_skyscraper_module
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) (hN : N.Acyclic) :
    ∃ (N' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
      (i : N ⟶ (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
      (p : (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj N' ⟶ N),
      N'.Acyclic ∧ i ≫ p = 𝟙 N := by
  have := _root_.Stacks.Cohomology.CechDeltaFunctor.moduleCatHasExactProducts.{r, max (u + 1) r} Λ
  refine ⟨(Φ.skyscraperSheafFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj N,
    { f n := Φ.skyscraperSection.app (N.X n)
      comm' i j _ := (Φ.skyscraperSection.naturality (N.d i j)).symm },
    { f n := Φ.skyscraperSheafAdjunction.counit.app (N.X n)
      comm' i j _ := (Φ.skyscraperSheafAdjunction.counit.naturality (N.d i j)).symm },
    hN.map Φ.skyscraperSheafFunctor, ?_⟩
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact Φ.skyscraperSection_comp_counit (N.X n)

/-- **The stalk of a K-flat complex of étale sheaves of `Λ`-modules is K-flat**
([Stacks, Tag 06YB]), for the tensor product of `Λ`-modules. -/
theorem kFlat_sheafFiber_etaleModule (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (hP : KFlat (etaleModuleTensor.{u, r} Λ X) P) :
    KFlat (curriedTensor (ModuleCat.{max (u + 1) r} Λ))
      ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  kFlat_map_of_retract_of_monoidal (A := EtaleModules.{u, r} Λ X)
    (A' := ModuleCat.{max (u + 1) r} Λ) Φ.sheafFiber
    (exists_retract_sheafFiber_skyscraper_module Λ Φ) P hP

/-- **The stalk of a left K-flat complex of étale sheaves of `Λ`-modules is left K-flat**
([Stacks, Tag 06YB]), for the tensor product of `Λ`-modules. -/
theorem kFlatLeft_sheafFiber_etaleModule (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (hP : KFlatLeft (etaleModuleTensor.{u, r} Λ X) P) :
    KFlatLeft (curriedTensor (ModuleCat.{max (u + 1) r} Λ))
      ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  kFlatLeft_map_of_retract_of_monoidal (A := EtaleModules.{u, r} Λ X)
    (A' := ModuleCat.{max (u + 1) r} Λ) Φ.sheafFiber
    (exists_retract_sheafFiber_skyscraper_module Λ Φ) P hP

end Stalk

section Detection

variable {X : Scheme.{u}}

/-- **K-flatness of a complex of étale sheaves of `Λ`-modules is detected at the stalks**: a
complex whose stalks at the residue geometric points are K-flat for the tensor product of
`Λ`-modules is K-flat. -/
theorem kFlat_etaleModule_of_forall_kFlat_sheafFiber
    (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (h : ∀ x : X, KFlat (curriedTensor (ModuleCat.{max (u + 1) r} Λ))
      ((((Scheme.pointSmallEtale (residueGeometricPoint X x)).ulift.{max (u + 1) r}).sheafFiber
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    KFlat (etaleModuleTensor.{u, r} Λ X) P :=
  kFlat_of_forall_kFlat_map_of_monoidal (A := EtaleModules.{u, r} Λ X)
    (A' := ModuleCat.{max (u + 1) r} Λ)
    (fun Ψ : (residueGeometricPointsUnconditional.{u, r} X).FullSubcategory ↦ Ψ.obj.sheafFiber)
    ((isConservativeFamilyOfPoints_residueGeometricPoints_unconditional.{u, r} X)
      |>.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)) P (by rintro ⟨_, ⟨x⟩⟩; exact h x)

/-- **Left K-flatness of a complex of étale sheaves of `Λ`-modules is detected at the
stalks.** -/
theorem kFlatLeft_etaleModule_of_forall_kFlatLeft_sheafFiber
    (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (h : ∀ x : X, KFlatLeft (curriedTensor (ModuleCat.{max (u + 1) r} Λ))
      ((((Scheme.pointSmallEtale (residueGeometricPoint X x)).ulift.{max (u + 1) r}).sheafFiber
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    KFlatLeft (etaleModuleTensor.{u, r} Λ X) P :=
  kFlatLeft_of_forall_kFlatLeft_map_of_monoidal (A := EtaleModules.{u, r} Λ X)
    (A' := ModuleCat.{max (u + 1) r} Λ)
    (fun Ψ : (residueGeometricPointsUnconditional.{u, r} X).FullSubcategory ↦ Ψ.obj.sheafFiber)
    ((isConservativeFamilyOfPoints_residueGeometricPoints_unconditional.{u, r} X)
      |>.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)) P (by rintro ⟨_, ⟨x⟩⟩; exact h x)

end Detection

section InverseImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The stalk at a geometric point `s` of `X` of the inverse image along `f` of a complex of
étale sheaves of `Λ`-modules is the stalk of that complex at `s ≫ f`. -/
noncomputable def sheafFiberEtaleModuleInverseImageComplexIso {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (P : CochainComplex (EtaleModules.{u, r} Λ Y) ℤ) :
    ((((Scheme.pointSmallEtale (s ≫ f)).ulift.{max (u + 1) r}).sheafFiber.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
      ((((Scheme.pointSmallEtale s).ulift.{max (u + 1) r}).sheafFiber.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((etaleModuleInverseImage.{u, r} Λ f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) :=
  ((Functor.mapHomologicalComplexCompIso (etaleModuleInverseImageSheafFiberIso.{u, r} Λ f s)
      (ComplexShape.up ℤ)).app P).symm

/-- **The inverse image of a K-flat complex of étale sheaves of `Λ`-modules is K-flat**
([Stacks, Tag 06YC]): its stalk at a geometric point is the stalk of the complex at the image
point, which is K-flat. -/
theorem kFlat_etaleModuleInverseImage_mapHomologicalComplex
    (K : CochainComplex (EtaleModules.{u, r} Λ Y) ℤ)
    (hK : KFlat (etaleModuleTensor.{u, r} Λ Y) K) :
    KFlat (etaleModuleTensor.{u, r} Λ X)
      (((etaleModuleInverseImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  kFlat_etaleModule_of_forall_kFlat_sheafFiber Λ _ fun x ↦
    KFlat.of_iso _ (kFlat_sheafFiber_etaleModule Λ
      ((Scheme.pointSmallEtale (residueGeometricPoint X x ≫ f)).ulift.{max (u + 1) r}) K hK)
      (sheafFiberEtaleModuleInverseImageComplexIso Λ f (residueGeometricPoint X x) K)

/-- **The inverse image of a left K-flat complex of étale sheaves of `Λ`-modules is left
K-flat** ([Stacks, Tag 06YC]). -/
theorem kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex
    (K : CochainComplex (EtaleModules.{u, r} Λ Y) ℤ)
    (hK : KFlatLeft (etaleModuleTensor.{u, r} Λ Y) K) :
    KFlatLeft (etaleModuleTensor.{u, r} Λ X)
      (((etaleModuleInverseImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  kFlatLeft_etaleModule_of_forall_kFlatLeft_sheafFiber Λ _ fun x ↦ by
    have h := kFlatLeft_sheafFiber_etaleModule Λ
      ((Scheme.pointSmallEtale (residueGeometricPoint X x ≫ f)).ulift.{max (u + 1) r}) K hK
    rw [kFlatLeft_iff_kFlat_flip] at h ⊢
    exact KFlat.of_iso _ h (sheafFiberEtaleModuleInverseImageComplexIso Λ f
      (residueGeometricPoint X x) K)

end InverseImage

end Stacks.EtaleCohomology

end
