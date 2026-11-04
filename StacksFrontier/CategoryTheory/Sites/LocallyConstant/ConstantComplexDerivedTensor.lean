module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantModuleSheafTensor
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensorRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantComplexKFlatness

/-!
# The derived tensor product of two constant complexes

Let `(C, J)` be a small site, `Λ` a commutative ring, `R` a sheaf of commutative rings and
`α : Λ̲ ⟶ R` a locally bijective morphism out of the constant presheaf of rings on `Λ`, so that
`Stacks.ConstantRingModules.derivedTensor` is the derived tensor product of Stacks 06YU read on
`D(Sheaf J (ModuleCat Λ))`.

This file computes that derived tensor product on the **constant complexes attached to bounded
above complexes of finite free `Λ`-modules** — it is the class of the total tensor complex of the
two corresponding complexes of constant sheaves of modules over `R` — and concludes that its
cohomology sheaves are locally constant of finite type. That conclusion is the content of the
bounded case of Stacks 094H once Stacks 094G and a finite free model have produced the two
complexes; it is **not** that bounded case, because the models are hypotheses here and are not
produced from the tag's `K` and `L`. No `@[stacks]` attribute is attached for that reason.

## Main definitions

* `Stacks.ConstantRingModules.constantSheafComplex` and `constSheafOfModulesComplex`: the constant
  complex attached to a complex of `Λ`-modules, in the two readings of a sheaf of `Λ`-modules.
* `Stacks.ConstantRingModules.constantSheafCompInverseIso` and `constantComplexBackwardIso`: the
  identification of the two, at a module and at a complex.
* `Stacks.ConstantRingModules.derivedTensorConstantComplexIso`: **the derived tensor product of
  two constant complexes is the total tensor complex of the two complexes of constant sheaves of
  modules.**

## Main results

* `Stacks.ConstantRingModules.isKFlat_constSheafOfModules_mapHomologicalComplex`: the complex of
  constant sheaves of modules on a bounded above complex of finite projective `Λ`-modules is
  K-flat over `R`.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_constantComplex`:
  **the cohomology sheaves of the derived tensor product of two such constant complexes are
  locally constant of finite type.**

## Implementation notes

**Where the three inputs come from, and that none of them is rebuilt.** The K-flatness is
`Stacks.SheafOfModules.isKFlat_mapHomologicalComplex_of_boundedAbove_finite_projective` of
`StacksFrontier.CategoryTheory.Sites.Modules.ConstantComplexKFlatness`, which is stated for an
arbitrary additive right exact functor into sheaves of modules over an arbitrary
`AlgebraicGeometry.RingedSite` carrying `Λ` to the unit object; the functor is
`Stacks.ConstantRingModules.constSheafOfModules` and its three properties are the instances and
the unit comparison of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantModuleSheafTensor`. Only the
*instance* of that K-flatness at `AlgebraicGeometry.RingedSite.constantFunctorOver` is pinned at
universe `0`, not the statement, so no universe obstruction arises and the ringed site is built
anonymously here, appearing in no statement — as in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensorRestriction`, and for
the same reason.

That K-flatness is what makes the `comparison` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` applicable, and the termwise local
constancy of the resulting total complex is
`Stacks.ConstantRingModules.isFiniteTypeLocallyConstantModules_mapBifunctor` of the same
module. The passage from the termwise statement to the cohomology sheaves is the fact that a
weak Serre class containing the terms of a complex contains its homology, which is a one-line
consequence of homology being a cokernel of a map into a kernel. It is written out at its one
use below rather than invoked: the library's two copies of it are a `private` lemma of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic`, which this module already
imports but cannot name, and the public
`CategoryTheory.ObjectProperty.prop_homology` of
`StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence`, whose import would add
forty-six mostly scheme-level modules to the closure of this site-level file. The weak Serre
property of Tag 093U's class is the instance
`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf`.

**The conjugation is definitional in the outer slot.** `derivedTensor` is
`tensorBackward ⋙ T.tensor ⋙ … ⋙ tensorForward`, so a value of it at a pair of objects is already
the composite applied to the two backward images; no transport of
`Stacks.ConstantRingModules.derivedTensor_obj` is needed, and the only comparisons used are the
two `CategoryTheory.Functor.mapDerivedCategoryFactors` of the equivalence and its inverse,
together with the identification of the two readings of a constant complex.

**What is not proved.** This is not the bounded case of Stacks 094H. What is owed on top of this
file is the production of the two models from the tag's own `K` and `L`: Tag 094G gives a cover on
which each is the constant complex on a bounded complex of *finite type* `Λ`-modules, and
pseudo-coherence upgrades that to a bounded above complex of *finite free* ones, which is the
shape consumed here. The two covers must then be made one, and the conclusion assembled by
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_local` through the slice
compatibility `Stacks.ConstantRingModules.constantDerivedTensorOverObjIso`.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules Stacks.ConstantSheaf Stacks.SheafOfModules
  Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] _root_.SheafOfModules.instAbelian
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

universe u

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (Λ : Type u) [CommRing Λ] (R : Sheaf J CommRingCat.{u})
  (α : constRing (C := C) Λ ⟶ (Tensor.ringSheaf.{u, u, u} R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- Reading the constant sheaves of `Λ`-modules back as sheaves of modules over `R`. -/
def constantSheafCompInverseIso :
    constantSheaf J (ModuleCat.{u} Λ) ⋙ (tensorEquiv Λ R α).inverse ≅
      constSheafOfModules.{u} Λ J α :=
  Functor.isoWhiskerRight (constantSheafModuleSheafIso.{u} Λ J α) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (tensorEquiv Λ R α).unitIso.symm ≪≫
    (constSheafOfModules.{u} Λ J α).rightUnitor

/-- The complex of constant sheaves of `Λ`-modules on `P`, read back as a complex of sheaves of
modules over `R`. -/
def constantComplexBackwardIso (P : CochainComplex (ModuleCat.{u} Λ) ℤ) :
    ((tensorEquiv Λ R α).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      ((constSheafOfModules.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexCompIso (constantSheafCompInverseIso Λ R α)
    (ComplexShape.up ℤ)).app P

/-- The ringed site whose structure sheaf is `R`; it appears in no statement. -/
private abbrev ambientRingedSite : RingedSite.{u, u, u} := { C := C, J := J, O := R }

/-- The complex of constant sheaves of modules on a bounded above complex of finite projective
`Λ`-modules is K-flat. -/
theorem isKFlat_constSheafOfModules_mapHomologicalComplex
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i))
    (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i)) :
    Stacks.SheafOfModules.IsKFlat R
      (((constSheafOfModules.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  Stacks.SheafOfModules.isKFlat_mapHomologicalComplex_of_boundedAbove_finite_projective
    (Y := ambientRingedSite R) (constSheafOfModules.{u} Λ J α)
    (_root_.PresheafOfModules.sheafificationObjUnitIso α) P b hfin hproj

/-- The constant complex on `P`, as a complex of sheaves of `Λ`-modules. -/
abbrev constantSheafComplex (P : CochainComplex (ModuleCat.{u} Λ) ℤ) :
    CochainComplex (Sheaf J (ModuleCat.{u} Λ)) ℤ :=
  ((constantSheaf J (ModuleCat.{u} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- The constant complex on `P`, as a complex of sheaves of modules over `R`. -/
abbrev constSheafOfModulesComplex (P : CochainComplex (ModuleCat.{u} Λ) ℤ) :
    CochainComplex (Modules R) ℤ :=
  ((constSheafOfModules.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- **The derived tensor product of two constant complexes is the total tensor complex of the
corresponding complexes of constant sheaves of modules.** -/
def derivedTensorConstantComplexIso
    (P Q : CochainComplex (ModuleCat.{u} Λ) ℤ) (b c : ℤ)
    [P.IsStrictlyLE b] [Q.IsStrictlyLE c]
    (hPfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hPproj : ∀ i : ℤ, Module.Projective Λ (P.X i))
    (hQfin : ∀ i : ℤ, Module.Finite Λ (Q.X i)) (hQproj : ∀ i : ℤ, Module.Projective Λ (Q.X i)) :
    ((derivedTensor Λ R α).obj (DerivedCategory.Q.obj (constantSheafComplex Λ P))).obj
        (DerivedCategory.Q.obj (constantSheafComplex Λ Q)) ≅
      DerivedCategory.Q.obj
        (((toModuleSheaf.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((Tensor.tensorComplex R).obj (constSheafOfModulesComplex Λ R α P)).obj
            (constSheafOfModulesComplex Λ R α Q))) :=
  let T := canonicalDerivedTensorProduct R
  let bP : (tensorBackward Λ R α).obj (DerivedCategory.Q.obj (constantSheafComplex Λ P)) ≅
      DerivedCategory.Q.obj (constSheafOfModulesComplex Λ R α P) :=
    ((tensorEquiv Λ R α).inverse.mapDerivedCategoryFactors.app (constantSheafComplex Λ P)) ≪≫
      DerivedCategory.Q.mapIso (constantComplexBackwardIso Λ R α P)
  let bQ : (tensorBackward Λ R α).obj (DerivedCategory.Q.obj (constantSheafComplex Λ Q)) ≅
      DerivedCategory.Q.obj (constSheafOfModulesComplex Λ R α Q) :=
    ((tensorEquiv Λ R α).inverse.mapDerivedCategoryFactors.app (constantSheafComplex Λ Q)) ≪≫
      DerivedCategory.Q.mapIso (constantComplexBackwardIso Λ R α Q)
  (tensorForward Λ R α).mapIso
      ((T.tensor.mapIso bP).app _ ≪≫ (T.tensor.obj _).mapIso bQ ≪≫
        T.comparison (constSheafOfModulesComplex Λ R α P) (constSheafOfModulesComplex Λ R α Q)
          (isKFlat_constSheafOfModules_mapHomologicalComplex Λ R α P b hPfin hPproj)
          (isKFlat_constSheafOfModules_mapHomologicalComplex Λ R α Q c hQfin hQproj)) ≪≫
    (tensorEquiv Λ R α).functor.mapDerivedCategoryFactors.app _

/-- **The cohomology sheaves of the derived tensor product of two constant complexes on
bounded above complexes of finite free `Λ`-modules are locally constant of finite type.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_constantComplex
    [IsNoetherianRing Λ]
    (P Q : CochainComplex (ModuleCat.{u} Λ) ℤ) (b c : ℤ)
    [P.IsStrictlyLE b] [Q.IsStrictlyLE c]
    (hPfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hPfree : ∀ i : ℤ, Module.Free Λ (P.X i))
    (hQfin : ∀ i : ℤ, Module.Finite Λ (Q.X i)) (hQfree : ∀ i : ℤ, Module.Free Λ (Q.X i))
    (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor Λ R α).obj (DerivedCategory.Q.obj (constantSheafComplex Λ P))).obj
          (DerivedCategory.Q.obj (constantSheafComplex Λ Q)))) := by
  have hPproj : ∀ i : ℤ, Module.Projective Λ (P.X i) := fun i =>
    have := hPfree i; inferInstance
  have hQproj : ∀ i : ℤ, Module.Projective Λ (Q.X i) := fun i =>
    have := hQfree i; inferInstance
  have hQfg : ∀ i : ℤ, ModuleCat.isFG Λ (Q.X i) := fun i =>
    have := hQfin i; (ModuleCat.isFG_iff _).2 inferInstance
  refine ObjectProperty.prop_of_iso (IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ)
    (((DerivedCategory.homologyFunctor _ i).mapIso
        (derivedTensorConstantComplexIso Λ R α P Q b c hPfin hPproj hQfin hQproj)).trans
      ((DerivedCategory.homologyFunctorFactors _ i).app _)).symm ?_
  -- The homology of a complex whose terms lie in a weak Serre class lies in it too: homology is
  -- a cokernel of a map into a kernel, and such a class is closed under both. That one-line
  -- argument is written out here rather than invoked, because `prop_homology` of
  -- `StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic` is `private` and the
  -- public restatement, `CategoryTheory.ObjectProperty.prop_homology` of
  -- `StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence`, would pull roughly
  -- fifty scheme-level modules into this site-level file.
  have hterm := isFiniteTypeLocallyConstantModules_mapBifunctor Λ R α P Q b c hPfin hPfree hQfg
  exact ObjectProperty.prop_of_isColimit_cokernelCofork
    (IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ)
    (HomologicalComplex.homologyIsCokernel _ _ _ rfl) (hterm _)
    (ObjectProperty.prop_of_isLimit_kernelFork
      (IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ)
      (HomologicalComplex.cyclesIsKernel _ _ _ rfl) (hterm _) (hterm _))

end Stacks.ConstantRingModules

end
