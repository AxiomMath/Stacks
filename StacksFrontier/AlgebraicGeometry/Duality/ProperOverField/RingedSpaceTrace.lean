module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Derived global sections of a scheme over a field, in the two frameworks of the library

Let `k` be a field and `f : X ⟶ Spec k` a scheme over `k`. The library has two derived
global-section functors on `D(𝒪_X)`:

* `AlgebraicGeometry.derivedGlobalSectionsOver f : D(𝒪_X) ⥤ D(k)`, the `k`-linear one, at which
  duality for proper schemes over `k` ([Stacks, Tag 0FVV]) and its trace are stated, on the
  locally small models of the derived categories;
* `Stacks.Cohomology.GlobalKunneth.baseSections X : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))`, at which the cup
  product of Cohomology, Section 0FKU is stated, on the standard models.

This file identifies their cohomology: for every `n`, `Hⁿ(RΓ(X, K))` computed with
`baseSections` and read over `k` through `k ⟶ Γ(X, 𝒪_X)`, is `Hⁿ(RΓ(X, K))` computed with
`derivedGlobalSectionsOver f`, naturally in `K`. Both functors are right derived functors of
`k`-linear global sections; restriction of scalars is exact; and the comparison of the two models
of the derived categories commutes with right derived functors and with cohomology.

## Main definitions

* `Stacks.Duality.globalRingHom`: `k ⟶ Γ(X, 𝒪_X)`.
* `Stacks.Duality.baseSectionsOverField`: `RΓ(X, -) ⋙ (restriction of scalars)`.
* `Stacks.Duality.derivedGlobalSectionsOverStandardIso`: at the standard models,
  `derivedGlobalSectionsOver f ≅ baseSectionsOverField f`.
* `Stacks.Duality.cohomologyBridge`: the natural identification of the two cohomologies.
* `Stacks.Duality.topTrace`: the trace `Hᵈ(X, ω_X) ⟶ k` on the cohomology of `ω_X[0]`.

## Main results

* `Stacks.Duality.bijective_map_comp_topTrace`: duality against the trace `Hᵈ(X, ω_X) ⟶ k`.

## Implementation notes

`Stacks.Cohomology.GlobalKunneth.baseSections` is defined only on the standard models of the
derived categories, so the comparison passes through the equivalences between the standard and
the locally small models.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedSectionsLeray

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`k ⟶ Γ(X, 𝒪_X)`**, the structure map on global sections. -/
abbrev globalRingHom : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

section Standard

attribute [local instance 100000] HasDerivedCategory.standard

/-- Restriction of scalars along `k ⟶ Γ(X, 𝒪_X)` is exact. -/
instance : (ModuleCat.restrictScalars.{u} (globalRingHom f)).PreservesHomology :=
  Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars _

/-- **`RΓ(X, -)` of Section 0FKU, read over `k`**: the derived global sections
`baseSections X : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))` followed by restriction of scalars along
`k ⟶ Γ(X, 𝒪_X)`. -/
abbrev baseSectionsOverField :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} k) :=
  baseSections X.toRingedSpace ⋙
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategory

/-- Taking sections over `⊤` is an additive functor on `𝒪_X`-modules. -/
instance sectionsOverOpenTop_additive : (sectionsOverOpen X.toRingedSpace ⊤).Additive where
  map_add := rfl

/-- The comparison from termwise `k`-linear global sections to `baseSectionsOverField f`, read on
homotopy categories. -/
def homotopyGlobalSectionsOverIso :
    homotopyGlobalSectionsOver f ≅
      ((homotopySectionsOverOpen X.toRingedSpace ⊤ ⋙
          (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategory :
        HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} k))) :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (F := sectionsOverOpen X.toRingedSpace ⊤)
        (G := ModuleCat.restrictScalars.{u} (globalRingHom f))
        (H := sectionsOverOpen X.toRingedSpace ⊤ ⋙ ModuleCat.restrictScalars.{u} (globalRingHom f))
        (Iso.refl _) (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator
      ((sectionsOverOpen X.toRingedSpace ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      ((ModuleCat.restrictScalars.{u} (globalRingHom f)).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      ((sectionsOverOpen X.toRingedSpace ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator
      ((sectionsOverOpen X.toRingedSpace ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategory).symm

/-- The comparison `Γ(X, -) ⟶ RΓ(X, -)` for `baseSectionsOverField f`. -/
def baseSectionsOverFieldUnit :
    homotopyGlobalSectionsOver f ⟶ DerivedCategory.Qh ⋙ baseSectionsOverField f :=
  (homotopyGlobalSectionsOverIso f).hom ≫
    Functor.whiskerRight (derivedSectionsOverOpenUnit X.toRingedSpace ⊤)
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategory ≫
    (Functor.associator DerivedCategory.Qh (baseSections X.toRingedSpace)
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategory).hom

/-- **`baseSectionsOverField f` is a right derived functor of `k`-linear global sections.** -/
theorem isRightDerivedFunctor_baseSectionsOverField :
    (baseSectionsOverField f).IsRightDerivedFunctor (baseSectionsOverFieldUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  refine
    Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
      X.toRingedSpace) DerivedCategory.Qh _ _ fun I hI => ?_
  have := hI
  have h : IsIso ((derivedSectionsOverOpenUnit X.toRingedSpace ⊤).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
      (sectionsOverOpen X.toRingedSpace ⊤) I
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
  · exact ((homotopyGlobalSectionsOverIso f).app _).isIso_hom
  · exact Functor.map_isIso (ModuleCat.restrictScalars.{u} (globalRingHom f)).mapDerivedCategory _
  · infer_instance

/-- **At the standard models, `derivedGlobalSectionsOver f ≅ baseSectionsOverField f`.** Both are
right derived functors of `k`-linear global sections, so the canonical comparison is
invertible. -/
def derivedGlobalSectionsOverStandardIso :
    derivedGlobalSectionsOver f ≅ baseSectionsOverField f :=
  haveI := isRightDerivedFunctor_baseSectionsOverField f
  @asIso _ _ _ _
    ((derivedGlobalSectionsOver f).rightDerivedDesc (derivedGlobalSectionsOverUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _
      (baseSectionsOverFieldUnit f))
    ((Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedGlobalSectionsOverUnit f) _ _ (baseSectionsOverFieldUnit f)).1
      (isRightDerivedFunctor_baseSectionsOverField f))

end Standard

/-! ### The two models of the derived categories -/

section Models

universe w₁ w₂

open StacksDraft.DerivedModel

variable (hX₁ : HasDerivedCategory.{w₁} X.Modules) (hk₁ : HasDerivedCategory.{w₁} (ModuleCat.{u} k))
  (hX₂ : HasDerivedCategory.{w₂} X.Modules) (hk₂ : HasDerivedCategory.{w₂} (ModuleCat.{u} k))

/-- `homotopyGlobalSectionsOver` at two models of `D(k)`. -/
def homotopyGlobalSectionsOverModelEquivIso :
    @homotopyGlobalSectionsOver k _ X f hk₁ ⋙ (modelEquiv hk₁ hk₂).functor ≅
      @homotopyGlobalSectionsOver k _ X f hk₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _)

/-- **`RΓ(X, -) : D(𝒪_X) ⥤ D(k)` does not depend on the models**: at two models of `D(𝒪_X)`
and of `D(k)` it commutes with the comparison equivalences. -/
def derivedGlobalSectionsOverModelEquivIso :
    @derivedGlobalSectionsOver k _ X f hX₁ hk₁ ⋙ (modelEquiv hk₁ hk₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙ @derivedGlobalSectionsOver k _ X f hX₂ hk₂ :=
  rightDerivedModelIso (HomotopyCategory.quasiIso X.Modules (.up ℤ))
    (@derivedGlobalSectionsOverUnit k _ X f hX₁ hk₁)
    (@derivedGlobalSectionsOverUnit k _ X f hX₂ hk₂)
    (Localization.compUniqFunctor _ _ _) (homotopyGlobalSectionsOverModelEquivIso f hk₁ hk₂)

end Models

/-! ### The cohomology of the two derived global-section functors -/

/-- **The two cohomologies of a scheme over a field agree.** For `K` in the standard model of
`D(𝒪_X)`, the `n`-th cohomology of `baseSections X K` (the framework of the cup product of
Section 0FKU), read over `k`, is the `n`-th cohomology of `derivedGlobalSectionsOver f` at the
locally small models (the framework of the duality of [Stacks, Tag 0FVV]) at the image of `K`,
naturally in `K`. -/
def cohomologyBridge (n : ℤ) :
    baseSections X.toRingedSpace ⋙
        @DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) _ _
          (HasDerivedCategory.standard _) n ⋙
        ModuleCat.restrictScalars.{u} (globalRingHom f) ≅
      (Scheme.Modules.derivedModelEquiv X).functor ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) n :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (baseRing X.toRingedSpace))
  Functor.isoWhiskerLeft (baseSections X.toRingedSpace)
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.restrictScalars.{u} (globalRingHom f)) n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@derivedGlobalSectionsOverStandardIso k _ X f).symm _ ≪≫
    Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.modelHomologyFunctorIso
      (HasDerivedCategory.standard _) (ModuleCat.hasDerivedCategory) n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedGlobalSectionsOverModelEquivIso f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) (Scheme.Modules.hasDerivedCategory X)
        ModuleCat.hasDerivedCategory) _ ≪≫
    Functor.associator _ _ _

/-! ### The trace `Hᵈ(X, ω_X) ⟶ k` in the framework of the cup product -/

section Trace

variable [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- The dualizing module `ω_X = H^{-dim X}(ω_X^•)`. -/
local notation "ωM" =>
  relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- `H⁰(X, -) = H⁰ ∘ RΓ(X, -)` on the locally small `D(𝒪_X)`, with values in `k`-vector spaces;
its shift sequence is `Hⁿ(X, -) = Hⁿ ∘ RΓ(X, -)`. -/
local notation "HX" => derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- The dualizing module `ω_X = H^{-dim X}(ω_X^•)` of [Stacks, Tag 0FVV], with `ω_X^•` at the
locally small model of `D(𝒪_X)`. -/
abbrev dualizingModule : X.Modules := ωM

/-- `ω_X` placed in degree zero, in the standard model of `D(𝒪_X)` (the framework of the cup
product). -/
abbrev dualizingModuleSingle : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _) :=
  (@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0).obj
    (dualizingModule f)

/-- **`ω_X[0] ≅ ω_X^•[-d]`** for `X` Cohen--Macaulay and equidimensional of dimension `d`, with
`ω_X[0]` read in the standard model and carried to the locally small one: this is
`ω_X^• ≅ ω_X[d]` of [Stacks, Tag 0FVZ], shifted by `-d`. -/
def dualizingModuleSingleIso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d) :
    (Scheme.Modules.derivedModelEquiv X).functor.obj (dualizingModuleSingle f) ≅
      (ωX).obj⟦-(d : ℤ)⟧ :=
  (Scheme.Modules.derivedModelEquivCompQIso X).app
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj ωM) ≪≫
    ((shiftFunctorCompIsoId (DerivedCategory X.Modules) (d : ℤ) (-(d : ℤ))
      (by omega)).app _).symm ≪≫
    (shiftFunctor (DerivedCategory X.Modules) (-(d : ℤ))).mapIso
      (relativeDualizingComplexIsoShiftOfIsProper f hCM hequi d hd).symm

/-- **The trace `t : Hᵈ(X, ω_X) ⟶ k`** of [Stacks, Tag 0FW0], on the cohomology of `ω_X[0]` in
the framework of the cup product of Section 0FKU: the cohomology `Hᵈ(X, ω_X)`, read over `k`, is
`Hᵈ(X, ω_X[0])` of `derivedGlobalSectionsOver f` (`cohomologyBridge`), which is
`Hᵈ(X, ω_X^•[-d]) = H⁰(X, ω_X^•)` by [Stacks, Tag 0FVZ] (`dualizingModuleSingleIso`), on which
the trace of [Stacks, Tag 0FVW] is `Stacks.Duality.traceOverField`. -/
def topTrace (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d) :
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
        (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyModule (dualizingModuleSingle f) d) ⟶
      ModuleCat.of k k :=
  (cohomologyBridge f d).hom.app (dualizingModuleSingle f) ≫
    (HX).shiftMap (dualizingModuleSingleIso f hCM hequi d hd).hom (d : ℤ) 0 (by omega) ≫
    traceOverField f

/-- **Duality against the trace `t : Hᵈ(X, ω_X) ⟶ k`, in the framework of the cup product.**
For `Z` in the standard model of `D(𝒪_X)` whose image in the locally small model has
quasi-coherent cohomology, a morphism `β : Z ⟶ ω_X[0]` is determined by the linear form
`Hᵈ(X, Z) ⟶ Hᵈ(X, ω_X) ⟶ k` it induces, and every linear form arises. This is part (5) of
[Stacks, Tag 0FVV] (`Stacks.Duality.bijective_dualityPairing`) in degree `-d`, through
`ω_X[0] ≅ ω_X^•[-d]` and the identification of the two cohomologies. -/
theorem bijective_map_comp_topTrace (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (Z : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (hZ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((Scheme.Modules.derivedModelEquiv X).functor.obj Z)).IsQuasicoherent) :
    Function.Bijective (fun β : Z ⟶ dualizingModuleSingle f =>
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((@DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) _ _
            (HasDerivedCategory.standard _) d).map ((baseSections X.toRingedSpace).map β)) ≫
        topTrace f hCM hequi d hd) := by
  let K : quasiCoherentDerivedCategory X := ⟨(Scheme.Modules.derivedModelEquiv X).functor.obj Z, hZ⟩
  let ι := (dualizingModuleSingleIso f hCM hequi d hd).hom
  have key : ∀ (a : ℤ) (ha : a = -(-(d : ℤ))), Function.Bijective
      (fun α : DerivedCategory.Ext K.obj (ωX).obj (-(d : ℤ)) =>
        (HX).shiftMap α a 0 (by omega) ≫ traceOverField f) := by
    rintro a rfl
    exact bijective_dualityPairing f K (-(d : ℤ))
  have h₁ := key d (by omega)
  have h₂ : Function.Bijective (fun β : Z ⟶ dualizingModuleSingle f =>
      ((Scheme.Modules.derivedModelEquiv X).functor.map β ≫ ι :
        DerivedCategory.Ext K.obj (ωX).obj (-(d : ℤ)))) :=
    (Iso.homToEquiv (dualizingModuleSingleIso f hCM hequi d hd)).bijective.comp
      ((Scheme.Modules.derivedModelEquiv X).fullyFaithfulFunctor.map_bijective _ _)
  have h₃ : Function.Bijective (fun g : ((HX).shift (d : ℤ)).obj K.obj ⟶ ModuleCat.of k k =>
      ((cohomologyBridge f d).app Z).hom ≫ g) :=
    (Iso.homFromEquiv ((cohomologyBridge f d).app Z).symm).bijective
  have h₁₂ : Function.Bijective (fun β : Z ⟶ dualizingModuleSingle f =>
      ((HX).shift (d : ℤ)).map ((Scheme.Modules.derivedModelEquiv X).functor.map β) ≫
        (HX).shiftMap ι (d : ℤ) 0 (by omega) ≫ traceOverField f) := by
    have h := h₁.comp h₂
    refine (congrArg Function.Bijective (funext fun β => ?_)).mp h
    exact Functor.shiftMap_comp'_assoc (HX) _ ι (d : ℤ) 0 (by omega) (traceOverField f)
  have eq : (fun β : Z ⟶ dualizingModuleSingle f =>
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((@DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) _ _
            (HasDerivedCategory.standard _) d).map ((baseSections X.toRingedSpace).map β)) ≫
        topTrace f hCM hequi d hd) = fun β => ((cohomologyBridge f d).app Z).hom ≫
          (((HX).shift (d : ℤ)).map ((Scheme.Modules.derivedModelEquiv X).functor.map β) ≫
            (HX).shiftMap ι (d : ℤ) 0 (by omega) ≫ traceOverField f) := by
    funext β
    exact ((cohomologyBridge f d).hom.naturality_assoc β _)
  rw [eq]
  exact h₃.comp h₁₂

end Trace

end Stacks.Duality

end
