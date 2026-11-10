module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear

/-!
# [Stacks, Tag 089W] is natural in the module

`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` compares `H^n(X, F)` with
`H^n(S, f_* F)` over `Γ(S, ⊤)` for an affine morphism `f : X ⟶ S` and a quasi-coherent `F`. It is
built at a *fixed* `F`, because its second factor
`Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso` inverts a component of the unit of
`R f_*` and that component is invertible only at an `f_*`-acyclic object. This file proves its
naturality for a morphism between two acyclic objects.

## Main definitions

* `Stacks.Cohomology.AffineComparison.singleRightDerivedUnit`: the natural transformation
  `F(-)[0] ⟶ RF((-)[0])` whose component at an `F`-acyclic object is invertible.

## Main results

* `Stacks.Cohomology.AffineComparison.singleRightDerivedUnit_app`: its component at an acyclic
  object is `rightDerivedFunctorPlusObjSingleIso`'s inverse.
* `Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso_naturality`,
  `Stacks.Cohomology.AffineComparison.rightDerivedPlusCollapseIso_naturality` and
  `Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso_naturality`: the collapse
  `R^n(G ∘ F) ≅ R^n G (F -)` of [Stacks, Tag 015M] is natural between `F`-acyclic objects, in
  both indexings.
* `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso_naturality` and
  `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_naturality`: **[Stacks, Tag 089W]
  is natural in the module.**
* `Stacks.Cohomology.AffineComparison.rightDerived_map_baseSmul_hom`: for a scheme over
  `Spec R`, the `R`-action on `H^n(X, F)` is `H^n(X, -)` of multiplication by the scalar.
* `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_baseSmul`: **the comparison of
  [Stacks, Tag 089W] commutes with multiplication by a scalar of the base ring.**

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open scoped AlgebraicGeometry ModuleCat.Algebra

namespace Stacks.Cohomology.AffineComparison

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Collapse

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The unit `F(-)[0] ⟶ RF((-)[0])`, as a natural transformation. -/
public def singleRightDerivedUnit :
    F ⋙ DerivedCategory.Plus.singleFunctor B 0 ⟶
      DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus :=
  (Functor.mapSingleFunctorCompQhIso F).inv ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor A 0)
      F.rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv
      F.rightDerivedFunctorPlus

omit [EnoughInjectives B] in
/-- Its component at an `F`-acyclic object is the inverse of
`rightDerivedFunctorPlusObjSingleIso`. -/
public theorem singleRightDerivedUnit_app (X : A) (hX : F.rightAcyclic X) :
    (singleRightDerivedUnit F).app X = (rightDerivedFunctorPlusObjSingleIso F X hX).inv := by
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := by
    have hX' : IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := hX
    have hd := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
      (HomotopyCategory.Plus.quasiIso A) F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith).1 inferInstance
    rw [← Functor.rightDerived_fac_app _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))
      (HomotopyCategory.Plus.quasiIso A) F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith]
    infer_instance
  simp [singleRightDerivedUnit, rightDerivedFunctorPlusObjSingleIso, asIso]

omit [EnoughInjectives B] in
/-- **Naturality of `rightDerivedFunctorPlusObjSingleIso`** between two `F`-acyclic objects. -/
public theorem rightDerivedFunctorPlusObjSingleIso_naturality {X Y : A} (φ : X ⟶ Y)
    (hX : F.rightAcyclic X) (hY : F.rightAcyclic Y) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map φ) ≫
        (rightDerivedFunctorPlusObjSingleIso F Y hY).hom =
      (rightDerivedFunctorPlusObjSingleIso F X hX).hom ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (F.map φ) := by
  have h := (singleRightDerivedUnit F).naturality φ
  rw [singleRightDerivedUnit_app F X hX, singleRightDerivedUnit_app F Y hY] at h
  have h' : (DerivedCategory.Plus.singleFunctor B 0).map (F.map φ) ≫
      (rightDerivedFunctorPlusObjSingleIso F Y hY).inv =
    (rightDerivedFunctorPlusObjSingleIso F X hX).inv ≫
      F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map φ) := h
  have h2 : (DerivedCategory.Plus.singleFunctor B 0).map (F.map φ) =
      ((rightDerivedFunctorPlusObjSingleIso F X hX).inv ≫
        F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map φ)) ≫
          (rightDerivedFunctorPlusObjSingleIso F Y hY).hom :=
    (Iso.comp_inv_eq _).1 h'
  rw [h2]
  simp

/-- **Naturality of the collapse `R^n(G ∘ F) ≅ R^n G (F -)`**, in the `ℤ`-indexed form, between
two `F`-acyclic objects. -/
public theorem rightDerivedPlusCollapseIso_naturality
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    {X Y : A} (φ : X ⟶ Y) (hX : F.rightAcyclic X) (hY : F.rightAcyclic Y) (n : ℤ) :
    ((F ⋙ G).rightDerivedPlus n).map φ ≫ (rightDerivedPlusCollapseIso F G hFG Y hY n).hom =
      (rightDerivedPlusCollapseIso F G hFG X hX n).hom ≫
        (G.rightDerivedPlus n).map (F.map φ) := by
  dsimp only [rightDerivedPlusCollapseIso, Functor.rightDerivedPlus, Functor.comp_map,
    Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (DerivedCategory.Plus.homologyFunctor C n).map ?_
  rw [Iso.app_hom, Iso.app_hom, ← Category.assoc,
    (DerivedPushforwardSections.compIso F G hFG).hom.naturality
      ((DerivedCategory.Plus.singleFunctor A 0).map φ)]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  rw [rightDerivedFunctorPlusObjSingleIso_naturality F φ hX hY]

/-- **Naturality of the collapse `R^n(G ∘ F) ≅ R^n G (F -)`** for Mathlib's `ℕ`-indexed right
derived functors, between two `F`-acyclic objects. -/
public theorem rightDerivedCollapseIso_naturality
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    {X Y : A} (φ : X ⟶ Y) (hX : F.rightAcyclic X) (hY : F.rightAcyclic Y) (n : ℕ) :
    ((F ⋙ G).rightDerived n).map φ ≫ (rightDerivedCollapseIso F G hFG Y hY n).hom =
      (rightDerivedCollapseIso F G hFG X hX n).hom ≫ (G.rightDerived n).map (F.map φ) := by
  dsimp only [rightDerivedCollapseIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc]
  rw [reassoc_of% ((Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) n).hom.naturality φ),
    reassoc_of% (rightDerivedPlusCollapseIso_naturality F G hFG φ hX hY (n : ℤ)),
    (Stacks.DerivedIndexing.rightDerivedIso G n).inv.naturality (F.map φ)]

end Collapse

section Comparison

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- **Naturality of `restrictScalarsRightDerivedIso`**: it is a component of a natural
isomorphism. -/
public theorem restrictScalarsRightDerivedIso_naturality {F F' : X.Modules} (φ : F ⟶ F')
    (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).map
          (((moduleGlobalSections X).rightDerived n).map φ) ≫
        (restrictScalarsRightDerivedIso f F' n).hom =
      (restrictScalarsRightDerivedIso f F n).hom ≫
        ((AlgebraicGeometry.Scheme.Modules.pushforward f ⋙
          moduleGlobalSections S).rightDerived n).map φ := by
  dsimp only [restrictScalarsRightDerivedIso, Iso.app_hom]
  exact (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X)
    (ModuleCat.restrictScalars.{u} f.appTop.hom)
    (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
    (sectionsRestrictionIsoTop f) n).hom.naturality φ

/-- **[Stacks, Tag 089W] is natural in the module.** -/
public theorem cohomologyIsoPushforward_naturality [AlgebraicGeometry.IsAffineHom f]
    {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] (φ : F ⟶ F') (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).map
          (((moduleGlobalSections X).rightDerived n).map φ) ≫
        (cohomologyIsoPushforward f F' n).hom =
      (cohomologyIsoPushforward f F n).hom ≫
        ((moduleGlobalSections S).rightDerived n).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).map φ) := by
  dsimp only [cohomologyIsoPushforward, Iso.trans_hom]
  simp only [Category.assoc]
  rw [reassoc_of% (restrictScalarsRightDerivedIso_naturality f φ n),
    rightDerivedCollapseIso_naturality (AlgebraicGeometry.Scheme.Modules.pushforward f)
      (moduleGlobalSections S) (rightAcyclic_moduleGlobalSections_pushforward_obj f) φ
      (rightAcyclic_pushforward_of_isAffineHom f F)
      (rightAcyclic_pushforward_of_isAffineHom f F') n]

end Comparison

section Scalars

variable {R : Type u} [CommRing R] (Y : Over (AlgebraicGeometry.Spec (.of R)))

/-- **The `R`-action on `H^n(X, F)` for a scheme over `Spec R` is `H^n(X, -)` of multiplication
by the scalar**, the scalar acting through the structure morphism on global sections. -/
public theorem rightDerived_map_baseSmul_hom (F : Y.left.Modules) (n : ℕ) (r : R)
    (z : ((((moduleGlobalSections Y.left).rightDerived n).obj F) : Type u)) :
    letI := AlgebraicGeometry.modulesLinear R Y
    (((moduleGlobalSections Y.left).rightDerived n).map (r • 𝟙 F)).hom z =
      ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom r • z := by
  let := AlgebraicGeometry.modulesLinear R Y
  let := baseSectionsAlgebra R Y
  have := linear_rightDerived_moduleGlobalSections R Y n
  have halg : (algebraMap R Γ(Y.left, ⊤)) r =
      ((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom r := by
    have hres : ∀ s : Γ(Y.left, ⊤),
        (Y.left.ringCatSheaf.obj.map
          (TopologicalSpace.Opens.leTop (⊤ : Y.left.Opens)).op).hom s = s := by
      intro s
      have h1 : (TopologicalSpace.Opens.leTop (⊤ : Y.left.Opens)).op =
          𝟙 (op (⊤ : Y.left.Opens)) := rfl
      rw [h1, CategoryTheory.Functor.map_id]
      rfl
    change AlgebraicGeometry.baseRingToSections R Y (op ⊤) r = _
    exact hres _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, ← halg]
  rfl

/-- **[Stacks, Tag 089W] commutes with multiplication by a scalar.** For a scheme `Y` over
`Spec R` and an affine `f : Y ⟶ S`, the comparison carries the `R`-action on `H^n(Y, F)` to
`H^n(S, f_*(r • 𝟙))`. -/
public theorem cohomologyIsoPushforward_baseSmul {S : AlgebraicGeometry.Scheme.{u}}
    (f : Y.left ⟶ S) [AlgebraicGeometry.IsAffineHom f]
    (F : Y.left.Modules) [F.IsQuasicoherent] (n : ℕ) (r : R)
    (z : ((((moduleGlobalSections Y.left).rightDerived n).obj F) : Type u)) :
    letI := AlgebraicGeometry.modulesLinear R Y
    (cohomologyIsoPushforward f F n).hom.hom
        (((AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom r • z) =
      (((moduleGlobalSections S).rightDerived n).map
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).map (r • 𝟙 F))).hom
          ((cohomologyIsoPushforward f F n).hom.hom z) := by
  let := AlgebraicGeometry.modulesLinear R Y
  rw [← rightDerived_map_baseSmul_hom Y F n r z]
  exact congrArg (fun φ : (ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections Y.left).rightDerived n).obj F) ⟶
      ((moduleGlobalSections S).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F) => φ.hom z)
    (cohomologyIsoPushforward_naturality f (r • 𝟙 F) n)

end Scalars

end Stacks.Cohomology.AffineComparison

end
