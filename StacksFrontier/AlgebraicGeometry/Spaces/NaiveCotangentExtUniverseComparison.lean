module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutQcqs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftForPresentationPreservesInjectives
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomBijectiveOfInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure

/-!
# `Ext` out of `NL_{X/Y}` at two module universes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The naive cotangent complex
`NL_{X/Y}` of Stacks 0D0V has its sections in `Type (u + 1)`, one universe above the structure
rings, because the small étale site of `X` has its objects there.  The finiteness theorems for
`Ext` groups on a proper algebraic space (Stacks 0D0T) are about `𝒪_X`-modules with sections in
`Type u`.  The bridge is `NL_{X/Y}` formed on the `Type u` model of the small étale site and
carried to `D(𝒪_X)` by the Comparison Lemma, `K := modelDerivedFunctor (Q NL_model)`.

This file proves that for a ring `R` acting on `𝒪_X` through `φ : R →+* Γ(X, 𝒪_X)`,

`Ext^i_{𝒪_X}(NL_{X/Y}, 𝒪_X) ≃ₗ[R] Hom_{D(𝒪_X)}(K, 𝒪_X[i])`

for every `i`, the left side computed at the module universe `u + 1` with the unit module raised
to that universe, the right side at the universe `u`.  The steps are: restriction to the model is
an equivalence at the universe `u + 1` and carries `NL_{X/Y}` to the universe lift of the naive
cotangent complex of the model (`AlgebraicGeometry.Space.restrictedNaiveCotangentComplexIso`);
raising the universe of the sections on the model is exact, fully faithful and preserves injective
objects (`SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects`), so it is
bijective on morphisms into the bounded below object `𝒪[i]`
(`CategoryTheory.Functor.mapDerivedCategory_map_bijective_of_isGE`); and the Comparison Lemma at
the universe `u` is an equivalence.  Every step is `R`-linear.

## Main definitions

* `AlgebraicGeometry.Space.modelRestrictGlobalSections`: the restriction of global functions of
  `𝒪_X` to the model.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_naiveCotangentExt_of_moduleFinite_modelHom`: the
  identification above in the form it is used — the `Ext` group at the module universe `u + 1`
  is a finite `R`-module as soon as the group of morphisms from the model complex at the
  universe `u` is.  The `R`-linear equivalence itself is assembled inside that proof and is not
  exported as a declaration of its own.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Global functions on the model -/

section Rings

variable (X : AlgebraicSpaces B S hS)

/-- **The global functions of `𝒪_X` restricted to the model** of the small étale site. -/
def modelRestrictGlobalSections :
    GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)) →+*
      GlobalSectionRing (modelRingSheaf B S hS X) where
  toFun s := ⟨fun V => s.1 (op ((modelEquiv B S hS X).inverse.obj V.unop)),
    fun {_ _} g => s.2 ((modelEquiv B S hS X).inverse.map g.unop).op⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

end Rings

/-! ### Linearity of the comparison functors -/

section Linear

variable {X : AlgebraicSpaces B S hS}

/-- The ring of sections of `𝒪_X` over an object of the small étale site is commutative. -/
instance (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2)).obj.obj V) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B S hS X.1 X.2).obj.obj V) a b⟩⟩

/-- The ring of sections of the structure sheaf of the model over any of its objects is
commutative. -/
instance (V : (SmallModel.{u} (SmallEtale B S hS X.1))ᵒᵖ) :
    IsMulCommutative ((modelRingSheaf B S hS X).obj.obj V) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B S hS X.1 X.2).obj.obj
    (op ((modelEquiv B S hS X).inverse.obj V.unop))) a b⟩⟩

/-- Restriction of `(u + 1)`-modules to the model carries multiplication by a global function to
multiplication by its restriction. -/
theorem smallEtaleModelModulesEquivULift_map_globalSmul
    (s : GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2)))
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) :
    (smallEtaleModelModulesEquivULift B S hS X).functor.map
        (globalSmul _ s M) =
      globalSmul _ (modelRestrictGlobalSections B S hS X s)
        ((smallEtaleModelModulesEquivULift B S hS X).functor.obj M) := by
  ext V x
  rfl

/-- Restriction of `u`-modules to the model carries multiplication by a global function to
multiplication by its restriction. -/
theorem modelModulesEquiv_map_globalSmul
    (s : GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2)))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modelModulesEquiv B S hS X).functor.map (globalSmul _ s M) =
      globalSmul _ (modelRestrictGlobalSections B S hS X s)
        ((modelModulesEquiv B S hS X).functor.obj M) := by
  ext V x
  rfl

/-- Raising the universe of the sections on the model carries multiplication by a global function
to multiplication by the same global function. -/
theorem modelULift_map_globalSmul (s : GlobalSectionRing (modelRingSheaf B S hS X))
    (M : RestrictedModelModules B S hS X) :
    (modelULift B S hS X).map (globalSmul _ s M) =
      globalSmul _ s ((modelULift B S hS X).obj M) := by
  ext V x
  rfl

variable {R : Type*} [CommRing R]
  (φ : R →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))

/-- Restriction of `(u + 1)`-modules to the model is `R`-linear. -/
theorem smallEtaleModelModulesEquivULift_functor_linear :
    letI : Linear R (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) :=
      Stacks.SheafOfModules.linearOver _ φ
    letI : Linear R (SheafOfModules.{u + 1} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ ((modelRestrictGlobalSections B S hS X).comp φ)
    (smallEtaleModelModulesEquivULift B S hS X).functor.Linear R :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ _ fun a M =>
    smallEtaleModelModulesEquivULift_map_globalSmul B S hS (φ a) M

/-- Restriction of `u`-modules to the model is `R`-linear. -/
theorem modelModulesEquiv_functor_linear :
    letI : Linear R (Modules.{u, u} B S hS X.1 X.2) := Stacks.SheafOfModules.linearOver _ φ
    letI : Linear R (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ ((modelRestrictGlobalSections B S hS X).comp φ)
    (modelModulesEquiv B S hS X).functor.Linear R :=
  Stacks.SheafOfModules.linear_of_map_globalSmul _ _ _ fun a M =>
    modelModulesEquiv_map_globalSmul B S hS (φ a) M

/-- Raising the universe of the sections on the model is `R`-linear. -/
theorem modelULift_linear (ψ : R →+* GlobalSectionRing (modelRingSheaf B S hS X)) :
    letI : Linear R (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ ψ
    letI : Linear R (SheafOfModules.{u + 1} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ ψ
    (modelULift B S hS X).Linear R := by
  rw [Functor.linear_iff]
  intro M a
  rw [Stacks.SheafOfModules.linearOver_smul_id, Stacks.SheafOfModules.linearOver_smul_id,
    modelULift_map_globalSmul]

end Linear

/-! ### The unit modules -/

section Unit

variable (X : AlgebraicSpaces B S hS)

/-- Restriction to the model carries the unit module raised to `Type (u + 1)` to the universe lift
of the unit module of the model. -/
def smallEtaleModelULiftUnitIso :
    (smallEtaleModelModulesEquivULift B S hS X).functor.obj
        (Stacks.SheafOfModules.uliftUnit.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) ≅
      (modelULift B S hS X).obj (SheafOfModules.unit (modelRingSheaf B S hS X)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl))

/-- The Comparison Lemma carries the structure sheaf to the structure sheaf of the model. -/
def modelModulesEquivUnitIso :
    (modelModulesEquiv B S hS X).functor.obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) ≅
      SheafOfModules.unit (modelRingSheaf B S hS X) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl))

end Unit

/-! ### The comparison of `Ext` groups -/

section Comparison

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {R : Type*} [CommRing R]
  (φ : R →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))

/-- **`Ext` out of `NL_{X/Y}` at the module universe `u + 1` is finite as soon as morphisms from
the model complex into the shifted structure sheaf at the universe `u` are.**  The ring `R` acts
through `φ : R →+* Γ(X, 𝒪_X)` on both sides. -/
theorem moduleFinite_naiveCotangentExt_of_moduleFinite_modelHom
    [HasDerivedCategory.{w}
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))]
    [IsNoetherianRing R] (i : ℤ)
    (h : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
      letI := HasDerivedCategory.standard (RestrictedModelModules B S hS X)
      letI : Linear R (Modules.{u, u} B S hS X.1 X.2) := Stacks.SheafOfModules.linearOver _ φ
      Module.Finite R ((modelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f)) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
          (SheafOfModules.unit _))⟦i⟧)) :
    letI : Linear R (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) :=
      Stacks.SheafOfModules.linearOver _ φ
    Module.Finite R (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.SheafOfModules.uliftUnit.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))) i) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (RestrictedModelModules B S hS X)
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (modelRingSheaf B S hS X))
  let φm := (modelRestrictGlobalSections B S hS X).comp φ
  let L1 : Linear R (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) :=
    Stacks.SheafOfModules.linearOver _ φ
  let L2 : Linear R (SheafOfModules.{u + 1} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ φm
  let L3 : Linear R (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ φm
  let L4 : Linear R (Modules.{u, u} B S hS X.1 X.2) := Stacks.SheafOfModules.linearOver _ φ
  let E' := smallEtaleModelModulesEquivULift B S hS X
  let U := modelULift B S hS X
  let E := modelModulesEquiv B S hS X
  have : E'.functor.Linear R := smallEtaleModelModulesEquivULift_functor_linear B S hS φ
  have : U.Linear R := modelULift_linear B S hS φm
  have : E.functor.Linear R := modelModulesEquiv_functor_linear B S hS φ
  have : E'.functor.IsEquivalence := E'.isEquivalence_functor
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  have : E'.functor.mapDerivedCategory.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence E'.functor
  have : E.inverse.mapDerivedCategory.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence E.inverse
  -- the objects
  let NL := naiveCotangentComplex B S hS f
  let NLm := modelNaiveCotangentComplex B S hS f
  let uX := Stacks.SheafOfModules.uliftUnit.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))
  let Om := SheafOfModules.unit (modelRingSheaf B S hS X)
  let OX := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  -- step 4: `Hom(K, 𝒪_X[i]) ≃ Hom(NL_model, 𝒪_model[i])`
  let EiD := E.inverse.mapDerivedCategory
  let eO : E.inverse.obj Om ≅ OX :=
    E.inverse.mapIso (modelModulesEquivUnitIso B S hS X).symm ≪≫ (E.unitIso.app OX).symm
  let eOi : EiD.obj (((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) ≅
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj OX)⟦i⟧ :=
    (EiD.commShiftIso i).app _ ≪≫ (shiftFunctor _ i).mapIso
      ((E.inverse.mapDerivedCategorySingleFunctor 0).app Om ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso eO)
  have hEi : Function.Bijective (EiD.mapLinearMap R :
      (DerivedCategory.Q.obj NLm ⟶ ((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) →ₗ[R] _) :=
    ⟨EiD.map_injective, EiD.map_surjective⟩
  let e4 : (DerivedCategory.Q.obj NLm ⟶ ((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) ≃ₗ[R]
      ((modelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f)) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj OX)⟦i⟧) :=
    (LinearEquiv.ofBijective _ hEi).trans (Linear.homCongr R (Iso.refl _) eOi)
  have h4 : Module.Finite R
      (DerivedCategory.Q.obj NLm ⟶ ((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) :=
    Module.Finite.equiv e4.symm
  -- step 3: raising the universe on the model
  let UD := U.mapDerivedCategory
  have : EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) :=
    enoughInjectives_modules B S hS X.1 X.2
  have : EnoughInjectives (RestrictedModelModules B S hS X) :=
    EnoughInjectives.of_equivalence E.inverse
  have : U.PreservesInjectiveObjects :=
    SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects.{u, u, u, u + 1}
      (modelRingSheaf B S hS X)
  have : PreservesFiniteLimits U :=
    SheafOfModules.uliftForPresentationFunctor_preservesFiniteLimits
  have : (((DerivedCategory.singleFunctor (RestrictedModelModules B S hS X) 0).obj
      Om)⟦i⟧).IsGE (-i) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 i (-i) (by omega)
  have hU := U.mapDerivedCategory_map_bijective_of_isGE (DerivedCategory.Q.obj NLm)
    (((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) (-i)
  let e3 := LinearEquiv.ofBijective (UD.mapLinearMap R :
    (DerivedCategory.Q.obj NLm ⟶ ((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) →ₗ[R] _) hU
  -- step 2: the restriction of `NL_{X/Y}` and of the unit to the model
  let E'D := E'.functor.mapDerivedCategory
  let iNL : E'D.obj (DerivedCategory.Q.obj NL) ≅ UD.obj (DerivedCategory.Q.obj NLm) :=
    E'.functor.mapDerivedCategoryFactors.app NL ≪≫
      DerivedCategory.Q.mapIso (restrictedNaiveCotangentComplexIso B S hS f) ≪≫
      (U.mapDerivedCategoryFactors.app NLm).symm
  let iU : E'D.obj (((DerivedCategory.singleFunctor _ 0).obj uX)⟦i⟧) ≅
      UD.obj (((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) :=
    (E'D.commShiftIso i).app _ ≪≫ (shiftFunctor _ i).mapIso
      ((E'.functor.mapDerivedCategorySingleFunctor 0).app uX ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (smallEtaleModelULiftUnitIso B S hS X) ≪≫
        ((U.mapDerivedCategorySingleFunctor 0).app Om).symm) ≪≫
      ((UD.commShiftIso i).app _).symm
  let e2 := Linear.homCongr R iNL iU
  have h2 : Module.Finite R (E'D.obj (DerivedCategory.Q.obj NL) ⟶
      E'D.obj (((DerivedCategory.singleFunctor _ 0).obj uX)⟦i⟧)) :=
    Module.Finite.equiv (e3.trans e2.symm)
  -- step 1: the restriction to the model is faithful
  exact Module.Finite.of_injective (E'D.mapLinearMap R :
    (DerivedCategory.Q.obj NL ⟶ ((DerivedCategory.singleFunctor _ 0).obj uX)⟦i⟧) →ₗ[R] _)
    E'D.map_injective

end Comparison

end AlgebraicGeometry.Space

end
