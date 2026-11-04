module

public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison

/-!
# Base change of the Hom modules of the derived category

Let `f : R → A` be a flat homomorphism of commutative rings and let `K`, `M` be objects of the
unbounded derived category `D(R)` of `R`-modules. Derived extension of scalars carries them to
objects of `D(A)`, and the derived-Hom base-change map
`RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` of [stacks 0E1X] compares the two derived
Hom objects. When that map is invertible — the content of [stacks 0A6A] — the Hom modules
themselves base change: `Hom_{D(A)}(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` is `A ⊗_R Hom_{D(R)}(K, M)`. Here
derived extension of scalars is any total left derived functor of termwise extension of scalars.

## Main definitions

* `StacksDraft.DerivedHom.HomModuleBaseChange.homLinearEquivCohomologyDerivedHom`: the
  `A`-linear identification of `Hom_{D(A)}(K, M)` with `H⁰(RHom_A(K, M))`.
* `StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv`: the underlying module
  of an extension of scalars is the ordinary tensor product.
* `StacksDraft.DerivedHom.HomModuleBaseChange.homBaseChangeLinearEquiv`: the `A`-linear
  equivalence `Hom_{D(A)}(K ⊗ᴸ_R A, M ⊗ᴸ_R A) ≃ A ⊗_R Hom_{D(R)}(K, M)` attached to an
  invertible derived-Hom base-change map and a flat ring map.
* `StacksDraft.DerivedHom.HomModuleBaseChange.homCongrLinearEquiv`: transport of a module of
  morphisms along isomorphisms of its source and target.

## Main results

* `StacksDraft.DerivedHom.HomModuleBaseChange.isIso_comparison_of_flat`: over a flat ring map the
  comparison from a total left derived functor of extension of scalars to the termwise extension
  is invertible.
* `StacksDraft.DerivedHom.HomModuleBaseChange.unit_app_Q_comp_map_comparison` and
  `StacksDraft.DerivedHom.HomModuleBaseChange.unit_app_Q_eq`: the unit of the adjunction of
  [stacks 0GMT] at the image of a cochain complex is the termwise unit `c ↦ 1 ⊗ c`, read through
  that comparison.
* `StacksDraft.DerivedHom.HomModuleBaseChange.map_eq_zero_iff_comp_unit_eq_zero`: a morphism of
  `D(R)` is annihilated by derived extension of scalars exactly when composing it with the unit
  of the adjunction of [stacks 0GMT] gives zero.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace StacksDraft.DerivedHom.HomModuleBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- Precomposition with an isomorphism, as an isomorphism of the modules of morphisms into a
fixed object of a linear category. -/
public def precompLinearEquiv (R : Type*) [Semiring R] {C : Type*} [Category C] [Preadditive C]
    [Linear R C] {X Y : C} (e : X ≅ Y) (Z : C) : (Y ⟶ Z) ≃ₗ[R] (X ⟶ Z) where
  toFun g := e.hom ≫ g
  map_add' g h := Preadditive.comp_add _ _ _ e.hom g h
  map_smul' r g := by simp [Linear.comp_smul]
  invFun g := e.inv ≫ g
  left_inv g := by simp
  right_inv g := by simp

/-- Postcomposition with an isomorphism, as an isomorphism of the modules of morphisms out of a
fixed object of a linear category. -/
public def postcompLinearEquiv (R : Type*) [Semiring R] {C : Type*} [Category C] [Preadditive C]
    [Linear R C] (X : C) {Y Z : C} (e : Y ≅ Z) : (X ⟶ Y) ≃ₗ[R] (X ⟶ Z) where
  toFun g := g ≫ e.hom
  map_add' g h := Preadditive.add_comp _ _ _ g h e.hom
  map_smul' r g := by simp [Linear.smul_comp]
  invFun g := g ≫ e.inv
  left_inv g := by simp
  right_inv g := by simp

/-- Transport of morphisms along isomorphisms of the source and of the target, as an isomorphism
of the modules of morphisms of a linear category. -/
public def homCongrLinearEquiv (R : Type*) [Semiring R] {C : Type*} [Category C] [Preadditive C]
    [Linear R C] {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') : (X' ⟶ Y) ≃ₗ[R] (X ⟶ Y') :=
  (precompLinearEquiv R e Y).trans (postcompLinearEquiv R X f)

/-- **Morphisms in the derived category are the degree-zero cohomology of derived Hom.** For
objects `K` and `M` of `D(A)` the `A`-module `Hom_{D(A)}(K, M)` is `H⁰(RHom_A(K, M))`. -/
public def homLinearEquivCohomologyDerivedHom (A : Type u) [CommRing A]
    (K M : DerivedCategory (ModuleCat.{u} A)) :
    (K ⟶ M) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj
          (Opposite.op K, M)) : Type u) :=
  (StacksDraft.DerivedHom.ExtComparison.homZeroLinearEquivOverRing.{u, u} A K M).symm.trans
    (((precompLinearEquiv A (StacksDraft.DerivedHom.ExtComparison.unitIsoSingle.{u, u} A)
            ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj
              (Opposite.op K, M))).symm.trans
          (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of A (ULift.{u} A))
            ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj
              (Opposite.op K, M)) 0 A)).trans
      ((StacksDraft.DerivedHom.ExtComparison.evalUnitEquiv.{u, u} A _).trans
        ULift.moduleEquiv))

section BaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The underlying `A`-module of an extension of scalars along `algebraMap R A` is the ordinary
tensor product `A ⊗_R N`. -/
public def extendScalarsObjTensorEquiv (N : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).obj N : Type u) ≃ₗ[A]
      TensorProduct R A N := by
  letI : Module A (TensorProduct R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) : Type u)
      (N : Type u)) :=
    inferInstanceAs (Module A
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).obj N : Type u))
  let eA : ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) : Type u) ≃ₗ[R]
      A :=
    { AddEquiv.refl A with
      map_smul' := fun r x ↦ (Algebra.smul_def (R := R) (A := A) r x).symm }
  let t := TensorProduct.congr eA (LinearEquiv.refl R (N : Type u))
  have key : ∀ (a : A) (w : TensorProduct R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) : Type u)
      (N : Type u)), t (a • w) = a • t w := by
    intro a w
    induction w using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul b n => rfl
    | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']
  exact { t.toAddEquiv with map_smul' := key }

/-- **The derived-Hom base-change map, read on Hom modules.** Let `A` be a flat `R`-algebra, let
`F` be a total left derived functor of termwise extension of scalars, and let `K`, `M` be
objects of `D(R)` for which the derived-Hom base-change map of [stacks 0E1X] is invertible.
Then the `A`-module of morphisms
`F K ⟶ F M` in `D(A)` is the base change of the `R`-module of morphisms `K ⟶ M` in `D(R)`. -/
public def homBaseChangeLinearEquiv (hflat : Module.Flat R A)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{u} R))
    (hbc : IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      (algebraMap R A) F comparison K M)) :
    (F.obj K ⟶ F.obj M) ≃ₗ[A] TensorProduct R A (K ⟶ M) := by
  haveI := hbc
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap R A)
  let Y := (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} R).obj (Opposite.op K, M)
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  haveI : D.functor.IsLeftDerivedFunctor cmpD
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := D.isLeftDerived
  let hFD : F ≅ D.functor :=
    Functor.leftDerivedUnique D.functor F comparison cmpD
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
  let bc : F.obj Y ≅ (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj
      (Opposite.op (F.obj K), F.obj M) :=
    asIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      (algebraMap R A) F comparison K M)
  exact (homLinearEquivCohomologyDerivedHom A (F.obj K) (F.obj M)).trans
    ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso bc).symm.toLinearEquiv).trans
      ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
            (hFD.app Y)).toLinearEquiv).trans
        (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso.{u, u, u}
              (algebraMap R A) (RingHom.flat_algebraMap_iff.mpr hflat) Y 0).toLinearEquiv).trans
          ((extendScalarsObjTensorEquiv _).trans
            (LinearEquiv.baseChange R A _ _
              (homLinearEquivCohomologyDerivedHom R K M).symm)))))

/-- **Over a flat ring map, derived extension of scalars is computed termwise.** The comparison
from a total left derived functor of extension of scalars along `algebraMap R A` to the termwise
extension is invertible. -/
public theorem isIso_comparison_of_flat (hflat : Module.Flat R A)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    IsIso comparison := by
  have : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
      (RingHom.flat_algebraMap_iff.mpr hflat)
  have : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteColimits _
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts F comparison
    (Functor.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso _ _)

/-- **The unit of the derived change-of-rings adjunction is the termwise unit.** On the image of
a cochain complex `C`, the unit of the adjunction of [stacks 0GMT], followed by restriction of
scalars applied to the comparison with the termwise extension, is the termwise unit
`c ↦ 1 ⊗ c`. -/
public theorem unit_app_Q_comp_map_comparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
            (algebraMap R A) F comparison).unit.app (DerivedCategory.Q.obj C) ≫
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategory.map
          (comparison.app C) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app C) ≫
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) := by
  have : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategory.IsRightAdjoint :=
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      (algebraMap R A) F comparison).isRightAdjoint
  exact Adjunction.derivedη_fac_app
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) comparison
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategoryFactors.inv C

/-- **The unit of the derived change-of-rings adjunction, solved for.** Where the comparison
with the termwise extension is invertible at `C`, the unit of the adjunction of [stacks 0GMT] at
the image of `C` is the termwise unit `c ↦ 1 ⊗ c` read through that comparison. -/
public theorem unit_app_Q_eq
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) [IsIso (comparison.app C)] :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
        (algebraMap R A) F comparison).unit.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app C) ≫
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C) ≫
          (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategory.map
            (CategoryTheory.inv (comparison.app C)) := by
  rw [← Category.assoc, ← unit_app_Q_comp_map_comparison F comparison C, Category.assoc,
    ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- **Derived base change annihilates a morphism exactly when the adjunction unit does.** For
`F` a total left derived functor of extension of scalars along `algebraMap R A` and `h : K ⟶ M`
in `D(R)`, the morphism `F h` is zero if and only if `h` followed by the unit of the adjunction
of [stacks 0GMT] is zero. -/
public theorem map_eq_zero_iff_comp_unit_eq_zero
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    {K M : DerivedCategory (ModuleCat.{u} R)} (h : K ⟶ M) :
    F.map h = 0 ↔
      h ≫ (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
        (algebraMap R A) F comparison).unit.app M = 0 := by
  set a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    (algebraMap R A) F comparison
  have hnat : h ≫ a.unit.app M =
      a.unit.app K ≫ (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategory.map
        (F.map h) := a.unit.naturality h
  refine ⟨fun h0 ↦ by rw [hnat, h0, Functor.map_zero, Limits.comp_zero], fun h0 ↦ ?_⟩
  refine (a.homEquiv K (F.obj M)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero,
    ← hnat, h0]

end BaseChange

end StacksDraft.DerivedHom.HomModuleBaseChange

end
