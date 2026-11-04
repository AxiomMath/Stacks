module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction

/-!
# Derived extension of scalars on a transpose is the counit followed by the plain transpose

Let `ψ : A → B` be a homomorphism of differential graded algebras over a commutative ring `R`.
Derived extension of scalars `- ⊗_A^𝐋 B` is left adjoint to derived restriction of scalars,
Tag 0BYX. Before deriving, ordinary extension of scalars `- ⊗_A B`, the tensor product with the
regular bimodule of `ψ`, is left adjoint to restriction of scalars on differential graded modules:
a homomorphism `g : X ⟶ Y_A` corresponds to `g^♯ : X ⊗_A B ⟶ Y`, `x ⊗ b ↦ g(x) · b`.

This file compares the two. The derived transpose of the class of `g` is the comparison
`X ⊗_A^𝐋 B ⟶ X ⊗_A B` of Tag 0BZ2 followed by the class of the plain transpose `g^♯`. When `X`
is orthogonal on the left to the acyclic modules the comparison is invertible, so the derived
transpose is then the plain one.

## Main definitions

* `DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars`: the adjunction between tensoring
  with the regular bimodule of `ψ` and restriction of scalars along `ψ`, on differential graded
  modules.
* `DifferentialGraded.Bimodule.plainTranspose`: the transpose `g^♯ : X ⊗_A B ⟶ Y` of a
  homomorphism `g : X ⟶ Y_A`.

## Main results

* `DifferentialGraded.Bimodule.derivedTranspose_eq`: the derived transpose of the class of `g` is
  the comparison of Tag 0BZ2 followed by the class of `g^♯`.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
* [Stacks Project, Tag 09LT](https://stacks.math.columbia.edu/tag/09LT)
* [Stacks Project, Tag 09LN](https://stacks.math.columbia.edu/tag/09LN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **Extension of scalars is left adjoint to restriction of scalars**, on differential graded
modules: tensoring with the regular bimodule of `ψ` is left adjoint to the internal hom out of
it (Tag 09LN), which is restriction of scalars by evaluation at the unit (Tag 0BYX). -/
def tensorRegularAdjRestrictScalars (ψ : A.Hom B) :
    tensorCompFunctor (regular ψ) ⊣ restrictScalarsFunctor ψ :=
  (tensorCompFunctor_adj_homModuleFunctor (regular ψ)).ofNatIsoRight
    (homModuleFunctorRegularIso ψ)

/-- **The plain transpose** `g^♯ : X ⊗_A B ⟶ Y` of a homomorphism `g : X ⟶ Y_A` of differential
graded `A`-modules. -/
def plainTranspose (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    (tensorCompFunctor (regular ψ)).obj X ⟶ Y :=
  ((tensorRegularAdjRestrictScalars ψ).homEquiv X Y).symm g

/-- **The plain transpose on a pure tensor**: `g^♯ (x ⊗ b) = g(x) · b`. -/
theorem plainTranspose_pure (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y)
    (p : ℤ) (x : X.grading p) (b : B.A) :
    (plainTranspose ψ g).toFun ((tensorPure (regular ψ) X).toLinearMap (x : X.M) b) =
      @HSMul.hSMul B.Aᵐᵒᵖ Y.M Y.M _ (MulOpposite.op b) (g.toFun (x : X.M)) := by
  have hp : plainTranspose ψ g = (tensorHomEquiv (regular ψ) X Y).symm
      (g ≫ (homModuleFunctorRegularIso ψ).inv.app Y) :=
    Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ g
  rw [hp]
  refine (tensorHomEquiv_symm_pure (regular ψ) X
    (g ≫ (homModuleFunctorRegularIso ψ).inv.app Y) p x b).trans ?_
  refine (regularHomogeneousMap_eq_smul_one Y p _ b).trans ?_
  refine congrArg _ ((homModuleRegularIso_hom_apply ψ Y p _).trans ?_)
  exact LinearMap.congr_fun (congrArg _root_.DifferentialGradedModule.Hom.toFun
    ((homModuleFunctorRegularIso ψ).inv_hom_id_app Y)) (g.toFun (x : X.M))

/-- The homotopy class of `g`, read as a map into the internal hom out of the regular bimodule
on the homotopy categories. -/
def homotopyHomOfRestrict (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    (toHomotopyCategory A).obj X ⟶
      (homHomotopyCategoryFunctor A B (regularModule B) (regularBimoduleStructure ψ)).obj
        ((toHomotopyCategory B).obj Y) :=
  (toHomotopyCategory A).map g ≫ (restrictScalarsHomotopyFunctorIso ψ).inv.app Y ≫
    (homHomotopyFunctorRegularIso ψ).inv.app ((toHomotopyCategory B).obj Y)

/-- At the class of a differential graded `B`-module `Y`, the comparison of the derived hom data
of the regular bimodule followed by its identification with derived restriction of scalars is the
inverse of the factorization `regularHomFactorization ψ`. -/
private theorem derivedHomData_comparison_comp_functorIsoDerivedRestriction_hom (ψ : A.Hom B)
    (Y : DifferentialGradedModule.{u, u, u} B) :
    (derivedHomData A B (regularModule B) (regularBimoduleStructure ψ)).comparison.app
        ((toHomotopyCategory B).obj Y) ≫
      (DerivedHomData.functorIsoDerivedRestriction ψ
        (derivedHomData A B (regularModule B) (regularBimoduleStructure ψ))).hom.app
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) =
      (regularHomFactorization ψ).inv.app ((toHomotopyCategory B).obj Y) := by
  set D := derivedHomData A B (regularModule B) (regularBimoduleStructure ψ)
  have := D.isRightDerived
  have := Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms' B)
    (derivedRestriction ψ) (regularHomFactorization ψ)
  exact (Functor.rightDerivedNatTrans_app D.functor (derivedRestriction ψ) D.comparison
    (regularHomFactorization ψ).inv (quasiIsomorphisms' B) (𝟙 _)
    ((toHomotopyCategory B).obj Y)).trans (Category.id_comp _)

/-- At the class of a differential graded `B`-module `Y`, the derived tensor product of the
comparison of the derived hom data followed by the counit of the derived tensor-hom adjunction is
the comparison of the derived tensor product followed by the class of the homotopy counit. -/
private theorem derivedTensorFunctor_map_comparison_comp_counit_app (ψ : A.Hom B)
    (Y : DifferentialGradedModule.{u, u, u} B) :
    (derivedTensorFunctor (regular ψ)).map
        ((derivedHomData A B (regularModule B) (regularBimoduleStructure ψ)).comparison.app
          ((toHomotopyCategory B).obj Y)) ≫
      (derivedTensorFunctor_adj_derivedHomFunctor (regular ψ)).counit.app
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) =
      (derivedTensorFunctorCounit (regular ψ)).app
          ((homHomotopyCategoryFunctor A B (regularModule B) (regularBimoduleStructure ψ)).obj
            ((toHomotopyCategory B).obj Y)) ≫
        (quasiIsomorphisms' B).Q.map
          ((tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor (regular ψ)).counit.app
            ((toHomotopyCategory B).obj Y)) := by
  set D := derivedHomData A B (regularModule B) (regularBimoduleStructure ψ)
  let β' : homHomotopyCategoryFunctor A B (regular ψ).rightModule (regular ψ).leftAction ⋙
      (quasiIsomorphisms' A).Q ⟶ (quasiIsomorphisms' B).Q ⋙ D.functor := D.comparison
  have : D.functor.IsRightDerivedFunctor β' (quasiIsomorphisms' B) := D.isRightDerived
  have := Functor.isRightDerivedFunctor_comp_of_coresolutions (quasiIsomorphisms' B) β'
    (derivedTensorFunctor (regular ψ))
    (exists_coresolution_map_bijective_of_propertyI_resolutions B
      (exists_propertyI_resolution B))
  exact Adjunction.derivedε_fac_app _ (quasiIsomorphisms' B)
    (derivedTensorFunctorCounit (regular ψ)) β' ((toHomotopyCategory B).obj Y)

/-- **The derived transpose, read through the comparison of the derived tensor product.** The
transpose under the derived adjunction of Tag 0BYX of the class of `g`, written as a map into
derived restriction of scalars through the factorization of derived restriction, is the
comparison `X ⊗_A^𝐋 B ⟶ X ⊗_A B` followed by the class of the transpose of `g` under the
adjunction of Tag 09LN on homotopy categories. -/
theorem derivedTranspose_eq_homotopy (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    ((derivedTensorFunctor_adj_derivedRestriction ψ).homEquiv _ _).symm
        ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map g) ≫
          (quasiIsomorphisms' A).Q.map ((restrictScalarsHomotopyFunctorIso ψ).inv.app Y) ≫
          (derivedRestrictionFactorization ψ).inv.app ((toHomotopyCategory B).obj Y)) =
      (derivedTensorFunctorCounit (regular ψ)).app ((toHomotopyCategory A).obj X) ≫
        (quasiIsomorphisms' B).Q.map
          (((tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor (regular ψ)).homEquiv _ _).symm
            (homotopyHomOfRestrict ψ g)) := by
  set D := derivedHomData A B (regularModule B) (regularBimoduleStructure ψ)
  set e := DerivedHomData.functorIsoDerivedRestriction ψ D
  set hadj := tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor (regular ψ)
  let β : homHomotopyCategoryFunctor A B (regularModule B) (regularBimoduleStructure ψ) ⋙
      (quasiIsomorphisms' A).Q ⟶ (quasiIsomorphisms' B).Q ⋙ D.functor := D.comparison
  have he : β.app ((toHomotopyCategory B).obj Y) ≫
      e.hom.app ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) =
        (regularHomFactorization ψ).inv.app ((toHomotopyCategory B).obj Y) :=
    derivedHomData_comparison_comp_functorIsoDerivedRestriction_hom ψ Y
  have hε : (derivedTensorFunctor (regular ψ)).map (β.app ((toHomotopyCategory B).obj Y)) ≫
      (derivedTensorFunctor_adj_derivedHomFunctor (regular ψ)).counit.app
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) =
      (derivedTensorFunctorCounit (regular ψ)).app
          ((homHomotopyCategoryFunctor A B (regularModule B) (regularBimoduleStructure ψ)).obj
            ((toHomotopyCategory B).obj Y)) ≫
        (quasiIsomorphisms' B).Q.map (hadj.counit.app ((toHomotopyCategory B).obj Y)) :=
    derivedTensorFunctor_map_comparison_comp_counit_app ψ Y
  have key : ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map g) ≫
        (quasiIsomorphisms' A).Q.map ((restrictScalarsHomotopyFunctorIso ψ).inv.app Y) ≫
        (derivedRestrictionFactorization ψ).inv.app ((toHomotopyCategory B).obj Y)) ≫
        e.inv.app ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) =
      (quasiIsomorphisms' A).Q.map (homotopyHomOfRestrict ψ g) ≫
        β.app ((toHomotopyCategory B).obj Y) := by
    have h2 : (regularHomFactorization ψ).inv.app ((toHomotopyCategory B).obj Y) =
        (quasiIsomorphisms' A).Q.map
            ((homHomotopyFunctorRegularIso ψ).hom.app ((toHomotopyCategory B).obj Y)) ≫
          (derivedRestrictionFactorization ψ).inv.app ((toHomotopyCategory B).obj Y) := rfl
    rw [← cancel_mono (e.hom.app _)]
    conv_rhs => rw [Category.assoc, he, h2]
    simp only [Category.assoc, Iso.inv_hom_id_app, homotopyHomOfRestrict, Functor.map_comp]
    rw [← Functor.map_comp_assoc (quasiIsomorphisms' A).Q
      ((homHomotopyFunctorRegularIso ψ).inv.app _), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg _ (congrArg _ (Category.comp_id _))
  have hD : derivedTensorFunctor_adj_derivedRestriction ψ =
      (derivedTensorFunctor_adj_derivedHomFunctor (regular ψ)).ofNatIsoRight e := rfl
  have hc : ((derivedTensorFunctor_adj_derivedHomFunctor (regular ψ)).ofNatIsoRight e).counit.app
      ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) =
      (derivedTensorFunctor (regular ψ)).map
        (e.inv.app ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y))) ≫
        (derivedTensorFunctor_adj_derivedHomFunctor (regular ψ)).counit.app
          ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj Y)) := rfl
  rw [hD, Adjunction.homEquiv_counit, hc]
  refine (((congrArg (fun k => k ≫ _) ((derivedTensorFunctor (regular ψ)).map_comp _ _)).trans
    (Category.assoc _ _ _)).symm.trans ?_)
  rw [key]
  refine ((congrArg (fun k => k ≫ _) ((derivedTensorFunctor (regular ψ)).map_comp _ _)).trans
    (Category.assoc _ _ _)).trans ?_
  rw [hε]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ _)
    ((derivedTensorFunctorCounit (regular ψ)).naturality (homotopyHomOfRestrict ψ g))).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k) ?_)
  exact ((quasiIsomorphisms' B).Q.map_comp _ _).symm.trans
    (congrArg (quasiIsomorphisms' B).Q.map
      (hadj.homEquiv_counit (g := homotopyHomOfRestrict ψ g)).symm)

/-- At the class of a differential graded `B`-module `Y`, the inverse of
`homHomotopyFunctorRegularIso ψ` is the composite of `restrictScalarsHomotopyFunctorIso ψ`, the
class of the inverse of `homModuleFunctorRegularIso ψ`, and the inverse of the descent
isomorphism `homHomotopyDescent` for the regular bimodule. -/
theorem homHomotopyFunctorRegularIso_inv_app (ψ : A.Hom B)
    (Y : DifferentialGradedModule.{u, u, u} B) :
    (homHomotopyFunctorRegularIso ψ).inv.app ((toHomotopyCategory B).obj Y) =
      ((restrictScalarsHomotopyFunctorIso ψ).hom.app Y ≫
        (toHomotopyCategory A).map ((homModuleFunctorRegularIso ψ).inv.app Y)) ≫
        (homHomotopyDescent (regularModule B) (regularBimoduleStructure ψ)).inv.app Y :=
  rfl

/-- At the class of a differential graded `B`-module `Y`, the counit of the tensor-hom adjunction
on homotopy categories is the tensor functor applied to the descent isomorphism
`homHomotopyDescent`, followed by the inverse of `tensorCompFunctor_quotient N` and the class of
the counit of the tensor-hom adjunction on modules. -/
theorem tensorHomotopyAdj_counit_app (N : Bimodule A B)
    (Y : DifferentialGradedModule.{u, u, u} B) :
    (tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor N).counit.app
        ((toHomotopyCategory B).obj Y) =
      (tensorHomotopyFunctor N).map
          ((homHomotopyDescent N.rightModule N.leftAction).hom.app Y ≫ 𝟙 _) ≫
        ((tensorCompFunctor_quotient N).inv.app _ ≫ 𝟙 _) ≫
        (toHomotopyCategory B).map ((tensorCompFunctor_adj_homModuleFunctor N).counit.app Y) :=
  rfl

/-- **The transpose on homotopy categories is the class of the plain transpose.** Under the
adjunction of Tag 09LN on homotopy categories the class of `g`, read into the internal hom out of
the regular bimodule, corresponds to the class of the plain transpose `g^♯`, through the
compatibility of tensoring with the passage to homotopy classes. -/
theorem homotopyTranspose_eq (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    ((tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor (regular ψ)).homEquiv _ _).symm
        (homotopyHomOfRestrict ψ g) =
      (tensorCompFunctor_quotient (regular ψ)).inv.app X ≫
        (toHomotopyCategory B).map (plainTranspose ψ g) := by
  have hh : homotopyHomOfRestrict ψ g =
      (toHomotopyCategory A).map (g ≫ (homModuleFunctorRegularIso ψ).inv.app Y) ≫
        (homHomotopyDescent (regularModule B) (regularBimoduleStructure ψ)).inv.app Y := by
    rw [homotopyHomOfRestrict, homHomotopyFunctorRegularIso_inv_app, Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hp : plainTranspose ψ g = (tensorCompFunctor (regular ψ)).map
      (g ≫ (homModuleFunctorRegularIso ψ).inv.app Y) ≫
        (tensorCompFunctor_adj_homModuleFunctor (regular ψ)).counit.app Y :=
    (Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ g).trans
      (Adjunction.homEquiv_counit _ _ _ _)
  set g' := g ≫ (homModuleFunctorRegularIso ψ).inv.app Y
  have hf : homotopyHomOfRestrict ψ g ≫
      ((homHomotopyDescent (regularModule B) (regularBimoduleStructure ψ)).hom.app Y ≫ 𝟙 _) =
      (toHomotopyCategory A).map g' := by
    refine (congrArg (fun k => _ ≫ k) (Category.comp_id _)).trans ?_
    rw [hh, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hn : (tensorHomotopyFunctor (regular ψ)).map ((toHomotopyCategory A).map g') ≫
      (tensorCompFunctor_quotient (regular ψ)).inv.app _ =
      (tensorCompFunctor_quotient (regular ψ)).inv.app X ≫
        (toHomotopyCategory B).map ((tensorCompFunctor (regular ψ)).map g') :=
    (tensorCompFunctor_quotient (regular ψ)).inv.naturality g'
  refine (Adjunction.homEquiv_counit _ _ _ _).trans ?_
  refine (congrArg (fun k => _ ≫ k) (tensorHomotopyAdj_counit_app (regular ψ) Y)).trans ?_
  refine ((tensorHomotopyFunctor (regular ψ)).map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => (tensorHomotopyFunctor (regular ψ)).map k ≫ _) hf).trans ?_
  refine (congrArg (fun k => _ ≫ k ≫ _) (Category.comp_id _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ _) hn).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k) ?_)
  rw [hp]
  exact ((toHomotopyCategory B).map_comp _ _).symm

/-- **The derived transpose is the comparison of the derived tensor product followed by the plain
transpose.** For a homomorphism `g : X ⟶ Y_A` of differential graded `A`-modules, the transpose
of its class under the adjunction of Tag 0BYX between derived extension and derived restriction
of scalars — the class of `g` being read into derived restriction through the factorization of
derived restriction — is the comparison `X ⊗_A^𝐋 B ⟶ X ⊗_A B` of Tag 0BZ2, followed by the class
of the plain transpose `g^♯ : X ⊗_A B ⟶ Y`. -/
theorem derivedTranspose_eq (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    ((derivedTensorFunctor_adj_derivedRestriction ψ).homEquiv _ _).symm
        ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map g) ≫
          (quasiIsomorphisms' A).Q.map ((restrictScalarsHomotopyFunctorIso ψ).inv.app Y) ≫
          (derivedRestrictionFactorization ψ).inv.app ((toHomotopyCategory B).obj Y)) =
      (derivedTensorFunctorCounit (regular ψ)).app ((toHomotopyCategory A).obj X) ≫
        (quasiIsomorphisms' B).Q.map ((tensorCompFunctor_quotient (regular ψ)).inv.app X) ≫
        (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map (plainTranspose ψ g)) := by
  rw [derivedTranspose_eq_homotopy, homotopyTranspose_eq, Functor.map_comp]

end DifferentialGraded.Bimodule
