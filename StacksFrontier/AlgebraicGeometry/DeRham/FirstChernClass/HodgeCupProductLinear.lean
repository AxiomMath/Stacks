module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotentSplitting
public import StacksFrontier.Homology.DerivedLinear
public import StacksFrontier.LinearAlgebra.PerfectPairing.TraceRescaling

/-!
# The cup product on Hodge cohomology is `Γ(X, 𝒪_X)`-bilinear and unital

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^p = Ω^p_{𝒪_X/A}`. A global function `g ∈ Γ(X, 𝒪_X)` acts on every `Ω^p` by multiplication, an
endomorphism of sheaves of `A`-modules, hence on the Hodge cohomology groups `H^i(X, Ω^p)` by
functoriality: this makes `H^i(X, Ω^p)` a module over `Γ(X, 𝒪_X)`. This file proves that the cup
product of Hodge cohomology of Tag 0FM4 (`AlgebraicGeometry.SheafOfModules.hodgeCup`) is
`Γ(X, 𝒪_X)`-bilinear for this structure and unital, that `H⁰(X, Ω^0)` is free of rank one on its
unit, and deduces the uniqueness clause of Tag 0FW4: a linear form `t` on `H^d(X, Ω^d)` making the
pairings `(ξ, ξ') ↦ t(ξ ∪ ξ')` perfect is unique up to a unit of `Γ(X, 𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.formsSMul`: multiplication by `g ∈ Γ(X, 𝒪_X)` on `Ω^p`.
* `AlgebraicGeometry.SheafOfModules.hodgeGroup`: the Hodge cohomology group `H^i(X, Ω^p)`.
* `AlgebraicGeometry.SheafOfModules.hodgeSMul`: the action of `g` on `H^i(X, Ω^p)`, and the
  resulting `Γ(X, 𝒪_X)`-module structure.
* `AlgebraicGeometry.SheafOfModules.hodgeUnit`: the unit `1 ∈ H⁰(X, Ω^0)`.
* `AlgebraicGeometry.SheafOfModules.hodgeCupBilin`: the cup product as a bilinear map.
* `AlgebraicGeometry.SheafOfModules.hodgeUnitEquiv`: `Γ(X, 𝒪_X) ≅ H⁰(X, Ω^0)`, `g ↦ g • 1`.
* `AlgebraicGeometry.SheafOfModules.hodgeDualityPairing`: the pairings of Tag 0FW4.

## Main results

* `AlgebraicGeometry.SheafOfModules.hodgeSingleCohomologyIso_naturality`: the identification of
  `H^i(X, Ω^p)` with the hypercohomology of `Ω^p[0]` is natural.
* `AlgebraicGeometry.SheafOfModules.hodgeCup_smul_left`, `hodgeCup_smul_right`,
  `hodgeCup_add_left`, `hodgeCup_add_right`: the cup product is `Γ(X, 𝒪_X)`-bilinear.
* `AlgebraicGeometry.SheafOfModules.hodgeCup_hodgeUnit`: **`1 ∪ ξ = ξ`**.
* `AlgebraicGeometry.SheafOfModules.bijective_smul_hodgeUnit`: `H⁰(X, Ω^0)` is free of rank one
  on `1`.
* `AlgebraicGeometry.SheafOfModules.hodgeCup_hodgeUnitEquiv`: `(g • 1) ∪ ξ = g • ξ`.
* `AlgebraicGeometry.SheafOfModules.hodgeTrace_unique`: **the trace of Tag 0FW4 is unique up to a
  unit of `H⁰(X, 𝒪_X)`.**

## References

* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- `⊗_A` preserves zero morphisms in its first variable. -/
local instance preservesZeroMorphisms_sheafTensor :
    (sheafTensor.{u, u, u, u, u} A).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `ℱ ⊗_A -` preserves zero morphisms. -/
local instance preservesZeroMorphisms_sheafTensor_obj
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :
    ((sheafTensor.{u, u, u, u, u} A).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-! ### Multiplication by a global function on differential forms -/

/-- **Multiplication by a global function** `g ∈ Γ(X, 𝒪_X)` on the sheaf `Ω^p` of `p`-forms, as an
endomorphism of sheaves of `A`-modules. -/
def formsSMul (g : X.presheaf.obj (op ⊤)) (p : ℕ) : deRhamTerm B p ⟶ deRhamTerm B p :=
  (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).map
    (Stacks.Cohomology.InvertibleDerived.smulHom g (B.exteriorPower p))

/-- On sections, `formsSMul B g p` is multiplication by the restriction of `g`. -/
theorem formsSMul_app (g : X.presheaf.obj (op ⊤)) (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower p).val.obj U) :
    (formsSMul B g p).val.app U x =
      Stacks.Cohomology.InvertibleDerived.ringSec
        (Stacks.Cohomology.InvertibleDerived.globalRes g U.unop) • x :=
  rfl

section SMulHom

open Stacks.Cohomology.InvertibleDerived

variable (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))

/-- Multiplication by `1` is the identity. -/
theorem smulHom_one : smulHom (1 : X.presheaf.obj (op ⊤)) F = 𝟙 F := by
  ext U m
  change ringSec (U := U) (globalRes (1 : X.presheaf.obj (op ⊤)) U.unop) • m = m
  rw [globalRes_one]
  exact (F.val.obj U).isModule.one_smul m

/-- Multiplication by a global function is additive in the function. -/
theorem smulHom_add (g h : X.presheaf.obj (op ⊤)) :
    smulHom (g + h) F = smulHom g F + smulHom h F := by
  ext U m
  change ringSec (U := U) (globalRes (g + h) U.unop) • m =
    ringSec (U := U) (globalRes g U.unop) • m + ringSec (U := U) (globalRes h U.unop) • m
  rw [globalRes_add]
  exact (F.val.obj U).isModule.add_smul _ _ m

/-- Multiplication by `0` is zero. -/
theorem smulHom_zero : smulHom (0 : X.presheaf.obj (op ⊤)) F = 0 := by
  ext U m
  change ringSec (U := U) (globalRes (0 : X.presheaf.obj (op ⊤)) U.unop) • m = 0
  rw [globalRes_zero]
  exact (F.val.obj U).isModule.zero_smul m

end SMulHom

/-- Multiplication by `1` on `Ω^p` is the identity. -/
theorem formsSMul_one (p : ℕ) : formsSMul B (1 : X.presheaf.obj (op ⊤)) p = 𝟙 _ := by
  rw [formsSMul, smulHom_one, CategoryTheory.Functor.map_id]

/-- Multiplication by `g * h` on `Ω^p` is multiplication by `h` followed by multiplication by
`g`. -/
theorem formsSMul_mul (g h : X.presheaf.obj (op ⊤)) (p : ℕ) :
    formsSMul B (g * h) p = formsSMul B h p ≫ formsSMul B g p := by
  rw [formsSMul, formsSMul, formsSMul, ← Functor.map_comp,
    Stacks.Cohomology.InvertibleDerived.smulHom_comp]

/-- Multiplication on `Ω^p` is additive in the global function. -/
theorem formsSMul_add (g h : X.presheaf.obj (op ⊤)) (p : ℕ) :
    formsSMul B (g + h) p = formsSMul B g p + formsSMul B h p := by
  rw [formsSMul, formsSMul, formsSMul, smulHom_add, Functor.map_add]

/-- Multiplication by `0` on `Ω^p` is zero. -/
theorem formsSMul_zero (p : ℕ) : formsSMul B (0 : X.presheaf.obj (op ⊤)) p = 0 := by
  rw [formsSMul, smulHom_zero, Functor.map_zero]

/-- Multiplication by `g ∈ Γ(X, 𝒪_X)` on the degree-`p` term of the de Rham complex. -/
def formsSMulC (g : X.presheaf.obj (op ⊤)) (p : ℕ) :
    (deRhamComplex B D).X p ⟶ (deRhamComplex B D).X p :=
  formsSMul B g p

/-! ### The action of global functions on Hodge cohomology -/

/-- **The Hodge cohomology group** `H^i(X, Ω^p)`: the `i`-th right derived functor of global
sections at the sheaf of `p`-forms. -/
abbrev hodgeGroup (p i : ℕ) : AddCommGrpCat.{u} :=
  ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p)

/-- Multiplication by `g ∈ Γ(X, 𝒪_X)` on `Ω^p`, read in abelian sheaves. -/
def formsSMulAb (g : X.presheaf.obj (op ⊤)) (p : ℕ) :
    (deRhamAbelianComplex B D).X p ⟶ (deRhamAbelianComplex B D).X p :=
  (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map (formsSMulC B D g p)

/-- Multiplication by `1` on `Ω^p`, read in abelian sheaves, is the identity. -/
theorem formsSMulAb_one (p : ℕ) : formsSMulAb B D (1 : X.presheaf.obj (op ⊤)) p = 𝟙 _ :=
  (congrArg (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
    (formsSMul_one B p)).trans ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
      (underlyingRingSheaf A)).map_id _)

/-- Multiplication by `g * h` on `Ω^p`, read in abelian sheaves, is multiplication by `h`
followed by multiplication by `g`. -/
theorem formsSMulAb_mul (g h : X.presheaf.obj (op ⊤)) (p : ℕ) :
    formsSMulAb B D (g * h) p = formsSMulAb B D h p ≫ formsSMulAb B D g p :=
  (congrArg (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
    (formsSMul_mul B g h p)).trans ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
      (underlyingRingSheaf A)).map_comp _ _)

/-- Multiplication on `Ω^p`, read in abelian sheaves, is additive in the global function. -/
theorem formsSMulAb_add (g h : X.presheaf.obj (op ⊤)) (p : ℕ) :
    formsSMulAb B D (g + h) p = formsSMulAb B D g p + formsSMulAb B D h p :=
  (congrArg (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
    (formsSMul_add B g h p)).trans ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
      (underlyingRingSheaf A)).map_add)

/-- Multiplication by `0` on `Ω^p`, read in abelian sheaves, is zero. -/
theorem formsSMulAb_zero (p : ℕ) : formsSMulAb B D (0 : X.presheaf.obj (op ⊤)) p = 0 :=
  (congrArg (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
    (formsSMul_zero B p)).trans ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
      (underlyingRingSheaf A)).map_zero _ _)

/-- The right derived functors of global sections are additive. -/
local instance rightDerived_sectionsFunctor_additive (i : ℕ) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).Additive :=
  Stacks.DerivedLinear.rightDerived_additive _ i

/-- **The action of `g ∈ Γ(X, 𝒪_X)` on `H^i(X, Ω^p)`**: the map induced by multiplication by `g`
on `Ω^p`. -/
def hodgeSMul (g : X.presheaf.obj (op ⊤)) (p i : ℕ) : hodgeGroup B D p i ⟶ hodgeGroup B D p i :=
  ((sectionsFunctor X.carrier ⊤).rightDerived i).map (formsSMulAb B D g p)

/-- The action of `Γ(X, 𝒪_X)` on `H^i(X, Ω^p)`, as a ring homomorphism to the additive
endomorphisms. -/
def hodgeActionHom (p i : ℕ) : X.presheaf.obj (op ⊤) →+* AddMonoid.End (hodgeGroup B D p i) where
  toFun g := (hodgeSMul B D g p i).hom
  map_one' := by
    rw [hodgeSMul, formsSMulAb_one, CategoryTheory.Functor.map_id]
    rfl
  map_mul' g h := by
    rw [hodgeSMul, formsSMulAb_mul, Functor.map_comp]
    rfl
  map_zero' := by
    rw [hodgeSMul, formsSMulAb_zero, Functor.map_zero]
    rfl
  map_add' g h := by
    rw [hodgeSMul, formsSMulAb_add, Functor.map_add]
    rfl

/-- **`H^i(X, Ω^p)` is a module over `Γ(X, 𝒪_X)`**, a global function acting through
multiplication on `Ω^p`. -/
instance (p i : ℕ) : Module (X.presheaf.obj (op ⊤)) (hodgeGroup B D p i) :=
  Module.compHom _ (hodgeActionHom B D p i)

/-- A global function `g` acts on `H^i(X, Ω^p)` through `hodgeSMul`. -/
theorem hodgeGroup_smul_def (g : X.presheaf.obj (op ⊤)) (p i : ℕ) (x : hodgeGroup B D p i) :
    g • x = (hodgeSMul B D g p i).hom x :=
  rfl

/-! ### Naturality of the identification with the hypercohomology of `Ω^p[0]` -/

/-- The identification of an object in degree `0`, extended from `ℕ` to `ℤ`, with the object in
degree `0` is natural. -/
theorem extendSingleIso_hom_naturality {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {M N : C} (g : M ⟶ N) :
    HomologicalComplex.extendMap ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map g)
        embeddingUpNat ≫ (HomologicalComplex.extendSingleIso embeddingUpNat N 0 0 (by simp)).hom =
      (HomologicalComplex.extendSingleIso embeddingUpNat M 0 0 (by simp)).hom ≫
        (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl,
    HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The inverse of the identification of `extendSingleIso_hom_naturality` is natural. -/
theorem extendSingleIso_inv_naturality {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasZeroObject C] {M N : C} (g : M ⟶ N) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g ≫
        (HomologicalComplex.extendSingleIso embeddingUpNat N 0 0 (by simp)).inv =
      (HomologicalComplex.extendSingleIso embeddingUpNat M 0 0 (by simp)).inv ≫
        HomologicalComplex.extendMap ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map g)
          embeddingUpNat := by
  rw [Iso.comp_inv_eq, Category.assoc, extendSingleIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- The identification `hodgeSinglePlusIso` of `Ω^p` in degree `0` with `Ω^p[0]`, abelianised and
extended, is natural in endomorphisms of `Ω^p`. -/
theorem hodgeSinglePlusIso_naturality (p : ℕ)
    (f : (deRhamComplex B D).X p ⟶ (deRhamComplex B D).X p) :
    (Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
        ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f) ≫
        (hodgeSinglePlusIso B D p).hom =
      (hodgeSinglePlusIso B D p).hom ≫
        modulePlusMap (A := A) ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f) := by
  apply ObjectProperty.hom_ext
  have h₁ := extendSingleIso_inv_naturality
    ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f)
  have h₂ := ((HomologicalComplex.singleMapHomologicalComplex
    (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)) (ComplexShape.up ℕ)
      0).inv.naturality f)
  have h₃ := (HomologicalComplex.extendMap_comp _ _ embeddingUpNat).symm.trans
    ((congrArg (fun φ => HomologicalComplex.extendMap φ embeddingUpNat) h₂).trans
      (HomologicalComplex.extendMap_comp _ _ embeddingUpNat))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h₃).trans (Category.assoc _ _ _).symm)))

/-- **The identification `H^i(X, Ω^p) ≅ H^i(X, Ω^p[0])` is natural** in endomorphisms of `Ω^p`. -/
theorem hodgeSingleCohomologyIso_naturality (p i : ℕ) (n : ℤ) (hn : (i : ℤ) = n)
    (f : (deRhamComplex B D).X p ⟶ (deRhamComplex B D).X p) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).map
        ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f) ≫
        (hodgeSingleCohomologyIso B D p i n hn).hom =
      (hodgeSingleCohomologyIso B D p i n hn).hom ≫
        moduleHypercohomologyMap (A := A)
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f) n := by
  subst hn
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i : ℤ)
  let Φ := (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus
  have e1 := (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X.carrier ⊤) i).hom.naturality
    ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f)
  have e2 := hodgeSinglePlusIso_naturality B D p f
  have e3 : H.map (Φ.map (DerivedCategory.Plus.Q.map
        ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
          ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f)))) ≫
      H.map (Φ.map (DerivedCategory.Plus.Q.map (hodgeSinglePlusIso B D p).hom)) =
      H.map (Φ.map (DerivedCategory.Plus.Q.map (hodgeSinglePlusIso B D p).hom)) ≫
        H.map (Φ.map (DerivedCategory.Plus.Q.map (modulePlusMap (A := A)
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f)))) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map (Φ.map_comp _ _).symm).trans
      ((congrArg (fun t => H.map (Φ.map t)) ((DerivedCategory.Plus.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Plus.Q.map e2).trans
          (DerivedCategory.Plus.Q.map_comp _ _)))).trans
        ((congrArg H.map (Φ.map_comp _ _)).trans (H.map_comp _ _))))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e1).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) e3).trans (Category.assoc _ _ _).symm)))

/-! ### The wedge product is `Γ(X, 𝒪_X)`-bilinear -/

/-- Two morphisms out of `Ω^p ⊗ Ω^q` agree if they agree on the images of all local pure
tensors. -/
private theorem tensorForms_hom_ext_unit_apply (p q : ℕ) {N : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (f g : ((sheafTensor.{u, u, u, u, u} A).obj (deRhamTerm B p)).obj (deRhamTerm B q) ⟶ N)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : (B.exteriorPower p).val.obj U)
      (y : (B.exteriorPower q).val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B q).val)).app U
            (x ⊗ₜ[A.obj.obj U] y)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B q).val)).app U
            (x ⊗ₜ[A.obj.obj U] y))) : f = g := by
  refine (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).injective ?_
  refine tensorForms_hom_ext B p q N _ _ ?_
  intro U a b ω η _ _
  exact (sheafificationHomEquiv_apply _ U _).trans
    ((h U _ _).trans (sheafificationHomEquiv_apply _ U _).symm)

/-- **The wedge product commutes with multiplication by a global function in the first
variable**: `(g ω) ∧ η = g (ω ∧ η)`. -/
theorem exteriorProductComponent_formsSMul_left (g : X.presheaf.obj (op ⊤)) (p q : ℕ) :
    ((sheafTensor.{u, u, u, u, u} A).map (formsSMul B g p)).app (deRhamTerm B q) ≫
        exteriorProductComponent B p q =
      exteriorProductComponent B p q ≫ formsSMul B g (p + q) := by
  refine tensorForms_hom_ext_unit_apply B p q _ _ fun U _ _ => ?_
  refine (congrArg (fun t => (exteriorProductComponent B p q).val.app U t)
    (tensorFunctor_map_unit_apply (N := deRhamTerm B q) (formsSMul B g p) U _ _)).trans ?_
  refine (exteriorProductComponent_unit_apply B p q U _ _).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (formsSMul B g (p + q)).val.app U t)
    (exteriorProductComponent_unit_apply B p q U _ _)).symm
  exact (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_left U _ _ _

/-- **The wedge product commutes with multiplication by a global function in the second
variable**: `ω ∧ (g η) = g (ω ∧ η)`. -/
theorem exteriorProductComponent_formsSMul_right (g : X.presheaf.obj (op ⊤)) (p q : ℕ) :
    ((sheafTensor.{u, u, u, u, u} A).obj (deRhamTerm B p)).map (formsSMul B g q) ≫
        exteriorProductComponent B p q =
      exteriorProductComponent B p q ≫ formsSMul B g (p + q) := by
  refine tensorForms_hom_ext_unit_apply B p q _ _ fun U _ _ => ?_
  refine (congrArg (fun t => (exteriorProductComponent B p q).val.app U t)
    (tensorFunctor_obj_map_unit_apply (M := deRhamTerm B p) (formsSMul B g q) U _ _)).trans ?_
  refine (exteriorProductComponent_unit_apply B p q U _ _).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (formsSMul B g (p + q)).val.app U t)
    (exteriorProductComponent_unit_apply B p q U _ _)).symm
  exact (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_right U _ _ _

section Pasting

variable {C : Type*} [Category* C]

/-- For a bifunctor `F`, if `E` intertwines `F.map μp` with `μ`, then the composite
`F(a, sq) ≫ F(sp, b') ≫ E` intertwines `F.map (sp.hom ≫ μp ≫ sp.inv)` with `μ`. -/
theorem wedgeSummand_paste_left (F : C ⥤ C ⥤ C) {a a' b b' t : C} (sp : a ≅ a') (sq : b ≅ b')
    (E : (F.obj a').obj b' ⟶ t) (μp : a' ⟶ a') (μ : t ⟶ t) (hE : (F.map μp).app b' ≫ E = E ≫ μ) :
    ((F.obj a).map sq.hom ≫ (F.map sp.hom).app b' ≫ E) ≫ μ =
      (F.map (sp.hom ≫ μp ≫ sp.inv)).app b ≫ (F.obj a).map sq.hom ≫ (F.map sp.hom).app b' ≫ E := by
  rw [Category.assoc, Category.assoc, ← hE, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    ← NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For a bifunctor `F`, if `E` intertwines `(F.obj a').map μq` with `μ`, then the composite
`F(a, sq) ≫ F(sp, b') ≫ E` intertwines `(F.obj a).map (sq.hom ≫ μq ≫ sq.inv)` with `μ`. -/
theorem wedgeSummand_paste_right (F : C ⥤ C ⥤ C) {a a' b b' t : C} (sp : a ≅ a') (sq : b ≅ b')
    (E : (F.obj a').obj b' ⟶ t) (μq : b' ⟶ b') (μ : t ⟶ t)
    (hE : (F.obj a').map μq ≫ E = E ≫ μ) :
    ((F.obj a).map sq.hom ≫ (F.map sp.hom).app b' ≫ E) ≫ μ =
      (F.obj a).map (sq.hom ≫ μq ≫ sq.inv) ≫ (F.obj a).map sq.hom ≫ (F.map sp.hom).app b' ≫ E := by
  simp only [Category.assoc, ← hE, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc, NatTrans.naturality_assoc]

/-- `ι ≫ d ≫ sI ≫ h = ι ≫ mm ≫ d ≫ sI`, pasted from `hh`, `hι`, `hm` and `key`. -/
theorem wedge_paste {P Q R T : C} (ι : P ⟶ Q) (d : Q ⟶ R) (sI : R ⟶ T) (h : T ⟶ T) (μ : R ⟶ R)
    (mm : Q ⟶ Q) (summ : P ⟶ R) (fm : P ⟶ P) (hh : sI ≫ h = μ ≫ sI) (hι : ι ≫ d = summ)
    (hm : ι ≫ mm = fm ≫ ι) (key : summ ≫ μ = fm ≫ summ) :
    ι ≫ ((d ≫ sI) ≫ h) = ι ≫ (mm ≫ (d ≫ sI)) := by
  simp only [Category.assoc]
  rw [hh, reassoc_of% hι, reassoc_of% key, reassoc_of% hm, reassoc_of% hι]

/-- For a bifunctor `F`, the composite of `F.map (e.hom ≫ u ≫ sp.inv ≫ xK.inv)` with the
identifications `xK`, `xL`, `sq`, `sp` and `E` is `F.map e.hom ≫ ul ≫ xL.hom ≫ sq.hom ≫ x`, given
`hU` and `hul`. -/
theorem unitSummand_paste (F : C ⥤ C ⥤ C) {O o₀ k₀ kk K₀ l₀ ll Lq t : C} (e : o₀ ≅ O)
    (u : O ⟶ K₀) (sp : kk ≅ K₀) (xK : k₀ ≅ kk) (xL : l₀ ≅ ll) (sq : ll ≅ Lq)
    (E : (F.obj K₀).obj Lq ⟶ t) (ul : (F.obj O).obj l₀ ⟶ l₀) (uq : (F.obj O).obj Lq ⟶ Lq)
    (x : Lq ⟶ t) (hU : (F.map u).app Lq ≫ E = uq ≫ x)
    (hul : ul ≫ xL.hom ≫ sq.hom = (F.obj O).map (xL.hom ≫ sq.hom) ≫ uq) :
    (F.map (e.hom ≫ u ≫ sp.inv ≫ xK.inv)).app l₀ ≫ (F.map xK.hom).app l₀ ≫
        (F.obj kk).map xL.hom ≫ (F.obj kk).map sq.hom ≫ (F.map sp.hom).app Lq ≫ E =
      (F.map e.hom).app l₀ ≫ ul ≫ xL.hom ≫ sq.hom ≫ x := by
  have hs : ∀ Y, (F.map sp.inv).app Y ≫ (F.map sp.hom).app Y = 𝟙 _ := fun Y => by
    rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      NatTrans.id_app]
  have hx : ∀ Y, (F.map xK.inv).app Y ≫ (F.map xK.hom).app Y = 𝟙 _ := fun Y => by
    rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      NatTrans.id_app]
  rw [reassoc_of% hul, ← hU]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc,
    reassoc_of% (hx l₀), reassoc_of% (hs l₀)]

/-- `ι ≫ T ≫ Mi = ι ≫ Mu ≫ Ex`, pasted from the identities `ha`, `hb`, `hc`, `hf`, `hε`, `hg` and
`core`. -/
theorem unitLaw_paste {P Q Q' V W P' P₁ P'' R Y Z V₁ V₂ V₃ : C} (ι : P ⟶ Q) (T : Q ⟶ Q')
    (Mi : Q' ⟶ W) (Mu : Q ⟶ V) (Ex : V ⟶ W) (A1 : P ⟶ P') (ι' : P' ⟶ Q') (b1 : P' ⟶ P₁)
    (b2 : P₁ ⟶ P'') (ιn : P'' ⟶ R) (mf : R ⟶ Y) (xMi : Y ⟶ W) (summ : P'' ⟶ Z) (sMi : Z ⟶ Y)
    (f1 : P ⟶ V₁) (f2 : V₁ ⟶ V) (ε : V ⟶ V) (g1 : V ⟶ V₂) (g2 : V₂ ⟶ V₃) (g3 : V₃ ⟶ Z)
    (ha : ι ≫ T = A1 ≫ ι') (hb : ι' ≫ Mi = (b1 ≫ b2) ≫ ιn ≫ mf ≫ xMi)
    (hc : ιn ≫ mf = summ ≫ sMi) (hf : ι ≫ Mu = f1 ≫ f2 ≫ ε) (hε : ε = 𝟙 V)
    (hg : Ex = (g1 ≫ g2 ≫ g3) ≫ sMi ≫ xMi)
    (core : A1 ≫ b1 ≫ b2 ≫ summ = f1 ≫ f2 ≫ g1 ≫ g2 ≫ g3) :
    ι ≫ T ≫ Mi = ι ≫ Mu ≫ Ex := by
  subst hε hg
  simp only [Category.comp_id, Category.assoc] at hf hb ⊢
  rw [reassoc_of% ha, hb, reassoc_of% hc, reassoc_of% hf, reassoc_of% core]

/-- `L ≫ X₁ ≫ c₁ ≫ hM = v ≫ hτ`, pasted from the identities `n`, `x`, `m` and `u`. -/
theorem unitPairing_paste {P P' Q₀ Q₁ R₀ R₁ W W' : C} (L : P ⟶ P') (X₀ : P' ⟶ Q₀)
    (X₁ X₁' : P' ⟶ Q₁) (c₀ : Q₀ ⟶ R₀) (c₁ : Q₁ ⟶ R₁) (hT : R₀ ⟶ R₁) (hM : R₁ ⟶ W)
    (hμ : R₀ ⟶ W') (hτ : W' ⟶ W) (v : P ⟶ W') (n : L ≫ X₀ ≫ c₀ ≫ hT = L ≫ X₁' ≫ c₁)
    (x : X₁' = X₁) (m : hT ≫ hM = hμ ≫ hτ) (u : L ≫ X₀ ≫ c₀ ≫ hμ = v) :
    L ≫ X₁ ≫ c₁ ≫ hM = v ≫ hτ := by
  subst x
  rw [← reassoc_of% n, m, reassoc_of% u]

/-- Composing with the image of an identity under three functors does nothing. -/
theorem comp_map_map_map_id {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* C₄] (H : C₃ ⥤ C₄) (Γ : C₂ ⥤ C₃) (Q : C₁ ⥤ C₂) (Y : C₁) {Z : C₄}
    (η : Z ⟶ H.obj (Γ.obj (Q.obj Y))) : η ≫ H.map (Γ.map (Q.map (𝟙 Y))) = η := by
  simp

end Pasting

/-- The wedge product of `Ω^p[0]` and `Ω^q[0]` intertwines multiplication by a global function on
`Ω^(p+q)` with an endomorphism `M` of the source, as soon as this holds on the unique summand. -/
private theorem hodgeSingleWedge_comp_formsSMulC_of_summand (g : X.presheaf.obj (op ⊤)) (p q : ℕ)
    (M : HomologicalComplex.mapBifunctor (hodgeSingle B D p) (hodgeSingle B D q)
      (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) ⟶
      HomologicalComplex.mapBifunctor (hodgeSingle B D p) (hodgeSingle B D q)
      (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ))
    (fm : ((sheafTensor.{u, u, u, u, u} A).obj ((hodgeSingle B D p).X 0)).obj
      ((hodgeSingle B D q).X 0) ⟶ ((sheafTensor.{u, u, u, u, u} A).obj
        ((hodgeSingle B D p).X 0)).obj ((hodgeSingle B D q).X 0))
    (hm : ∀ hab, HomologicalComplex.ιMapBifunctor (hodgeSingle B D p) (hodgeSingle B D q)
      (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) 0 0 0 hab ≫ M.f 0 =
        fm ≫ HomologicalComplex.ιMapBifunctor (hodgeSingle B D p) (hodgeSingle B D q)
          (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) 0 0 0 hab)
    (key : ∀ hab, hodgeSingleWedgeSummand B D p q 0 0 hab ≫ formsSMulC B D g (p + q) =
      fm ≫ hodgeSingleWedgeSummand B D p q 0 0 hab) :
    hodgeSingleWedge B D p q ≫
        (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g (p + q)) =
      M ≫ hodgeSingleWedge B D p q := by
  apply HomologicalComplex.to_single_hom_ext
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by
    have : a + b = 0 := hab
    omega
  have hw : (hodgeSingleWedge B D p q).f 0 =
      HomologicalComplex.mapBifunctorDesc (fun a b h => hodgeSingleWedgeSummand B D p q a b h) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((deRhamComplex B D).X (p + q))).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  have hι : HomologicalComplex.ιMapBifunctor (hodgeSingle B D p) (hodgeSingle B D q)
      (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) 0 0 0 hab ≫
      HomologicalComplex.mapBifunctorDesc (fun a b h => hodgeSingleWedgeSummand B D p q a b h) =
      hodgeSingleWedgeSummand B D p q 0 0 hab :=
    HomologicalComplex.ι_mapBifunctorDesc _ _ _ _
  have hh : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
      ((deRhamComplex B D).X (p + q))).inv ≫
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g (p + q))).f 0 =
      formsSMulC B D g (p + q) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        ((deRhamComplex B D).X (p + q))).inv := by
    rw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
  have e := wedge_paste _ _ _ _ _ _ _ _ hh hι (hm hab) (key hab)
  rw [← hw] at e
  exact e

/-- The wedge product of `Ω^p[0]` and `Ω^q[0]` commutes with multiplication by a global function
in the first variable. -/
theorem hodgeSingleWedge_formsSMul_left (g : X.presheaf.obj (op ⊤)) (p q : ℕ) :
    hodgeSingleWedge B D p q ≫
        (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g (p + q)) =
      ((tensorBifunctorNat (A := A)).obj (hodgeSingle B D p)).map (𝟙 _) ≫
        ((tensorBifunctorNat (A := A)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g p))).app
            (hodgeSingle B D q) ≫ hodgeSingleWedge B D p q := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  refine hodgeSingleWedge_comp_formsSMulC_of_summand B D g p q _
    (((sheafTensor.{u, u, u, u, u} A).map
      (((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g p)).f 0)).app
      ((hodgeSingle B D q).X 0))
    (fun hab => ?_) fun hab => ?_
  · refine (HomologicalComplex.ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [HomologicalComplex.single_map_f_self]
    exact wedgeSummand_paste_left (sheafTensor.{u, u, u, u, u} A)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X p))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X q))
      (exteriorProductComponent B p q) (formsSMul B g p) (formsSMul B g (p + q))
      (exteriorProductComponent_formsSMul_left B g p q)

/-- The wedge product of `Ω^p[0]` and `Ω^q[0]` commutes with multiplication by a global function
in the second variable. -/
theorem hodgeSingleWedge_formsSMul_right (g : X.presheaf.obj (op ⊤)) (p q : ℕ) :
    hodgeSingleWedge B D p q ≫
        (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g (p + q)) =
      ((tensorBifunctorNat (A := A)).obj (hodgeSingle B D p)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g q)) ≫
        ((tensorBifunctorNat (A := A)).map (𝟙 (hodgeSingle B D p))).app (hodgeSingle B D q) ≫
          hodgeSingleWedge B D p q := by
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  refine hodgeSingleWedge_comp_formsSMulC_of_summand B D g p q _
    (((sheafTensor.{u, u, u, u, u} A).obj ((hodgeSingle B D p).X 0)).map
      (((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g q)).f 0))
    (fun hab => ?_) fun hab => ?_
  · refine (HomologicalComplex.ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  · rw [HomologicalComplex.single_map_f_self]
    exact wedgeSummand_paste_right (sheafTensor.{u, u, u, u, u} A)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X p))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X q))
      (exteriorProductComponent B p q) (formsSMul B g q) (formsSMul B g (p + q))
      (exteriorProductComponent_formsSMul_right B g p q)

/-! ### The cup product is `Γ(X, 𝒪_X)`-bilinear -/

/-- `moduleHypercohomologyMap` sends the identity to the identity. -/
theorem moduleHypercohomologyMap_id (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) (n : ℤ) :
    moduleHypercohomologyMap (A := A) (𝟙 K) n = 𝟙 _ := by
  have h : modulePlusMap (A := A) (𝟙 K) = 𝟙 _ :=
    ObjectProperty.hom_ext _ ((congrArg (fun t => HomologicalComplex.extendMap t embeddingUpNat)
      ((abelianisationFunctor (A := A)).map_id K)).trans (HomologicalComplex.extendMap_id _ _))
  rw [moduleHypercohomologyMap, h, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- The identification of `hodgeSingleCohomologyIso_naturality`, inverted, on elements. -/
theorem hodgeSingleCohomologyIso_inv_naturality_apply (p i : ℕ) (n : ℤ) (hn : (i : ℤ) = n)
    (f : (deRhamComplex B D).X p ⟶ (deRhamComplex B D).X p)
    (z : moduleHypercohomology (A := A) (hodgeSingle B D p) n) :
    (hodgeSingleCohomologyIso B D p i n hn).inv.hom
        ((moduleHypercohomologyMap (A := A)
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f) n).hom z) =
      (((sectionsFunctor X.carrier ⊤).rightDerived i).map
        ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f)).hom
        ((hodgeSingleCohomologyIso B D p i n hn).inv.hom z) := by
  have h : (hodgeSingleCohomologyIso B D p i n hn).inv ≫
      ((sectionsFunctor X.carrier ⊤).rightDerived i).map
        ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map f) =
      moduleHypercohomologyMap (A := A)
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f) n ≫
          (hodgeSingleCohomologyIso B D p i n hn).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hodgeSingleCohomologyIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  exact (ConcreteCategory.congr_hom h z).symm

/-- **The cup product on Hodge cohomology is `Γ(X, 𝒪_X)`-linear in the first variable**:
`(g ξ) ∪ ξ' = g (ξ ∪ ξ')`. -/
theorem hodgeCup_smul_left (g : X.presheaf.obj (op ⊤)) (p q r : ℕ) (hr : p + q = r)
    (i j l : ℕ) (hl : i + j = l) (x : hodgeGroup B D p i) (y : hodgeGroup B D q j) :
    hodgeCup B D p q r hr i j l hl (g • x) y = g • hodgeCup B D p q r hr i j l hl x y := by
  subst hr hl
  rw [hodgeCup_eq, hodgeCup_eq, hodgeGroup_smul_def, hodgeGroup_smul_def, hodgeSMul, hodgeSMul,
    formsSMulAb, formsSMulAb]
  have n1 := ConcreteCategory.congr_hom
    (hodgeSingleCohomologyIso_naturality B D p i i rfl (formsSMulC B D g p)) x
  have c := canonicalPairing_naturality
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g p))
    (𝟙 (hodgeSingle B D q)) (hodgeSingleWedge B D p q) (hodgeSingleWedge B D p q)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g (p + q)))
    (hodgeSingleWedge_formsSMul_left B D g p q) i j
    ((hodgeSingleCohomologyIso B D p i i rfl).hom.hom x)
    ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y)
  rw [moduleHypercohomologyMap_id] at c
  rw [← hodgeSingleCohomologyIso_inv_naturality_apply]
  refine congrArg (hodgeSingleCohomologyIso B D (p + q) (i + j) ((i : ℤ) + (j : ℤ)) _).inv.hom ?_
  refine Eq.trans ?_ c.symm
  exact congrArg (fun t => canonicalPairing (hodgeSingleWedge B D p q) (i : ℤ) (j : ℤ) t
    ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y)) n1

/-- **The cup product on Hodge cohomology is `Γ(X, 𝒪_X)`-linear in the second variable**:
`ξ ∪ (g ξ') = g (ξ ∪ ξ')`. -/
theorem hodgeCup_smul_right (g : X.presheaf.obj (op ⊤)) (p q r : ℕ) (hr : p + q = r)
    (i j l : ℕ) (hl : i + j = l) (x : hodgeGroup B D p i) (y : hodgeGroup B D q j) :
    hodgeCup B D p q r hr i j l hl x (g • y) = g • hodgeCup B D p q r hr i j l hl x y := by
  subst hr hl
  rw [hodgeCup_eq, hodgeCup_eq, hodgeGroup_smul_def, hodgeGroup_smul_def, hodgeSMul, hodgeSMul,
    formsSMulAb, formsSMulAb]
  have n1 := ConcreteCategory.congr_hom
    (hodgeSingleCohomologyIso_naturality B D q j j rfl (formsSMulC B D g q)) y
  have c := canonicalPairing_naturality (𝟙 (hodgeSingle B D p))
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g q))
    (hodgeSingleWedge B D p q) (hodgeSingleWedge B D p q)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (formsSMulC B D g (p + q)))
    (hodgeSingleWedge_formsSMul_right B D g p q) i j
    ((hodgeSingleCohomologyIso B D p i i rfl).hom.hom x)
    ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y)
  rw [moduleHypercohomologyMap_id] at c
  rw [← hodgeSingleCohomologyIso_inv_naturality_apply]
  refine congrArg (hodgeSingleCohomologyIso B D (p + q) (i + j) ((i : ℤ) + (j : ℤ)) _).inv.hom ?_
  refine Eq.trans ?_ c.symm
  exact congrArg (fun t => canonicalPairing (hodgeSingleWedge B D p q) (i : ℤ) (j : ℤ)
    ((hodgeSingleCohomologyIso B D p i i rfl).hom.hom x) t) n1

/-- The cup product on Hodge cohomology is additive in the first variable. -/
theorem hodgeCup_add_left (p q r : ℕ) (hr : p + q = r) (i j l : ℕ) (hl : i + j = l)
    (x x' : hodgeGroup B D p i) (y : hodgeGroup B D q j) :
    hodgeCup B D p q r hr i j l hl (x + x') y =
      hodgeCup B D p q r hr i j l hl x y + hodgeCup B D p q r hr i j l hl x' y := by
  subst hr hl
  rw [hodgeCup_eq, hodgeCup_eq, hodgeCup_eq]
  unfold canonicalPairing
  simp only [map_add, TensorProduct.add_tmul]

/-- The cup product on Hodge cohomology is additive in the second variable. -/
theorem hodgeCup_add_right (p q r : ℕ) (hr : p + q = r) (i j l : ℕ) (hl : i + j = l)
    (x : hodgeGroup B D p i) (y y' : hodgeGroup B D q j) :
    hodgeCup B D p q r hr i j l hl x (y + y') =
      hodgeCup B D p q r hr i j l hl x y + hodgeCup B D p q r hr i j l hl x y' := by
  subst hr hl
  rw [hodgeCup_eq, hodgeCup_eq, hodgeCup_eq]
  unfold canonicalPairing
  simp only [map_add, TensorProduct.tmul_add]

/-! ### The unit of the wedge product -/

/-- **The unit `A ⟶ Ω^0` of the wedge product**: the morphism of sheaves of `A`-modules sending `1`
to the unit `1 ∈ Ω^0` of the exterior algebra. -/
def unitToForms :
    _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A) ⟶
      (deRhamComplex B D).X 0 :=
  ((deRhamComplex B D).X 0).unitHomEquiv.symm B.exterior.one

/-- On sections, `unitToForms` sends `r` to `r • 1`. -/
theorem unitToForms_app (U : (Opens X.carrier)ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj.obj U) :
    (unitToForms B D).val.app U r =
      (show (deRhamComplex B D).X 0 |>.val.obj U from r • (show (deRhamTerm B 0).val.obj U from
        B.exterior.one.eval U)) :=
  rfl

open Stacks.Cohomology.DerivedGlobalCupProduct (sheafTensorUnitLeft) in
/-- **`1 ∧ ω = ω`**: the wedge product with the unit of `Ω^0`, precomposed with `A ⟶ Ω^0`, is the
left unitor `A ⊗_A Ω^q ≅ Ω^q`. -/
theorem exteriorProductComponent_unitToForms (q : ℕ) :
    ((sheafTensor.{u, u, u, u, u} A).map (unitToForms B D)).app ((deRhamComplex B D).X q) ≫
        exteriorProductComponent B 0 q =
      (sheafTensorUnitLeft (baseRingedSpace A)).app ((deRhamComplex B D).X q) ≫
        ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom := by
  refine (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).injective ?_
  refine PresheafOfModules.hom_ext fun U => ModuleCat.MonoidalCategory.tensor_ext fun r ω => ?_
  refine (sheafificationHomEquiv_apply _ U _).trans
    (Eq.trans ?_ (sheafificationHomEquiv_apply _ U _).symm)
  refine (congrArg (fun t => (exteriorProductComponent B 0 q).val.app U t)
    (tensorFunctor_map_unit_apply (N := (deRhamComplex B D).X q) (unitToForms B D) U r ω)).trans ?_
  refine (exteriorProductComponent_unit_apply B 0 q U _ ω).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun t => ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom.val.app U t)
    (Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul (baseRingedSpace A)
      ((deRhamComplex B D).X q) U r ω)).symm
  refine DirectSum.of_injective (β := gradedForms B U) ((0 + q : ℕ) : ℤ) ?_
  refine (ofGradedForm_mul B U ((0 : ℕ) : ℤ) (q : ℤ) _ ω).trans ?_
  refine (scalarForm_mul B U (φ.hom.app U r) (q : ℤ) ω).trans ?_
  exact (ofGradedForm_XIsoOfEq B D (zero_add q).symm U _).symm

open Stacks.Cohomology.DerivedGlobalCupProduct (unitSingleComplex unitLeftAction sheafTensorUnitLeft
  unitSingleComplexXIso) in
/-- **The unit `A[0] ⟶ Ω^0[0]`**, as a morphism of `ℤ`-indexed complexes into the extension of
`Ω^0[0]`. -/
def unitToFormsInt :
    (CochainComplex.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ⟶
      (hodgeSingle B D 0).extend embeddingUpNat :=
  (CochainComplex.singleFunctor _ 0).map (unitToForms B D) ≫
    (HomologicalComplex.extendSingleIso embeddingUpNat ((deRhamComplex B D).X 0) 0 0
      (by simp)).inv

open Stacks.Cohomology.DerivedGlobalCupProduct (unitSingleComplex unitLeftAction sheafTensorUnitLeft
  unitSingleComplexXIso) in
/-- **The wedge product with the unit is the action of `A[0]`**: on `Tot(A[0] ⊗ Ω^q[0])`, the
unit `A[0] ⟶ Ω^0[0]` followed by the extended wedge product is the action of `A[0]` followed by
`Ω^q = Ω^{0 + q}`. -/
theorem mapBifunctorMap_unitToFormsInt_multiplicationInt (q : ℕ) :
    HomologicalComplex.mapBifunctorMap (unitToFormsInt B D)
        (𝟙 ((hodgeSingle B D q).extend embeddingUpNat)) (sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℤ) ≫ multiplicationInt (hodgeSingleWedge B D 0 q) =
      unitLeftAction (baseRingedSpace A) ((hodgeSingle B D q).extend embeddingUpNat) ≫
        HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
          ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) embeddingUpNat := by
  ext n : 1
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  by_cases ha : a = 0
  swap
  · exact (isZero_tensorFunctor_obj_obj_of_left
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ a ha) _).eq_of_src _ _
  by_cases hb : b = 0
  swap
  · exact (isZero_tensorFunctor_obj_obj_of_right _
      ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ b hb).of_iso
        ((HomologicalComplex.eval _ _ b).mapIso (HomologicalComplex.extendSingleIso embeddingUpNat
          ((deRhamComplex B D).X q) 0 0 (by simp))))).eq_of_src _ _
  subst ha hb
  obtain rfl : n = 0 := by
    have : (0 : ℤ) + 0 = n := hab
    omega
  have hψ : (unitToFormsInt B D).f 0 =
      (unitSingleComplexXIso (S := baseRingedSpace A)).hom ≫ unitToForms B D ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X 0)).inv ≫
        ((hodgeSingle B D 0).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp)).inv := by
    change ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (unitToForms B D) ≫
      (HomologicalComplex.extendSingleIso embeddingUpNat ((deRhamComplex B D).X 0) 0 0
        (by simp)).inv).f 0 = _
    rw [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.extendSingleIso_inv_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have ha' : HomologicalComplex.ιMapBifunctor _ _ (sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℤ) 0 0 0 hab ≫
      (HomologicalComplex.mapBifunctorMap (unitToFormsInt B D)
        (𝟙 ((hodgeSingle B D q).extend embeddingUpNat)) (sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℤ)).f 0 =
      ((sheafTensor.{u, u, u, u, u} A).map ((unitToFormsInt B D).f 0)).app
          (((hodgeSingle B D q).extend embeddingUpNat).X 0) ≫
        HomologicalComplex.ιMapBifunctor ((hodgeSingle B D 0).extend embeddingUpNat)
          ((hodgeSingle B D q).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℤ) 0 0 0 hab := by
    refine (HomologicalComplex.ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  have hb' : HomologicalComplex.ιMapBifunctor ((hodgeSingle B D 0).extend embeddingUpNat)
        ((hodgeSingle B D q).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℤ) 0 0 0 hab ≫ (multiplicationInt (hodgeSingleWedge B D 0 q)).f 0 =
      (((sheafTensor.{u, u, u, u, u} A).map
          ((hodgeSingle B D 0).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp)).hom).app
            (((hodgeSingle B D q).extend embeddingUpNat).X 0) ≫
        ((sheafTensor.{u, u, u, u, u} A).obj ((hodgeSingle B D 0).X 0)).map
          ((hodgeSingle B D q).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp)).hom) ≫
        HomologicalComplex.ιMapBifunctor (hodgeSingle B D 0) (hodgeSingle B D q)
          (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) 0 0 0 (by simp) ≫
        (hodgeSingleWedge B D 0 q).f 0 ≫
        ((hodgeSingle B D (0 + q)).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp)).inv :=
    (ι_multiplicationInt_f (hodgeSingleWedge B D 0 q) 0 0 0 (by simp)).trans
      (Category.assoc _ _ _).symm
  have hw : (hodgeSingleWedge B D 0 q).f 0 =
      HomologicalComplex.mapBifunctorDesc (fun a b h => hodgeSingleWedgeSummand B D 0 q a b h) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((deRhamComplex B D).X (0 + q))).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  have hι : HomologicalComplex.ιMapBifunctor (hodgeSingle B D 0) (hodgeSingle B D q)
      (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) 0 0 0 (by simp) ≫
      HomologicalComplex.mapBifunctorDesc (fun a b h => hodgeSingleWedgeSummand B D 0 q a b h) =
      hodgeSingleWedgeSummand B D 0 q 0 0 (by simp) :=
    HomologicalComplex.ι_mapBifunctorDesc _ _ _ _
  have hc' : HomologicalComplex.ιMapBifunctor (hodgeSingle B D 0) (hodgeSingle B D q)
      (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) 0 0 0 (by simp) ≫
      (hodgeSingleWedge B D 0 q).f 0 =
      hodgeSingleWedgeSummand B D 0 q 0 0 (by simp) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((deRhamComplex B D).X (0 + q))).inv := by
    rw [hw, reassoc_of% hι]
  have hf' := Stacks.Cohomology.DerivedGlobalCupProduct.ιMapBifunctor_unitLeftAction_f
    (S := baseRingedSpace A)
    ((hodgeSingle B D q).extend embeddingUpNat) 0 0 hab
  have hg' : (HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
      ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) embeddingUpNat).f 0 =
      (((hodgeSingle B D q).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X q)).hom ≫
        ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((deRhamComplex B D).X (0 + q))).inv ≫
        ((hodgeSingle B D (0 + q)).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp)).inv := by
    rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) (by simp),
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc]
  have core := unitSummand_paste (sheafTensor.{u, u, u, u, u} A)
    (unitSingleComplexXIso (S := baseRingedSpace A)) (unitToForms B D)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X 0))
    ((hodgeSingle B D 0).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp))
    ((hodgeSingle B D q).extendXIso embeddingUpNat (i' := 0) (i := 0) (by simp))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 ((deRhamComplex B D).X q))
    (exteriorProductComponent B 0 q)
    ((sheafTensorUnitLeft (baseRingedSpace A)).app
      (((hodgeSingle B D q).extend embeddingUpNat).X 0))
    ((sheafTensorUnitLeft (baseRingedSpace A)).app ((deRhamComplex B D).X q))
    ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom
    (exteriorProductComponent_unitToForms B D q)
    ((sheafTensorUnitLeft (baseRingedSpace A)).naturality _).symm
  rw [hψ] at ha'
  exact unitLaw_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha' hb' hc' hf'
    (eqToHom_refl _ _) hg' core

/-! ### The unit law -/

section UnitLaw

open Stacks.Cohomology.DerivedGlobalCupProduct (unitClass totalCupPairing unitLeftAction
  cohomologyModule)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open CategoryTheory.MonoidalCategory

/-- **The unit class `1 ∈ H⁰(X, Ω^0[0])`**, on cohomology modules: the image of the class
`1 ∈ H⁰(X, A)` of the unit section under the unit `A ⟶ Ω^0` of the wedge product. -/
def hodgeUnitModule : cohomologyModule (moduleDerived (A := A) (hodgeSingle B D 0)) 0 :=
  (cohomologyModuleMap 0 (unitToFormsInt B D)).hom
    ((unitClass (S := baseRingedSpace A)).hom (1 : baseRing (baseRingedSpace A)))

/-- The unit law of the cup product along the wedge product, on cohomology modules, as an identity
of morphisms out of the base ring. -/
theorem canonicalPairingModule_unit_comp (q : ℕ) (j : ℤ)
    (η : ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)) ⟶
      cohomologyModule (moduleDerived (A := A) (hodgeSingle B D q)) j) :
    (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
        ((unitClass (S := baseRingedSpace A) ≫ cohomologyModuleMap 0 (unitToFormsInt B D)) ⊗ₘ η) ≫
        canonicalPairingModule (hodgeSingleWedge B D 0 q) 0 j =
      (η ≫ eqToHom (congrArg (fun n => cohomologyModule (moduleDerived (A := A)
          (hodgeSingle B D q)) n) (zero_add j).symm)) ≫
        cohomologyModuleMap (0 + j) (HomologicalComplex.extendMap
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
            ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) embeddingUpNat) := by
  rw [canonicalPairingModule_eq]
  have n := Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_naturality'
    (S := baseRingedSpace A) (unitToFormsInt B D) (𝟙 ((hodgeSingle B D q).extend embeddingUpNat))
    0 j unitClass η
  have m := (cohomologyModuleMap_comp (0 + j) _ _).symm.trans
    ((congrArg (cohomologyModuleMap (A := A) (0 + j))
      (mapBifunctorMap_unitToFormsInt_multiplicationInt B D q)).trans
        (cohomologyModuleMap_comp (0 + j) _ _))
  have u := Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_unitClass
    (S := baseRingedSpace A) ((hodgeSingle B D q).extend embeddingUpNat)
    (exists_isStrictlyGE_hodgeSingle B D q) j η
  exact unitPairing_paste _ _ _ _ _ _ _ _ _ _ _ n
    (congrArg (fun t => _ ⊗ₘ t) (comp_map_map_map_id _ _ _ _ η)) m u

/-- **The unit law of the cup product along the wedge product, on cohomology modules**: the cup
product of the unit class with `η ∈ H^j(X, Ω^q[0])` is `η`, read in
`H^{0 + j}(X, Ω^{0 + q}[0])`. -/
theorem canonicalPairingModule_hodgeUnitModule (q : ℕ) (j : ℤ)
    (η : cohomologyModule (moduleDerived (A := A) (hodgeSingle B D q)) j) :
    (canonicalPairingModule (hodgeSingleWedge B D 0 q) 0 j).hom (hodgeUnitModule B D ⊗ₜ η) =
      (cohomologyModuleMap (0 + j) (HomologicalComplex.extendMap
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
            ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) embeddingUpNat)).hom
        ((eqToHom (congrArg (fun n => cohomologyModule (moduleDerived (A := A)
          (hodgeSingle B D q)) n) (zero_add j).symm)).hom η) := by
  have e1 : (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing (baseRingedSpace A)) _ η)).hom
      (1 : baseRing (baseRingedSpace A)) = η := by
    simp
  have key := ConcreteCategory.congr_hom (canonicalPairingModule_unit_comp B D q j
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing (baseRingedSpace A)) _ η)))
      (1 : baseRing (baseRingedSpace A))
  refine Eq.trans ?_ (key.trans ?_)
  · exact congrArg (fun t => (canonicalPairingModule (hodgeSingleWedge B D 0 q) 0 j).hom
      (hodgeUnitModule B D ⊗ₜ t)) e1.symm
  · exact congrArg (fun t => (cohomologyModuleMap (0 + j) (HomologicalComplex.extendMap
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
            ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) embeddingUpNat)).hom
        ((eqToHom (congrArg (fun n => cohomologyModule (moduleDerived (A := A)
          (hodgeSingle B D q)) n) (zero_add j).symm)).hom t)) e1

/-- The identification `moduleHypercohomologyIso` commutes with moving the degree. -/
theorem moduleHypercohomologyIso_inv_eqToHom (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ)
    {a b : ℤ} (h : a = b) (z : moduleHypercohomology (A := A) K a) :
    (moduleHypercohomologyIso K b).inv.hom
        ((eqToHom (congrArg (fun n => cohomologyModule (moduleDerived (A := A) K) n) h)).hom
          ((moduleHypercohomologyIso K a).hom.hom z)) =
      (eqToHom (congrArg (fun n => moduleHypercohomology (A := A) K n) h)).hom z := by
  subst h
  exact (moduleHypercohomologyIso K a).hom_inv_id_apply z

/-- **The hypercohomology class of the unit** `1 ∈ H⁰(X, Ω^0[0])`. -/
def hodgeUnitHyp : moduleHypercohomology (A := A) (hodgeSingle B D 0) 0 :=
  (moduleHypercohomologyIso (hodgeSingle B D 0) 0).inv.hom (hodgeUnitModule B D)

/-- **The unit law of the cup product along the wedge product**, on hypercohomology: the cup
product of the unit class with `η ∈ H^j(X, Ω^q[0])` is `η`, read in
`H^{0 + j}(X, Ω^{0 + q}[0])`. -/
theorem canonicalPairing_hodgeUnitHyp (q : ℕ) (j : ℤ)
    (η : moduleHypercohomology (A := A) (hodgeSingle B D q) j) :
    canonicalPairing (hodgeSingleWedge B D 0 q) 0 j (hodgeUnitHyp B D) η =
      (moduleHypercohomologyMap (A := A) ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
          ((deRhamComplex B D).XIsoOfEq (zero_add q).symm).hom) (0 + j)).hom
        ((eqToHom (congrArg (fun n => moduleHypercohomology (A := A) (hodgeSingle B D q) n)
          (zero_add j).symm)).hom η) := by
  unfold canonicalPairing hodgeUnitHyp
  rw [Iso.inv_hom_id_apply, canonicalPairingModule_hodgeUnitModule,
    ← moduleHypercohomologyIso_inv_naturality_apply,
    moduleHypercohomologyIso_inv_eqToHom _ (zero_add j).symm]

/-- Transporting a Hodge class along `H^i(X, Ω^p) ≅ H^i(X, Ω^p[0])`, equalities of the degrees, and
back is transporting it along the equalities. -/
theorem hodgeSingleCohomologyIso_transport {p p' : ℕ} (h : p = p') {i i' : ℕ} (hi : i = i')
    {n n' : ℤ} (hn : (i : ℤ) = n) (hn' : (i' : ℤ) = n') (hnn : n = n') (y : hodgeGroup B D p i) :
    (hodgeSingleCohomologyIso B D p' i' n' hn').inv.hom
        ((moduleHypercohomologyMap (A := A) ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
          ((deRhamComplex B D).XIsoOfEq h).hom) n').hom
          ((eqToHom (congrArg (fun m => moduleHypercohomology (A := A) (hodgeSingle B D p) m)
            hnn)).hom ((hodgeSingleCohomologyIso B D p i n hn).hom.hom y))) =
      (eqToHom (by subst h hi; rfl : hodgeGroup B D p i = hodgeGroup B D p' i')).hom y := by
  subst h hi hnn
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, CategoryTheory.Functor.map_id,
    moduleHypercohomologyMap_id, eqToHom_refl]
  exact (hodgeSingleCohomologyIso B D p i n hn').hom_inv_id_apply y

/-- **The unit `1 ∈ H⁰(X, Ω^0)` of Hodge cohomology**: the class of the unit section of `Ω^0`. -/
def hodgeUnit : hodgeGroup B D 0 0 :=
  (hodgeSingleCohomologyIso B D 0 0 ((0 : ℕ) : ℤ) rfl).inv.hom (hodgeUnitHyp B D)

/-- The unit law of the Hodge cup product, with the target indices free. -/
theorem hodgeCup_hodgeUnit_eqToHom (q r : ℕ) (hr : 0 + q = r) (j l : ℕ) (hl : 0 + j = l)
    (y : hodgeGroup B D q j) :
    hodgeCup B D 0 q r hr 0 j l hl (hodgeUnit B D) y =
      (eqToHom (by subst hr hl; simp : hodgeGroup B D q j = hodgeGroup B D r l)).hom y := by
  subst hr hl
  rw [hodgeCup_eq]
  refine (congrArg (hodgeSingleCohomologyIso B D (0 + q) (0 + j) (((0 : ℕ) : ℤ) + (j : ℤ))
    (by push_cast; rfl)).inv.hom ((congrArg (fun t => canonicalPairing (hodgeSingleWedge B D 0 q)
      ((0 : ℕ) : ℤ) (j : ℤ) t ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y))
        (Iso.inv_hom_id_apply _ _)).trans (canonicalPairing_hodgeUnitHyp B D q (j : ℤ)
          ((hodgeSingleCohomologyIso B D q j j rfl).hom.hom y)))).trans ?_
  exact hodgeSingleCohomologyIso_transport B D (zero_add q).symm (zero_add j).symm rfl _
    (by simp) y

/-- **The unit law of the cup product on Hodge cohomology**: `1 ∪ ξ = ξ` for `1 ∈ H⁰(X, Ω^0)` and
every `ξ ∈ H^j(X, Ω^q)`. -/
theorem hodgeCup_hodgeUnit (q j : ℕ) (y : hodgeGroup B D q j) :
    hodgeCup B D 0 q q (zero_add q) 0 j j (zero_add j) (hodgeUnit B D) y = y :=
  (hodgeCup_hodgeUnit_eqToHom B D q q (zero_add q) j j (zero_add j) y).trans
    (by rw [eqToHom_refl]; rfl)

end UnitLaw

/-! ### `H⁰(X, Ω^0)` is free of rank one on the unit -/

section RankOne

open Stacks.Cohomology.InvertibleDerived (ringSec globalRes globalRes_top)

/-- The global sections `g · 1` of `Ω^0`, for `g ∈ Γ(X, 𝒪_X)`. -/
def formsZeroSection (g : X.presheaf.obj (op ⊤)) :
    (sectionsFunctor X.carrier ⊤).obj ((deRhamAbelianComplex B D).X 0) :=
  (show (B.exteriorPower 0).val.obj (op ⊤) from
    ringSec (U := op ⊤) g • B.exterior.one.eval (op ⊤))

/-- **`Γ(X, Ω^0) = Γ(X, 𝒪_X)`**: every global section of `Ω^0` is `g · 1` for exactly one `g`. -/
theorem bijective_formsZeroSection : Function.Bijective (formsZeroSection B D) := by
  refine ⟨fun g h hgh => ?_, fun x => ?_⟩
  · have e := congrArg (fun x : (B.exteriorPower 0).val.obj (op ⊤) =>
      B.exteriorPieceZeroIsoUnit.hom.val.app (op ⊤) x) hgh
    simp only [formsZeroSection] at e
    rw [map_smul, map_smul, B.exteriorPieceZeroIsoUnit_one] at e
    have e' : ringSec (U := op ⊤) g * 1 = ringSec (U := op ⊤) h * 1 := e
    rw [mul_one, mul_one] at e'
    exact e'
  · exact B.exists_exterior_eq_smul_one (op ⊤) (show (B.exteriorPower 0).val.obj (op ⊤) from x)

/-- Multiplication by `g` on `Ω^0`, on global sections of the form `h · 1`. -/
theorem sectionsFunctor_map_formsSMulAb_formsZeroSection (g h : X.presheaf.obj (op ⊤)) :
    ((sectionsFunctor X.carrier ⊤).map (formsSMulAb B D g 0)).hom (formsZeroSection B D h) =
      formsZeroSection B D (g * h) := by
  change ringSec (U := op ⊤) (globalRes g ⊤) • (ringSec (U := op ⊤) h •
      B.exterior.one.eval (op ⊤)) = ringSec (U := op ⊤) (g * h) • B.exterior.one.eval (op ⊤)
  rw [globalRes_top, ← mul_smul]
  rfl

/-- The class in `H⁰(X, Ω^0)` of the global section `g · 1`, through `H⁰(X, -) = Γ(X, -)`. -/
def hodgeZeroClass (g : X.presheaf.obj (op ⊤)) : hodgeGroup B D 0 0 :=
  ((sectionsFunctor X.carrier ⊤).rightDerivedZeroIsoSelf.inv.app
    ((deRhamAbelianComplex B D).X 0)).hom (formsZeroSection B D g)

/-- **`Γ(X, 𝒪_X) = H⁰(X, Ω^0)`**: `g ↦` the class of `g · 1` is a bijection. -/
theorem bijective_hodgeZeroClass : Function.Bijective (hodgeZeroClass B D) :=
  ((ConcreteCategory.bijective_of_isIso
    ((sectionsFunctor X.carrier ⊤).rightDerivedZeroIsoSelf.inv.app
      ((deRhamAbelianComplex B D).X 0)))).comp (bijective_formsZeroSection B D)

/-- The class of `(g * h) · 1` is `g` times the class of `h · 1`. -/
theorem hodgeZeroClass_mul (g h : X.presheaf.obj (op ⊤)) :
    hodgeZeroClass B D (g * h) = g • hodgeZeroClass B D h := by
  rw [hodgeGroup_smul_def, hodgeZeroClass, hodgeZeroClass, hodgeSMul,
    ← sectionsFunctor_map_formsSMulAb_formsZeroSection]
  exact (ConcreteCategory.congr_hom
    ((sectionsFunctor X.carrier ⊤).rightDerivedZeroIsoSelf.inv.naturality
      (formsSMulAb B D g 0)) (formsZeroSection B D h))

/-- **`H⁰(X, Ω^0)` is free of rank one over `Γ(X, 𝒪_X)` on the unit**: `g ↦ g • 1` is a bijection
`Γ(X, 𝒪_X) ⟶ H⁰(X, Ω^0)`. -/
theorem bijective_smul_hodgeUnit :
    Function.Bijective (fun g : X.presheaf.obj (op ⊤) => g • hodgeUnit B D) := by
  have hφ := bijective_hodgeZeroClass B D
  obtain ⟨s, hs⟩ := hφ.2 (hodgeUnit B D)
  obtain ⟨t, ht⟩ := hφ.2 (hodgeCup B D 0 0 0 (zero_add 0) 0 0 0 (zero_add 0)
    (hodgeZeroClass B D 1) (hodgeZeroClass B D 1))
  have hst : s * t = 1 := by
    refine hφ.1 ?_
    rw [hodgeZeroClass_mul, ht, ← hodgeCup_smul_left, ← hodgeZeroClass_mul, mul_one, hs,
      hodgeCup_hodgeUnit]
  have key : (fun g : X.presheaf.obj (op ⊤) => g • hodgeUnit B D) =
      hodgeZeroClass B D ∘ (fun g => g * s) := by
    funext g
    rw [Function.comp_apply, ← hs, ← hodgeZeroClass_mul]
  rw [key]
  refine hφ.comp ⟨fun a b hab => ?_, fun a => ⟨a * t, by
    change a * t * s = a
    rw [mul_assoc, mul_comm t s, hst, mul_one]⟩⟩
  simpa [mul_assoc, hst] using congrArg (· * t) hab

end RankOne

/-! ### The cup product as a bilinear map, and uniqueness of the trace up to a unit -/

/-- **The cup product on Hodge cohomology, as a `Γ(X, 𝒪_X)`-bilinear map**
`H^i(X, Ω^p) × H^j(X, Ω^q) ⟶ H^l(X, Ω^r)`. -/
def hodgeCupBilin (p q r : ℕ) (hr : p + q = r) (i j l : ℕ) (hl : i + j = l) :
    hodgeGroup B D p i →ₗ[X.presheaf.obj (op ⊤)] hodgeGroup B D q j →ₗ[X.presheaf.obj (op ⊤)]
      hodgeGroup B D r l :=
  LinearMap.mk₂ _ (hodgeCup B D p q r hr i j l hl) (hodgeCup_add_left B D p q r hr i j l hl)
    (fun g x y => hodgeCup_smul_left B D g p q r hr i j l hl x y)
    (hodgeCup_add_right B D p q r hr i j l hl)
    (fun g x y => hodgeCup_smul_right B D g p q r hr i j l hl x y)

/-- `hodgeCupBilin`, evaluated, is `hodgeCup`. -/
@[simp]
theorem hodgeCupBilin_apply (p q r : ℕ) (hr : p + q = r) (i j l : ℕ) (hl : i + j = l)
    (x : hodgeGroup B D p i) (y : hodgeGroup B D q j) :
    hodgeCupBilin B D p q r hr i j l hl x y = hodgeCup B D p q r hr i j l hl x y :=
  rfl

/-- **`Γ(X, 𝒪_X) ≅ H⁰(X, Ω^0)`**, `g ↦ g • 1`. -/
noncomputable def hodgeUnitEquiv :
    X.presheaf.obj (op ⊤) ≃ₗ[X.presheaf.obj (op ⊤)] hodgeGroup B D 0 0 :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (hodgeUnit B D))
    (bijective_smul_hodgeUnit B D)

/-- `hodgeUnitEquiv` sends `g` to `g • 1`. -/
@[simp]
theorem hodgeUnitEquiv_apply (g : X.presheaf.obj (op ⊤)) :
    hodgeUnitEquiv B D g = g • hodgeUnit B D :=
  rfl

/-- **The cup product with a class of degree `(0, 0)` is the module action**:
`(g • 1) ∪ ξ = g • ξ`. -/
theorem hodgeCup_hodgeUnitEquiv (g : X.presheaf.obj (op ⊤)) (q j : ℕ) (y : hodgeGroup B D q j) :
    hodgeCup B D 0 q q (zero_add q) 0 j j (zero_add j) (hodgeUnitEquiv B D g) y = g • y := by
  rw [hodgeUnitEquiv_apply, hodgeCup_smul_left, hodgeCup_hodgeUnit]

/-- The `k`-module structure on `H^i(X, Ω^p)` through a `k`-algebra structure on `Γ(X, 𝒪_X)`. -/
abbrev hodgeGroupModuleOf (k : Type*) [CommSemiring k] [Algebra k (X.presheaf.obj (op ⊤))]
    (p i : ℕ) : Module k (hodgeGroup B D p i) :=
  Module.compHom _ (algebraMap k (X.presheaf.obj (op ⊤)))

/-- Through `hodgeGroupModuleOf`, the actions of `k` and of `Γ(X, 𝒪_X)` on `H^i(X, Ω^p)` form a
scalar tower. -/
theorem hodgeGroup_isScalarTower (k : Type*) [CommSemiring k] [Algebra k (X.presheaf.obj (op ⊤))]
    (p i : ℕ) :
    letI := hodgeGroupModuleOf B D k p i
    IsScalarTower k (X.presheaf.obj (op ⊤)) (hodgeGroup B D p i) := by
  let := hodgeGroupModuleOf B D k p i
  exact ⟨fun a g x => by
    change (a • g) • x = algebraMap k (X.presheaf.obj (op ⊤)) a • g • x
    rw [Algebra.smul_def, mul_smul]⟩

/-- **The pairings `H^q(X, Ω^p) × H^{d - q}(X, Ω^{d - p}) ⟶ H^d(X, Ω^d)` of Tag 0FW4**, for
`p, q ≤ d`, as `Γ(X, 𝒪_X)`-bilinear maps. -/
def hodgeDualityPairing (d : ℕ) (pq : {pq : ℕ × ℕ // pq.1 ≤ d ∧ pq.2 ≤ d}) :
    hodgeGroup B D pq.1.1 pq.1.2 →ₗ[X.presheaf.obj (op ⊤)]
      hodgeGroup B D (d - pq.1.1) (d - pq.1.2) →ₗ[X.presheaf.obj (op ⊤)] hodgeGroup B D d d :=
  hodgeCupBilin B D pq.1.1 (d - pq.1.1) d (by omega) pq.1.2 (d - pq.1.2) d (by omega)

/-- **The trace of Tag 0FW4 is unique up to a unit of `H⁰(X, 𝒪_X)`.** Let `k` be a field with a
`k`-algebra structure on `Γ(X, 𝒪_X)`, and let `t : H^d(X, Ω^d) ⟶ k` make every pairing
`H^q(X, Ω^p) × H^{d - q}(X, Ω^{d - p}) ⟶ k`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`, `p, q ≤ d`, perfect. Then a
second linear form `t'` makes all these pairings perfect if and only if `t' = t ∘ (u • -)` for a
unit `u` of `Γ(X, 𝒪_X)`, and this unit is unique. -/
theorem hodgeTrace_unique (k : Type*) [Field k] [Algebra k (X.presheaf.obj (op ⊤))] (d : ℕ) :
    letI : ∀ p i, Module k (hodgeGroup B D p i) := fun p i => hodgeGroupModuleOf B D k p i
    haveI : ∀ p i, IsScalarTower k (X.presheaf.obj (op ⊤)) (hodgeGroup B D p i) :=
      fun p i => hodgeGroup_isScalarTower B D k p i
    ∀ (t t' : hodgeGroup B D d d →ₗ[k] k),
      (∀ pq, (((hodgeDualityPairing B D d pq).restrictScalars₁₂ k k).compr₂ t).IsPerfPair) →
      ((∀ pq, (((hodgeDualityPairing B D d pq).restrictScalars₁₂ k k).compr₂ t').IsPerfPair) ↔
        ∃! u : (X.presheaf.obj (op ⊤))ˣ,
          t' = t ∘ₗ Algebra.lsmul k k (hodgeGroup B D d d) (u : X.presheaf.obj (op ⊤))) := by
  let : ∀ p i, Module k (hodgeGroup B D p i) := fun p i => hodgeGroupModuleOf B D k p i
  have : ∀ p i, IsScalarTower k (X.presheaf.obj (op ⊤)) (hodgeGroup B D p i) :=
    fun p i => hodgeGroup_isScalarTower B D k p i
  intro t t' ht
  refine LinearMap.isPerfPair_compr₂_iff_existsUnique_unit
    (fun pq => (hodgeDualityPairing B D d pq).restrictScalars₁₂ k k)
    (fun pq g a b => hodgeCup_smul_left B D g _ _ _ _ _ _ _ _ a b)
    (i₀ := ⟨(0, 0), Nat.zero_le d, Nat.zero_le d⟩)
    ((hodgeUnitEquiv B D).restrictScalars k) (LinearEquiv.refl k (hodgeGroup B D d d))
    (fun g v => ?_) t t' ht
  change hodgeCup B D 0 (d - 0) d _ 0 (d - 0) d _ (g • hodgeUnit B D) v = g • v
  rw [hodgeCup_smul_left, hodgeCup_hodgeUnit_eqToHom]
  rfl

end AlgebraicGeometry.SheafOfModules
