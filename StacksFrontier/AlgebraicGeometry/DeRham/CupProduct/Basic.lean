module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.Algebra.Homology.ComplexShapeSignsNat
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedForms
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
import StacksCore.Tactic.StacksAttribute

/-!
# Wedge multiplication on the relative de Rham complex

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B` the
structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative differentials
and let `B` also denote a package of the three algebras of Stacks Section 17.21 for `Ω`. Wedging
differential forms,

`Ωᵖ × Ωᵠ → Ωᵖ⁺ᵠ,   (ω, η) ↦ ω ∧ η`,

is `A`-bilinear and obeys the graded Leibniz rule `d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, so it
assembles into a morphism of complexes of sheaves of `A`-modules

`∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•`

out of the total complex of the tensor-product bicomplex.

This file supplies the components of that morphism and the Leibniz rule they satisfy: the terms
`Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ` are `exteriorProductComponent`, the total complex is `tensorSquare`, and
`exteriorProductComponent_d` is the Leibniz identity, which is exactly the compatibility a family
of components must satisfy in order to descend to the total complex.

## Main definitions

* `Stacks.SheafOfModules.Tensor.sheafTensor`: the tensor product of sheaves of `A`-modules,
  curried into a bifunctor.
* `AlgebraicGeometry.SheafOfModules.tensorSquare`: the total complex of the tensor-product
  bicomplex of the relative de Rham complex with itself.
* `AlgebraicGeometry.SheafOfModules.exteriorProductComponent`: wedge multiplication as a single
  morphism `Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ` of sheaves of `A`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.tensorForms_hom_ext`: **two morphisms out of
  `Ωᵖ ⊗_A Ωᵠ` which agree on the pure tensors of multiples of exact wedges are equal.** This is
  the separation statement that makes the Leibniz rule checkable on generators.
* `AlgebraicGeometry.SheafOfModules.exteriorProductComponent_unit_apply`: the component computes
  the wedge product on a local pure tensor.
* `AlgebraicGeometry.SheafOfModules.exteriorProductComponent_d`: **the graded Leibniz rule for the
  components**, which is exactly the condition that they assemble into a morphism out of the total
  complex.

## Implementation notes

The total complex is indexed by `ℕ`, as is the de Rham complex, so the Koszul signs for
`ComplexShape.up ℕ` are needed; Mathlib provides them only for `ComplexShape.up ℤ`. The instance
`ComplexShape.TensorSigns (ComplexShape.up ℕ)` is of general interest and is supplied in
`StacksFrontier.Algebra.Homology.ComplexShapeSignsNat`.

The tensor product of two sheaves of `A`-modules is the sheafification of the tensor product of
the underlying presheaves (`Stacks.SheafOfModules.Tensor.sheafTensor`), so a morphism
out of it is given by a morphism out of the presheaf tensor product
(`AlgebraicGeometry.SheafOfModules.exteriorProductPresheafMap`) and is determined by its values on
the sheafification-unit images of local pure tensors. Additivity of the tensor bifunctor in each
variable is needed for the total complex to exist, and is proved from
`CategoryTheory.MonoidalPreadditive` for presheaves of modules together with additivity of
sheafification; the latter is read off the sheafification adjunction.

The de Rham differential is a hypothesis rather than
`AlgebraicGeometry.SheafOfModules.deRhamDifferential`: everything here holds for an arbitrary one,
and there is only one (`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq`).

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- The objectwise tensor product of presheaves of modules is additive in each variable. -/
private theorem presheafOfModulesMonoidalPreadditive {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MonoidalPreadditive (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) := by
  constructor <;> (repeat intro) <;> exact PresheafOfModules.hom_ext fun U =>
    ModuleCat.MonoidalCategory.tensor_ext (by intro x y; simp; rfl)

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### Additivity of the tensor product of sheaves of modules -/

/-- Sheafification of presheaves of `A`-modules is additive: it is a left adjoint, hence preserves
binary coproducts, hence binary biproducts. -/
theorem moduleSheafification_additive (A : TopCat.Sheaf CommRingCat.{u} X.carrier) :
    (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).Additive := by
  let F := PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)
  let _ : F.IsLeftAdjoint := by
    dsimp only [F]
    infer_instance
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  let _ : Limits.PreservesBinaryBiproducts F :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

/-- The tensor product bifunctor on sheaves of modules over a sheaf of commutative rings is
additive. -/
instance tensorFunctor_additive {space : TopCat.{u}}
    (coefficients : TopCat.Sheaf CommRingCat.{u} space) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients :
      _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
        _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
          _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive coefficients

/-- Tensoring with a fixed sheaf of modules `moduleSheaf` is an additive functor. -/
instance tensorFunctor_obj_additive {space : TopCat.{u}}
    (coefficients : TopCat.Sheaf CommRingCat.{u} space)
    (moduleSheaf : _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients).obj moduleSheaf :
      _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
        _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive coefficients moduleSheaf

/-- The tensor product bifunctor on sheaves of modules preserves zero morphisms, for any choice
of zero morphisms on the source and target categories. -/
instance tensorFunctor_preservesZeroMorphisms {space : TopCat.{u}}
    (coefficients : TopCat.Sheaf CommRingCat.{u} space)
    (sourceZero : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients)))
    (targetZero : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
        _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))) :
    @Functor.PreservesZeroMorphisms _ _ _ _ sourceZero targetZero
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients) := by
  have source_eq : sourceZero = (Preadditive.preadditiveHasZeroMorphisms : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))) := Subsingleton.elim _ _
  have target_eq : targetZero = (Preadditive.preadditiveHasZeroMorphisms : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
        _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))) := Subsingleton.elim _ _
  cases source_eq
  cases target_eq
  exact Functor.preservesZeroMorphisms_of_additive
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients :
      _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
        _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
          _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))

/-- Tensoring with a fixed sheaf of modules preserves zero morphisms, for any choice of zero
morphisms on the source and target categories. -/
instance tensorFunctor_obj_preservesZeroMorphisms {space : TopCat.{u}}
    (coefficients : TopCat.Sheaf CommRingCat.{u} space)
    (moduleSheaf : _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))
    (sourceZero targetZero : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))) :
    @Functor.PreservesZeroMorphisms _ _ _ _ sourceZero targetZero
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients).obj
        moduleSheaf) := by
  have source_eq : sourceZero = (Preadditive.preadditiveHasZeroMorphisms : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))) := Subsingleton.elim _ _
  have target_eq : targetZero = (Preadditive.preadditiveHasZeroMorphisms : Limits.HasZeroMorphisms
      (_root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))) := Subsingleton.elim _ _
  cases source_eq
  cases target_eq
  exact Functor.preservesZeroMorphisms_of_additive
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} coefficients).obj moduleSheaf :
      _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients) ⥤
        _root_.SheafOfModules.{u} (underlyingRingSheaf coefficients))

/-- The local sections of `⋀ᵖ Ω` over an open set, as a module over the sections of `A`: the
restriction of scalars along `φ`, recorded at the spelling of the ring of sections that the
monoidal structure on presheaves of `A`-modules uses. -/
noncomputable instance exteriorPowerSectionsModule (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) :
    Module ((A.obj ⋙ forget₂ CommRingCat RingCat).obj U) ((B.exteriorPower p).val.obj U) :=
  ((deRhamTerm B p).val.obj U).isModule

/-! ### Separation on pure tensors of multiples of exact wedges -/

/-- **Two morphisms out of `Ωᵖ ⊗_A Ωᵠ`, read on the underlying presheaves, which agree on the pure
tensors `(a · ω) ⊗ (b · η)` with `ω` and `η` exact wedges, are equal.**

The exact wedges generate `⋀ᵖ Ω` locally in each variable
(`AlgebraicGeometry.SheafOfModules.exteriorPower_induction`), and the common target is a sheaf, so
agreement on a covering family suffices. -/
theorem tensorForms_hom_ext (p q : ℕ)
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    (f g : PresheafOfModules.tensorObj (O := A.obj)
      (deRhamTerm B p).val (deRhamTerm B q).val ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj N.val)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U)
      (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U),
      IsExactWedge B U p ω → IsExactWedge B U q η →
      f.app U ((a • ω) ⊗ₜ[A.obj.obj U] (b • η)) =
        g.app U ((a • ω) ⊗ₜ[A.obj.obj U] (b • η))) : f = g := by
  have nat (k : PresheafOfModules.tensorObj (O := A.obj)
      (deRhamTerm B p).val (deRhamTerm B q).val ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj N.val)
      {U V : (Opens X.carrier)ᵒᵖ} (r : U ⟶ V) (x : (B.exteriorPower p).val.obj U)
      (y : (B.exteriorPower q).val.obj U) :
      N.val.map r (k.app U (x ⊗ₜ[A.obj.obj U] y)) =
        k.app V ((B.exteriorPower p).val.map r x ⊗ₜ[A.obj.obj V]
          (B.exteriorPower q).val.map r y) :=
    (PresheafOfModules.naturality_apply k r (x ⊗ₜ[A.obj.obj U] y)).symm
  refine PresheafOfModules.hom_ext fun U => ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  refine exteriorPower_induction B p
    (fun V x => ∀ y : (B.exteriorPower q).val.obj V,
      f.app V (x ⊗ₜ[A.obj.obj V] y) = g.app V (x ⊗ₜ[A.obj.obj V] y)) ?_ ?_ ?_ ?_ ?_ U x y
  · intro V y
    erw [TensorProduct.zero_tmul]
    exact (map_zero _).trans (map_zero _).symm
  · intro V x z hx hz y
    erw [TensorProduct.add_tmul]
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) (hx y) (hz y)).trans (map_add _ _ _).symm)
  · intro V x hx y
    erw [TensorProduct.neg_tmul]
    exact (map_neg _ _).trans ((congrArg Neg.neg (hx y)).trans (map_neg _ _).symm)
  · intro V x S hS hx y
    refine N.isSheaf.isSeparated _ _ hS _ _ fun W r hr => ?_
    change N.val.map r.op _ = N.val.map r.op _
    exact (nat f r.op x y).trans ((hx W r hr _).trans (nat g r.op x y).symm)
  · intro V a x hx y
    have hy : ∀ r : V ⟶ V,
        f.app V ((B.exteriorPower p).val.map r (a • x) ⊗ₜ[A.obj.obj V] y) =
          g.app V ((B.exteriorPower p).val.map r (a • x) ⊗ₜ[A.obj.obj V] y) := by
      refine exteriorPower_induction B q
        (fun W y => ∀ r : V ⟶ W,
          f.app W ((B.exteriorPower p).val.map r (a • x) ⊗ₜ[A.obj.obj W] y) =
            g.app W ((B.exteriorPower p).val.map r (a • x) ⊗ₜ[A.obj.obj W] y)) ?_ ?_ ?_ ?_ ?_ V y
      · intro W r
        erw [TensorProduct.tmul_zero]
        exact (map_zero _).trans (map_zero _).symm
      · intro W y z hy hz r
        erw [TensorProduct.tmul_add]
        exact (map_add _ _ _).trans ((congrArg₂ (· + ·) (hy r) (hz r)).trans (map_add _ _ _).symm)
      · intro W y hy r
        erw [TensorProduct.tmul_neg]
        exact (map_neg _ _).trans ((congrArg Neg.neg (hy r)).trans (map_neg _ _).symm)
      · intro W y S hS hy r
        refine N.isSheaf.isSeparated _ _ hS _ _ fun Z t ht => ?_
        change N.val.map t.op _ = N.val.map t.op _
        refine (nat f t.op _ y).trans (Eq.trans ?_ (nat g t.op _ y).symm)
        have hc : (B.exteriorPower p).val.map t.op
            ((B.exteriorPower p).val.map r (a • x)) =
            (B.exteriorPower p).val.map (r ≫ t.op) (a • x) :=
          ((B.exteriorPower p).val.map_comp_apply r t.op (a • x)).symm
        refine (congrArg (fun w => ConcreteCategory.hom (f.app (op Z))
          (w ⊗ₜ[A.obj.obj (op Z)] (B.exteriorPower q).val.map t.op y)) hc).trans ?_
        refine (hy Z t ht (r ≫ t.op)).trans ?_
        exact (congrArg (fun w => ConcreteCategory.hom (g.app (op Z))
          (w ⊗ₜ[A.obj.obj (op Z)] (B.exteriorPower q).val.map t.op y)) hc).symm
      · intro W b y hy r
        have hs : (B.exteriorPower p).val.map r (a • x) =
            X.sheaf.obj.map r a • (B.exteriorPower p).val.map r x :=
          (B.exteriorPower p).val.map_smul r a x
        refine (congrArg (fun w => ConcreteCategory.hom (f.app W)
          (w ⊗ₜ[A.obj.obj W] (b • y))) hs).trans ?_
        refine (h W _ b _ y (isExactWedge_map B p r x hx) hy).trans ?_
        exact (congrArg (fun w => ConcreteCategory.hom (g.app W)
          (w ⊗ₜ[A.obj.obj W] (b • y))) hs).symm
    have hi : (B.exteriorPower p).val.map (𝟙 V) (a • x) = a • x :=
      (ConcreteCategory.congr_hom ((B.exteriorPower p).val.presheaf.map_id V) (a • x)).trans rfl
    refine Eq.trans (congrArg (fun w => ConcreteCategory.hom (f.app V)
      (w ⊗ₜ[A.obj.obj V] y)) hi).symm ?_
    refine (hy (𝟙 V)).trans ?_
    exact congrArg (fun w => ConcreteCategory.hom (g.app V) (w ⊗ₜ[A.obj.obj V] y)) hi

/-! ### The components of the wedge product -/

/-- Wedge multiplication of a `p`-form by a `q`-form, as a morphism out of the tensor product of
the underlying **presheaves** of `A`-modules. -/
noncomputable def exteriorProductPresheafMap (p q : ℕ) :
    PresheafOfModules.tensorObj (O := A.obj) (deRhamTerm B p).val (deRhamTerm B q).val ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj
        (deRhamTerm B (p + q)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun x y => (B.exterior.mul (p : ℤ) (q : ℤ)).app U x y)
    (by
      intro x x' y
      exact congrArg (fun k : (B.exteriorPower q).val.obj U →+ _ => k y)
        (((B.exterior.mul (p : ℤ) (q : ℤ)).app U).map_add x x'))
    (by
      intro r x y
      exact (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_left U (φ.hom.app U r) x y)
    (by
      intro x y y'
      exact ((B.exterior.mul (p : ℤ) (q : ℤ)).app U x).map_add y y')
    (by
      intro r x y
      exact (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_right U (φ.hom.app U r) x y)
  naturality {U V} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
    exact ((B.exterior.mul (p : ℤ) (q : ℤ)).naturality f x y).symm

/-- **Wedge multiplication `Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ`**, as a morphism of sheaves of `A`-modules: the
descent of `AlgebraicGeometry.SheafOfModules.exteriorProductPresheafMap` along the sheafification
that defines the tensor product of sheaves of modules. -/
noncomputable def exteriorProductComponent (p q : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj (deRhamTerm B p)).obj
      (deRhamTerm B q) ⟶ deRhamTerm B (p + q) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).symm
      (exteriorProductPresheafMap B p q)

/-- The component computes the wedge product on a local pure tensor. -/
theorem exteriorProductComponent_unit_apply (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower p).val.obj U) (y : (B.exteriorPower q).val.obj U) :
    (exteriorProductComponent B p q).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B q).val)).app U (x
            ⊗ₜ[A.obj.obj U] y)) =
      formProduct B p q U x y :=
  lift_unit_apply (Opens.grothendieckTopology X.carrier)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)
    (PresheafOfModules.tensorObj (O := A.obj) (deRhamTerm B p).val (deRhamTerm B q).val)
    (deRhamTerm B (p + q))
    (exteriorProductPresheafMap B p q) U (x ⊗ₜ[A.obj.obj U] y)

/-! ### The Leibniz rule for the components -/

variable (D : DeRhamDifferential B)

/-- The tensor product of sheaves of modules, read on the sheafification unit of a pure tensor, in
the first variable. -/
theorem tensorFunctor_map_unit_apply
    {M M' N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (f : M ⟶ M') (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    Eq
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map f).app N).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj M.val N.val)).app U
          (x ⊗ₜ[A.obj.obj U] y)))
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj M'.val N.val)).app U
        (f.val.app U x ⊗ₜ[A.obj.obj U] y)) :=
  PresheafOfModules.unit_naturality_apply
    (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)
    (PresheafOfModules.tensorHom f.val (𝟙 N.val)) U (x ⊗ₜ[A.obj.obj U] y)

/-- The tensor product of sheaves of modules, read on the sheafification unit of a pure tensor, in
the second variable. -/
theorem tensorFunctor_obj_map_unit_apply
    {M N N' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (f : N ⟶ N')
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    Eq
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj M).map f).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj M.val N.val)).app U
          (x ⊗ₜ[A.obj.obj U] y)))
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj M.val N'.val)).app U
        (x ⊗ₜ[A.obj.obj U] f.val.app U y)) :=
  PresheafOfModules.unit_naturality_apply
    (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)
    (PresheafOfModules.tensorHom (𝟙 M.val) f.val) U (x ⊗ₜ[A.obj.obj U] y)

/-- Reindexing a term of the de Rham complex does not change the image of a local section in the
ring of all local sections. -/
theorem ofGradedForm_XIsoOfEq {p q : ℕ} (h : p = q) (U : (Opens X.carrier)ᵒᵖ)
    (x : (deRhamTerm B p).val.obj U) :
    ofGradedForm B U (q : ℤ) (((deRhamComplex B D).XIsoOfEq h).hom.val.app U x) =
      ofGradedForm B U (p : ℤ) x := by
  subst q
  rfl

/-- The sheafification homomorphism equivalence, read on the unit image of a local section. -/
theorem sheafificationHomEquiv_apply
    {M : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj}
    {N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (f : (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj M ⟶ N)
    (U : (Opens X.carrier)ᵒᵖ) (x : M.obj U) :
    (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj) f).app U x =
      f.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).unit.app M).app U x) :=
  rfl

/-- Evaluating a morphism of sheaves of modules on a fixed local section is additive in the
morphism. -/
private def sheafHomEval
    {M N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A)}
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) : (M ⟶ N) →+ N.val.obj U where
  toFun f := f.val.app U x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The graded Leibniz rule for the components of the wedge product.** -/
theorem exteriorProductComponent_d (p q : ℕ) :
    exteriorProductComponent B p q ≫ (deRhamComplex B D).d (p + q) (p + q + 1) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map
        ((deRhamComplex B D).d p (p + 1))).app
          ((deRhamComplex B D).X q) ≫
        exteriorProductComponent B (p + 1) q ≫
          ((deRhamComplex B D).XIsoOfEq (show p + 1 + q = p + q + 1 by omega)).hom +
      (-1 : ℤ) ^ p • (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj
            ((deRhamComplex B D).X p)).map ((deRhamComplex B D).d q (q + 1)) ≫
            exteriorProductComponent B p (q + 1) ≫
              ((deRhamComplex B D).XIsoOfEq
                (show p + (q + 1) = p + q + 1 by omega)).hom) := by
  have hp₁ : p + 1 + q = p + q + 1 := by omega
  have hp₂ : p + (q + 1) = p + q + 1 := by omega
  refine (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).injective ?_
  refine tensorForms_hom_ext B p q ((deRhamComplex B D).X (p + q + 1)) _ _ ?_
  intro U a b ω η hω hη
  refine (sheafificationHomEquiv_apply _ U _).trans
    (Eq.trans ?_ (sheafificationHomEquiv_apply _ U _).symm)
  change sheafHomEval (N := (deRhamComplex B D).X (p + q + 1)) U _
      (exteriorProductComponent B p q ≫ (deRhamComplex B D).d (p + q) (p + q + 1)) =
    sheafHomEval
      (M := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj
        ((deRhamComplex B D).X p)).obj ((deRhamComplex B D).X q))
      (N := (deRhamComplex B D).X (p + q + 1)) U _
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map
            ((deRhamComplex B D).d p (p + 1))).app ((deRhamComplex B D).X q) ≫
            exteriorProductComponent B (p + 1) q ≫ ((deRhamComplex B D).XIsoOfEq hp₁).hom +
          (-1 : ℤ) ^ p •
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj
              ((deRhamComplex B D).X p)).map ((deRhamComplex B D).d q (q + 1)) ≫
              exteriorProductComponent B p (q + 1) ≫ ((deRhamComplex B D).XIsoOfEq hp₂).hom))
  rw [map_add, map_zsmul]
  change ((deRhamComplex B D).d (p + q) (p + q + 1)).val.app U
      ((exteriorProductComponent B p q).val.app U _) =
    ((deRhamComplex B D).XIsoOfEq hp₁).hom.val.app U
        ((exteriorProductComponent B (p + 1) q).val.app U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map
            ((deRhamComplex B D).d p (p + 1))).app
            ((deRhamComplex B D).X q)).val.app U _)) +
      (-1 : ℤ) ^ p • ((deRhamComplex B D).XIsoOfEq hp₂).hom.val.app U
        ((exteriorProductComponent B p (q + 1)).val.app U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj
            ((deRhamComplex B D).X p)).map
            ((deRhamComplex B D).d q (q + 1))).val.app U _))
  have e0 := exteriorProductComponent_unit_apply B p q U (a • ω) (b • η)
  have e1 := (congrArg (fun z => (exteriorProductComponent B (p + 1) q).val.app U z)
      (tensorFunctor_map_unit_apply (N := (deRhamComplex B D).X q)
        ((deRhamComplex B D).d p (p + 1)) U (a • ω) (b • η))).trans
    (exteriorProductComponent_unit_apply B (p + 1) q U
      (((deRhamComplex B D).d p (p + 1)).val.app U (a • ω)) (b • η))
  have e2 := (congrArg (fun z => (exteriorProductComponent B p (q + 1)).val.app U z)
      (tensorFunctor_obj_map_unit_apply (M := (deRhamComplex B D).X p)
        ((deRhamComplex B D).d q (q + 1)) U (a • ω) (b • η))).trans
    (exteriorProductComponent_unit_apply B p (q + 1) U (a • ω)
      (((deRhamComplex B D).d q (q + 1)).val.app U (b • η)))
  refine (congrArg (fun z => ((deRhamComplex B D).d (p + q) (p + q + 1)).val.app U z) e0).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· + ·)
    (congrArg (fun z => ((deRhamComplex B D).XIsoOfEq hp₁).hom.val.app U z) e1)
    (congrArg (fun z => (-1 : ℤ) ^ p •
      ((deRhamComplex B D).XIsoOfEq hp₂).hom.val.app U z) e2)).symm
  refine DirectSum.of_injective (β := gradedForms B U) ((p + q + 1 : ℕ) : ℤ) ?_
  change localDifferential B D (p + q) U (formProduct B p q U (a • ω) (b • η)) = _
  refine (localLeibniz_smul_exactWedge B D p q U a b ω η hω hη).trans (Eq.trans ?_
    (map_add (ofGradedForm B U ((p + q + 1 : ℕ) : ℤ)) _ _).symm)
  refine congrArg₂ (· + ·) ?_ ?_
  · exact (ofGradedForm_mul B U ((p + 1 : ℕ) : ℤ) (q : ℤ)
      (((deRhamComplex B D).d p (p + 1)).val.app U (a • ω)) (b • η)).symm.trans
      (ofGradedForm_XIsoOfEq B D hp₁ U _).symm
  · refine Eq.trans ?_ (map_zsmul (ofGradedForm B U ((p + q + 1 : ℕ) : ℤ)) _ _).symm
    refine congrArg (fun z : totalForms B U => (-1 : ℤ) ^ p • z) ?_
    exact (ofGradedForm_mul B U (p : ℤ) ((q + 1 : ℕ) : ℤ) (a • ω)
      (((deRhamComplex B D).d q (q + 1)).val.app U (b • η))).symm.trans
      (ofGradedForm_XIsoOfEq B D hp₂ U _).symm

/-! ### The wedge product -/

/-- The total complex of the tensor-product bicomplex of the relative de Rham complex with
itself: `Tot(Ω^• ⊗_A Ω^•)`. -/
noncomputable abbrev tensorSquare :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  @HomologicalComplex.mapBifunctor
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    _ _ _ ℕ ℕ ℕ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    Preadditive.preadditiveHasZeroMorphisms Preadditive.preadditiveHasZeroMorphisms
    (SheafOfModules.instPreadditive (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    (deRhamComplex B D) (deRhamComplex B D)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
    (Functor.preservesZeroMorphisms_of_additive _)
    (fun _ => Functor.preservesZeroMorphisms_of_additive _)
    (ComplexShape.up ℕ) inferInstance inferInstance inferInstance

end AlgebraicGeometry.SheafOfModules

end
