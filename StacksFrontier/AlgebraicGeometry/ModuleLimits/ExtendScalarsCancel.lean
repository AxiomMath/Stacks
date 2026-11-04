module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Cancelling an intermediate ring in a composite extension of scalars

For ring maps `a : A →+* B` and `b : B →+* R` this file provides the comparison
`R ⊗[B] (B ⊗[A] P) ≅ R ⊗[A] P` between the iterated and the composite extension of scalars
`ModuleCat.extendScalars`, its naturality in `P`, and the computation of its components on the
elements `1 ⊗ₜ y`.

## Main definitions

* `Stacks.ModuleCat.cancelIsoApp`: the comparison, one module at a time.
* `Stacks.ModuleCat.cancelIso`: the comparison, as a natural isomorphism of functors.

## Main results

* `Stacks.ModuleCat.cancelIsoApp_hom_one_tmul`: the comparison sends `1 ⊗ₜ y` to the image of `y`
  under the canonical map induced by `b`.
* `Stacks.ModuleCat.extendScalars_map_comp_cancelIsoApp`: a map descended along the canonical maps
  is a map of the comparisons.
-/

@[expose] public section

open CategoryTheory TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.ModuleCat

variable {A B R : Type u} [CommRing A] [CommRing B] [CommRing R] (a : A →+* B) (b : B →+* R)
  (p : A →+* R) (hp : ∀ x, p x = b (a x))

/-- The comparison `R ⊗[B] (B ⊗[A] P) ≅ R ⊗[A] P` between the extension of scalars of `P` along
`a : A →+* B` followed by `b : B →+* R` and its extension of scalars along a ring map
`p : A →+* R` agreeing with the composite of `a` and `b`. -/
noncomputable def cancelIsoApp (P : ModuleCat.{u} A) :
    (ModuleCat.extendScalars b).obj ((ModuleCat.extendScalars a).obj P) ≅
      (ModuleCat.extendScalars p).obj P :=
  let _ : Algebra A B := a.toAlgebra
  let _ : Algebra B R := b.toAlgebra
  let _ : Algebra A R := p.toAlgebra
  let _ : IsScalarTower A B R := IsScalarTower.of_algebraMap_eq hp
  LinearEquiv.toModuleIso (AlgebraTensorModule.cancelBaseChange A B R R P)

/-- The comparison `Stacks.ModuleCat.cancelIsoApp` is natural in the module. -/
lemma cancelIsoApp_naturality {P Q : ModuleCat.{u} A} (v : P ⟶ Q) :
    (ModuleCat.extendScalars b).map ((ModuleCat.extendScalars a).map v) ≫
        (cancelIsoApp a b p hp Q).hom
      = (cancelIsoApp a b p hp P).hom ≫ (ModuleCat.extendScalars p).map v := by
  let _ : Algebra A B := a.toAlgebra
  let _ : Algebra B R := b.toAlgebra
  let _ : Algebra A R := p.toAlgebra
  let _ : IsScalarTower A B R := IsScalarTower.of_algebraMap_eq hp
  exact ModuleCat.hom_ext
    (AlgebraTensorModule.lTensor_comp_cancelBaseChange (M := R) A B R v.hom).symm

/-- The comparison `R ⊗[B] (B ⊗[A] -) ≅ R ⊗[A] -` as a natural isomorphism. -/
noncomputable def cancelIso :
    ModuleCat.extendScalars a ⋙ ModuleCat.extendScalars b ≅ ModuleCat.extendScalars p :=
  NatIso.ofComponents (cancelIsoApp a b p hp) (fun v => cancelIsoApp_naturality a b p hp v)

/-- The components of `Stacks.ModuleCat.cancelIso` are the comparisons
`Stacks.ModuleCat.cancelIsoApp`. -/
@[simp]
lemma cancelIso_hom_app (P : ModuleCat.{u} A) :
    (cancelIso a b p hp).hom.app P = (cancelIsoApp a b p hp P).hom := rfl

/-- `TensorProduct.AlgebraTensorModule.cancelBaseChange` on the elements `1 ⊗ₜ y`, in plain
tensor-product language. -/
lemma cancelBaseChange_one_tmul {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra B R] [Algebra A R] [IsScalarTower A B R]
    (P : Type u) [AddCommGroup P] [Module A P] (y : B ⊗[A] P) :
    AlgebraTensorModule.cancelBaseChange A B R R P ((1 : R) ⊗ₜ[B] y)
      = LinearMap.rTensor P (IsScalarTower.toAlgHom A B R).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β p => simp [Algebra.smul_def]
  | add y z hy hz => simp [TensorProduct.tmul_add, hy, hz]

/-- The comparison sends `1 ⊗ₜ y` to the image of `y` under the map `B ⊗[A] P → R ⊗[A] P`
induced by an `A`-algebra map `f : B →ₐ[A] R` agreeing with `b`. -/
lemma cancelIsoApp_hom_one_tmul (P : ModuleCat.{u} A)
    (f : letI : Algebra A B := a.toAlgebra
         letI : Algebra A R := p.toAlgebra
         B →ₐ[A] R)
    (hf : ∀ β : B, f β = b β) (y : (ModuleCat.extendScalars a).obj P) :
    letI : Algebra A B := a.toAlgebra
    letI : Algebra A R := p.toAlgebra
    (cancelIsoApp a b p hp P).hom ((1 : R) ⊗ₜ[B,b] y)
      = LinearMap.rTensor (↑P) f.toLinearMap y := by
  let _ : Algebra A B := a.toAlgebra
  let _ : Algebra B R := b.toAlgebra
  let _ : Algebra A R := p.toAlgebra
  let _ : IsScalarTower A B R := IsScalarTower.of_algebraMap_eq hp
  have hfeq : f.toLinearMap = (IsScalarTower.toAlgHom A B R).toLinearMap :=
    LinearMap.ext fun β => hf β
  rw [hfeq]
  show AlgebraTensorModule.cancelBaseChange A B R R (↑P) ((1 : R) ⊗ₜ[B] y) = _
  exact cancelBaseChange_one_tmul (A := A) (B := B) (R := R) (↑P) y

/-- A map between the base changes to `R` that is the base change along `b` of a map between the
base changes to `B` is, through the comparison, the image of that map under extension of scalars
along `b`. -/
lemma extendScalars_map_comp_cancelIsoApp (M N : ModuleCat.{u} A)
    (f : letI : Algebra A B := a.toAlgebra
         letI : Algebra A R := p.toAlgebra
         B →ₐ[A] R)
    (hf : ∀ β : B, f β = b β)
    (u : (ModuleCat.extendScalars p).obj M ⟶ (ModuleCat.extendScalars p).obj N)
    (ul : (ModuleCat.extendScalars a).obj M ⟶ (ModuleCat.extendScalars a).obj N)
    (hul : letI : Algebra A B := a.toAlgebra
           letI : Algebra A R := p.toAlgebra
           ∀ y : (ModuleCat.extendScalars a).obj M,
             u (LinearMap.rTensor (↑M) f.toLinearMap y)
               = LinearMap.rTensor (↑N) f.toLinearMap (ul y)) :
    (ModuleCat.extendScalars b).map ul ≫ (cancelIsoApp a b p hp N).hom
      = (cancelIsoApp a b p hp M).hom ≫ u := by
  let _ : Algebra A B := a.toAlgebra
  let _ : Algebra A R := p.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro y
  show (cancelIsoApp a b p hp N).hom ((ModuleCat.extendScalars b).map ul ((1 : R) ⊗ₜ[B,b] y))
    = u ((cancelIsoApp a b p hp M).hom ((1 : R) ⊗ₜ[B,b] y))
  rw [ModuleCat.ExtendScalars.map_tmul]
  exact ((cancelIsoApp_hom_one_tmul a b p hp N f hf _).trans (hul y).symm).trans
    (congrArg _ (cancelIsoApp_hom_one_tmul a b p hp M f hf y).symm)

end Stacks.ModuleCat

end
