module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.SheafTensorPairing

/-!
# Restriction of scalars along a ring isomorphism is monoidal

For a ring homomorphism `ψ : A ⟶ B` the base-change map
`Stacks.Cech.SheafTensorPairing.baseChange` compares the tensor product over `A` of two
`B`-modules read as `A`-modules with their tensor product over `B` read the same way.  It is
always surjective, and this file proves that **for a ring isomorphism it is invertible**: the
inverse is the additive map `x ⊗_B y ↦ x ⊗_A y`, which is `A`-linear because the two scalar
actions correspond under the isomorphism.

The consequence used downstream is
`Stacks.ModuleCat.RingIsoTransport.restrictDirectSumTensorIso`: restriction of scalars along a
ring isomorphism carries a direct sum of tensor products to the direct sum of the tensor
products of the restrictions.  That is what lets a statement about modules over `Γ(Spec k, 𝒪)`
be read as one about `k`-vector spaces, the two rings being isomorphic but not equal.

## Main definitions

* `Stacks.ModuleCat.RingIsoTransport.invMap`: the inverse of base change along an isomorphism.
* `Stacks.ModuleCat.RingIsoTransport.baseChangeIso`: base change, packaged as an isomorphism.
* `Stacks.ModuleCat.RingIsoTransport.restrictDirectSumTensorIso`: the direct-sum form.

## Main results

* `Stacks.ModuleCat.RingIsoTransport.isIso_baseChange`: **base change along a ring isomorphism
  is invertible.**
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped DirectSum TensorProduct

universe u v

namespace Stacks.ModuleCat.RingIsoTransport

variable {A B : Type u} [CommRing A] [CommRing B] (E : A ≃+* B) (M N : ModuleCat.{u} B)

/-- An element of `M`, read in `M` with its scalars restricted along `E`. -/
def toRestricted (x : (M : Type u)) :
    ((ModuleCat.restrictScalars (E : A →+* B)).obj M : Type u) := x

/-- The `A`-action on `M` with its scalars restricted along `E` is the `B`-action along `E⁻¹`. -/
lemma toRestricted_smul (b : B) (x : (M : Type u)) :
    toRestricted E M (b • x) = (E.symm b) • toRestricted E M x := by
  rw [ModuleCat.restrictScalars.smul_def (E : A →+* B) (E.symm b) (toRestricted E M x)]
  change (b • x : (M : Type u)) = ((E : A →+* B) (E.symm b)) • (x : (M : Type u))
  simp

/-- The additive map `M ⊗_B N ⟶ M ⊗_A N` inverse to base change along an isomorphism. -/
def invAddHom : ((M : Type u) ⊗[B] (N : Type u)) →+
    (((ModuleCat.restrictScalars (E : A →+* B)).obj M) ⊗[A]
      ((ModuleCat.restrictScalars (E : A →+* B)).obj N)) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
        (fun y => TensorProduct.tmul A (toRestricted E M x) (toRestricted E N y))
        (fun y y' => TensorProduct.tmul_add _ _ _))
      (fun x x' => by
        refine AddMonoidHom.ext fun y => ?_
        exact TensorProduct.add_tmul (toRestricted E M x) (toRestricted E M x')
          (toRestricted E N y)))
    (fun b x y => by
      change TensorProduct.tmul A (toRestricted E M (b • x)) (toRestricted E N y) =
        TensorProduct.tmul A (toRestricted E M x) (toRestricted E N (b • y))
      rw [toRestricted_smul, toRestricted_smul, TensorProduct.smul_tmul])

/-- The inverse of base change takes a pure tensor over `B` to the same pure tensor over `A`. -/
@[simp]
lemma invAddHom_tmul (x : (M : Type u)) (y : (N : Type u)) :
    invAddHom E M N (x ⊗ₜ[B] y) =
      TensorProduct.tmul A (toRestricted E M x) (toRestricted E N y) := rfl

/-- The inverse of base change is `B`-semilinear along `E⁻¹`. -/
lemma invAddHom_smul (b : B) (z : (M : Type u) ⊗[B] (N : Type u)) :
    invAddHom E M N (b • z) = (E.symm b) • invAddHom E M N z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.smul_tmul', invAddHom_tmul, invAddHom_tmul, toRestricted_smul,
      TensorProduct.smul_tmul']
  | add z z' h h' => rw [smul_add, map_add, map_add, h, h', smul_add]

/-- The inverse of base change along a ring isomorphism, as a map of `A`-modules. -/
def invMap : (ModuleCat.restrictScalars (E : A →+* B)).obj (M ⊗ N) ⟶
      ModuleCat.of A (((ModuleCat.restrictScalars (E : A →+* B)).obj M) ⊗[A]
        ((ModuleCat.restrictScalars (E : A →+* B)).obj N)) :=
  ConcreteCategory.ofHom (C := ModuleCat A)
    { toFun := fun z => invAddHom E M N z
      map_add' := fun z z' => (invAddHom E M N).map_add z z'
      map_smul' := fun a z => by
        rw [ModuleCat.restrictScalars.smul_def (E : A →+* B) a z]
        rw [invAddHom_smul E M N ((E : A →+* B) a) z]
        rw [show (E.symm ((E : A →+* B) a)) = a from E.symm_apply_apply a]
        rfl }

/-- Base change undoes its inverse. -/
lemma baseChange_invAddHom (t : (M : Type u) ⊗[B] (N : Type u)) :
    ((Stacks.Cech.SheafTensorPairing.baseChange (E : A →+* B) M N).hom
      (invAddHom E M N t) : (M : Type u) ⊗[B] (N : Type u)) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add t t' h h' => rw [map_add, map_add, h, h']; rfl

/-- **Restriction of scalars along a ring isomorphism is monoidal.** -/
instance isIso_baseChange :
    IsIso (Stacks.Cech.SheafTensorPairing.baseChange (E : A →+* B) M N) :=
  ⟨invMap E M N,
    ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl),
    ModuleCat.hom_ext (LinearMap.ext fun t => baseChange_invAddHom E M N t)⟩

/-- Base change along a ring isomorphism, packaged as an isomorphism. -/
def baseChangeIso :
    ModuleCat.of A (((ModuleCat.restrictScalars (E : A →+* B)).obj M) ⊗[A]
        ((ModuleCat.restrictScalars (E : A →+* B)).obj N)) ≅
      (ModuleCat.restrictScalars (E : A →+* B)).obj (M ⊗ N) :=
  asIso (Stacks.Cech.SheafTensorPairing.baseChange (E : A →+* B) M N)

/-- **Restriction of scalars along a ring isomorphism commutes with a direct sum of tensor
products.** -/
def restrictDirectSumTensorIso {ι : Type v} (P Q : ι → ModuleCat.{u} B) :
    (ModuleCat.restrictScalars (E : A →+* B)).obj
        (ModuleCat.of B (⨁ i, TensorProduct B (P i) (Q i))) ≅
      ModuleCat.of A (⨁ i, TensorProduct A
        ((ModuleCat.restrictScalars (E : A →+* B)).obj (P i))
        ((ModuleCat.restrictScalars (E : A →+* B)).obj (Q i))) :=
  (DirectSum.congrLinearEquiv
    (fun i => (baseChangeIso E (P i) (Q i)).symm.toLinearEquiv)).toModuleIso

end Stacks.ModuleCat.RingIsoTransport

end
