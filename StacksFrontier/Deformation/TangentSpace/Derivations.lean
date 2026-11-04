module

public import Mathlib.Algebra.Module.TransferInstance
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.Deformation.TangentSpace.SquareZero

/-!
# The tangent space of a prorepresentable functor is a space of derivations (Stacks 06IC)

Let `S` be a Noetherian complete local `Λ`-algebra with residue field `k`. The tangent
space of the functor prorepresented by `S` — that is, the value of `restrictedCoyoneda S`
on the dual numbers `k[ε]` — is canonically the `k`-vector space of `Λ`-derivations
`S → k`, where `S` acts on `k` through its augmentation.

A morphism `S ⟶ k[ε]` of complete local algebras is exactly an augmentation-compatible
`Λ`-algebra map, i.e. a square-zero point of `S`, and Tag 06IC's square-zero-point
description identifies those with derivations. The only work here is bookkeeping: the dual
numbers of Tag 06IB are modelled on `ULift k` so that their carrier universe can contain
both the carrier of `S` and the residue field independently, so the derivation module has
to be transported along `ULift.moduleEquiv`, and the two `Λ`- and `S`-module structures on
`ULift k` coming from `Module.compHom` have to be identified with the ones `ULift.module'`
provides.

The resulting bijection is used to transport the additive and `k`-linear structures onto
the tangent space, which is how the tangent space of a prorepresentable functor becomes a
`k`-vector space.

## Main results

* `Deformation.dualNumberDerivationsEquiv`: the underlying bijection.
* `Deformation.tangentSpaceDerivationsLinearEquiv`: **Stacks 06IC**, the `k`-linear
  identification of the tangent space with the derivations.
* `Deformation.tangentSpaceDerivationsLinearEquiv_apply` and
  `Deformation.tangentSpaceDerivationsLinearEquiv_precomp`: its value on a tangent vector,
  and its compatibility with precomposition in the representing algebra.
* `Deformation.tangentSpace_finiteDimensional`: **Stacks 06IC**, the tangent space is
  finite-dimensional when `Λ → k` is finite, which is the chapter's standing assumption.
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The tangent space of the functor prorepresented by `S` is in bijection with the
`Λ`-derivations from `S` to its residue field. -/
@[sga "3 VIIA 1.2.1" "special case"]
noncomputable def dualNumberDerivationsEquiv
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceArtinian Λ k (restrictedCoyoneda S) ≃ Derivation Λ S k := by
  letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
  letI : IsScalarTower Λ S k :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [show algebraMap Λ S r • x = residueHom S (algebraMap Λ S r) * x from rfl,
        (residueHom S).commutes]
      exact (Algebra.smul_def r x).symm
  let A := artinianToComplete.obj (artinianDualNumbers Λ k)
  let mΛ : Module Λ (ULift.{v} k) := Module.compHom (ULift.{v} k) (algebraMap Λ k)
  let mS : Module S (ULift.{v} k) :=
    Module.compHom (ULift.{v} k) (residueHom S).toRingHom
  let nΛ : Module Λ (ULift.{v} k) := ULift.module'
  let nS : Module S (ULift.{v} k) := ULift.module'
  have hΛmod : mΛ = nΛ :=
    Module.ext' _ _ fun r x ↦ ULift.ext _ _ (Algebra.smul_def r x.down).symm
  have hSmod : mS = nS := Module.ext' _ _ fun _ _ ↦ rfl
  have htype : Derivations S (ULift.{v} k) = Derivation Λ S (ULift.{v} k) :=
    congrArg₂ (@Derivation Λ S (ULift.{v} k) _ _ _ _) hSmod hΛmod
  exact (squareZeroPointsDerivationsEquivHom S A (ULift.{v} k) (RingEquiv.refl _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)).trans
    ((Equiv.cast htype).trans (ULift.moduleEquiv : ULift.{v} k ≃ₗ[S] k).compDer.toEquiv)

/-- The canonical additive structure on the tangent space of the functor represented
by `S`. -/
noncomputable instance tangentSpaceAddCommGroup
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    AddCommGroup (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) :=
  (dualNumberDerivationsEquiv S).addCommGroup

/-- The canonical `k`-module structure on the tangent space of the functor represented
by `S`. -/
noncomputable instance tangentSpaceModule
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    Module k (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) :=
  ((dualNumberDerivationsEquiv S).addEquiv).module k

/-- **Stacks Project, Tag 06IC.** The tangent space of the functor represented by `S`
is canonically linearly equivalent to the `Λ`-derivations from `S` to its residue field. -/
@[stacks 06IC "tangent_space_derivations"]
noncomputable def tangentSpaceDerivationsLinearEquiv
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceArtinian Λ k (restrictedCoyoneda S) ≃ₗ[k] Derivation Λ S k :=
  letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
  (dualNumberDerivationsEquiv S).addEquiv.linearEquiv k

/-- Transporting a derivation along equalities of its two module structures does not
change its values. -/
private theorem cast_derivation_module_apply
    {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
    [Algebra R A] (mA nA : Module A M) (mR nR : Module R M)
    (hA : mA = nA) (hR : mR = nR)
    (D : @Derivation R A M _ _ _ _ mA mR) (a : A) :
    (cast (by rw [hA, hR] :
      @Derivation R A M _ _ _ _ mA mR = @Derivation R A M _ _ _ _ nA nR) D) a = D a := by
  subst nA
  subst nR
  rfl

/-- A tangent vector corresponds to the downlifted square-zero component. -/
@[stacks 06IC "tangent_space_derivations"]
theorem tangentSpaceDerivationsLinearEquiv_apply
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (f : tangentSpaceArtinian Λ k (restrictedCoyoneda S)) (s : S) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    tangentSpaceDerivationsLinearEquiv S f s = (f.hom s).snd.down := by
  let : Algebra S k := (residueHom S).toRingHom.toAlgebra
  let : IsScalarTower Λ S k :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [show algebraMap Λ S r • x = residueHom S (algebraMap Λ S r) * x from rfl,
        (residueHom S).commutes]
      exact (Algebra.smul_def r x).symm
  let A := artinianToComplete.obj (artinianDualNumbers Λ k)
  let mΛ : Module Λ (ULift.{v} k) := Module.compHom (ULift.{v} k) (algebraMap Λ k)
  let mS : Module S (ULift.{v} k) :=
    Module.compHom (ULift.{v} k) (residueHom S).toRingHom
  let nΛ : Module Λ (ULift.{v} k) := ULift.module'
  let nS : Module S (ULift.{v} k) := ULift.module'
  have hΛmod : mΛ = nΛ :=
    Module.ext' _ _ fun r x ↦ ULift.ext _ _ (Algebra.smul_def r x.down).symm
  have hSmod : mS = nS := Module.ext' _ _ fun _ _ ↦ rfl
  have htype : Derivations S (ULift.{v} k) = Derivation Λ S (ULift.{v} k) :=
    congrArg₂ (@Derivation Λ S (ULift.{v} k) _ _ _ _) hSmod hΛmod
  let E := squareZeroPointsDerivationsEquivHom S A (ULift.{v} k) (RingEquiv.refl _)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  show ((cast htype (E f)) s).down = _
  rw [cast_derivation_module_apply mS nS mΛ nΛ hSmod hΛmod (E f) s]
  exact congrArg ULift.down
    (squareZeroPointsDerivationsEquivHom_apply S A (ULift.{v} k) (RingEquiv.refl _)
      (fun _ ↦ rfl) (fun _ ↦ rfl) f s)

/-- The identification commutes with precomposition by morphisms of representing
algebras. -/
@[stacks 06IC "tangent_space_derivations"]
theorem tangentSpaceDerivationsLinearEquiv_precomp
    (T S : CompleteLocalAlgCat.{u, max v w, w} Λ k) (g : T ⟶ S)
    (f : tangentSpaceArtinian Λ k (restrictedCoyoneda S)) (t : T) :
    tangentSpaceDerivationsLinearEquiv T (g ≫ f) t =
      tangentSpaceDerivationsLinearEquiv S f (g.hom t) := by
  rw [tangentSpaceDerivationsLinearEquiv_apply, tangentSpaceDerivationsLinearEquiv_apply,
    CompleteLocalAlgCat.comp_hom]
  rfl

/-- **Stacks Project, Tag 06IC.** The tangent space of a prorepresentable functor is
finite-dimensional, under the chapter's standing assumption that `Λ → k` is finite. -/
@[stacks 06IC "finite_tangent_space", sga "7 VI 1.11" "(ii), special case"]
theorem tangentSpace_finiteDimensional [Module.Finite Λ k]
    (S : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    FiniteDimensional k (tangentSpaceArtinian Λ k (restrictedCoyoneda S)) := by
  let := (residueHom S).toRingHom.toAlgebra
  have : Module.Finite k (Derivation Λ S k) := derivation_module_finite S.residueEquiv
  exact Module.Finite.equiv (tangentSpaceDerivationsLinearEquiv S).symm

end Deformation

end
