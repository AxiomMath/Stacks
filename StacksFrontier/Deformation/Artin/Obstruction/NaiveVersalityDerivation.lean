module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The forced shape of a lift into the dual numbers

Let `Λ ⟶ A` be a ring map and `k` a field, and suppose `k` is also an `A`-algebra through a
fixed `Λ`-algebra map `ψ : A →ₐ[Λ] k`. A ring map `q : A →ₐ[Λ] TrivSqZeroExt k k` into the dual
numbers over `k` that agrees with `ψ` after composing with the augmentation
`TrivSqZeroExt.fstHom` is forced, by the square-zero kernel of that augmentation, to have the
shape `a ↦ (ψ a, θ (D a))` for a *unique* `A`-linear map `θ : Ω[A⁄Λ] →ₗ[A] k`, where `D` is the
universal derivation of `A` over `Λ`: indeed `a ↦ q(a).snd` is itself a `Λ`-derivation of `A`
valued in `k` (with the `A`-module structure on `k` coming from `ψ`), by the ring-homomorphism
property of `q` together with the Leibniz rule for multiplication in `TrivSqZeroExt`, and every
such derivation factors uniquely through the universal one into `Ω[A⁄Λ]`.

This is the first half of the comparison, for Stacks tag 07YM, between the lifting property
defining `Deformation.Artin.IsVersalAt` and the tangent-space description of versality: tested
at the dual-numbers extension of the residue field `k` of a point, a witness of the lifting
property is exactly such a `q`, and this file isolates the algebra fact that identifies its
class with a canonical element of `Ω[A⁄Λ] →ₗ[A] k`.

## Main results

* `Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq` — the forced-shape statement:
  every lift of `ψ` through the dual-numbers augmentation determines a unique `A`-linear map
  `Ω[A⁄Λ] →ₗ[A] k` recovering it via the universal derivation.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

namespace Deformation.Artin

universe u

variable {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra Λ k]
variable [Algebra A k] [IsScalarTower Λ A k]
variable (ψ : A →ₐ[Λ] k) (hψ : ∀ a : A, algebraMap A k a = ψ a)

include hψ in
/-- Every lift of `ψ : A →ₐ[Λ] k` through the dual-numbers augmentation
`TrivSqZeroExt.fstHom Λ k k` determines, and is determined by, a unique `A`-linear map
`θ : Ω[A⁄Λ] →ₗ[A] k` recovering it as `a ↦ (ψ a, θ (D a))` through the universal derivation `D`
of `A` over `Λ`. The `A`-module structure on `k` used for `θ` is the one coming from `ψ`
(`hψ`); the square-zero kernel of the augmentation forces `q a` to agree with `ψ a` on the
first coordinate, and the second coordinate is then a `Λ`-derivation of `A` valued in `k` by
the Leibniz rule for multiplication in the trivial square-zero extension, hence factors
uniquely through `Ω[A⁄Λ]`. -/
@[ega "0 20.1.5" "partial", sga "7 VI 1.17" "partial"]
public theorem exists_unique_kaehler_of_fstHom_comp_eq
    (q : A →ₐ[Λ] TrivSqZeroExt k k) (hq : (TrivSqZeroExt.fstHom Λ k k).comp q = ψ) :
    ∃! θ : Ω[A⁄Λ] →ₗ[A] k, ∀ a : A,
      q a = TrivSqZeroExt.inl (ψ a) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D Λ A a)) := by
  have hfst : ∀ a : A, (q a).fst = ψ a := fun a => congrFun (congrArg DFunLike.coe hq) a
  have hadd : ∀ a b : A, (q (a + b)).snd = (q a).snd + (q b).snd := fun a b => by
    rw [map_add, TrivSqZeroExt.snd_add]
  have hsmul : ∀ (r : Λ) (a : A), (q (r • a)).snd = r • (q a).snd := fun r a => by
    rw [map_smul, TrivSqZeroExt.snd_smul]
  have hone : (q 1).snd = 0 := by rw [map_one, TrivSqZeroExt.snd_one]
  let Dlin : A →ₗ[Λ] k := { toFun := fun a => (q a).snd, map_add' := hadd, map_smul' := hsmul }
  let D' : Derivation Λ A k :=
    { toLinearMap := Dlin
      map_one_eq_zero' := hone
      leibniz' := fun a b => by
        change (q (a * b)).snd = a • (q b).snd + b • (q a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul, hfst a, hfst b,
          Algebra.smul_def a, Algebra.smul_def b, hψ, hψ]
        ring }
  refine ⟨D'.liftKaehlerDifferential, fun a => ?_, fun θ' hθ' => ?_⟩
  · have hsnd : D'.liftKaehlerDifferential (KaehlerDifferential.D Λ A a) = (q a).snd :=
      Derivation.liftKaehlerDifferential_comp_D D' a
    rw [show q a = TrivSqZeroExt.inl (q a).fst + TrivSqZeroExt.inr (q a).snd from
        (TrivSqZeroExt.inl_fst_add_inr_snd_eq (q a)).symm, hfst, hsnd]
  · have hcompDer : θ'.compDer (KaehlerDifferential.D Λ A) = D' := by
      ext a
      change θ' (KaehlerDifferential.D Λ A a) = (q a).snd
      have hsnd := congrArg TrivSqZeroExt.snd (hθ' a)
      rwa [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        eq_comm] at hsnd
    exact Derivation.liftKaehlerDifferential_unique θ' D'.liftKaehlerDifferential
      (hcompDer.trans D'.liftKaehlerDifferential_comp.symm)

end Deformation.Artin
