module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A free module with a cyclic free adic quotient is free of rank one

Let `A` be a commutative ring, `J ⊆ A` a proper ideal and `M` a free `A`-module. If the quotient
`M / J M` is isomorphic to `A / J`, then `M` is isomorphic to `A`.

The point is that the rank of a free module is detected after any base change to a nonzero ring:
a basis `ι` of `M` base-changes to a basis of `(A/J) ⊗_A M ≅ M / J M` indexed by the same `ι`,
so a second basis of that module indexed by a single element forces `ι` to be a singleton, the
nonzero commutative ring `A / J` having the invariant basis number property.

## Main results

* `Stacks.FreeOfAdicQuotients.nonempty_linearEquiv_self_of_quotient_linearEquiv` — the statement
  above.
-/

@[expose] public section

open TensorProduct

namespace Stacks.FreeOfAdicQuotients

universe u v

/-- **A free module whose quotient by a proper ideal is cyclic free is free of rank one.** Let
`A` be a commutative ring, `J ≠ A` an ideal and `M` a free `A`-module with
`M / J M ≃ₗ[A] A / J`. Then `M ≃ₗ[A] A`.

The isomorphism `M / J M ≃ₗ[A] A / J` is `A/J`-linear, both sides being `A/J`-modules and
`A ⟶ A/J` being surjective, and `M / J M` is `(A/J) ⊗_A M`, which has a basis indexed by any
basis of `M`. Two bases of one module over the nonzero commutative ring `A/J` are equinumerous,
so a basis of `M` has exactly one element. -/
public theorem nonempty_linearEquiv_self_of_quotient_linearEquiv {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Free A M] {J : Ideal A} (hJ : J ≠ ⊤)
    (h : Nonempty ((M ⧸ (J • (⊤ : Submodule A M))) ≃ₗ[A] (A ⧸ J))) :
    Nonempty (M ≃ₗ[A] A) := by
  classical
  obtain ⟨g⟩ := h
  have hnt : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hsurj : Function.Surjective (algebraMap A (A ⧸ J)) := Ideal.Quotient.mk_surjective
  set b : Module.Basis (Module.Free.ChooseBasisIndex A M) A M := Module.Free.chooseBasis A M
  set e : ((A ⧸ J) ⊗[A] M) ≃ₗ[A ⧸ J] (A ⧸ J) :=
    LinearEquiv.extendScalarsOfSurjective hsurj
      ((TensorProduct.quotTensorEquivQuotSMul M J).trans g)
  set eq : Module.Free.ChooseBasisIndex A M ≃ Unit :=
    (b.baseChange (A ⧸ J)).indexEquiv ((Module.Basis.singleton Unit (A ⧸ J)).map e.symm)
  exact ⟨(b.reindex eq).repr.trans (Finsupp.uniqueLinearEquiv A A ())⟩

end Stacks.FreeOfAdicQuotients

end
