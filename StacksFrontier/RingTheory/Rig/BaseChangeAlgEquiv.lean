module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeTensor

/-!
# An isomorphic object is a completed base change along the identity

Let `A` be a ring, `I ⊆ A` an ideal and `B`, `C` two objects of the category of `I`-adically
complete `A`-algebras of finite type modulo `I` (**Stacks 0AL4**) whose carriers are isomorphic
as `A`-algebras.  This file exhibits `B` as the completed base change of `C` along the identity
of `(A, I)`, in the shape the engine forms of **Stacks 0GB2** and **Stacks 0GAM** consume: a
ring equivalence of `B.carrier` with `(C ⊗_A A)^∧_I` compatible with the structure map of `A`
and with the map `C.carrier → B.carrier` the isomorphism defines.

## Main results

* `Rig.exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv`: the identification and its two
  compatibilities.

## Implementation notes

Base change along the identity does nothing, but saying so takes three steps, and they are the
same three for every property transported this way — which is why they are here and not spelled
out twice.  The right unitor `C ⊗_A A ≃ₐ[A] C` matches the two ideals, by
the right unitor's action on the structure map; `C` is already `I`-adically complete, so the
canonical map into the completion of `C ⊗_A A` is an isomorphism
(`AdicCompletion.ofAlgEquiv`); and composing the given isomorphism with those two gives the
identification.

The map `C.carrier → B.carrier` is *not* fixed by the data: it is whatever `Algebra` instance
is in scope, and the hypothesis `halg` says that instance is the one `e.symm` defines.  The
instance is left to the caller because the engine forms take it as an instance argument, so it
has to be in scope at the call site in any case; asking for `halg` rather than building the
instance here is what lets one construction serve both callers.

The universes of the two carriers are unrelated: `B.carrier` may live in `Type (max u w)` and
`C.carrier` in `Type (max u v)`.  A cross-universe `≃ₐ[A]` is the normal case here, since the
carrier of an object built by completing a polynomial algebra over `A` lives in `Type u` while
a carrier handed in from geometry does not.

## References

* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
* [Stacks Project, Tag 0GAM](https://stacks.math.columbia.edu/tag/0GAM)
* [Stacks Project, Tag 0GB2](https://stacks.math.columbia.edu/tag/0GB2)
-/

@[expose] public noncomputable section

namespace Rig

universe u v w

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **An isomorphic object is the completed base change along the identity.**  If the carriers
of two objects of `Rig.AdicFiniteTypeAlgebra A I` are isomorphic as `A`-algebras by `e`, and
the `A`-algebra `B.carrier` is regarded as a `C.carrier`-algebra through `e.symm`, then
`B.carrier` is identified with `(C ⊗_A A)^∧_I` compatibly with the structure map of `A` and
with the map `C.carrier → B.carrier`.

This is exactly the data `Rig.isRigEtale_of_completedBaseChange` (Stacks 0GB2) and
`Rig.isRigSmooth_of_completedBaseChange` (Stacks 0GAM) take, for `A₁ = A₂ = A` and
`I₁ = I₂ = I`; the remaining hypothesis of either, that `V(I A) = V(I)`, holds because base
change along the identity maps `I` to itself. -/
public theorem exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv
    {B : AdicFiniteTypeAlgebra.{u, w} A I} {C : AdicFiniteTypeAlgebra.{u, v} A I}
    (e : B.carrier ≃ₐ[A] C.carrier) [Algebra C.carrier B.carrier]
    (halg : ∀ x : C.carrier, algebraMap C.carrier B.carrier x = e.symm x) :
    ∃ e' : B.carrier ≃+* completedBaseChangedAlgebra (A₂ := A) (I₂ := I) C,
      (∀ a : A, e' (algebraMap A B.carrier a) =
          algebraMap (baseChangedAlgebra (A₂ := A) C)
            (completedBaseChangedAlgebra (A₂ := A) (I₂ := I) C) (baseChangedRight A C a)) ∧
        ∀ x : C.carrier, e' (algebraMap C.carrier B.carrier x) =
          algebraMap (baseChangedAlgebra (A₂ := A) C)
            (completedBaseChangedAlgebra (A₂ := A) (I₂ := I) C) (baseChangedLeft A C x) := by
  have hrid : ∀ a : A, (Algebra.TensorProduct.rid A A C.carrier).symm
      ((algebraMap A C.carrier) a) = Algebra.TensorProduct.includeRight a := fun a => by
    rw [Algebra.TensorProduct.rid_symm_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  let rid : baseChangedAlgebra (A₂ := A) C ≃ₐ[A] C.carrier :=
    Algebra.TensorProduct.rid A A C.carrier
  have hJ : Ideal.map (rid.symm : _ →+* _) C.adicIdeal
      = baseChangedIdeal (A₂ := A) (I₂ := I) C := by
    rw [AdicFiniteTypeAlgebra.adicIdeal, Ideal.map_map]
    exact congrArg (fun f : A →+* _ => Ideal.map f I) (RingHom.ext hrid)
  have : IsAdicComplete (baseChangedIdeal (A₂ := A) (I₂ := I) C)
      (baseChangedAlgebra (A₂ := A) C) := by
    rw [← hJ]
    exact (IsAdicComplete.congr_ringEquiv C.adicIdeal rid.symm.toRingEquiv).mpr
      C.isAdicallyComplete
  refine ⟨(e.toRingEquiv.trans rid.symm.toRingEquiv).trans
    (AdicCompletion.ofAlgEquiv
      (baseChangedIdeal (A₂ := A) (I₂ := I) C)).toRingEquiv, fun a => ?_, fun x => ?_⟩
  · change (AdicCompletion.ofAlgEquiv _) (rid.symm (e (algebraMap A B.carrier a))) = _
    rw [e.commutes, hrid]
    rfl
  · change (AdicCompletion.ofAlgEquiv _) (rid.symm (e (algebraMap C.carrier B.carrier x))) = _
    rw [halg, e.apply_symm_apply, Algebra.TensorProduct.rid_symm_apply]
    rfl

end Rig

end
