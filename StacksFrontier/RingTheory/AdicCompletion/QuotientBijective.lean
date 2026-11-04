module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The quotient of an adic completion by a finitely generated ideal

For a finitely generated ideal `I` of a ring `R`, the completion map induces an isomorphism
`R ⧸ I ≃ AdicCompletion I R ⧸ I · AdicCompletion I R`. The content is Mathlib's
`AdicCompletion.ker_evalOneₐ_eq_map`, which identifies the kernel of `AdicCompletion.evalOneₐ`
with the extension of `I`; this packages it as bijectivity of `Ideal.quotientMap`.
-/

@[expose] public section

namespace AdicCompletion

/-- Completion induces an isomorphism on the quotient by a finitely generated ideal. -/
theorem quotientMap_bijective {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map) := by
  let q := Ideal.quotientMap (I.map (algebraMap R (AdicCompletion I R)))
    (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map
  let E := (Ideal.quotientEquivAlgOfEq R (AdicCompletion.ker_evalOneₐ_eq_map I hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I))
  have he (x : R ⧸ I) : E (q x) = x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  refine ⟨fun x y hxy => (he x).symm.trans ((congrArg E hxy).trans (he y)),
    fun y => ⟨E y, E.injective (he _)⟩⟩

end AdicCompletion
