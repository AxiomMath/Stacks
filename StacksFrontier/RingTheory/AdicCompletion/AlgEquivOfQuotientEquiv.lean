module

public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial

/-!
# Uniqueness for `adicCompletionAlgEquivOfQuotientEquiv`

`adicCompletionAlgEquivOfQuotientEquiv` builds an algebra equivalence of adic completions out of
compatible algebra equivalences of all the infinitesimal neighbourhoods, and
`AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv` says that its level-`n` reduction is
the given level-`n` equivalence. This file proves that these reductions determine it.

## Main results

* `AdicCompletion.eq_adicCompletionAlgEquivOfQuotientEquiv_of_evalₐ`: a map with the same
  level-`n` reductions as the equivalence equals it.
-/

@[expose] public noncomputable section

namespace AdicCompletion

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]

/-- The level-`n` identities pin `adicCompletionAlgEquivOfQuotientEquiv` down: a map computed by
the same level-`n` equivalences is that equivalence. -/
public theorem eq_adicCompletionAlgEquivOfQuotientEquiv_of_evalₐ (I : Ideal R) (J : Ideal S)
    (e : ∀ n : ℕ, (R ⧸ I ^ n) ≃ₐ[A] (S ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))
    (F : AdicCompletion I R → AdicCompletion J S)
    (hF : ∀ (n : ℕ) (x : AdicCompletion I R), evalₐ J n (F x) = e n (evalₐ I n x))
    (x : AdicCompletion I R) :
    F x = adicCompletionAlgEquivOfQuotientEquiv I J e he x :=
  ext_evalₐ fun n => (hF n x).trans
    (evalₐ_adicCompletionAlgEquivOfQuotientEquiv I J e he n x).symm

end AdicCompletion

end
