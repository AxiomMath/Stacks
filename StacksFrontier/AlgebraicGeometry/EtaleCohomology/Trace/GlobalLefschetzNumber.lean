module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace

/-!
# The global Lefschetz number

Let `Λ` be a finite ring, `X` a projective curve over a finite field `k` and `K` an object of
`D_ctf(X, Λ)`. The canonical map `c_K : π_X^{-1}K → K` base changes to `X_k̄` and induces an
action `π_X^*` on `RΓ(X_k̄, K|_{X_k̄})`, which is a perfect complex of `Λ`-modules. The global
Lefschetz number of `K` is the trace of that action, an element of the additive commutator
quotient `Λ^natural`.

## Main definitions

* `Stacks.EtaleCohomology.FrobeniusActionOnCohomology` — the datum the definition operates on:
  a perfect object of `D(Λ)` together with an endomorphism of it.
* `Stacks.EtaleCohomology.globalLefschetzNumber` — the global Lefschetz number.

## Main results

* `Stacks.EtaleCohomology.globalLefschetzNumber_eq_alternatingTrace` — the global Lefschetz
  number is the alternating sum of the traces of any cochain endomorphism representing the
  action on any bounded finite-projective representative.

## Implementation notes

The coefficient ring is an arbitrary, possibly noncommutative, finite ring, as in the source:
the traces in play are those of `CategoryTheory.FilteredDerived.perfectDerivedTrace`, valued in
`Λ^natural`, and `Λ^natural` is a proper quotient of `Λ` exactly when `Λ` is noncommutative. No
commutativity hypothesis enters anywhere.

The geometric input enters only where the source uses it, namely through the perfect complex
`RΓ(X_k̄, K|_{X_k̄})` and the endomorphism `π_X^*` of it. Both are taken as the data of
`FrobeniusActionOnCohomology`, so the projectivity of `X`, its dimension, and the
constructibility and finite Tor dimension of `K` — hypotheses the definition itself does not
need, only its well-posedness does — are not imposed. The ring and module universes are
independent.

## References

* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The datum underlying the global Lefschetz number: the perfect complex
`RΓ(X_k̄, K|_{X_k̄})` of `Λ`-modules together with the action `π_X^*` on it induced by the
canonical map `c_K`.

See [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX). -/
public structure FrobeniusActionOnCohomology (Λ : Type u) [Ring Λ] [Finite Λ] where
  /-- The perfect complex `RΓ(X_k̄, K|_{X_k̄})`. -/
  cohomology : CategoryTheory.FilteredDerived.PerfectDerivedCategory.{u, v} Λ
  /-- The action `π_X^*` induced by the base change of the canonical map `c_K`. -/
  frobeniusAction : cohomology.obj ⟶ cohomology.obj

/-- The global Lefschetz number of `K`: the trace of the action `π_X^*` on the perfect complex
`RΓ(X_k̄, K|_{X_k̄})`, an element of the additive commutator quotient `Λ^natural`.

See [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX). -/
@[stacks 03TX]
public def globalLefschetzNumber (Λ : Type u) [Ring Λ] [Finite Λ]
    (D : FrobeniusActionOnCohomology.{u, v} Λ) :
    CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient Λ :=
  CategoryTheory.FilteredDerived.perfectDerivedTrace Λ D.cohomology D.frobeniusAction

/-- The global Lefschetz number is the alternating sum of the traces of any cochain
endomorphism representing `π_X^*` on any bounded finite-projective representative of
`RΓ(X_k̄, K|_{X_k̄})`. -/
public theorem globalLefschetzNumber_eq_alternatingTrace (Λ : Type u) [Ring Λ] [Finite Λ]
    (D : FrobeniusActionOnCohomology.{u, v} Λ)
    (P : CochainComplex (ModuleCat.{v} Λ) ℤ)
    (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex Λ P)
    (e : DerivedCategory.Q.obj P ≅ D.cohomology.obj) (g : P ⟶ P)
    (hg : DerivedCategory.Q.map g = e.hom ≫ D.frobeniusAction ≫ e.inv) :
    globalLefschetzNumber Λ D =
      CategoryTheory.FilteredDerived.alternatingTrace Λ P hP g :=
  CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_alternatingTrace Λ D.cohomology
    D.frobeniusAction P hP e g hg

end Stacks.EtaleCohomology

end
