module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne

/-!
# The trace formula without a bound on the dimension

Let `k` be a finite field with `q = p ^ n` elements, let `X` be a separated scheme of finite
type over `k`, let `Λ` be a finite ring whose cardinality is prime to that of `k`, and let `K`
be a bounded below complex of sheaves of `Λ`-modules on the small étale site of `X`.  The trace
formula

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

is stated in the source for `X` of dimension at most one, and remarked to hold in any
dimension.  Nothing in the deduction of
`Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_localLefschetzNumber` uses the
dimension of `X`: the inputs are the dévissage of `RΓ_c(X_k̄, K)` along the rational points
with the identification of its graded pieces, and the Galois descent of Steps 7 to 9, and the
identity follows from those two for a scheme of any dimension.  That is the content of this
file.

## Main results

* `Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_localLefschetzNumber_of_galoisDescent`
  — the trace formula for a separated finite type scheme over a finite field, with no bound on
  its dimension, from the dévissage and the Galois descent.

## Implementation notes

What is removed relative to
`Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_localLefschetzNumber` is the
hypothesis `topologicalKrullDim X ≤ 1`, which that theorem carries because the source carries
it and does not use.  Everything else is unchanged, except that the Galois descent of Steps 7
to 9 enters as the structure `Stacks.EtaleCohomology.LefschetzGaloisDescent` rather than as its
fields spelled out one at a time, so that the identity is deduced from the trace formula of
[Stacks, Tag 03TZ] and no part of its proof is repeated here.

This is not the source's dévissage.  The source reduces the general case to the
dimension-one case using proper base change, so that in any dimension the two inputs are
produced rather than assumed.  That reduction, and with it Remark 03UI (1) in full, is
`Stacks.EtaleCohomology.canonicalTraceFormula_of_isCtf` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaAnyDimensionCtf`.  What this
file records is that the inputs suffice whatever the dimension of `X` is.  A reduction along a
*finite stratification* of `X` by subschemes of dimension at most one, which
`Stacks.EtaleCohomology.StratifiedDevissage` would support, is not available, and not for want
of machinery: a scheme of dimension two is
not a finite union of locally closed subschemes of dimension at most one, so such a statement
would be empty above dimension one.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (1); the full
  statement is `Stacks.EtaleCohomology.canonicalTraceFormula_of_isCtf`
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03TZ](https://stacks.math.columbia.edu/tag/03TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FilteredDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r t

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The trace formula in any dimension, from its inputs.**  Let `k` be a finite field
with `p ^ q` elements, let `k̄` be an algebraically closed extension of `k`, let `X` be a
separated scheme of finite type over `k` — of arbitrary dimension — let `Λ` be a finite ring
whose cardinality is prime to that of `k`, and let `K` be a bounded below complex of sheaves of
`Λ`-modules on the small étale site of `X`.  Then

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in `Λ^natural`, given the dévissage of `RΓ_c(X_k̄, K)` along the rational points with the
identification of its graded pieces and the Galois descent of Steps 7 to 9 of the source.  The
bound `topologicalKrullDim X ≤ 1` of
`Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_localLefschetzNumber` plays no part in
the deduction and is absent here.  Remark 03UI (1), with these inputs produced from
`K ∈ D_ctf(X, Λ)`, is `Stacks.EtaleCohomology.canonicalTraceFormula_of_isCtf`. -/
public theorem compactSupportLefschetzNumber_eq_localLefschetzNumber_of_galoisDescent
    {k : Type u} [Field k] [Fintype k] {p q : ℕ} [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (Y : Over (Spec (.of k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [CharP kbar p]
    (Λ : Type r) [Ring Λ] [Finite Λ]
    (_hcoprime : Nat.Coprime (Nat.card Λ) (Fintype.card k))
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    [Fintype (rationalPoints Y.hom)]
    (j : CompactificationOf
      (Over.mk (pullback.snd Y.hom (Stacks.Frobenius.specAlgebraMap k kbar))))
    (E : CompactificationEndomorphism j
      (Stacks.Frobenius.geometricFrobeniusBaseChange Y kbar p q hcard))
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((compactlySupportedCohomology.{u, r} kbar
          (pullback.snd Y.hom (Stacks.Frobenius.specAlgebraMap k kbar)) j Λ).obj
        (baseChangeCoefficients.{u, r} Λ Y kbar K))))
    (hstalkPerfect : ∀ x : rationalPoints Y.hom, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x.1 K)))
    (devissage : LefschetzDevissage.{r, max (u + 1) r, u} Λ (rationalPoints Y.hom))
    (hglobal : devissage.globalDatum =
      frobeniusActionOnCompactSupport.{u, r} Λ E γ
        (baseChangeCoefficients.{u, r} Λ Y kbar K) hperf)
    (hstalk : devissage.stalkDatum =
      geometricFrobeniusStalkDatum.{u, r} Λ kbar p q hcard Y.hom K hstalkPerfect)
    (group : Type t) [Fintype group]
    (descent : LefschetzGaloisDescent.{r, max (u + 1) r, u, t} Λ devissage group) :
    compactSupportLefschetzNumber.{u, r} Λ E γ
        (baseChangeCoefficients.{u, r} Λ Y kbar K) hperf =
      localLefschetzNumber Λ (rationalPoints Y.hom)
        (geometricFrobeniusStalkDatum.{u, r} Λ kbar p q hcard Y.hom K hstalkPerfect) := by
  have key := descent.globalLefschetzNumber_eq_localLefschetzNumber
  rw [hglobal, hstalk] at key
  exact key

end Stacks.EtaleCohomology

end
