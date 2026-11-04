module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceFormula

/-!
# The trace formula with constant coefficients, and Weil's formula

The trace formula of [Stacks, Tag 03UG] applies to a coefficient system `K`, and its right hand
side `∑_{x ∈ X(k)} Tr(π_x | K_x̄)` is a sum of traces that vary with the point.  Weil's
geometric trace formula, [Stacks, Tag 03U1], is about constant coefficients: it computes the
number of fixed points of an endomorphism `φ` of a curve, `V(φ) = Δ_C · Γ_φ`, as
`1 - Tr_J(φ^*) + deg φ`.  This file makes the comparison of the two precise.

Constant coefficients means that the stalk of `K` at every rational point is the same perfect
complex with the same Frobenius acting on it — for `K = Λ` the stalk is `Λ` and `π_x` is the
identity, independently of `x`.  For such a coefficient system the right hand side of the trace
formula collapses: it is `#X(k)` times the trace at a single point.  So with constant
coefficients the trace formula computes the number of rational points of `X`, which is exactly
what Weil's formula computes for the geometric Frobenius, whose fixed points on `X_k̄` are the
rational points of `X`.  Combining the two:

`Tr(π_X^* | RΓ_c(X_k̄, Λ)) = (1 - Tr_J(π_X^*) + deg π_X) · Tr(π_x | Λ)`

in `Λ^natural`.  This is the sense in which Weil's formula is the constant-coefficient case of
the trace formula, and the sense in which the trace formula is stronger: nothing in its right
hand side is a point count unless the coefficient system is constant.

## Main definitions

* `Stacks.EtaleCohomology.constantStalkDatum` — the stalk datum of [Stacks, Tag 03TY] of a
  constant coefficient system: one perfect complex with one endomorphism, at every rational
  point.

## Main results

* `Stacks.EtaleCohomology.localLefschetzNumber_constantStalkDatum` — with constant coefficients
  the local Lefschetz number is `#X(k)` times the trace at a single point.
* `Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_weil_of_constantCoefficients` — the
  trace formula with constant coefficients, its right hand side evaluated by Weil's formula.

## Implementation notes

The trace formula `Stacks.EtaleCohomology.compactSupportLefschetzNumber`
`_eq_localLefschetzNumber` is used as it stands, with all of its hypotheses, so the identity
proved here is conditional in exactly the same way and on exactly the same inputs.  Two further
hypotheses carry the two geometric facts that make the comparison:

`hconstant`, that the stalk datum produced from the geometry is the constant one, which is what
the coefficient system `K` being constant amounts to for the right hand side — the stalk of a
constant sheaf and the triviality of the Frobenius action on it are not computed in this
development; and

`hfixedPoints`, that `#X(k)` is the intersection number `V(π_X) = Δ_C · Γ_{π_X}` of Weil's
formula, which is the statement that the fixed points of the geometric Frobenius are the
rational points, counted with multiplicity one.

Weil's formula itself is not derived from the trace formula, and in this development it cannot
be: `Stacks.EtaleCohomology.JacobianCorrespondence.fixedPointNumber_eq` is an identity between
intersection numbers on `C × C` and a trace on the jacobian, with no sheaf and no `Λ` in it,
and the source uses it as an *input* to the proof of the trace formula, through the absence of
fixed points on a Galois cover in Steps 7 to 9.  What is proved here is that the two formulas
compute the same number once the coefficients are constant.

## References

* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
* [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FilteredDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r t w z

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Constant coefficients -/

/-- **The stalk datum of a constant coefficient system.**  For a constant coefficient system the
stalk at every rational point is the same perfect complex `S` of `Λ`-modules and the Frobenius
acts on it by the same endomorphism `g`; for `K` the constant sheaf `Λ` these are `Λ` and the
identity. -/
public def constantStalkDatum (Λ : Type u) [Ring Λ] [Finite Λ] (points : Type w)
    (S : PerfectDerivedCategory.{u, r} Λ) (g : S.obj ⟶ S.obj) :
    FrobeniusActionOnStalks.{u, r, w} Λ points where
  stalk _ := S
  frobeniusAction _ := g

/-- **With constant coefficients the local Lefschetz number is a point count.**  The sum
`∑_{x ∈ X(k)} Tr(π_x | K_x̄)` of [Stacks, Tag 03TY] has equal terms when the coefficient system
is constant, so it is `#X(k)` times the trace at a single rational point. -/
@[stacks 03UJ "with constant coefficients the right hand side of 03UG collapses to #X(k) times \
the trace at one rational point, which is the point count Weil's formula 03U1 computes"]
public theorem localLefschetzNumber_constantStalkDatum (Λ : Type u) [Ring Λ] [Finite Λ]
    (points : Type w) [Fintype points] (S : PerfectDerivedCategory.{u, r} Λ)
    (g : S.obj ⟶ S.obj) :
    localLefschetzNumber Λ points (constantStalkDatum.{u, r, w} Λ points S g) =
      (Fintype.card points : ℤ) • perfectDerivedTrace Λ S g := by
  simp only [localLefschetzNumber, constantStalkDatum, Finset.sum_const, Finset.card_univ,
    natCast_zsmul]

/-! ### Weil's formula as the constant-coefficient case -/

/-- **The trace formula with constant coefficients is Weil's formula (Stacks 03UJ).**  In the
situation of `Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_localLefschetzNumber`,
suppose the coefficient system is constant, so that the stalk of `K` at every rational point is
one perfect complex `S` with one endomorphism `g` on it, and suppose the number of rational
points of `X` is the intersection number `V(π_X) = Δ_C · Γ_{π_X}` of Weil's formula for the
geometric Frobenius.  Then

`Tr(π_X^* | RΓ_c(X_k̄, K)) = (1 - Tr_J(π_X^*) + deg π_X) · Tr(π_x | K_x̄)`

in `Λ^natural`: the right hand side of the trace formula is the point count, and Weil's formula
[Stacks, Tag 03U1] evaluates it on the jacobian of the curve. -/
@[stacks 03UJ "RESTRICTED: 03UG specialised to constant coefficients computes #X(k), and 03U1 \
evaluates that count as 1 - Tr_J + deg; the hypotheses of the library's 03UG are carried \
unchanged, and the constancy of the stalks and the fixed point count are hypotheses"]
public theorem compactSupportLefschetzNumber_eq_weil_of_constantCoefficients
    {k : Type u} [Field k] [Fintype k] {p q : ℕ} [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (Y : Over (Spec (.of k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (hdim : topologicalKrullDim Y.left ≤ 1)
    (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [CharP kbar p]
    (Λ : Type r) [Ring Λ] [Finite Λ]
    (hcoprime : Nat.Coprime (Nat.card Λ) (Fintype.card k))
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
    (group : Type t) [Fintype group] (prime exponent level : ℕ)
    (stabilizerExponent : group → ℕ) (coefficientTrace : group → ℤ)
    (moduleTrace : group → AdditiveCommutatorQuotient Λ)
    (hprime : Nat.Prime prime)
    (hannihilate : ∀ y : AdditiveCommutatorQuotient Λ, ((prime : ℤ) ^ exponent) • y = 0)
    (hlevel : ∀ g : group, stabilizerExponent g + exponent ≤ level)
    (hdecomposition : globalLefschetzNumber Λ devissage.openDatum =
      ∑ g : group, coefficientTrace g • moduleTrace g)
    (hdivisible : ∀ g : group, ((prime : ℤ) ^ level) ∣
      ((prime : ℤ) ^ stabilizerExponent g) * coefficientTrace g)
    (S : PerfectDerivedCategory.{r, max (u + 1) r} Λ) (g : S.obj ⟶ S.obj)
    (hconstant : geometricFrobeniusStalkDatum.{u, r} Λ kbar p q hcard Y.hom K hstalkPerfect =
      constantStalkDatum.{r, max (u + 1) r, u} Λ (rationalPoints Y.hom) S g)
    {Adiv : Type w} [AddCommGroup Adiv] {EndJ : Type z} [Ring EndJ]
    (W : JacobianCorrespondence Adiv EndJ) (frobenius : W.EndomorphismData)
    (hfixedPoints : (Fintype.card (rationalPoints Y.hom) : ℤ) =
      W.fixedPointNumber frobenius) :
    compactSupportLefschetzNumber.{u, r} Λ E γ
        (baseChangeCoefficients.{u, r} Λ Y kbar K) hperf =
      (1 - W.trace frobenius.pullback + frobenius.degree) • perfectDerivedTrace Λ S g := by
  have key := compactSupportLefschetzNumber_eq_localLefschetzNumber.{u, r, t} hcard Y hdim kbar
    Λ hcoprime K j E γ hperf hstalkPerfect devissage hglobal hstalk group prime exponent level
    stabilizerExponent coefficientTrace moduleTrace hprime hannihilate hlevel hdecomposition
    hdivisible
  rw [key, hconstant, localLefschetzNumber_constantStalkDatum, hfixedPoints,
    W.fixedPointNumber_eq]

end Stacks.EtaleCohomology

end
