module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingAffine
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingReduction

/-!
# The functor of finitely presented quotients is limit preserving (Stacks 082Q, corrected)

**Stacks 082Q as written is false.**  It asserts that in Situation 082M, if (a) `f : X → B` is
quasi-compact and quasi-separated and (b) `F` is of finite presentation, then `Q^{fp}_{F/X/B}`
is limit preserving.  The proof in the source reduces to an affine chart and then treats
`X = Spec(B₀)` as *of finite presentation over* `B = Spec(A₀)` in order to apply Algebra,
Lemma 02JO; nothing in (a) provides that.  A counterexample to the statement as written:

* `k = ℚ`, `B = Spec k[t]`, `B₀ = k[t][y_a : a ∈ k]/((t - a) y_a : a ∈ k)`, `X = Spec B₀`, so
  `X → B` is affine, hence quasi-compact and quasi-separated, and `F = 𝒪_X` is of finite
  presentation;
* `T = Spec k(t)` is the directed limit of the affine schemes `T_g = Spec k[t]_g`, `g ≠ 0`;
* `X_T = Spec k(t)` (every `y_a` dies once `t - a` is inverted), so the identity quotient
  `F_T → F_T` lies in `Q^{fp}(T)`;
* at a stage `T_g`, a quotient `B₀ ⊗ k[t]_g → Q` flat over `k[t]_g` is torsion free, so it kills
  every `y_a`, and if it pulls back to the identity quotient over `k(t)` it is
  `B₀ ⊗ k[t]_g → k[t]_g`, whose kernel `(y_a : g(a) ≠ 0)` is not finitely generated: `Q` is not
  of finite presentation.  So the identity quotient is in the image of no stage, and
  `colim Q^{fp}(T_g) → Q^{fp}(T)` is not surjective.

Unqualified names below are in the namespace `AlgebraicGeometry.Space.QuotientSituation`. The
formal counterexample is `not_forall_finitePresentationQuotientsFunctor_limitPreserving`, with
algebraic core `AlgebraicGeometry.QuotientFunctorCounterexample.not_finitePresentation_quotient`.

The source's argument does go through once `f` is also **locally of finite presentation**, which
is the hypothesis added here: with `f` of finite presentation (Stacks 03XP (3): locally of finite
presentation, quasi-compact and quasi-separated) and `F` of finite presentation, `Q^{fp}_{F/X/B}`
is limit preserving.

## Main results

* `finitePresentationQuotientsFunctor_limitPreserving_of_isLocallyOfFinitePresentation`:
  **Stacks 082Q**, corrected.

## Implementation notes

The proof follows the source. The change of base to an affine stage `T₀` (Remark 08JW) and the
passage to an affine étale chart `U → X_{T₀}` with an affine étale chart of `U ×_X U` (Stacks 03H6,
with the quotients glued by Stacks 08IU) are
`limitPreserving_finitePresentationQuotientsFunctor_of_affineCase`; the affine case — Stacks 07V7
for an inverse system of affine schemes, Algebra, Lemma 05LI for the surjectivity and Algebra,
Lemma 02JO (through Stacks 0CWZ (2)) for the flatness at a stage — is
`limitPreserving_finitePresentationQuotientsFunctor_affine`. The index categories of the directed
systems are taken in the universe of the schemes, the largest that Stacks 05LY (used for the
flatness at a stage) allows.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 082Q, corrected.**  In Situation 082M assume that (a) `f : X ⟶ Y` is quasi-compact
and quasi-separated, and also locally of finite presentation, and (b) `F` is of finite
presentation.  Then `Q^{fp}_{F/X/Y}` is limit preserving: for a directed limit `T = lim T_i` of
affine schemes over `Y`, `Q^{fp}_{F/X/Y}(T) = colim Q^{fp}_{F/X/Y}(T_i)`.

The tag as written, without local finite presentation of `f`, is false:
`not_forall_finitePresentationQuotientsFunctor_limitPreserving`
(in `StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingSpaceCounterexample`)
proves the negation, with `X = Spec ℚ[t][y_a]/((t - a) y_a)` over `Spec ℚ[t]` and
`T = Spec ℚ(t)`. -/
@[stacks 082Q "corrected per the 082Q erratum: f also locally of finite presentation; as written \
  the statement is false, see not_forall_finitePresentationQuotientsFunctor_limitPreserving"]
theorem finitePresentationQuotientsFunctor_limitPreserving_of_isLocallyOfFinitePresentation
    (D : QuotientSituation B S hS) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hF : D.F.IsFinitePresentationOnSite) :
    LimitPreserving.{u, u + 1, u, u} D.testScheme D.finitePresentationQuotientsFunctor :=
  D.limitPreserving_finitePresentationQuotientsFunctor_of_affineCase hF ⟨hlfp, hqc, hqs⟩
    limitPreserving_finitePresentationQuotientsFunctor_affine

end AlgebraicGeometry.Space.QuotientSituation

end
