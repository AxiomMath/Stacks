module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Finitely generated unramified field extensions are finite separable

Proof of Lemma 090W: for a finitely generated field extension `K/k` the six conditions
"finite separable", `Ω[K⁄k] = 0`, formally unramified, unramified, formally étale and étale are
equivalent.

## Main results

* `Stacks.Unramified.FieldExtension.solution`: the six items of Lemma 090W, in the source's order,
  as one `List.TFAE`.

## Implementation notes

*Each item is a differential condition with a finiteness condition attached, and the finiteness is
free.* Over a finitely generated field extension separability implies algebraicity, hence
finiteness as a module, hence finite type, hence — the base field being Noetherian — finite
presentation. So the three items carrying a finiteness condition are equivalent to the three that
do not: `Algebra.Unramified k K` to `Algebra.FormallyUnramified k K`, `Algebra.Etale k K` to
`Algebra.FormallyEtale k K`, and item (1) to plain `Algebra.IsSeparable k K`. Those two
cancellations are the private lemmas `unramified_iff_formallyUnramified_of_field` and
`etale_iff_formallyEtale_of_field`; neither is in Mathlib, and both are stated for an arbitrary
essentially finite type extension of fields rather than specialized to this proof.

*The hard implication is Mathlib's.* The source deduces `Ω[K⁄k] = 0 ⇒ K/k` finite separable by
descending to a finite type `k`-subalgebra `A ⊆ K` with `K = Frac A`, localizing `A` to make
`Ω[A⁄k] = 0` (differentials localize, Lemma 00RT, and are finitely generated, Lemma 00RZ), and
then applying Lemma 00UW at the prime `(0)`. `Algebra.FormallyUnramified.iff_isSeparable` carries
out exactly that reduction, and `Ω[K⁄k] = 0` is by definition formal unramifiedness
(`Algebra.formallyUnramified_iff`, the source's Lemma 00UO), so none of the localization steps is
reproved. Likewise the source's descent from étale to formally unramified through Lemmas 00UR,
00UU and 00UV is replaced by `Algebra.FormallyEtale.iff_formallyUnramified_of_field`, which is the
equivalence of items (3) and (5) outright.

## References

* [StacksProject 090W](https://stacks.math.columbia.edu/tag/090W)
-/

@[expose] public section

namespace Stacks.Unramified.FieldExtension

/-- A separable finitely generated field extension is finite: separability forces algebraicity,
and an algebraic essentially finite type extension is finite. -/
private theorem finite_of_isSeparable (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (h : Algebra.IsSeparable k K) : Module.Finite k K :=
  have := h
  have : Algebra.IsAlgebraic k K := Algebra.IsSeparable.isAlgebraic k K
  Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- For a finitely generated field extension the finite type condition in the definition of
unramified (the source's Definition 00UT) is automatic: a formally unramified such extension is
separable, hence finite. -/
private theorem unramified_iff_formallyUnramified_of_field (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] :
    Algebra.Unramified k K ↔ Algebra.FormallyUnramified k K := by
  refine ⟨fun h => h.formallyUnramified, fun h => ⟨h, ?_⟩⟩
  have := finite_of_isSeparable k K ((Algebra.FormallyUnramified.iff_isSeparable k K).mp h)
  infer_instance

/-- For a finitely generated field extension the finite presentation condition in the definition
of étale is automatic: a formally étale such extension is separable, hence finite, hence of finite
type, hence of finite presentation over the Noetherian base `k`. -/
private theorem etale_iff_formallyEtale_of_field (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] : Algebra.Etale k K ↔ Algebra.FormallyEtale k K := by
  refine ⟨fun h => h.formallyEtale, fun h => ⟨h, ?_⟩⟩
  have := finite_of_isSeparable k K ((Algebra.FormallyEtale.iff_isSeparable k K).mp h)
  exact (Algebra.FinitePresentation.of_finiteType (R := k) (A := K)).mp inferInstance

/-- **Stacks 090W.** Let `K/k` be a finitely generated field extension. The following are
equivalent:

1. `K` is a finite separable field extension of `k`;
2. `Ω[K⁄k] = 0`;
3. `K` is formally unramified over `k`;
4. `K` is unramified over `k`;
5. `K` is formally étale over `k`;
6. `K` is étale over `k`. -/
@[ega "0 19.10.3"]
public theorem solution (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    List.TFAE
      [Module.Finite k K ∧ Algebra.IsSeparable k K,
       Subsingleton Ω[K⁄k],
       Algebra.FormallyUnramified k K,
       Algebra.Unramified k K,
       Algebra.FormallyEtale k K,
       Algebra.Etale k K] := by
  -- (1) ↔ (3) is the source's `Ω[K⁄k] = 0 ⇒ K/k` finite separable, finiteness cancelled.
  tfae_have 1 ↔ 3 := by
    rw [Algebra.FormallyUnramified.iff_isSeparable k K]
    exact ⟨And.right, fun h => ⟨finite_of_isSeparable k K h, h⟩⟩
  -- (2) ↔ (3) is the definition of formal unramifiedness (the source's Lemma 00UO).
  tfae_have 2 ↔ 3 := (Algebra.formallyUnramified_iff k K).symm
  tfae_have 3 ↔ 4 := (unramified_iff_formallyUnramified_of_field k K).symm
  tfae_have 3 ↔ 5 := Algebra.FormallyEtale.iff_formallyUnramified_of_field.symm
  tfae_have 5 ↔ 6 := (etale_iff_formallyEtale_of_field k K).symm
  tfae_finish

end Stacks.Unramified.FieldExtension

end

/-!
# Finitely generated unramified field extensions are finite separable

Let `K` be a finitely generated field extension of a field `k`. Then `K` is a finite separable
extension of `k` as soon as it carries any one of the unramifiedness properties of the
differential calculus: vanishing of the module of Kähler differentials `Ω[K⁄k]`, formal
unramifiedness, unramifiedness, formal étaleness, or étaleness. All six conditions are therefore
equivalent, and for such an extension the a priori much weaker "no infinitesimal deformations"
condition `Ω[K⁄k] = 0` already forces finiteness together with separability.

The hypothesis is what makes this true: the algebraic closure `ℚ̄` of `ℚ` has `Ω[ℚ̄⁄ℚ] = 0` and is
formally étale over `ℚ`, yet it is neither finite over `ℚ` nor of finite type, so it satisfies
(2), (3) and (5) while failing (1), (4) and (6).

## Main results

* `Algebra.FormallyUnramified.tfae_isSeparable_unramified_etale`: for a finitely generated field
  extension `K/k`, the six conditions of Lemma 090W, in the source's order, as one `List.TFAE`.

## Implementation notes

*"Finitely generated field extension" is `Algebra.EssFiniteType k K`.* For fields these agree:
`IntermediateField.fg_top_iff` reads `(⊤ : IntermediateField k K).FG ↔ Algebra.EssFiniteType k K`,
and `(⊤).FG` is exactly `K = k(x₁, …, x_n)` for finitely many `xᵢ`. Note that the source's
hypothesis is strictly weaker than finite generation *as an algebra* (`Algebra.FiniteType`), which
already fails for `k(t)/k`, so `EssFiniteType` and not `FiniteType` is the faithful spelling; it
is also the hypothesis of the Mathlib sibling `Algebra.FormallyUnramified.iff_isSeparable`.

*`Ω[K⁄k] = 0` is `Subsingleton Ω[K⁄k]`.* This is Mathlib's way of saying a module is zero when the
module is not presented as a submodule of anything. Mathlib takes it as the *definition* of
`Algebra.FormallyUnramified` (`Algebra.formallyUnramified_iff`), so the source's `(2) ↔ (3)`,
its Lemma 00UO, holds by unfolding one class; both items are kept so that the statement carries
the whole of the source's lemma and so that either spelling can be quoted from the same chain.

*Unramified and étale are Mathlib's classes, and they are the source's notions.*
`Algebra.Unramified k K` is `Algebra.FormallyUnramified k K` together with
`Algebra.FiniteType k K`, which is Definition 00UT(1) verbatim once `Ω[K⁄k] = 0` is read as formal
unramifiedness. `Algebra.Etale k K` is `Algebra.FormallyEtale k K` together with
`Algebra.FinitePresentation k K`; the source's Definition 00U1 instead asks for finite presentation
with `NL_{K/k}` quasi-isomorphic to zero, and the two agree by the source's own Lemma 00UR. This is
the only item stated in a form other than the source's; the departure is recorded here rather than
avoided, because the formally-étale-plus-finite-presentation form is the one Mathlib's API is
phrased in.

*Item (1) keeps both halves of "finite separable".* `Algebra.IsSeparable k K` alone would be an
equivalent item, since a separable extension is algebraic and
`Algebra.finite_of_essFiniteType_of_isAlgebraic` upgrades that to `Module.Finite k K` under the
hypothesis; carrying `Module.Finite k K` in the item makes finiteness directly available from the
chain, as the source's wording promises.

Faithfulness. (1) No hypothesis is dead: `Algebra.EssFiniteType k K` is used by every implication
into (1), (4) or (6), and dropping it breaks the lemma at `ℚ̄/ℚ` as above. (2) The scalars and base
are the source's: every condition is over the base field `k` itself — `Ω[K⁄k]` is the module of
`k`-differentials, and finiteness, separability, finite type, finite presentation and the four
unramifiedness properties are all relative to `k → K`, never to an intermediate field. (3) No
canonical map needs pinning: all six conditions are properties of the extension `k → K`, and the
one map in sight, the universal derivation `K → Ω[K⁄k]`, is pinned by `KaehlerDifferential`
being the canonical construction. (4) The instantiation is not degenerate: `k = ℚ`, `K = ℚ(√2)`
satisfies all six conditions, while `k = ℚ`, `K = ℚ(t)` satisfies none of them, `Ω[ℚ(t)⁄ℚ]` being
free of rank one.

## References

* [StacksProject 090W](https://stacks.math.columbia.edu/tag/090W)
* [StacksProject 00UO](https://stacks.math.columbia.edu/tag/00UO)
* [StacksProject 00UR](https://stacks.math.columbia.edu/tag/00UR)
* [StacksProject 00UT](https://stacks.math.columbia.edu/tag/00UT)

## Tags

field extension, finitely generated field extension, separable, Kähler differentials, formally
unramified, unramified, formally étale, étale
-/

@[expose] public section

/-- **Stacks 090W.** Let `K/k` be a finitely generated field extension. The following are
equivalent:

1. `K` is a finite separable field extension of `k`;
2. `Ω[K⁄k] = 0`;
3. `K` is formally unramified over `k`;
4. `K` is unramified over `k`;
5. `K` is formally étale over `k`;
6. `K` is étale over `k`. -/
@[stacks 090W "The six items are the entries, in the source's order, of one `List.TFAE`. A
finitely generated field extension is `Algebra.EssFiniteType`, `Ω[K⁄k] = 0` is
`Subsingleton Ω[K⁄k]`, and étale is Mathlib's formally étale plus finite presentation, which is
the source's Definition 00U1 by its Lemma 00UR. See the module docstring.",
  ega "0 21.7.4"
  "more general",
  ega "0 19.10.3" "(iii)",
  ega "IV 17.4.2" "field extension K/k",
  ega "IV 17.4.1" "field extension case",
  ega "IV 17.15.11" "X = Spec of a field",
  sga "1 I 3.1" "(i)<=>(ii), field ext",
  sga "3 XI 1.3" "field extension case",
  ega "0 21.7.4" "more general"]
public theorem Algebra.FormallyUnramified.tfae_isSeparable_unramified_etale
    (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    List.TFAE
      [Module.Finite k K ∧ Algebra.IsSeparable k K,
       Subsingleton Ω[K⁄k],
       Algebra.FormallyUnramified k K,
       Algebra.Unramified k K,
       Algebra.FormallyEtale k K,
       Algebra.Etale k K] := by apply Stacks.Unramified.FieldExtension.solution

end
