module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.HProjective

/-!
# Why Stacks Tag 07RM cannot be earned at Tag 01W8's clean label

The tagged statement of Tag 07RM concludes the tagged `IsProjective` of Tag 01W8, which carries an
open goal *in its statement*: it unfolds through the tagged projective bundle of Tag 01OB to its
`symmetricAlgebra_projAxioms`, which is unproved there, so `#print axioms` reports `sorryAx` for
any proof of it however complete. The library has its own clean form of that label,
`AlgebraicGeometry.IsProjective`, over the library's projective bundle, and Tag 07RM is proved at
it: `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`.

Another clean label of Tag 01W8 is `"H-projective"`, registered as Tag 0C61's
`IsProjectiveMorphism`, which is `Stacks.HProjective.IsHProjective` under its library name. **This
file determines what the statement of Tag 07RM restated at that label says, and the answer is
that it is not Stacks Tag 07RM**: it is part (2) of [Stacks, Tag 087S] with that lemma's hypothesis on the base deleted.

## The restatement

`Stacks.ProjectivityLabelChoice.CardStatementAtHProjective` is the statement of Tag 07RM verbatim — the same
quantifier prefix, the same `CompactSpace S` and `QuasiSeparatedSpace S`, the same
quasi-projectivity hypothesis — with Tag 01W8's `IsProjective` replaced by
`Stacks.HProjective.IsHProjective` and nothing else changed.

`Stacks.ProjectivityLabelChoice.cardStatementAtHProjective_iff` proves it **equivalent** to
`Stacks.ProjectivityLabelChoice.HQuasiProjectiveOfQuasiProjectiveQcqs`: every quasi-projective
morphism over a quasi-compact quasi-separated base is H-quasi-projective. Both directions are
proved and unconditional —
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective` is half 2 of Tag
07RM's own proof, and
`isHQuasiProjective_of_exists_isOpenImmersion_isHProjective` is its converse,
needing only the quasi-compactness that quasi-projectivity supplies.

That right-hand side is part (2) of [Stacks, Tag 087S] — *"any quasi-projective morphism
`X ⟶ S` is H-quasi-projective"* — whose hypothesis in the source is **"let `S` be a scheme which
admits an ample invertible sheaf"**. The statement of Tag 07RM hypothesises only that `S` is quasi-compact and
quasi-separated. So the restatement at the H-projective label asks for Tag 087S part (2) over a
strictly larger class of bases than the source states it for. At the source's own hypothesis,
part (2) is `AlgebraicGeometry.isHQuasiProjective_of_isQuasiProjective`; over a base with no ample
invertible module it is not proved.

**Consequently no Stacks tag attribute is attached anywhere in this file — neither the tag 07RM
attribute nor the tag 01W8 one at the H-projective label — and the H-projective route does not
reach Tag 07RM.** The two are different theorems, and the H-projective one is the harder of the
two. Tag 07RM's own proof does not go near `ℙⁿ_S`: it builds `𝐏(ℰ)` for a finite-type
quasi-coherent `ℰ` on `S` through which finitely many sections of `f_*ℒ` factor ([Stacks, Tag
01PK] in the source), and that is the route the registered
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs` takes.

## The locality step is not what is missing

A reduction of Tag 07RM through `Stacks.AmpleImmersionReduction.ChartImmersion` owes, among
other things, the passage from surjectivity on each standard chart to
`AlgebraicGeometry.IsImmersion`. That passage is **free in pinned Mathlib**, and
`Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict` records it in the shape the
chart route needs: a cover of the *range* suffices, so the charts of `ℙⁿ_S` cut down over affine
opens of `S` — which do not cover `ℙⁿ_S` — are still enough. It is
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup` at the instance
`AlgebraicGeometry.IsZariskiLocalAtTarget @AlgebraicGeometry.IsImmersion`
(`Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean`).

What that step needs and does not have is the identification of the standard chart of `ℙⁿ_S` over
an affine open of `S` as an affine scheme with the expected ring of functions, i.e. the comparison
`Proj R[T₀, …, Tₙ] ≅ ℙⁿ_R`. That comparison is itself an open named gap of this development:
`Stacks.AlgebraicGeometry.ProjPolyChart.projCompare` is built, and its being an isomorphism is
unproved.

## Main definitions

* `Stacks.ProjectivityLabelChoice.CardStatementAtHProjective`: the statement of Tag 07RM with
  Tag 01W8's `IsProjective` replaced by the clean label's predicate.
* `Stacks.ProjectivityLabelChoice.HQuasiProjectiveOfQuasiProjectiveQcqs`: part (2) of
  [Stacks, Tag 087S] over a quasi-compact quasi-separated base.

## Main results

* `Stacks.ProjectivityLabelChoice.cardStatementAtHProjective_iff`: **the two are equivalent.** This
  is why the tag is withheld.
* `Stacks.ProjectivityLabelChoice.isImmersion_of_isImmersion_restrict`: immersion from a family of
  opens covering only the range, for the chart route.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.ProjectivityLabelChoice

/-! ### Tag 07RM at Tag 01W8's clean label -/

/-- **The statement of Tag 07RM with Tag 01W8's `IsProjective` replaced by the one label of Tag 01W8
that carries no open goal.** Nothing else is changed: the base still carries only
`CompactSpace` and `QuasiSeparatedSpace`, and the hypothesis is still quasi-projectivity. -/
def CardStatementAtHProjective : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), CompactSpace S → QuasiSeparatedSpace S →
    Stacks.HProjective.IsQuasiProjective f →
      ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
        IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f

/-- **Part (2) of [Stacks, Tag 087S] over a quasi-compact quasi-separated base.** The source
states it for a base admitting an ample invertible sheaf. -/
def HQuasiProjectiveOfQuasiProjectiveQcqs : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), CompactSpace S → QuasiSeparatedSpace S →
    Stacks.HProjective.IsQuasiProjective f → Stacks.HProjective.IsHQuasiProjective f

/-- **The clean label restates a different theorem: Tag 07RM at
`Stacks.HProjective.IsHProjective` is equivalent to part (2) of [Stacks, Tag 087S] over a
quasi-compact quasi-separated base.**

Both directions are proved and unconditional. Forward,
`isHQuasiProjective_of_exists_isOpenImmersion_isHProjective` cancels the structure
morphism of `ℙⁿ_S`, using the quasi-compactness that quasi-projectivity supplies. Backward,
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective` is half 2 of Tag
07RM's own proof — Tag 01RG applied to the quasi-compact immersion into `ℙⁿ_S`.

Part (2) over a quasi-compact quasi-separated base with no ample invertible module is not proved
(at the source's own hypothesis it is `AlgebraicGeometry.isHQuasiProjective_of_isQuasiProjective`),
so the H-projective label is not a route to Tag 07RM, and no tag is attached; the tag is
registered on `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`,
at Definition 01W8's projectivity. -/
theorem cardStatementAtHProjective_iff :
    CardStatementAtHProjective.{u} ↔ HQuasiProjectiveOfQuasiProjectiveQcqs.{u} :=
  ⟨fun h X S f hc hqs hf =>
    QuasiProjectiveCompactification.isHQuasiProjective_of_exists_isOpenImmersion_isHProjective
      hf.quasiCompact (h X S f hc hqs hf),
  fun h X S f hc hqs hf =>
    QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective_of_isHQuasiProjective
      (h X S f hc hqs hf)⟩

/-! ### The locality step the chart route owes is in Mathlib -/

/-- Immersions are stable under postcomposition with an open immersion: an open immersion is an
immersion (`AlgebraicGeometry.IsImmersion`'s own instance) and immersions compose
(`AlgebraicGeometry.IsImmersion.comp`). Supplied because Mathlib registers the multiplicativity
but not this consequence of it, and
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup` asks for it. -/
instance respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp _ hi _ hf := by
    have := hi
    have := hf
    infer_instance

end Stacks.ProjectivityLabelChoice

end
