module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SchemeIsReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.Deformation.ToposThickening.ObstructionIX.DoubledOriginDatum

/-!
# Stacks 03K0 is false as stated: the counterexample, with nothing assumed

`AlgebraicGeometry.Space.isEmpty_directedApproximation_of_not_isAbsolutelyQuasiSeparated` of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation` says that a
quasi-compact scheme which is not quasi-separated carries no directed approximation in the
sense of Stacks 03K0 — that is, none with clause (1) in the form the source states it, over
every quasi-compact test scheme. This module exhibits such a scheme and so turns that
conditional statement into a counterexample which assumes nothing: `03K0` has a quasi-compact
reasonable algebraic space among its hypotheses for which its conclusion is unattainable.

## Main results

* `AlgebraicGeometry.Space.not_isAbsolutelyQuasiSeparated_yoneda_doubledOrigin`: the
  doubled-origin scheme, viewed on a big fppf site that contains it, is not a quasi-separated
  algebraic space.
* `AlgebraicGeometry.Space.isEmpty_directedApproximation_doubledOrigin`: it carries no directed
  approximation in the source's sense.
* `AlgebraicGeometry.Space.exists_quasiCompact_reasonable_isEmpty_directedApproximation`:
  **the refutation of Stacks 03K0 as stated.** There exist a big fppf site and a sheaf on it
  which is an algebraic space, quasi-compact, reasonable and representable — every hypothesis
  of 03K0, and no separation hypothesis, which 03K0 does not make — carrying no directed
  approximation. The big fppf site is produced inside the proof, so nothing is hypothesised.

## The witness

Stacks Example 01KL: two copies of `Spec k[t₀, t₁, t₂, …]` glued along the complement of the
origin, `AlgebraicGeometry.doubledOriginDatum`. It is quasi-compact because its two charts
cover it (`AlgebraicGeometry.compactSpace_scheme`) and it is not quasi-separated because the
intersection of those two charts is the punctured spectrum, which is not quasi-compact
(`AlgebraicGeometry.not_quasiSeparatedSpace_scheme`). It is a reasonable algebraic space for no
reason beyond being a scheme: `AlgebraicGeometry.Space.isReasonableSpace_yoneda`, which is the
composite `(θ) ⇒ (ζ) ⇒ (ε) ⇒ (δ)` of the diagram of Stacks 03JX.

Those three inputs are theorems here, so the refutation below assumes nothing; in particular it
is not conditional on assertions of the Stacks Project.

## Implementation notes

The base scheme is the terminal one, over which the absolute separation conditions of
Stacks 03BS are stated; `AlgebraicGeometry.BigFppfSite.contains_terminal` discharges the
containment hypothesis for every big fppf site, and
`AlgebraicGeometry.BigFppfSite.exists_contains` produces a site containing the doubled-origin
scheme, so the final statement quantifies over nothing.

The step from absolute quasi-separatedness of the represented presheaf back to
quasi-separatedness of the underlying scheme — the arrow `(η) ∧ (θ) ⇒ (ι)` of Stacks 03JX — is
the forward direction of
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace`.

## References

* [Stacks Project, Tag 03K0](https://stacks.math.columbia.edu/tag/03K0)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 01KL](https://stacks.math.columbia.edu/tag/01KL)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {k : Type u} [Field k] (D : DoubledOriginData k) (B : BigFppfSite.{u})
    (hD : B.Contains D.scheme)

/-- The doubled-origin scheme as an object of a big fppf site over the terminal scheme. -/
noncomputable def doubledOriginObj :
    BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  BigFppfOver.mk B _ B.contains_terminal hD (terminal.from D.scheme)

/-- The presheaf represented by the doubled-origin scheme is a sheaf for the big fppf topology,
because that topology is subcanonical. -/
noncomputable def doubledOriginSheaf :
    Sheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) B.contains_terminal) (Type u) :=
  ⟨yoneda.obj (doubledOriginObj D B hD),
    BigFppfOver.isSheaf_yoneda_obj B _ B.contains_terminal _⟩

/-- The doubled-origin scheme represents its sheaf, by construction. -/
theorem isRepresentable_doubledOriginSheaf :
    (doubledOriginSheaf D B hD).obj.IsRepresentable :=
  ⟨⟨doubledOriginObj D B hD, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩⟩

/-- The doubled-origin scheme is an algebraic space over the terminal scheme: it is
representable, and Stacks 02X0 makes every representable presheaf on the big fppf site an
algebraic space. -/
theorem isAlgebraicSpace_doubledOrigin :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal (doubledOriginSheaf D B hD).obj :=
  isAlgebraicSpace_yoneda B _ B.contains_terminal _

/-- **The doubled-origin scheme is quasi-compact**, by
`AlgebraicGeometry.compactSpace_scheme`: its two affine charts cover it. -/
theorem isQuasiCompactSpace_doubledOrigin :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal
      (doubledOriginSheaf D B hD).obj :=
  isQuasiCompactSpace_yoneda_obj B _ B.contains_terminal (compactSpace_scheme D)

/-- **The doubled-origin scheme is a reasonable algebraic space**, by Stacks 03JX
`(θ) ⇒ (δ)`: it is a scheme, and that alone suffices — no separation hypothesis is involved,
which is the whole point, since the scheme is not quasi-separated. -/
theorem isReasonableSpace_doubledOrigin :
    IsReasonableSpace B (⊤_ Scheme.{u}) B.contains_terminal (doubledOriginSheaf D B hD).obj :=
  isReasonableSpace_yoneda B _ B.contains_terminal _

/-- **The doubled-origin scheme is not a quasi-separated algebraic space.** Absolute
quasi-separatedness of a represented presheaf is quasi-separatedness of the underlying scheme
by the arrow `(η) ∧ (θ) ⇒ (ι)` of Stacks 03JX, and the doubled-origin scheme is not a
quasi-separated space: the intersection of its two affine charts is the punctured spectrum of
`k[t₀, t₁, t₂, …]`, which is not quasi-compact. -/
theorem not_isAbsolutelyQuasiSeparated_yoneda_doubledOrigin :
    ¬ IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal
      (doubledOriginSheaf D B hD).obj := fun h ↦
  not_quasiSeparatedSpace_scheme D
    ((isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B _ B.contains_terminal
      B.contains_terminal (doubledOriginObj D B hD)).1 h)

/-- **The doubled-origin scheme carries no directed approximation in the sense of
Stacks 03K0.** It satisfies every hypothesis of that lemma — it is a quasi-compact reasonable
algebraic space over the terminal scheme — and clause (1) of its conclusion, as the source
states it over every quasi-compact test scheme, would force it to be quasi-separated, which it
is not. -/
theorem isEmpty_directedApproximation_doubledOrigin :
    IsEmpty (DirectedApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal
      (doubledOriginSheaf D B hD)) :=
  have _ := isRepresentable_doubledOriginSheaf D B hD
  isEmpty_directedApproximation_of_not_isAbsolutelyQuasiSeparated B _ B.contains_terminal
    B.contains_terminal _ (isQuasiCompactSpace_doubledOrigin D B hD)
    (not_isAbsolutelyQuasiSeparated_yoneda_doubledOrigin D B hD)

/-- **Stacks 03K0 is false as stated.** There are a big fppf site, a scheme over its terminal
object, and no hypotheses at all, for which the lemma's hypotheses hold and its conclusion
fails: the represented sheaf is an algebraic space, representable, quasi-compact and
reasonable, and it carries no directed system of quasi-compact quasi-separated algebraic
spaces with the three clauses of 03K0, because clause (1) over every quasi-compact test scheme
forces quasi-separatedness of the space itself — a hypothesis 03K0 does not make.

The witness is the doubled-origin scheme of Example 01KL, and the three facts about it that the
refutation needs are proved in this library: quasi-compactness
(`AlgebraicGeometry.compactSpace_scheme`), failure of quasi-separatedness
(`AlgebraicGeometry.not_quasiSeparatedSpace_scheme`) and reasonableness
(`AlgebraicGeometry.Space.isReasonableSpace_yoneda`, the composite `(θ) ⇒ (δ)` of Stacks 03JX).

The repair supported by the source's own proof is
`AlgebraicGeometry.Space.exists_correctedDirectedApproximation`, whose clause (1) quantifies
over test schemes that are quasi-compact *and quasi-separated*; it holds for every
quasi-compact reasonable algebraic space, this one included. -/
@[stacks 03K0 "refutation of clause (1) as stated, assuming nothing: the doubled-origin scheme \
of Example 01KL is a quasi-compact reasonable algebraic space with no such system"]
theorem exists_quasiCompact_reasonable_isEmpty_directedApproximation (k : Type u) [Field k] :
    ∃ (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))
      (X : Sheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u))
      (_ : X.obj.IsRepresentable),
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X.obj ∧
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X.obj ∧
      IsReasonableSpace B (⊤_ Scheme.{u}) hZ X.obj ∧
      IsEmpty (DirectedApproximation B (⊤_ Scheme.{u}) hZ hZ X) := by
  obtain ⟨B, hD⟩ := BigFppfSite.exists_contains (doubledOriginDatum k).scheme
  refine ⟨B, B.contains_terminal, doubledOriginSheaf (doubledOriginDatum k) B hD,
    isRepresentable_doubledOriginSheaf _ B hD,
    isAlgebraicSpace_doubledOrigin _ B hD, isQuasiCompactSpace_doubledOrigin _ B hD,
    isReasonableSpace_doubledOrigin _ B hD, isEmpty_directedApproximation_doubledOrigin _ B hD⟩

end AlgebraicGeometry.Space

end
