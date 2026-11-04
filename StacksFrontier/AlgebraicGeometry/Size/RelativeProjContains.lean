module

public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Proj
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Relative `Proj` lies in the big fppf site, under a uniform bound on its sections

Let `S` be a scheme of a big fppf site `B` and `A` a quasi-coherent graded `𝒪_S`-algebra. If a
*single* cardinal `c` below `B.cutoff` bounds the graded ring of homogeneous sections
`A.sectionRing U` for every affine open `U` of `S`, then the relative projective spectrum
`Proj_S(A)` is itself a scheme of `B`.

This is the size side condition that Stacks tag 084B rests on: the functor of Situation 0849 is
an algebraic space over `B` only if the relative `Proj` representing it is an object of `B`, and
no hypothesis on universes alone gives that — the cutoff of a big fppf site is an arbitrary
strong prelimit above `ℵ₀`, in general far below the ambient universe.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjSize.contains_proj_sectionRing`: `Proj` over an in-site
  affine piece lies in the site.
* `Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj`: the glued relative `Proj`
  lies in the site.
* `Stacks.AlgebraicGeometry.RelativeProjSize.contains_pullback_relativeProj`: and so does every
  pullback of it along a morphism from a scheme of the site.

## Implementation notes

**The bound is a hypothesis, and it has to be uniform.** A bound
`Cardinal.mk (A.sectionRing U) < B.cutoff` imposed on each affine `U` separately would not do.
The cutoff of a big fppf site is a strong prelimit of uncountable cofinality but need *not* be
regular, so a supremum of fewer than `B.cutoff` cardinals each below `B.cutoff` can equal
`B.cutoff`, while the base may have as many as `B.cutoff.ord.cof` affine opens; assembling the
charts over a cover indexed by them therefore needs one cardinal that bounds them all.
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` is exactly the assembly step
that consumes such a cardinal, and it has no cofinality side condition for that reason.

Whether this uniform bound should instead become a *field* of the Situation 0849 datum — so
that the statements below become unconditional — is a question about faithfulness to the source
and is **open**; nothing here presumes an answer, and no `@[stacks]` attribute is attached.
What is settled is that the bound cannot be dropped: Tag 084B is false without it, by the
example of `Proj k[x_i : i ∈ I]` with `#I ≥ B.cutoff` over `S = Spec k`, whose charts have rings
of functions of cardinality at least `B.cutoff`.

**No power of `c` is needed.** One might expect the covering estimate to cost a power `c ^ c`,
bounded below the cutoff by the strong prelimit property. It does not: with `c` bounding the
section *ring* over every affine open, `AlgebraicGeometry.Scheme.size_Proj_le` bounds each chart
by `max ℵ₀ c` directly, the number of charts is at most `S.size`, and
`max S.size (max ℵ₀ c)` is already below the cutoff. So only
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` is used below — not
`Cardinal.IsStrongPrelimit`, and not the uncountable cofinality of the cutoff. A power is spent
only in the *other* step, which turns degreewise bounds on the homogeneous pieces into a bound
on the section ring, and that step is not performed here: the hypothesis `hsec` is already a
bound on the section ring.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public section

open AlgebraicGeometry Cardinal CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjFlat
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjSize

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **`Proj` over an in-site affine piece lies in the site** (Tags 000P, 000Q, 000R (9)). If the
graded ring of homogeneous sections of a quasi-coherent graded `𝒪_S`-algebra over an affine open
`U` has fewer than `B.cutoff` elements, then the projective spectrum of that ring is itself a
scheme of `B`.

This is `AlgebraicGeometry.BigFppfSite.contains_Proj` for the section ring: both the number of
charts of `Proj (A.grading U)` and each chart's ring of functions are bounded by the single
cardinal `Cardinal.mk (A.sectionRing U)`.

The statement-of-record for this step additionally carries a containment of the base and an
affineness hypothesis on `U`. Neither is needed and so neither is assumed: the estimate is in
the section ring alone, and it is `Cardinal.mk (A.sectionRing U)` that must be below the cutoff
whatever `U` is. The form below therefore applies wherever that one would. -/
theorem contains_proj_sectionRing {U : S.Opens}
    (hsec : Cardinal.mk (A.sectionRing U) < B.cutoff) :
    B.Contains (AlgebraicGeometry.Proj (A.grading U)) :=
  B.contains_Proj (A.grading U) hsec

/-- **Relative `Proj` lies in the site** (Tags 000P, 000Q, 000R (9)). If the base is a scheme of
`B` and a single cardinal `c` below `B.cutoff` bounds the graded section rings over all of its
affine opens, then the relative projective spectrum of a quasi-coherent graded `𝒪_S`-algebra is a
scheme of `B`.

It is covered by the charts of `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart`
(`Stacks.AlgebraicGeometry.RelativeProjFlat.chartCover`), indexed by the affine opens of the
base, of which there are at most `S.size < B.cutoff`; and each chart is
`Proj (A.grading U)`, of size at most `max ℵ₀ c` by
`AlgebraicGeometry.Scheme.size_Proj_le` applied with that one cardinal. So
`max S.size (max ℵ₀ c)` bounds the whole cover and
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` concludes.

The uniformity of `c` is what makes this work over an index set — the affine opens of `S` — of
uncontrolled cofinality; see the module docstring, which also records that whether `c` should
become a field of the Situation 0849 datum is an open question, and that no power of `c` is
spent here. -/
theorem contains_relativeProj (hbase : B.Contains S) {c : Cardinal.{u}} (hc : c < B.cutoff)
    (hsec : ∀ U : S.Opens, IsAffineOpen U → Cardinal.mk (A.sectionRing U) ≤ c) :
    B.Contains (relativeProj A).scheme := by
  have : Nonempty S.affineOpens := ⟨⟨⊥, isAffineOpen_bot S⟩⟩
  have : ∀ U : S.affineOpens, IsOpenImmersion ((relativeProj A).chart U.1 U.2) :=
    fun U => isOpenImmersion_chart (relativeProj A) U.1 U.2
  refine B.contains_of_openCover_of_size_le (μ := max S.size (max ℵ₀ c))
    (max_lt hbase (max_lt B.aleph0_lt_cutoff hc))
    (S.mk_affineOpens_le_size.trans (le_max_left _ _))
    (fun U : S.affineOpens => (relativeProj A).chart U.1 U.2)
    (fun x => ⟨(chartCover A (relativeProj A)).idx x,
      (chartCover A (relativeProj A)).covers x⟩)
    fun U => ?_
  exact ((Scheme.size_Proj_le (A.grading U.1)).trans
    (max_le_max le_rfl (hsec U.1 U.2))).trans (le_max_right _ _)

/-- **Stacks 000R (1).** The fibre product of the relative `Proj` with any scheme of the site
over the base is again a scheme of the site: relative `Proj` and *its pullbacks* lie in `B`.
Unlike `Stacks.AlgebraicGeometry.RelativeProjSize.contains_relativeProj`, this needs nothing of
the cutoff beyond what that statement already uses, the fibre-product closure of the cutoff
being available. -/
theorem contains_pullback_relativeProj (hbase : B.Contains S) {c : Cardinal.{u}}
    (hc : c < B.cutoff)
    (hsec : ∀ U : S.Opens, IsAffineOpen U → Cardinal.mk (A.sectionRing U) ≤ c)
    {Z : Scheme.{u}} (hZ : B.Contains Z) (g : Z ⟶ S) :
    B.Contains (CategoryTheory.Limits.pullback g (relativeProj A).toBase) :=
  Scheme.size_pullback_lt g (relativeProj A).toBase hZ
    (contains_relativeProj B A hbase hc hsec)

end Stacks.AlgebraicGeometry.RelativeProjSize

end
