module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartComparison
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartTransRestrict
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartTransSpec
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCompatible

/-!
# A glueing datum for the determinant of a two-term perfect complex

Let `X` be a scheme and let `L` be a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`.
Every affine open `V` of `X` carries the determinant
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` of `L` there, and for an inclusion `V ≤ W` of
affine opens `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` identifies the
determinant on `V` with the restriction along `V ⟶ W` of the determinant on `W`. This file
assembles those into a glueing datum
`AlgebraicGeometry.AffineOpensGlue.ChartComparison` for `X`, whose family of modules is
`chartDet L` and whose comparisons are
`AlgebraicGeometry.DeterminantTwoTerm.chartDetComp`, and whose cocycle condition is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_trans`. The sheaf of modules it glues
to is an invertible module on `X`: that is the determinant of `L` on `X`.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartTheta`: the family of restriction isomorphisms of
  the determinant along the inclusions of affine opens, named so that the glueing datum and its
  cocycle condition speak of one fixed term.
* `AlgebraicGeometry.DeterminantTwoTerm.chartComparisonOfTheta`: **the glueing datum for the
  determinant built from an arbitrary family of restriction isomorphisms** satisfying the cocycle
  condition. Every reconciliation this file needs happens in this declaration, where the family
  is a variable.
* `AlgebraicGeometry.DeterminantTwoTerm.chartComparison`: **the glueing datum of the
  determinant**, the previous definition at `chartTheta`. It takes no hypothesis.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartTheta_trans`: the cocycle condition for
  `chartTheta`, which is `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_trans` fed by
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso_trans`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartComparison_mod` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartComparison_comp`: the datum is the determinant —
  its family of modules is `chartDet L` and its comparisons are `chartDetComp L`, both by
  definitional unfolding.
* `AlgebraicGeometry.DeterminantTwoTerm.isInvertibleModule_chartComparison_glued`: **the glued
  sheaf of modules is invertible**, because each `chartDet L V` is.

## Implementation notes

**The kernel diagnosis, and the pattern that defeated it.** The next files in this development
will meet the same wall, so it is recorded in full.

`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` contains
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` at
`AlgebraicGeometry.DeterminantTwoTerm.isoSpec_hom_specMap_chartRestriction`, and
`pullbackCongr hf` is `CategoryTheory.eqToIso` of a transported `rfl`. The two sides of that
equality are not syntactically equal, so the transport can never iota-reduce, and any kernel
defeq check that has to look inside it fails to terminate within the budget — reported as
`(kernel) deterministic timeout`, and no elaborator option that would raise the budget may be
used in this repository. This is the obstruction already recorded in
`StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartNaturalSheaf` and
`StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartTransSpec`.

What is new here, and is the whole reason for the shape of this file, is **where** that cost is
paid: not in any proof, but in *elaborating the cocycle condition at the determinant's own
family a second time*. In any spelling of it — through `chartDetRestrictIso`, through
`chartTheta`, or through `AlgebraicGeometry.AffineOpensGlue.compOfRestrictIso` — the condition is
accepted as the type of a *theorem* and refused in the type of a *definition*. On
one and the same cocycle:

* `theorem f (hθ : <the cocycle>) : True := trivial` checks in seconds, and so does
  `chartTheta_trans`, whose type *is* the cocycle;
* `def f (hθ : <the same cocycle>) : Nat := 0` fails with `(kernel) deterministic timeout`, and
  so does every definition carrying such a binder, whatever its body — including the glueing
  datum built that way, and `AffineOpensGlue.ofRestrictIso` applied to the determinant's family;
* supplying the cocycle to the datum as a *lambda*,
  `fun _ _ _ h h' => chartDetRestrictIso_trans L h h' (chartDetSpecPullbackIso_trans L h h')`,
  fails as well: the elaborator abstracts the lambda into an auxiliary proof whose statement is
  the cocycle, elaborated again;
* supplying it as the *named theorem* `chartTheta_trans L` checks in seconds.

Instantiating a definition whose family is a variable is likewise fine:
`chartComparisonOfTheta L (chartTheta L)` checks, and a dump of its cocycle binder against the
written-out one under `pp.explicit`, `pp.universes` and `pp.proofs` is byte-identical — so the
difference is in nothing the pretty printer shows, and the rule is about elaboration, not about
the mathematics.

The pattern is therefore: **state the structure once with the family a variable, prove the
cocycle condition once as a named theorem, and let the two meet only as constants.**
`chartComparisonOfTheta` holds the whole construction with `θ` a variable, where the comparisons
are `AlgebraicGeometry.AffineOpensGlue.compOfRestrictIso` and the cocycle field is the pointwise
`AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso_at` — pointwise because the
universally quantified `comp_trans_of_restrictIso` cannot be instantiated at the determinant's
family either, and with the inequality of `AlgebraicGeometry.restrictLocal` spelled as the
`comp_trans` field spells it, so that the field is a plain application. `chartComparison` is then
that definition applied to the two constants `chartTheta L` and `chartTheta_trans L`, and no
declaration in this file carries the cocycle condition as a hypothesis.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The restriction isomorphisms of the determinant along the inclusions of affine opens**, as
one named family: for affine opens `V ≤ W` of `X`, the determinant of `L` on `V` is the
restriction along `V ⟶ W` of the determinant of `L` on `W`.

This is `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` with the inclusion of the
underlying opens spelled as `AlgebraicGeometry.AffineOpensGlue.coe_le_coe`, which is the spelling
the glueing machinery of
`StacksFrontier/AlgebraicGeometry/RestrictPushforwardCoherence.lean` uses; the two inequalities are
proofs of the same proposition. Naming the family is what lets the glueing datum and its cocycle
condition speak of one fixed term. -/
def chartTheta (L : PerfectTwoTermAmplitude X) (V W : X.affineOpens) (h : V ≤ W) :
    chartDet L V ≅ Scheme.Modules.restrict (chartDet L W)
      (X.homOfLE (AffineOpensGlue.coe_le_coe h)) :=
  chartDetRestrictIso L h

/-- **The glueing datum of the determinant, built from an arbitrary family of restriction
isomorphisms.** Given, for each inclusion `V ≤ W` of affine opens of `X`, an isomorphism of the
determinant of `L` on `V` with the restriction along `V ⟶ W` of the determinant of `L` on `W`,
and the cocycle condition for that family along a chain of two inclusions — modulo the coherence
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso` of the restriction functors — the
determinants on the affine opens form a glueing datum
`AlgebraicGeometry.AffineOpensGlue.ChartComparison`.

The comparison attached to an inclusion is
`AlgebraicGeometry.AffineOpensGlue.compOfRestrictIso`, which peels the two pushforwards off, and
the cocycle field is `AlgebraicGeometry.AffineOpensGlue.comp_trans_of_restrictIso_at` at the
chain in question.

The family `θ` is a variable on purpose: this is the one declaration of this file in which the
comparisons have to be reconciled with the fields of
`AlgebraicGeometry.AffineOpensGlue.ChartComparison`, and at a variable family that reconciliation
is free. See the implementation notes. -/
def chartComparisonOfTheta (L : PerfectTwoTermAmplitude X)
    (θ : ∀ (V W : X.affineOpens) (h : V ≤ W),
      chartDet L V ≅ Scheme.Modules.restrict (chartDet L W)
        (X.homOfLE (AffineOpensGlue.coe_le_coe h)))
    (hθ : ∀ (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W),
      (θ V V' h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
            (θ V' W h').hom ≫
          (AffineOpensGlue.restrictFunctorTransIso (AffineOpensGlue.coe_le_coe h)
            (AffineOpensGlue.coe_le_coe h')
            (AffineOpensGlue.coe_le_coe (h.trans h'))).hom.app (chartDet L W) =
        (θ V W (h.trans h')).hom) :
    AffineOpensGlue.ChartComparison X where
  mod := chartDet L
  comp := fun {V W} h => AffineOpensGlue.compOfRestrictIso (chartDet L) θ V W h
  comp_trans := fun {V V' W} h h' =>
    AffineOpensGlue.comp_trans_of_restrictIso_at (chartDet L) θ V V' W h h' (hθ V V' W h h')

/-- **The cocycle condition for the restriction isomorphisms of the determinant.** Along a chain
`V ≤ V' ≤ W` of inclusions of affine opens of `X`, restricting the determinant from `W` to `V'`
and then to `V` agrees with restricting it from `W` to `V` in one step, read through the coherence
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso` of the restriction functors.

This is `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_trans` fed by
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso_trans`, the same statement on the
spectra. It is stated as a named theorem rather than passed to
`AlgebraicGeometry.DeterminantTwoTerm.chartComparisonOfTheta` as a lambda because that is what
the kernel will pay for; see the implementation notes. -/
theorem chartTheta_trans (L : PerfectTwoTermAmplitude X) :
    ∀ (V V' W : X.affineOpens) (h : V ≤ V') (h' : V' ≤ W),
      (chartTheta L V V' h).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
            (chartTheta L V' W h').hom ≫
          (AffineOpensGlue.restrictFunctorTransIso (AffineOpensGlue.coe_le_coe h)
            (AffineOpensGlue.coe_le_coe h')
            (AffineOpensGlue.coe_le_coe (h.trans h'))).hom.app (chartDet L W) =
        (chartTheta L V W (h.trans h')).hom :=
  fun _ _ _ h h' => chartDetRestrictIso_trans L h h' (chartDetSpecPullbackIso_trans L h h')

/-- **The glueing datum of the determinant of a two-term perfect complex.** The determinants of
`L` on the affine opens of `X`, together with the restriction isomorphisms
`AlgebraicGeometry.DeterminantTwoTerm.chartTheta` along the inclusions and the cocycle condition
`AlgebraicGeometry.DeterminantTwoTerm.chartTheta_trans` for them, form a glueing datum
`AlgebraicGeometry.AffineOpensGlue.ChartComparison` for `X`.

Its family of modules is `AlgebraicGeometry.DeterminantTwoTerm.chartDet` and its comparisons are
`AlgebraicGeometry.DeterminantTwoTerm.chartDetComp`, by
`AlgebraicGeometry.DeterminantTwoTerm.chartComparison_mod` and
`chartComparison_comp`; the sheaf of modules it glues to is the determinant of `L` on `X`, and it
is invertible by
`AlgebraicGeometry.DeterminantTwoTerm.isInvertibleModule_chartComparison_glued`. -/
def chartComparison (L : PerfectTwoTermAmplitude X) : AffineOpensGlue.ChartComparison X :=
  chartComparisonOfTheta L (chartTheta L) (chartTheta_trans L)

/-- The glueing datum of the determinant has the determinant on each affine open as its member
there. -/
theorem chartComparison_mod (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    (chartComparison L).mod V = chartDet L V :=
  rfl

/-- **The comparisons of the glueing datum of the determinant are
`AlgebraicGeometry.DeterminantTwoTerm.chartDetComp`.** Both are the two peeling isomorphisms with
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` in the middle; the peeling
isomorphisms of `StacksFrontier/AlgebraicGeometry/RestrictPushforwardCoherence.lean` and of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermChartComparison.lean` have the same bodies, so
this holds by unfolding. -/
theorem chartComparison_comp (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    (chartComparison L).comp h = chartDetComp L h :=
  rfl

/-- **The sheaf of modules glued from the determinants on the affine opens is invertible.**
Invertibility is local on `X` and the determinant on each affine open is invertible by
`AlgebraicGeometry.DeterminantTwoTerm.isInvertibleModule_chartDet`, so
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.isInvertibleModule_glued` applies. This
sheaf of modules is the determinant of `L` on `X`. -/
theorem isInvertibleModule_chartComparison_glued (L : PerfectTwoTermAmplitude X) :
    Stacks.Ample.IsInvertibleModule X (chartComparison L).glued :=
  (chartComparison L).isInvertibleModule_glued (isInvertibleModule_chartDet L)

end AlgebraicGeometry.DeterminantTwoTerm

end
