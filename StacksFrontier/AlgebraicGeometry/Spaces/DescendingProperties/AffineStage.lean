module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage.SpecGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage.ChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage.ExistsAffineStage

/-!
# An affine limit of algebraic spaces has an affine stage

Let `X = lim_i X_i` be a directed inverse limit of quasi-compact and quasi-separated algebraic
spaces over `S` with affine transition morphisms, the situation of Stacks 084R. If `X` is an
affine algebraic space then so is `X_i` for some `i` at or beyond the distinguished index. This
is **Stacks 07SQ**, and it is proved here.

**Stacks 0A0R** is then immediate and is recorded at the end of the file: if the system lies
over a quasi-compact and quasi-separated algebraic space `Y` and `X ⟶ Y` is affine, then
`X_i ⟶ Y` is affine for all `i` large enough. The whole of that argument except its appeal to
Stacks 07SQ is carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineOverBaseDescent.lean`, which
this file imports; the appeal is discharged here, where Stacks 07SQ is available.

The proof is the source's. Over a terminal base, an affine étale surjective chart `U₀ ⟶ X₀` of
the distinguished stage base changes to a system of affine charts `U_i` of the stages whose
limit `U` is an affine étale surjective chart of `X`; so the regular functions on `U` form an
étale algebra with surjective spectrum over a `u`-model `A` of `Γ(X, 𝒪_X)`. The ring of global
functions of the limit is the filtered colimit of those of the stages — Stacks 07SI for the
structure sheaf — so the commutative-algebra core
`MvPolynomial.exists_ge_etale_surjective_quotient_of_directed` presents that algebra by a square
family of polynomials over the model `A_j` of a stage, étale and with surjective spectrum
already there. Its coordinates and the relations they satisfy descend to a stage `m`, and that
is the data of display 70.5.10.1 — the square of Stacks 084U. Over the limit that square is
Cartesian, because its two horizontal edges are isomorphisms there and the presentation base
changes; so Stacks 084S makes the morphism of the display an isomorphism at some stage `k`, and
there the étale covering `Spec A_m[x]/(g) ⟶ Spec A_m` descends affineness of `X_k ⟶ Spec A_m` by
Stacks 03WG. The source of an affine morphism with affine target is affine.

## Main results

* `AlgebraicGeometry.Space.etale_globalFunctionsChartRestriction`: restriction of global
  functions to an affine surjective étale chart of an affine algebraic space over a terminal
  base is étale with surjective spectrum. This is the geometric input of the core.
* `AlgebraicGeometry.Space.exists_isIso_specMapOfGlobalHom_of_isAffineSpace`: over a terminal
  base, the canonical morphism of Stacks 05Z1 from an affine algebraic space to the functor of
  points of the spectrum of a model of its global functions is an isomorphism, with its chart
  formula.
* `AlgebraicGeometry.Space.DescentSituation.exists_ge_eval₂_map_eq_zero`: the coordinates and
  the relations of a presentation over the limit descend to a single stage.
* `AlgebraicGeometry.Space.DescentSituation.isPullback_toLimit_coordinateHom`: the square of
  Stacks 084U is Cartesian over the limit.
* `AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj`: **Stacks 07SQ**.
* `AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app`: **Stacks 0A0R**, the
  unconditional statement — the descent over a base of
  `AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app_of_affineStage` with
  its hypothesis of Stacks 07SQ discharged by the previous item.

## Implementation notes

*Why a terminal base, and how the hypothesis is removed.* The identification of an affine
algebraic space with the spectrum of its global functions is
`AlgebraicGeometry.Space.isIso_toSpecGlobalFunctions`, which is Stacks 05Z1 and needs the
terminal base to turn a ring homomorphism into a morphism over the base. Affineness of an
algebraic space is absolute, by
`AlgebraicGeometry.Space.isAffineSpace_viewOverIntegers_iff`, so nothing is lost: the whole
descent is carried out over the terminal scheme in
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_isTerminal` and
transported back along
`AlgebraicGeometry.Space.DescentSituation.viewOverIntegers`, exactly as for Stacks
084T.

*The index-size hypothesis.* Every statement about a whole descent situation here carries
`#I < B.cutoff.ord.cof`. That is the explicit form of the all-rings-in-the-site convention under
which Stacks 07SF holds, and it is genuinely used three times: it makes the limit of the affine
charts of the system an object of the site (Stacks 07SF), it makes the ring of global functions
of the limit the filtered colimit of those of the stages (Stacks 07SI for the structure sheaf,
through Stacks 07SF again), and it is a field of the morphism descent system of Stacks 084W that
Stacks 084S is applied to. It is the same hypothesis Stacks 084T and Stacks 086X
carry, and it is not a weakening of the source, whose Situation 70.5.5 reads inside a fixed
site. Stacks 0A0R inherits it through its appeal to Stacks 07SQ and nowhere else, so it is
carried there in the same form.

*The two spellings of the global functions.* `AlgebraicGeometry.Space.globalFunctions` and
`AlgebraicGeometry.Space.globalFunctions'` are the same term declared twice, so they are equal
by `rfl` but not reducibly; no rewrite crosses between them. The identifications
`AlgebraicGeometry.Space.stageModelEquiv` and
`AlgebraicGeometry.Space.limitModelEquiv` are the primed readings of
`AlgebraicGeometry.Space.globalFunctionsModelEquiv`, and the ring homomorphisms of the directed
system — `AlgebraicGeometry.Space.DescentSituation.modelTransition` and `.modelProjection` — are
`AlgebraicGeometry.Space.globalFunctionsMap` conjugated by them.

*Why the proof is cut into named pieces.* Assembling the three geometric steps in one tactic
block exceeds the compiler's heartbeat limit, and raising that limit is not available here, so
each step is a declaration of its own: the Cartesian square at the limit, the descent of the
display, and the two halves of the passage from the presentation to the affine stage.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 0A0R](https://stacks.math.columbia.edu/tag/0A0R)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/
