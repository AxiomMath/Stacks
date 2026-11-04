module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.TerminalPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The Segre embedding: reduction of the relative statement to the absolute one

Relative projective space `AlgebraicGeometry.projectiveSpaceOver n S` is by construction the base
change of the integral model `AlgebraicGeometry.projectiveSpaceAtUniverse n` along the unique
morphism from `S` to the terminal scheme, with the first pullback projection as its structure
morphism.  This file exploits that definition to show that the whole content of the relative
Segre embedding over an arbitrary base lies in the absolute case over the terminal scheme: a
single closed immersion
`projectiveSpaceOver m (projectiveSpaceAtUniverse n) ⟶ projectiveSpaceAtUniverse (n * m + n + m)`
produces, by base change, a closed immersion over `S` for every scheme `S`, with no hypothesis on
`S` at all.

## What is proved, and the route

* `Stacks.AlgebraicGeometry.SegreEmbedding.productIso`: the fibre product over `S` of relative
  projective spaces of dimensions `n` and `m` is relative projective `m`-space over relative
  projective `n`-space over `S`, that is `projectiveSpaceOver m (projectiveSpaceOver n S)`, and
  the isomorphism carries the structure morphism of the latter to the first projection
  (`productIso_hom_comp_over`).  Both sides are limits of diagrams over the terminal scheme, so
  this is `Stacks.CategoryTheory.TerminalPullback.isPullback_prodSnd` specialised.

* `Stacks.AlgebraicGeometry.SegreEmbedding.segreOver`: the morphism over `S` induced by a
  morphism `σ` of the integral models.  It is
  `Stacks.CategoryTheory.TerminalPullback.baseChangeMap`, a `pullback.lift` whose first component
  is the structure morphism, so the over-`S` condition in the shape Tag 01WD states it — through
  the first projection — is `Stacks.AlgebraicGeometry.SegreEmbedding.segreOver_comp_over`, and it
  holds for every `σ` whatsoever.

* `Stacks.AlgebraicGeometry.SegreEmbedding.isClosedImmersion_segreOver`: `segreOver n m S σ` is a
  base change of `σ` by `Stacks.CategoryTheory.TerminalPullback.isPullback_baseChangeMap`, and
  closed immersions are stable under base change by
  `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`, so `σ` closed makes
  `segreOver n m S σ` closed.

* `Stacks.AlgebraicGeometry.SegreEmbedding.exists_segreEmbedding_of_absolute`: the existence
  statement of Tag 01WD for every base scheme `S`, granted the absolute closed immersion.  Its
  conclusion is the statement of Tag 01WD verbatim, the structure morphisms being the first pullback
  projections by reflexivity
  (`Stacks.AlgebraicGeometry.SegreEmbedding.projectiveSpaceOver_over_hom`).

## Implementation notes

The three integral models `projectiveSpaceAtUniverse n`, `projectiveSpaceAtUniverse m` and
`projectiveSpaceAtUniverse (n * m + n + m)` enter only as opaque objects, so everything here is
the specialisation of the category-theoretic results in
`StacksFrontier.AlgebraicGeometry.SegreEmbedding.TerminalPullback`, where they are three
arbitrary objects of an arbitrary category with a terminal object and pullbacks.

## What is not done

The absolute Segre closed immersion is **not** constructed.  Precisely, nothing in this directory
produces a term of `Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre n m`, the hypothesis of
`Stacks.AlgebraicGeometry.SegreEmbedding.exists_segreEmbedding_of_absolute`; by the results proved
here that single statement is the entire remaining content of Tag 01WD.

The shape of the missing argument is this.  Write `R` for `ULift.{u} ℤ`, the coefficient ring of
the integral models, and `𝒮` for the Segre product of the two polynomial rings in `n + 1` and
`m + 1` variables, graded by the common degree in the two groups of variables.

Both the ring and the presentation now exist in this directory, for arbitrary index types and an
arbitrary commutative ring:

* `Stacks.RingTheory.SegreProduct.segre R X Y` with its grading
  `Stacks.RingTheory.SegreProduct.grading R X Y` and the `GradedAlgebra` structure
  `Stacks.RingTheory.SegreProduct.gradingGradedAlgebra`, in
  `StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreRing.lean`;
* the graded ring homomorphism `Stacks.RingTheory.SegreProduct.presentation R X Y` from the
  total-degree grading of the polynomial ring on `X × Y` — the variables `z_{ij}` — sending
  `z_{ij}` to `x_i * y_j`, together with
  `Stacks.RingTheory.SegreProduct.surjective_gradedAddHom`, surjectivity on components in every
  degree, and its `Filter.atTop` restatement
  `Stacks.RingTheory.SegreProduct.eventually_surjective_gradedAddHom`, in
  `StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegrePresentation.lean`.

That surjectivity is exactly the hypothesis of
`Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective`,
and that criterion has now been applied: in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreClosedImmersion.lean`,
`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegreHom n m` is a morphism from
`AlgebraicGeometry.Proj` of the Segre product to `projectiveSpaceAtUniverse (n * m + n + m)` and
`isClosedImmersion_absoluteSegreHom` says it is a closed immersion, unconditionally.  The
reindexing of the `(n + 1) * (m + 1)` variables `z_{ij}` by `Fin (n * m + n + m + 1)` that this
needs is `Stacks.AlgebraicGeometry.ProjPoly.segreTargetIso`, in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/ProjPoly.lean`.

So the one remaining mathematical input is a single isomorphism of schemes,

`Stacks.AlgebraicGeometry.SegreClosedImmersion.projSegre (ULift.{u} ℤ) (Fin (n + 1))`
`    (Fin (m + 1)) ≅ projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n)`,

whose left-hand side is `AlgebraicGeometry.Proj` of the Segre product under its canonical
grading.  `Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso` turns
that isomorphism into `AbsoluteSegre n m`, and
`exists_segreEmbedding_of_absolute` turns that into Tag 01WD over every base scheme.  Nothing
else is owed anywhere in this directory.

The isomorphism itself is not proved.  It is a gluing argument: `Proj` of the Segre product is
covered by the standard opens where one generator `x_i y_j` is invertible, on which it is the
spectrum of a degree-zero homogeneous localisation; the product of the two projective spaces is
covered by the corresponding products of standard opens; and the two covers have to be matched
and the overlaps checked.  The ring-theoretic half of that argument is done:
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreCharts.lean` exhibits those opens as affine
opens and proves they cover, and
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreChartRing.lean` computes the chart ring,
identifying it with the tensor product of the two chart rings of the two projective spaces, which
are themselves computed in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/PolyChart.lean`.  What is untouched is the
geometry: no morphism between `Proj` of the Segre product and a product of projective spaces is
constructed, in either direction.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Stacks.CategoryTheory

namespace Stacks.AlgebraicGeometry.SegreEmbedding

universe u

variable (n m : ℕ) (S : Scheme.{u})

/-- The structure morphism of relative projective space is the first pullback projection. -/
public theorem projectiveSpaceOver_over_hom :
    (projectiveSpaceOver n S ↘ S) =
      pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  rfl

/-! ### The fibre product of two relative projective spaces -/

/-- The fibre product over `S` of relative projective spaces of dimensions `n` and `m` is
relative projective `m`-space over relative projective `n`-space over `S`. -/
public noncomputable def productIso :
    pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ≅
      projectiveSpaceOver m (projectiveSpaceOver n S) :=
  (TerminalPullback.isPullback_prodSnd S (projectiveSpaceAtUniverse.{u} n)
    (projectiveSpaceAtUniverse.{u} m)).isoPullback

/-- `productIso` followed by the structure morphism to relative projective `n`-space is the first
projection of the fibre product. -/
public theorem productIso_hom_comp_over :
    (productIso n m S).hom ≫
        (projectiveSpaceOver m (projectiveSpaceOver n S) ↘ projectiveSpaceOver n S) =
      pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) :=
  (TerminalPullback.isPullback_prodSnd S (projectiveSpaceAtUniverse.{u} n)
    (projectiveSpaceAtUniverse.{u} m)).isoPullback_hom_fst

/-! ### The morphism induced by an absolute Segre morphism -/

variable (σ : projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n) ⟶
  projectiveSpaceAtUniverse.{u} (n * m + n + m))

/-- The morphism over `S` induced by a morphism `σ` of the integral models, by base change along
the unique morphism from `S` to the terminal scheme. -/
public noncomputable def segreOver :
    pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ⟶
      projectiveSpaceOver (n * m + n + m) S :=
  TerminalPullback.baseChangeMap S (projectiveSpaceAtUniverse.{u} n)
    (projectiveSpaceAtUniverse.{u} m) (projectiveSpaceAtUniverse.{u} (n * m + n + m)) σ

/-- The induced morphism is a morphism over `S`, in the shape Tag 01WD states the condition:
through the first projection.  This holds for every `σ`. -/
public theorem segreOver_comp_over :
    segreOver n m S σ ≫ (projectiveSpaceOver (n * m + n + m) S ↘ S) =
      pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ≫
        (projectiveSpaceOver n S ↘ S) :=
  TerminalPullback.baseChangeMap_comp_fst S (projectiveSpaceAtUniverse.{u} n)
    (projectiveSpaceAtUniverse.{u} m) (projectiveSpaceAtUniverse.{u} (n * m + n + m)) σ

/-- The induced morphism is a base change of `σ`, along the projection of `ℙᴺ_S` to the integral
model of `ℙᴺ`. -/
public theorem isPullback_segreOver :
    IsPullback (TerminalPullback.prodMap S (projectiveSpaceAtUniverse.{u} n)
        (projectiveSpaceAtUniverse.{u} m)) (segreOver n m S σ) σ
      (projectiveSpaceOver.toIntegralAtUniverse (n * m + n + m) S) :=
  TerminalPullback.isPullback_baseChangeMap S (projectiveSpaceAtUniverse.{u} n)
    (projectiveSpaceAtUniverse.{u} m) (projectiveSpaceAtUniverse.{u} (n * m + n + m)) σ

/-- Closed immersions are stable under base change, so a closed immersion of the integral models
induces one over every base scheme. -/
public theorem isClosedImmersion_segreOver (hσ : IsClosedImmersion σ) :
    IsClosedImmersion (segreOver n m S σ) :=
  TerminalPullback.baseChangeMap_mem S (projectiveSpaceAtUniverse.{u} n)
    (projectiveSpaceAtUniverse.{u} m) (projectiveSpaceAtUniverse.{u} (n * m + n + m)) σ
    @IsClosedImmersion hσ

/-- The absolute Segre statement, which this directory does **not** prove: a closed immersion of
the fibre product over the terminal scheme of the integral models of `ℙⁿ` and `ℙᵐ` into the
integral model of `ℙᴺ`, `N = n * m + n + m`.  By
`Stacks.AlgebraicGeometry.SegreEmbedding.exists_segreEmbedding_of_absolute` this is the whole
remaining content of Tag 01WD. -/
public def AbsoluteSegre (n m : ℕ) : Prop :=
  ∃ σ : projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n) ⟶
    projectiveSpaceAtUniverse.{u} (n * m + n + m), IsClosedImmersion σ

/-- **Tag 01WD, granted the absolute case.**  A closed immersion of the fibre product over the
terminal scheme of the integral models of `ℙⁿ` and `ℙᵐ` into the integral model of `ℙᴺ`,
`N = n * m + n + m`, yields for every base scheme `S` a closed immersion over `S` of
`ℙⁿ_S ×_S ℙᵐ_S` into `ℙᴺ_S`. -/
public theorem exists_segreEmbedding_of_absolute (h : AbsoluteSegre.{u} n m) :
    ∃ f : pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion f ∧
        f ≫ (projectiveSpaceOver (n * m + n + m) S ↘ S) =
          pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ≫
            (projectiveSpaceOver n S ↘ S) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨segreOver n m S σ, isClosedImmersion_segreOver n m S σ hσ, segreOver_comp_over n m S σ⟩

end Stacks.AlgebraicGeometry.SegreEmbedding

end
