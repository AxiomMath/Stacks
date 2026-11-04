module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction

/-!
# Stacks 09YB: an integral scheme cover, refining a prescribed étale cover

Stacks 09YB asserts, for a quasi-compact and quasi-separated algebraic space `X` over a scheme
`S`, that

1. there is a surjective integral morphism `Y ⟶ X` with `Y` a scheme, and that
2. given a surjective étale `p : U ⟶ X` the cover `Y` may be chosen so that every point of `Y`
   has an open neighbourhood `V ⊆ Y` with `V ⟶ X` factoring through `p`.

**Clause (2) is proved here from clause (1).** That is not the source's route — the source
proves the two clauses together, by an induction on a bound for the degree of the geometric
fibres of `U ⟶ X` — and it is a strictly stronger reduction: *any* surjective integral scheme
cover of `X` can be refined, by one finite surjective morphism of finite presentation, into one
which factors Zariski locally through any prescribed surjective étale `p`. The input is
Stacks 0CP0, which dominates an fppf covering of a quasi-compact quasi-separated *scheme* by a
finite surjective morphism of finite presentation carrying a Zariski covering whose members
factor through the given covering; the scheme it is applied to is the cover of clause (1), which
is quasi-compact and quasi-separated because it is integral over `X`.

**Clause (1) is proved too**, by the source's induction on that degree bound, in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction`. Nothing is carried; see
*What is and is not proved* below.

## Main definitions

* `AlgebraicGeometry.Space.FactorsZariskiLocallyThrough` is the local clause of Stacks 09YB (2)
  and of Stacks 09YC (2): every point of the cover has a *representable* open subspace
  neighbourhood over which the cover factors through the prescribed morphism.

## Main results

* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_and_refining`: **both clauses of
  Stacks 09YB**, unconditionally. This is the declaration the `@[stacks 09YB]` attribute sits
  on, and it is the only one that carries it.

## Implementation notes

### Clause (2) from clause (1)

The argument is in `StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleRefinement`
and runs in three steps.

* The cover `f : h_Y ⟶ X` of clause (1) is integral, so the scheme `Y` is quasi-compact
  (`AlgebraicGeometry.Space.compactSpace_of_isIntegralHom`) and quasi-separated: an integral
  morphism is separated, hence quasi-separated, so `h_Y` is absolutely quasi-separated and
  `AlgebraicGeometry.Space.quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated` reads that
  off as a property of the representing scheme.
* The fibre product `U ×_X h_Y` is an algebraic space, so it has a surjective étale chart `W`
  by an object of the site; its projection to `Y` is surjective and étale as a morphism of
  schemes, and it comes with a morphism `h_W ⟶ U` over `X`. This is
  `AlgebraicGeometry.Space.exists_etale_chart_over`.
* `{W ⟶ Y}` is therefore a one-member fppf covering of `Y`, and
  `AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage`
  — Stacks 0CP0 — dominates it by a finite surjective `g : Z ⟶ Y` of finite presentation
  together with an open covering of `Z` each member of which maps to `Y` through `W`. The
  source `Z` and the members of the covering are objects of the site by Stacks 000R (5) and
  (3), and the covering is turned into the representable-open-subspace form of the local clause
  by `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_factoring_of_openCover`.
  The composite `h_Z ⟶ h_Y ⟶ X` is integral, being finite followed by integral, and
  surjective.

The same three steps give clause (2) of Stacks 09YC from its clause (1), with finiteness and
finite presentation carried through the composite instead of integrality; see
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverExistence`.

### What is and is not proved

Both clauses are proved, and **no hypothesis is carried**.

* Clause (1) is
  `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_isQuasiCompactSpace`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction`: the source's induction on
  an integer `d` bounding the degree of the geometric fibres of an étale chart `U ⟶ X`. Its
  step is the source's. Stacks 0ABS factors the chart as a quasi-compact open immersion
  `j : h_U ⟶ Y` followed by an integral `π : Y ⟶ X`
  (`AlgebraicGeometry.Space.zariskiMainTheorem`); one may and does assume `j(U)` dense
  in `Y` (`AlgebraicGeometry.Space.exists_isSchemeTheoreticallyDense_isIntegralHom_factorization`);
  the complementary summand of the splitting `h_U ×_X Y = h_U ⨿ W`
  (`AlgebraicGeometry.Space.exists_graphComplement_decomposition`) is a surjective étale chart
  of an open subspace `V ⊆ Y` with every field-valued fibre of degree `< d` and with
  `Y ∖ V ⊆ j(U)`
  (`AlgebraicGeometry.Space.exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt`, over the
  pointwise drop
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits` and the
  carry `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange` across
  Stacks 07S8); the induction hypothesis covers `V`; Stacks 0G2D
  (`AlgebraicGeometry.Space.exists_isIntegralHom_isPullback_of_isOpenImmersion`) extends that
  cover over `Y`, the reduced induced structure of Stacks 03IQ on `Y ∖ V` fills in the rest, and
  the composite with `π` covers `X`
  (`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_openSubspace_cover` and
  `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_comp`). The recursion bottoms out
  at `d = 0`, where no fibre can have degree below `d`, so `V` has no points, `j` is a
  surjective open immersion hence an isomorphism, and the chart itself is integral.

  The bound `d` exists because a quasi-separated algebraic space is reasonable — Stacks 03JX in
  the shape `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_isAbsolutelyQuasiSeparated` —
  and the degree stratification of Stacks 07S8 turns that into a bound at *every* presentation
  of *every* field-valued fibre, which is the third clause of
  `AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`.

  No additivity of the degree across the splitting is used, and no coproduct presentation of
  the splitting is needed: what the argument takes from the splitting is only the point omitted
  by `W` in each fibre over `j(U)`, supplied by the graph, so the lattice form suffices.

  The induction carries no affineness of its chart — the summand `W` is produced as a site
  object with no finiteness property attached — but it does carry quasi-compactness of the
  chart's source and separatedness of the chart, and both are restored at the recursive call
  from the integrality of the summand's factorization `φ : h_W ⟶ h_U` through the old chart.
  Affineness is needed only to start the induction.

* Clause (2) is proved from clause (1), by the three steps above. Note that the reduction of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverReductions`,
  `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_etale_refinement`, is a
  different statement: it derives clause (1) from clause (2) for all `X` and `U` simultaneously,
  whereas what is proved here is clause (2) for `X` from clause (1) for `X`.

Stacks 09YZ is **not carried**: Stacks 0CP0, which the deduction of clause (2) uses, is
proved unconditionally in this library over a quasi-compact quasi-separated base.

The last sentence of Stacks 0ABS, that a quasi-finite separated morphism is quasi-affine, is
proved unconditionally as
`AlgebraicGeometry.Space.isQuasiAffineHom_of_isQuasiFinite_isSeparated`; it is not the
factorization the induction needs.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
* [Stacks Project, Tag 082J](https://stacks.math.columbia.edu/tag/082J)
* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The local clause of Stacks 09YB (2) and Stacks 09YC (2).** A morphism `f : h_Y ⟶ X` from
the presheaf represented by an object `Y` of the site *factors through `p : U ⟶ X` Zariski
locally on `Y`* when every point of `h_Y` lies in the point set of a representable open
subspace of `h_Y` along which `f` factors through `p`.

Representability of the neighbourhood is what makes this the source's assertion: the source
asks for an open neighbourhood in the *scheme* `Y`. -/
def FactorsZariskiLocallyThrough {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : U ⟶ X)
    (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) : Prop :=
  ∀ y : points B S hS (yoneda.obj Y),
    ∃ W : Subfunctor (yoneda.obj Y),
      IsOpenSubspace B S hS W ∧
      W.toFunctor.IsRepresentable ∧
      y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
      ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p

/-- **Stacks Project, Tag 09YB.** Let `X` be a quasi-compact and quasi-separated algebraic
space over a scheme `S`. Then

1. there is a surjective integral morphism to `X` from the presheaf represented by an object of
   the big fppf site — a scheme over `S` — and
2. given a surjective étale morphism `p : U ⟶ X` from an algebraic space, such a cover can be
   chosen so that it factors through `p` on a representable open subspace neighbourhood of
   every one of its points.

**Both clauses are proved, over no hypothesis.** Clause (1) is the source's induction on a bound
for the degree of the geometric fibres of an étale chart, performed in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction`; clause (2) is deduced here
from clause (1) by the unconditional Stacks 0CP0. -/
@[stacks 09YB]
theorem existsIntegralSurjectiveSchemeCover_and_refining
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ExistsIntegralSurjectiveSchemeCover B S hS X ∧
      ∀ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS U →
        ∀ p : U ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
          ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
            IsSurjective B S hS f ∧ IsIntegralHom B S hS f ∧
              FactorsZariskiLocallyThrough B S hS p Y f := by
  have h1 : ExistsIntegralSurjectiveSchemeCover B S hS X :=
    existsIntegralSurjectiveSchemeCover_of_isQuasiCompactSpace B S hS hZ X hX hXqc hXqs
  refine ⟨h1, fun U hU p hpsurj hpet => ?_⟩
  obtain ⟨Z, g, hgsurj, hgint, hloc⟩ :=
    exists_integralSurjectiveSchemeCover_refining_of_clause_one B S hS hZ hX hU hXqc hXqs p hpsurj
      hpet h1
  exact ⟨Z, g, hgsurj, hgint, hloc⟩

end AlgebraicGeometry.Space

end
