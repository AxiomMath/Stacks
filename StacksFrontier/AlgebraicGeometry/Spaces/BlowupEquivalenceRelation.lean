module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentEquivalenceRelation

/-!
# The descent datum of the relative Proj of a Rees algebra

Let `S` be a scheme, let `X` be an algebraic space over `S` with étale presentation `(U, R)`,
and let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals.  The relative Proj `P_U` of the Rees
algebra of `ℐ|_U` and the relative Proj `P_R` of the Rees algebra of `ℐ|_R` come with two
projections `P_R ⇉ P_U`, the comparison morphisms of relative Proj over the two legs `R ⇉ U`
of the relation, and `P_R` is the base change of `P_U` along each leg.  The blowup of `X`
along the closed subspace cut out by `ℐ` is the quotient of `P_U` by those two projections,
and for that quotient to be an algebraic space they have to form an internal equivalence
relation.

This file analyses that condition.  Of the four things an internal equivalence relation
asserts, *joint monicity is free*: it is inherited from the joint monicity of the two legs
`R ⇉ U` through either of the two cartesian squares, and it is proved here with no hypothesis
beyond the presentation and the sheaf of ideals.  The remaining three — reflexivity, symmetry
and transitivity — collapse, by `Stacks.Descent.isEquivalenceRelation_of_canonical`, to three
equations about the *source* projection alone: the two cartesian squares already produce
canonical candidates `ρ`, `σ` and `τ` for the three witnesses which satisfy their condition
against the *target* projection by construction.  Those three equations are the normalisation
and cocycle conditions of the descent datum.

**They are not discharged here, and they are not weaker than the condition they replace.**
`AlgebraicGeometry.Space.normalisation_of_isEquivalenceRelation_post_reesProj` proves the
converse, so the three equations and the equivalence-relation condition are equivalent; what
this file buys is that the condition is reduced from a structure on a pair of morphisms to
three explicit equations between explicit morphisms, with the joint-monicity part removed.
That is why nothing here carries a `@[stacks 085Q]` attribute: the three declarations of
Tag 085Q in `StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj` carry the condition
honestly as a parameter, and a restatement of it would add no coverage.

All three equations are now proved elsewhere, so the condition itself is discharged:
reflexivity and symmetry in
`StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationNormalisation` and transitivity
in `StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity`, which
assembles them into `AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj`. The
`@[stacks 085Q]` declarations that carry no equivalence-relation hypothesis are
`blowUpAlong'`, `blowUpAlongHom'` and `exceptionalDivisor'` in
`StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationClosed`.

**What closing the three equations needs.** Each of them identifies a canonical candidate with
a comparison morphism of relative Proj: `ρ` with the base change along the diagonal
`U ⟶ R`, `σ` with the base change along the symmetry `R ⟶ R`, and `τ` with the base change
along the composition `R ×_U R ⟶ R`.  Each identification is an instance of a composition law
`relativeProjBaseChange g Φ ≫ relativeProjBaseChange h Ψ = relativeProjBaseChange (g ≫ h) Θ`.
That law is now available, as
`Stacks.RelativeProj.Situation.relativeProjBaseChange_comp` in
`StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeComposition`, resting on a chart
cover of the source indexed by *triples* of affine opens — `baseChangeCover` is indexed by pairs
and supplies no intermediate affine — together with its Rees instantiation
`Stacks.Blowup.reesSituationBaseChange_comp`.  Reflexivity and symmetry are consequently proved,
in `StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationNormalisation`.  Transitivity
remains, and needs the relative Proj of the Rees algebra on `R ×_U R`.  No composition law
follows from the two cartesian squares alone: if
`φ` is an automorphism of `P_U` over `U` then replacing the source projection by
`φ ≫ (source projection)` leaves both squares cartesian and destroys reflexivity unless
`φ = 𝟙`.

## Main definitions

* `AlgebraicGeometry.Space.presentationEquivalenceRelation` is the internal equivalence
  relation that the two legs of an étale presentation form, read in the category of
  `S`-schemes.
* `AlgebraicGeometry.Space.reesProjTransitivityCone` is the fibre product
  `P_R ×_{P_U} P_R` of the source projection against the target projection, as the limiting
  pullback cone that the transitivity condition is stated over.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_presentationRelation`: the two legs of an
  étale presentation form an internal equivalence relation on the presenting scheme.
* `AlgebraicGeometry.Space.isPullback_post_reesProjTarget` and
  `AlgebraicGeometry.Space.isPullback_post_reesProjSource`: the two cartesian squares
  exhibiting `P_R` as the base change of `P_U`, read in the category of `S`-schemes.
* `AlgebraicGeometry.Space.jointlyMono₂_post_reesProj`: **the two projections
  `P_R ⇉ P_U` are jointly monic, with no hypothesis.**
* `AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj_of_normalisation`: the two
  projections form an internal equivalence relation as soon as the three normalisation and
  cocycle equations hold.
* `AlgebraicGeometry.Space.normalisation_of_isEquivalenceRelation_post_reesProj`: the three
  equations conversely follow from the equivalence-relation condition, so the reduction is an
  equivalence and not a weakening.

## Implementation notes

The cartesian squares are proved in `StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj`
in the big fppf category over `S`, while the equivalence-relation condition is stated in the
category of `S`-schemes, where the étale equivalence relation of the presentation lives.  They
are transported along `Over.post B.inclusion` by
`AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_post`, which is the same transport
that the glueing datum uses for the square over the chart of the base.

The equivalence-relation structure on the two legs is extracted from the `Prop`-valued
condition carried by the presentation, so it is a choice; it is harmless, because the
reflexivity and symmetry witnesses of an internal equivalence relation are unique by joint
monicity, and the pullback cone stored in the structure is never used — the transitivity
condition is stated over `AlgebraicGeometry.Space.reesProjTransitivityCone` instead, which is
the fibre product that `CategoryTheory.Limits.pullback` provides in the slice category.

The converse is proved through the uniqueness statements `Stacks.Descent.eq_reflHom`,
`Stacks.Descent.eq_symHom` and `Stacks.Descent.eq_transHom`; for transitivity the witness
stored in a chosen equivalence-relation structure lives over that structure's own pullback
cone, so it is transported to `AlgebraicGeometry.Space.reesProjTransitivityCone` by the
universal property before the uniqueness statement is applied.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS}

/-! ### The relation of a presentation, read in the category of `S`-schemes -/

/-- **The two legs of an étale presentation form an internal equivalence relation.** The
presentation carries the condition for the target and source maps of the pre-relation it
assembles out of them, and those are the two legs by the two projection formulae for a
product. -/
theorem isEquivalenceRelation_presentationRelation
    (P : Presentation B S hS X.obj X.property) :
    CategoryTheory.IsEquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source) := by
  have h := P.isEtaleEquivalenceRelation.isEquivalenceRelation
  have et : Stacks.Groupoids.PreRelation.target
      (Limits.prod.lift ((Over.post B.inclusion).map P.target)
        ((Over.post B.inclusion).map P.source)) =
      (Over.post B.inclusion).map P.target := Limits.prod.lift_fst _ _
  have es : Stacks.Groupoids.PreRelation.source
      (Limits.prod.lift ((Over.post B.inclusion).map P.target)
        ((Over.post B.inclusion).map P.source)) =
      (Over.post B.inclusion).map P.source := Limits.prod.lift_snd _ _
  rw [et, es] at h
  exact h

/-- The internal equivalence relation that the two legs of an étale presentation form, as a
structure: the reflexivity, symmetry and transitivity witnesses together with the joint
monicity of the two legs. -/
def presentationEquivalenceRelation (P : Presentation B S hS X.obj X.property) :
    EquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source) :=
  (isEquivalenceRelation_presentationRelation P).nonempty_equivalenceRelation.some

/-! ### The two cartesian squares in the category of `S`-schemes -/

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
  (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
  (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation N hN P).relativeProj)
  (hcR : B.Contains (reesRelationSituation N hN P).relativeProj)

/-- **`P_R` is the base change of `P_U` along the target leg**, read in the category of
`S`-schemes: the square is cartesian in the big fppf category over `S` and the forgetful
functor to `S`-schemes reflects fibre products. -/
theorem isPullback_post_reesProjTarget :
    IsPullback ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjRelationHom N hN P hcR))
      ((Over.post B.inclusion).map (reesProjChartHom N hN P hcU))
      ((Over.post B.inclusion).map P.target) :=
  RelativeProjGlueingData.isPullback_post (isPullback_reesProjTarget N hN P hcU hcR)

/-- **`P_R` is the base change of `P_U` along the source leg**, read in the category of
`S`-schemes: the square is cartesian in the big fppf category over `S` and the forgetful
functor to `S`-schemes reflects fibre products. -/
theorem isPullback_post_reesProjSource :
    IsPullback ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjRelationHom N hN P hcR))
      ((Over.post B.inclusion).map (reesProjChartHom N hN P hcU))
      ((Over.post B.inclusion).map P.source) :=
  RelativeProjGlueingData.isPullback_post (isPullback_reesProjSource N hN P hcU hcR)

/-! ### Joint monicity, which is free -/

/-- **The two projections `P_R ⇉ P_U` are jointly monic**, with no hypothesis beyond the
presentation and the sheaf of ideals.  Two morphisms into `P_R` that agree after both
projections agree after the two legs of the relation composed with the structure morphism of
`P_R`, hence after that structure morphism because the legs are jointly monic, and then the
cartesian square over the target leg separates them.  This is one of the four conditions
defining an internal equivalence relation, and it is the only one the two cartesian squares
supply. -/
theorem jointlyMono₂_post_reesProj :
    JointlyMono₂ ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR)) :=
  Stacks.Descent.jointlyMono₂_of_isPullback
    (presentationEquivalenceRelation P).toReflexiveRelation.toJointlyMono₂
    (isPullback_post_reesProjTarget N hN P hcU hcR)
    (isPullback_post_reesProjSource N hN P hcU hcR)

/-! ### The three remaining equations -/

/-- The fibre product `P_R ×_{P_U} P_R` of the source projection against the target
projection, as a limiting pullback cone: the object over which transitivity of the two
projections is stated. -/
abbrev reesProjTransitivityCone :
    PullbackCone ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR)) :=
  PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition

/-- **The two projections `P_R ⇉ P_U` form an internal equivalence relation as soon as the
three normalisation and cocycle equations hold.** The two cartesian squares produce canonical
candidates for the three witnesses out of the reflexivity, symmetry and transitivity witnesses
of the relation of the presentation, each satisfying its condition against the target
projection by construction; what is assumed here is its condition against the source
projection.  Joint monicity is not assumed: it is
`AlgebraicGeometry.Space.jointlyMono₂_post_reesProj`. -/
theorem isEquivalenceRelation_post_reesProj_of_normalisation
    (e : EquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source))
    (hr : Stacks.Descent.reflHom e.toReflexiveRelation
          (isPullback_post_reesProjTarget N hN P hcU hcR) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) = 𝟙 _)
    (hs : Stacks.Descent.symHom e.toSymmetricRelation
          (isPullback_post_reesProjTarget N hN P hcU hcR)
          (isPullback_post_reesProjSource N hN P hcU hcR) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
      (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
    (ht : Stacks.Descent.transHom e.toTransitiveRelation
          (isPullback_post_reesProjTarget N hN P hcU hcR)
          (isPullback_post_reesProjSource N hN P hcU hcR)
          (reesProjTransitivityCone N hN P hcU hcR) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
      (reesProjTransitivityCone N hN P hcU hcR).snd ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR)) :
    CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR)) :=
  Stacks.Descent.isEquivalenceRelation_of_canonical e
    (isPullback_post_reesProjTarget N hN P hcU hcR)
    (isPullback_post_reesProjSource N hN P hcU hcR)
    (reesProjTransitivityCone N hN P hcU hcR) (pullbackIsPullback _ _) hr hs ht

/-- **The three equations are exactly the equivalence-relation condition, not a weakening of
it.** If the two projections do form an internal equivalence relation then its three witnesses
are the canonical candidates, by the uniqueness statements of
`StacksFrontier.AlgebraicGeometry.Spaces.DescentEquivalenceRelation`, so each of them satisfies
the equation against the source projection.  Together with
`AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj_of_normalisation` this says that
the reduction to three equations rearranges the condition and removes its joint-monicity part,
and assumes nothing less. -/
theorem normalisation_of_isEquivalenceRelation_post_reesProj
    (e : EquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source))
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    Stacks.Descent.reflHom e.toReflexiveRelation
          (isPullback_post_reesProjTarget N hN P hcU hcR) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) = 𝟙 _ ∧
    Stacks.Descent.symHom e.toSymmetricRelation
          (isPullback_post_reesProjTarget N hN P hcU hcR)
          (isPullback_post_reesProjSource N hN P hcU hcR) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
      (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) ∧
    Stacks.Descent.transHom e.toTransitiveRelation
          (isPullback_post_reesProjTarget N hN P hcU hcR)
          (isPullback_post_reesProjSource N hN P hcU hcR)
          (reesProjTransitivityCone N hN P hcU hcR) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
      (reesProjTransitivityCone N hN P hcU hcR).snd ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) := by
  obtain ⟨e'⟩ := heq.nonempty_equivalenceRelation
  refine ⟨?_, ?_, ?_⟩
  · rw [← Stacks.Descent.eq_reflHom e.toReflexiveRelation
      (isPullback_post_reesProjTarget N hN P hcU hcR)
      (isPullback_post_reesProjSource N hN P hcU hcR) e'.reflexivity₁ e'.reflexivity₂]
    exact e'.reflexivity₂
  · rw [← Stacks.Descent.eq_symHom e.toSymmetricRelation
      (isPullback_post_reesProjTarget N hN P hcU hcR)
      (isPullback_post_reesProjSource N hN P hcU hcR) e'.symmetry₁ e'.symmetry₂]
    exact e'.symmetry₂
  · set c := reesProjTransitivityCone N hN P hcU hcR
    have h₁ : (PullbackCone.IsLimit.lift e'.isLimit c.fst c.snd c.condition ≫ e'.t) ≫
        (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) =
        c.fst ≫ (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) := by
      rw [Category.assoc, e'.transitivity₁, PullbackCone.IsLimit.lift_fst_assoc]
    have h₂ : (PullbackCone.IsLimit.lift e'.isLimit c.fst c.snd c.condition ≫ e'.t) ≫
        (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
        c.snd ≫ (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) := by
      rw [Category.assoc, e'.transitivity₂, PullbackCone.IsLimit.lift_snd_assoc]
    rw [← Stacks.Descent.eq_transHom e.toTransitiveRelation
      (isPullback_post_reesProjTarget N hN P hcU hcR)
      (isPullback_post_reesProjSource N hN P hcU hcR) c h₁ h₂]
    exact h₂

end AlgebraicGeometry.Space

end
