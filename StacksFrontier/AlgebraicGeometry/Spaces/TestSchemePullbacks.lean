module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemeFpqcSite

/-!
# Fibre products of test schemes, and flat covering families inside a covering sieve

The test schemes over an algebraic space `Y` over a scheme `S` of a big fppf site have fibre
products: the fibre product of the underlying objects of the big fppf site, equipped with the
structure morphism to `Y` inherited through either projection.  The underlying-scheme functor
preserves them.  Consequently the precoverage generating the fpqc topology on the test schemes
is stable under base change and has pullbacks, so each of its covering sieves contains a whole
covering family of that precoverage, which represents an fpqc covering of algebraic spaces in
the sense of Stacks 03MQ.

## Main results

* `AlgebraicGeometry.Space.exists_isFpqcCovering_family_of_mem_fpqcTopology`: a covering sieve
  of a test scheme `T` over `Y` contains a family of arrows whose images under
  `AlgebraicGeometry.schemeSpaceFunctor` are an fpqc covering of the algebraic space
  represented by `T`; in particular every member of the family is flat.
* `AlgebraicGeometry.Space.exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology`:
  that family is moreover jointly surjective on the points of Stacks 03BU.

## Implementation notes

That the fibre products exist and that the projection to the big fppf site preserves them are
both instances of the general fact that the projection out of a category of costructured arrows
creates connected limits; this needs nothing of the functor the arrows point along, since the
structure morphism of the fibre product is inherited.  Preservation by the underlying-scheme
functor then comes from preservation of fibre products by the forgetful functor to schemes.

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The test schemes over an algebraic space have fibre products: the fibre product of the
underlying objects of the big fppf site, equipped with the structure morphism inherited through
either projection. -/
instance hasPullbacks_schemesOver (Y : AlgebraicSpaces B S hS) :
    HasPullbacks (SchemesOver Y) :=
  CostructuredArrow.hasLimitsOfShape_of_isConnected

/-- The underlying-scheme functor on the test schemes over an algebraic space preserves fibre
products. -/
instance preservesLimitsOfShape_walkingCospan_testSchemeFunctor
    (Y : AlgebraicSpaces B S hS) :
    PreservesLimitsOfShape WalkingCospan (testSchemeFunctor Y) := by
  unfold testSchemeFunctor
  exact comp_preservesLimitsOfShape _ _

/-- A covering sieve of a test scheme `T` over an algebraic space for the fpqc topology on the
test schemes contains an indexed family of arrows whose underlying family of morphisms of
schemes covers `T` for the fpqc topology on schemes. -/
private theorem exists_mem_fpqcPrecoverage_family_of_mem_fpqcTopology
    {Y : AlgebraicSpaces B S hS} {T : SchemesOver Y} {R : Sieve T} (hR : R ∈ fpqcTopology Y T) :
    ∃ (I : Type (u + 1)) (T' : I → SchemesOver Y) (g : ∀ i, T' i ⟶ T), (∀ i, R.arrows (g i)) ∧
      Presieve.ofArrows (fun i ↦ (testSchemeFunctor Y).obj (T' i))
          (fun i ↦ (testSchemeFunctor Y).map (g i)) ∈
        Scheme.fpqcPrecoverage ((testSchemeFunctor Y).obj T) := by
  obtain ⟨P, hP, hPR⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨I, T', g, rfl⟩ := P.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hP
  exact ⟨I, T', g, fun i ↦ hPR _ _ (Presieve.ofArrows.mk i), hP⟩

/-- **A covering sieve of test schemes contains an fpqc covering family.** If `R` is a covering
sieve of a test scheme `T` over an algebraic space `Y` for the fpqc topology on the test
schemes, then `R` contains a family of arrows whose images under
`AlgebraicGeometry.schemeSpaceFunctor` are an fpqc covering of Stacks 03MQ of the
algebraic space represented by `T`; in particular each of them is flat. -/
theorem exists_isFpqcCovering_family_of_mem_fpqcTopology {Y : AlgebraicSpaces B S hS}
    {T : SchemesOver Y} {R : Sieve T} (hR : R ∈ fpqcTopology Y T) :
    ∃ (I : Type (u + 1)) (T' : I → SchemesOver Y) (g : ∀ i, T' i ⟶ T), (∀ i, R.arrows (g i)) ∧
      IsFpqcCovering B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) := by
  obtain ⟨I, T', g, hg, hP⟩ := exists_mem_fpqcPrecoverage_family_of_mem_fpqcTopology hR
  exact ⟨I, T', g, hg,
    represented_fpqc_family B S hS I (fun i ↦ (T' i).left) (fun i ↦ (g i).left) hP⟩

/-- **A covering sieve of test schemes contains a flat family which is jointly surjective on
points.** If `R` is a covering sieve of a test scheme `T` over an algebraic space `Y` for the
fpqc topology on the test schemes, then `R` contains a family of arrows which, read on the
algebraic spaces the test schemes represent, is an fpqc covering of Stacks 03MQ and is jointly
surjective on the points of Stacks 03BU. -/
theorem exists_isFpqcCovering_jointlySurjective_family_of_mem_fpqcTopology
    {Y : AlgebraicSpaces B S hS} {T : SchemesOver Y} {R : Sieve T} (hR : R ∈ fpqcTopology Y T) :
    ∃ (I : Type (u + 1)) (T' : I → SchemesOver Y) (g : ∀ i, T' i ⟶ T), (∀ i, R.arrows (g i)) ∧
      IsFpqcCovering B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) ∧
      IsJointlySurjective B S hS (fun i ↦ (schemeSpace (T' i).left).1)
        (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) := by
  obtain ⟨I, T', g, hg, hP⟩ := exists_mem_fpqcPrecoverage_family_of_mem_fpqcTopology hR
  refine ⟨I, T', g, hg,
    represented_fpqc_family B S hS I (fun i ↦ (T' i).left) (fun i ↦ (g i).left) hP,
    jointlySurjective_yoneda_of_scheme B S hS (fun i ↦ (T' i).left) (fun i ↦ (g i).left)
      fun x ↦ ?_⟩
  exact ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hP)).1 x

end AlgebraicGeometry.Space

end
