module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Equiv

/-!
# The slice equivalence is an equivalence of sites

`AlgebraicGeometry.smallEtaleEquivalenceOver` identifies the small étale site of an object `U`
of the small étale site of `X` with the slice of the latter over `U`. This file shows that the
identification carries the étale topology of `U` to the localized topology at `U`, so that it
is an equivalence of sites and not merely of categories.

Both directions of cover preservation come down to the same observation: a covering family of
the small étale site of `U` and its image in the slice are the same family of schemes and
arrows, only read in different categories. Translating between a covering sieve and a covering
family in the first place uses that the small étale precoverage is stable under composition and
base change, has isomorphisms, and has fibre products; translating between a sieve on an object
of the slice and a sieve on its underlying object uses `CategoryTheory.Sieve.overEquiv`. The
topologies are then identified by the general theory of dense subsites: an equivalence of
categories which is cocontinuous in both directions exhibits each topology as the one induced
from the other.

## Main results

* `AlgebraicGeometry.smallEtaleEquivalenceOver_functor_coverPreserving` and
  `AlgebraicGeometry.smallEtaleEquivalenceOver_inverse_coverPreserving` — the equivalence and
  its inverse preserve covering sieves.
* `AlgebraicGeometry.smallEtaleEquivalenceOver_topology` — the topology induced along the
  equivalence from the localized topology at `U` is the étale topology of `U`.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- The slice equivalence carries covering sieves of the small étale site of `U` to covering
sieves of the localization of the small étale site of `X` at `U`. -/
public theorem smallEtaleEquivalenceOver_functor_coverPreserving :
    CoverPreserving (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      ((SmallEtale.topology B X hX).over U)
      (smallEtaleEquivalenceOver B X hX U).functor := by
  let e := smallEtaleEquivalenceOver B X hX U
  let G := Over.forget U
  constructor
  intro V S hS
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, hR, hRS⟩ := hS
  rw [SmallEtale.mem_precoverage_iff] at hR
  obtain ⟨E, rfl, hE⟩ := hR
  have hEbase : (E.map (e.functor ⋙ G)).presieve₀ ∈
      SmallEtale.precoverage B X hX (G.obj (e.functor.obj V)) := by
    rw [SmallEtale.mem_precoverage_iff]
    exact ⟨E.map (e.functor ⋙ G), rfl, hE⟩
  have hGen : Sieve.generate (E.map e.functor).presieve₀ ∈
      ((SmallEtale.topology B X hX).over U) (e.functor.obj V) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    have hle : (E.map (e.functor ⋙ G)).presieve₀ ≤
        Presieve.functorPushforward G ((E.map e.functor).presieve₀) := by
      rintro Y f ⟨i⟩
      exact Presieve.image_mem_functorPushforward G _ ⟨i⟩
    exact (SmallEtale.topology B X hX).superset_covering (Sieve.generate_mono hle)
      (Precoverage.generate_mem_toGrothendieck hEbase)
  apply ((SmallEtale.topology B X hX).over U).superset_covering ?_ hGen
  rw [PreZeroHypercover.presieve₀_map, Sieve.generate_map_eq_functorPushforward]
  exact Sieve.functorPushforward_monotone _ _ ((Sieve.generate_le_iff _ _).2 hRS)

/-- The inverse of the slice equivalence carries covering sieves of the localization of the
small étale site of `X` at `U` to covering sieves of the small étale site of `U`. -/
public theorem smallEtaleEquivalenceOver_inverse_coverPreserving :
    CoverPreserving ((SmallEtale.topology B X hX).over U)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (smallEtaleEquivalenceOver B X hX U).inverse := by
  let e := smallEtaleEquivalenceOver B X hX U
  have : (SmallEtale.precoverage B X hX).IsStableUnderBaseChange :=
    smallEtale_precoverage_stableUnderBaseChange B X hX
  constructor
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨Q, hQ, hQR⟩ := hR
  rw [SmallEtale.mem_precoverage_iff] at hQ
  obtain ⟨E, rfl, hE⟩ := hQ
  let E' : PreZeroHypercover T :=
    { I₀ := E.I₀
      X i := Over.mk (E.f i ≫ T.hom)
      f i := Over.homMk (E.f i) (by simp) }
  have hESource : (E'.map e.inverse).presieve₀ ∈
      SmallEtale.precoverage B U.obj.left.1 U.obj.left.property (e.inverse.obj T) := by
    rw [SmallEtale.mem_precoverage_iff]
    exact ⟨E'.map e.inverse, rfl, hE⟩
  have hE'le : E'.presieve₀ ≤ R.arrows := by
    rintro Z g ⟨i⟩
    have hbase : (Sieve.overEquiv T R).arrows (E.f i) := hQR _ _ ⟨i⟩
    rwa [Sieve.overEquiv_iff] at hbase
  apply (SmallEtale.topology B U.obj.left.1 U.obj.left.property).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hESource)
  rw [Sieve.generate_le_iff, PreZeroHypercover.presieve₀_map]
  exact (Presieve.map_le_functorPushforward e.inverse E'.presieve₀).trans
    (Presieve.functorPushforward_monotone hE'le)

/-- **The slice equivalence is an equivalence of sites.** The topology induced along
`AlgebraicGeometry.smallEtaleEquivalenceOver` from the localization of the small étale topology
of `X` at `U` is the small étale topology of `U`. -/
public theorem smallEtaleEquivalenceOver_topology :
    (smallEtaleEquivalenceOver B X hX U).functor.inducedTopology
        ((SmallEtale.topology B X hX).over U) =
      SmallEtale.topology B U.obj.left.1 U.obj.left.property := by
  let e := smallEtaleEquivalenceOver B X hX U
  let J := SmallEtale.topology B U.obj.left.1 U.obj.left.property
  let K := (SmallEtale.topology B X hX).over U
  have : e.functor.IsCoverDense K := inferInstance
  have : e.functor.IsCocontinuous J K :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving J K).2
      (smallEtaleEquivalenceOver_inverse_coverPreserving B X hX U)
  have : e.inverse.IsCocontinuous K J :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2
      (smallEtaleEquivalenceOver_functor_coverPreserving B X hX U)
  have : e.inverse.IsDenseSubsite K J :=
    Equivalence.isDenseSubsite_inverse_of_isCocontinuous J K e
  have hJ : J = e.functor.inducedTopology (e.inverse.inducedTopology J) := by
    ext V S
    simp [Functor.mem_inducedTopology_iff_of_isCoverDense,
      Sieve.functorPushforward_equivalence_eq_pullback]
  change e.functor.inducedTopology K = J
  rw [Equivalence.eq_inducedTopology_of_isDenseSubsite J K e, ← hJ]

end AlgebraicGeometry
