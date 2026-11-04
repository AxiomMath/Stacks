module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleComparisonSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImageComparisonOfBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSitePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ProperRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheafProperBaseChange

/-!
# The ph topology and the étale topology form a comparison situation

Let `B` be a chosen big ph site. Its underlying category carries the ph topology and, through
`AlgebraicGeometry.phAssociatedBigEtaleSite`, the étale topology. Stacks 0F0I says that the pair
(ph, étale), with the proper morphisms as distinguished class and the sheaves `π_X⁻¹F` pulled back
from torsion abelian sheaves on the small étale sites as the classes `𝒜'_X`, satisfies the
assumptions of the comparison situation of Stacks 0EZ3.

The étale-side part of the situation, which does not depend on the finer topology, is
`AlgebraicGeometry.properEtaleCohomologyComparison`. This file supplies the three ph-specific
inputs: étale coverings are ph coverings, the ph sheaf condition for `π_X⁻¹F` (Stacks 0DDW), and
the refinement of a ph covering by an étale covering, a single proper surjection over each member
and an étale covering of its source (property 0EZ8).

## Main results

* `AlgebraicGeometry.BigPHSite.etalePrecoverage_le_precoverage` — étale coverings are ph
  coverings.
* `AlgebraicGeometry.BigPHSite.exists_properRefinement` — **property 0EZ8** for the ph topology.
* `AlgebraicGeometry.phEtaleCohomologyComparison` — **Stacks 0F0I**.

## Implementation notes

The refinement follows the definition of a ph covering (Stacks 0DBG) rather than the source's
route through Stacks 0DET: over each affine open `U` of the target, a ph covering is refined by a
standard ph covering of `U`, which is presented by a proper surjection `W ⟶ U` and a finite
affine open covering of `W`. The affine opens of the target form the étale covering, the proper
surjection is a ph covering by Stacks 0DES, and the affine open covering of `W` is the étale
covering of its source; the three stages are assembled from this affine-local step by
`AlgebraicGeometry.BigEtaleSite.exists_properRefinement_of_affine`, shared with the h topology.
Every scheme involved lies in the size-bounded category of the site:
open subschemes by Stacks 000R (4), and `W` by Stacks 000R (5), being of finite type over `U`.

Stacks 0F0I is proved as `AlgebraicGeometry.phEtaleCohomologyComparison`, with two inputs that rest
on the proper base change theorem: `h0A3U`, Stacks 0A3U for sheaves of sets, which gives the ph
sheaf condition of Stacks 0DDW; and `h095T`, Stacks 095T, which gives the comparison of higher
direct images along proper morphisms of Stacks 0DDJ (2)
(`AlgebraicGeometry.properDirectImageComparison_of_cohomologyCommutesWithBaseChange`). It carries
no `@[stacks 0F0I]` tag, since it takes both inputs as hypotheses.

## References

* [Stacks Project, Tag 0F0I](https://stacks.math.columbia.edu/tag/0F0I)
* [Stacks Project, Tag 0DBG](https://stacks.math.columbia.edu/tag/0DBG)
* [Stacks Project, Tag 0DES](https://stacks.math.columbia.edu/tag/0DES)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigPHSite

variable (B : BigPHSite.{u})

/-- Étale coverings of the underlying category of a big ph site are ph coverings: the precoverage
of the associated big étale site is contained in the precoverage of the ph site. -/
public theorem etalePrecoverage_le_precoverage :
    (phAssociatedBigEtaleSite B).precoverage ≤ B.precoverage := by
  intro X R hR
  obtain ⟨E, hR, hE⟩ := hR
  exact ⟨E, hR, ((etaleBounded_eq_phEtaleBounded B ⟨X, E⟩).mpr hE).1⟩

/-- **Property 0EZ8 for the ph topology.** Every ph covering of an object `U` of a big ph site is
refined in three stages: by an étale covering `{V ⟶ U}`, then by a single proper surjection
`W ⟶ V` over each member, which is a ph covering, and finally by an étale covering of `W`.

The étale covering consists of the affine opens of `U`. Over an affine open `V` the definition
of a ph covering (Stacks 0DBG) provides a standard ph covering of `V` refining the given one; it
is presented by a proper surjection `W ⟶ V`, a ph covering by Stacks 0DES, and a finite affine
open covering of `W` whose members map into members of the given covering. -/
public theorem exists_properRefinement (U : B.Schemes) (R : Presieve U)
    (hR : R ∈ B.precoverage U) :
    ∃ S : Presieve U, S ∈ (phAssociatedBigEtaleSite B).precoverage U ∧
      ∀ ⦃V : B.Schemes⦄ (v : V ⟶ U), S v →
        ∃ (W : B.Schemes) (f : W ⟶ V), IsProper (B.inclusion.map f) ∧
          Presieve.singleton f ∈ B.precoverage V ∧
          ∃ T : Presieve W, T ∈ (phAssociatedBigEtaleSite B).precoverage W ∧
            T.FactorsThruAlong R (f ≫ v) :=
  (phAssociatedBigEtaleSite B).exists_properRefinement_of_affine B.precoverage fun O hO => by
    obtain ⟨E, rfl, hE⟩ := hR
    have hph : IsPHCovering (E.map B.inclusion).X (E.map B.inclusion).f := hE.1
    have : IsAffine O.toScheme := hO
    obtain ⟨𝒰, h𝒰, ⟨ψ⟩⟩ := hph.2 O hO
    obtain ⟨W₀, p, j, hp, hps, hj, hcov, hcomp⟩ := h𝒰.exists_presentation
    have := hp
    have := hps
    have hW : W₀.size < B.cutoff := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p
      (Scheme.size_lt_of_isOpenImmersion O.ι U.2)
    let W : B.Schemes := ⟨W₀, hW⟩
    let f : W ⟶ B.obj O.toScheme (Scheme.size_lt_of_isOpenImmersion O.ι U.2) := ⟨p⟩
    refine ⟨W, f, hp, ?_, 𝒰.I₀, 𝒰.X, j, hj, hcov, fun k => ?_⟩
    · have hs : (PreZeroHypercover.singleton.{u + 1} f).presieve₀ = Presieve.singleton f := by
        simp
      rw [← hs, B.mem_precoverage_iff_isPHCovering]
      exact (surjective_proper_isPHCovering p).reindex Equiv.punitEquivPUnit
    · let s : E.I₀ := ψ.s₀ k
      let h : 𝒰.X k ⟶ pullback (B.inclusion.map (E.f s)) O.ι := ψ.h₀ k
      have hw : h ≫ pullback.snd (B.inclusion.map (E.f s)) O.ι = 𝒰.f k := ψ.w₀ k
      refine ⟨E.X s, E.f s, Presieve.ofArrows.mk _,
        h ≫ pullback.fst (B.inclusion.map (E.f s)) O.ι, ?_⟩
      have hc : pullback.fst (B.inclusion.map (E.f s)) O.ι ≫ B.inclusion.map (E.f s) =
          pullback.snd _ O.ι ≫ O.ι := pullback.condition
      calc (h ≫ pullback.fst (B.inclusion.map (E.f s)) O.ι) ≫ B.inclusion.map (E.f s)
          = (h ≫ pullback.snd (B.inclusion.map (E.f s)) O.ι) ≫ O.ι := by
            rw [Category.assoc, hc, Category.assoc]
        _ = j k ≫ p ≫ O.ι := by rw [hw, ← hcomp k, Category.assoc]

end BigPHSite

/-- **Stacks 0F0I, closing-ready**, untagged while the proper base change inputs are hypotheses.
For a big ph site `B`, the comparison of the ph topology with the étale
topology on its underlying category, with the proper morphisms as distinguished class `𝒫` and,
over every object `X`, the class `𝒜'_X` of abelian sheaves `π_X⁻¹F` on `(Sch/X)_étale` with `F` a
torsion abelian sheaf on `X_étale`, satisfies properties (0EZ4)–(0EZ8) of the comparison situation
of Stacks 0EZ3; and `𝒜'_X` is a weak Serre subcategory.

The weak Serre property, (0EZ4) and (0EZ5) are proved in
`AlgebraicGeometry.properEtaleCohomologyComparison`, and (0EZ8) is
`AlgebraicGeometry.BigPHSite.exists_properRefinement`. Two inputs rest on the proper base change
theorem: `h0A3U`, Stacks 0A3U for sheaves of sets, from which (0EZ6) — the sheaves `π_X⁻¹F` are ph
sheaves, Stacks 0DDW — is deduced; and `h095T`, Stacks 095T, which gives the comparison of higher
direct images along proper morphisms of Stacks 0DDJ (2), from which (0EZ7) is deduced together with
Stacks 0DDD (1)
(proved, `AlgebraicGeometry.SmallEtale.torsionSheafProperty_rightDerived_smallPushforward`). -/
public def phEtaleCohomologyComparison (B : BigPHSite.{u})
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f) :
    Stacks.ComparingTopologies.CohomologyComparison (phAssociatedBigEtaleSite B).Scheme :=
  properEtaleCohomologyComparison (phAssociatedBigEtaleSite B) B.precoverage
    (BigPHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
    (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
    (BigPHSite.exists_properRefinement B)

section Fields

variable (B : BigPHSite.{u})
  (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g), IsProper f →
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
  (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
    Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)

/-- The finer topology of `phEtaleCohomologyComparison` is the ph topology of `B`. -/
@[simp]
public theorem phEtaleCohomologyComparison_fineCoverage :
    (phEtaleCohomologyComparison B h0A3U h095T).fineCoverage = B.precoverage := rfl

/-- The coarser topology of `phEtaleCohomologyComparison` is the étale topology of `B`. -/
@[simp]
public theorem phEtaleCohomologyComparison_coarseCoverage :
    (phEtaleCohomologyComparison B h0A3U h095T).coarseCoverage =
      (phAssociatedBigEtaleSite B).precoverage := rfl

/-- The distinguished class of `phEtaleCohomologyComparison` is the class of proper morphisms. -/
@[simp]
public theorem phEtaleCohomologyComparison_morphismProperty :
    (phEtaleCohomologyComparison B h0A3U h095T).morphismProperty =
      fun _ _ f => IsProper ((phAssociatedBigEtaleSite B).inclusion.map f) := rfl

/-- The class `𝒜'_X` of `phEtaleCohomologyComparison` consists of the sheaves `π_X⁻¹F` with `F` a
torsion abelian sheaf on `X_étale`. -/
@[simp]
public theorem phEtaleCohomologyComparison_weakSerre (X : (phAssociatedBigEtaleSite B).Scheme) :
    (phEtaleCohomologyComparison B h0A3U h095T).weakSerre X =
      smallEtaleTorsionPullbackClass (phAssociatedBigEtaleSite B) X
        ((phAssociatedBigEtaleSite B).topology.over X) := rfl

end Fields

end AlgebraicGeometry

end
