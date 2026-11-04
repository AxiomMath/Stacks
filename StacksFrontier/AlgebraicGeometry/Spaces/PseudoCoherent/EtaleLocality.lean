module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.SiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# Pseudo-coherence on an algebraic space is étale local

Let `X` be an algebraic space over a scheme `S` and let `K` be a complex of `𝒪_X`-modules on the
small étale site. This file proves that `m`-pseudo-coherence of `K` (Stacks 08FT) is local for
the étale topology in the two forms the descent arguments for algebraic spaces use:

* restriction along an étale morphism `f : Y ⟶ X` of algebraic spaces preserves it;
* if every chart `U` of `X` has a covering `{V ⟶ U}` such that `K` restricted to each algebraic
  space `V` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_etaleModulePullback`: étale restriction
  preserves `m`-pseudo-coherence of a complex.
* `AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_of_charts`: `m`-pseudo-coherence of a
  complex can be checked on the charts of coverings.

## Implementation notes

Both statements rest on the slice form of Stacks 04M0: for an étale `f : Y ⟶ X` and a chart `W`
of `Y`, postcomposition with `f` is an equivalence of the slice of the small étale site of `Y`
at `W` with the slice of the small étale site of `X` at the composite chart
(`AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence`), and the restriction of
the étale pullback of a module to the slice at `W` is, on the nose, the reindexing of the
restriction of the module to the slice at the composite chart. So the local data of
pseudo-coherence correspond (`Stacks.SheafOfModules.hasStrictlyPerfectApproximation_reindex_iff`)
and only the covering families need to be moved, by cover lifting along postcomposition in one
direction and by cover preservation in the other.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive

/-! ### Étale restriction -/

/-- Having a strictly perfect approximation of the étale restriction `f^*K` at an object `W` of the
small étale site of `Y` is equivalent to having one of `K` at the composite chart `f ∘ W`. -/
private theorem hasStrictlyPerfectApproximation_pullback_iff {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (m : ℤ)
    (W : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).HasStrictlyPerfectApproximation
        (((etaleModulePullback B S hS f hf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m
        W ↔
      (smallEtaleRingedSite B S hS X.1 X.2).HasStrictlyPerfectApproximation K m
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj W) :=
  exists_strictlyPerfect_approximation_reindex_iff
    (J' := (smallEtaleRingedSite B S hS Y.1 Y.2).J.over W)
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf W)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj W))
    ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj W)) m

section Etale

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)

/-- **Étale restriction preserves `m`-pseudo-coherence.** If `K` is an `m`-pseudo-coherent
complex of `𝒪_X`-modules and `f : Y ⟶ X` is étale, then the étale restriction `f^*K` is an
`m`-pseudo-coherent complex of `𝒪_Y`-modules. -/
theorem isPseudoCoherentComplexFrom_etaleModulePullback
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (m : ℤ)
    (hK : RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2) K m) :
    RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
      (smallEtaleRingedSite B S hS Y.1 Y.2)
      (((etaleModulePullback B S hS f hf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m := by
  let ψ := smallEtaleRingedSitePostcomp B S hS f hf
  refine (RingedSite.isPseudoCoherentComplexFrom_iff _ _ m).2
    fun U => ?_
  obtain ⟨T, hT, hdata⟩ :=
    (RingedSite.isPseudoCoherentComplexFrom_iff _ K m).1 hK
      (ψ.obj U)
  refine ⟨((Sieve.generate T).functorPullback ψ).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact SmallEtale.smallEtalePostcomp_cover_lift B S hS f hf U _ hT
  · rintro W g ⟨W₀, a, g₀, hg₀, -⟩
    exact (hasStrictlyPerfectApproximation_pullback_iff B S hS f hf K m W).2
      (RingedSite.hasStrictlyPerfectApproximation_of_hom _ K m a (hdata g₀ hg₀))

end Etale

/-! ### Checking pseudo-coherence on charts -/

section Charts

variable {X : AlgebraicSpaces B S hS}

/-- The identity chart of the algebraic space represented by a chart `V` of `X` becomes `V`
itself under postcomposition with the structure morphism of `V`. -/
def postcompIdEtaleChartIso (V : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (smallEtaleRingedSitePostcomp B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) ≅ V :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom]
    exact (Category.id_comp _).symm))

/-- The sieve of all arrows into `U` whose source carries a strictly perfect approximation of
the restriction of `K` in degrees `≥ m`. -/
def approximationSieve (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (m : ℤ)
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) : Sieve U where
  arrows Z _ := (smallEtaleRingedSite B S hS X.1 X.2).HasStrictlyPerfectApproximation K m Z
  downward_closed hZ g := RingedSite.hasStrictlyPerfectApproximation_of_hom _ K m g hZ

/-- The pullback of `approximationSieve K m U` along `f : V ⟶ U` is `approximationSieve K m V`. -/
theorem approximationSieve_pullback (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (m : ℤ) {U V : (smallEtaleRingedSite B S hS X.1 X.2).C} (f : V ⟶ U) :
    (approximationSieve B S hS K m U).pullback f = approximationSieve B S hS K m V :=
  rfl

/-- If the restriction of `K` to the algebraic space represented by a chart `V` is
`m`-pseudo-coherent, then the objects over which `K` admits a strictly perfect approximation
cover `V`. -/
theorem approximationSieve_mem_of_chart (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (m : ℤ) (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (hV : RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
      (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2)
      (((etaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m) :
    approximationSieve B S hS K m V ∈ (smallEtaleRingedSite B S hS X.1 X.2).J V := by
  let φ := chartToSpace B S hS X V
  let hφ := isEtale_chartToSpace B S hS X V
  let ψ := smallEtaleRingedSitePostcomp B S hS φ hφ
  obtain ⟨T, hT, hdata⟩ :=
    (RingedSite.isPseudoCoherentComplexFrom_iff _ _ m).1 hV
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))
  have hcov : ((Sieve.generate T).functorPushforward ψ).pullback
      (postcompIdEtaleChartIso B S hS V).inv ∈ (smallEtaleRingedSite B S hS X.1 X.2).J V :=
    (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable _
      ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS φ hφ).cover_preserve hT)
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering ?_ hcov
  rintro Z k ⟨W, g, h, ⟨W₀, c, g₀, hg₀, rfl⟩, -⟩
  have h₀ := (hasStrictlyPerfectApproximation_pullback_iff B S hS φ hφ K m W₀).1
    (hdata g₀ hg₀)
  exact RingedSite.hasStrictlyPerfectApproximation_of_hom _ K m (h ≫ ψ.map c) h₀

/-- **`m`-pseudo-coherence can be checked on charts.** If every chart `U` of `X` admits a
covering `{V ⟶ U}` such that the restriction of `K` to each algebraic space `V` is
`m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentComplexFrom_of_charts
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (m : ℤ)
    (h : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C, ∃ T : Presieve U,
      Sieve.generate T ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U ∧
        ∀ ⦃V : (smallEtaleRingedSite B S hS X.1 X.2).C⦄ (f : V ⟶ U), T f →
          RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
            (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2)
            (((etaleModulePullback B S hS (chartToSpace B S hS X V)
              (isEtale_chartToSpace B S hS X V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) m) :
    RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2) K m := by
  refine (RingedSite.isPseudoCoherentComplexFrom_iff _ _ m).2
    fun U => ?_
  obtain ⟨T, hT, hdata⟩ := h U
  refine ⟨(approximationSieve B S hS K m U).arrows, ?_, fun _ _ hZ => hZ⟩
  rw [Sieve.generate_sieve]
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive hT _ ?_
  rintro V f ⟨V₀, b, f₀, hf₀, rfl⟩
  rw [approximationSieve_pullback, ← approximationSieve_pullback B S hS K m b]
  exact (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable b
    (approximationSieve_mem_of_chart B S hS K m V₀ (hdata f₀ hf₀))

end Charts

end AlgebraicGeometry.Space
