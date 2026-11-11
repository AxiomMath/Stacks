module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportDisjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# The derived existence theorem: the support of `Hʲ(K)` specializes into `X₀`

In the situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)` be the object of the existence theorem. Every point of the support of a
cohomology sheaf `Hʲ(K)` specializes to a point of the image of `|X₀|` in `|X|`. This is the
specialization step of the per-degree support clause of the errata entry 0DIR(support of K).

## The proof

The thickenings `Xₙ ⟶ Xₙ₊₁` are surjective on points, so every `|Xₙ|` has the same image `R₀`
in `|X|` as `|X₀|`. The set `R₀` is closed (`X₀ ⟶ X` is a closed immersion), hence compact, `|X|`
being quasi-compact. If no specialization of `x` lies in `R₀`, then `R₀` is contained in the
open complement of the closure of `x`, and since `|X|` has a basis of quasi-compact open sets
there is a quasi-compact open `O` with `R₀ ⊆ O` and `x ∉ O`. The closed set `Q = Oᶜ` has
quasi-compact complement and misses every `|Xₙ|`, so by
`AlgebraicGeometry.Space.SupportedDerivedExistenceSystem.disjoint_supportOfSheaf_homology_…`
it misses the support of `Hʲ(K)`; but `x ∈ Q`.

## Main results

* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.range_pointsMap_spaceProjection_subset`:
  the image of `|Xₙ|` in `|X|` lies in the image of `|X₀|`.
* `…SupportedDerivedExistenceSystem.exists_specializes_mem_range_of_mem_supportOfSheaf_…`: the
  main statement.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **Every `|Xₙ|` has its image in `|X|` inside the image of `|X₀|`**: the thickenings
`Xₖ ⟶ Xₖ₊₁` are surjective on points and commute with the projections to `X`. -/
theorem range_pointsMap_spaceProjection_subset (n : ℕ) :
    Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom) ⊆
      Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom) := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := surjective_pointsMap_transitionSpace D.system D.B D.containsLimitBase
      D.containsBaseAt D.X n (D.transition_surjective n) (D.transition_locallyNilpotent n) z
    refine ih ⟨w, ?_⟩
    rw [← transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n]
    exact pointsMap_comp_apply D.B _ D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)).hom w

end SeparatedDerivedExistenceSystem

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **Every point of the support of `Hʲ(K)` specializes to a point of `|X₀|`.** In the
situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)`. Every point of the support of the cohomology sheaf `Hʲ(K)` specializes
to a point of the image of `|X₀|` in `|X|`. -/
theorem exists_specializes_mem_range_of_mem_supportOfSheaf_homology_quasicoherentLimit (j : ℤ)
    (x : points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)
    (hx : x ∈ supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2).O)).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
          D.containsLimitBase D.X.left.1 D.X.left.2) j).obj
          ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
            D.X.left).ι.obj D.quasicoherentLimit)))) :
    ∃ y ∈ Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase _
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X 0).hom),
      x ⤳ y := by
  by_contra hne
  push Not at hne
  let B := D.B
  let S := limitBase D.system
  let hS := D.containsLimitBase
  let X := D.X.left
  set R₀ := Set.range (pointsMap B S hS _
    (spaceProjection D.system B hS D.containsBaseAt D.X 0).hom) with hR₀
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS D.X.hom
      D.finitePresentation.2.1
      (isAffineSpace_yoneda _ _ _ _ D.isAffine_limitBaseObject)
  have : CompactSpace (points B S hS X.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS X.2 hXqc
  have hR₀k : IsCompact R₀ :=
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 _
      (isClosedImmersion_spaceProjection D.system B hS D.containsBaseAt D.X
        D.transition_surjective 0)).isCompact
  -- a quasi-compact open neighbourhood of `R₀` avoiding `x`
  have hU : ∀ y ∈ R₀, ∃ V : Set (points B S hS X.1), IsOpen V ∧ IsCompact V ∧ y ∈ V ∧ x ∉ V :=
    fun y hy => by
      have hyU : (closure {x})ᶜ ∈ nhds y := isClosed_closure.isOpen_compl.mem_nhds
        fun hyx => hne y hy (specializes_iff_mem_closure.2 hyx)
      obtain ⟨V, hV, hVU⟩ := (hasBasis_nhds_isOpen_isCompact B S hS X.1 X.2 y).mem_iff.mp hyU
      exact ⟨V, hV.1, hV.2.1, hV.2.2, fun hxV => hVU hxV (subset_closure rfl)⟩
  choose! V hVo hVc hyV hxV using hU
  obtain ⟨t, htR, hRt⟩ := hR₀k.elim_nhds_subcover V
    fun y hy => (hVo y hy).mem_nhds (hyV y hy)
  let O := ⋃ y ∈ t, V y
  have hOo : IsOpen O := isOpen_biUnion fun y hyt => hVo y (htR y hyt)
  have hOc : IsCompact O := t.isCompact_biUnion fun y hyt => hVc y (htR y hyt)
  have hRO : R₀ ⊆ O := fun z hz => by
    obtain ⟨y, hyt, hzy⟩ := Set.mem_iUnion₂.1 (hRt hz)
    exact Set.mem_biUnion hyt hzy
  have hxO : x ∉ O := fun hx' => by
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 hx'
    exact hxV y (htR y hyt) hxy
  have hdisj := D.disjoint_supportOfSheaf_homology_quasicoherentLimit Oᶜ hOo.isClosed_compl
    (by rwa [compl_compl]) (fun n => Set.disjoint_compl_right_iff_subset.2
      ((D.range_pointsMap_spaceProjection_subset n).trans hRO)) j
  exact Set.disjoint_left.1 hdisj hx hxO

end SupportedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
