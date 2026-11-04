module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# The completion of an algebraic space along a closed subset is locally adic*

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `T ⊆ |X|` be a closed subset. **Stacks 0AQ1 (1)** says that if the inclusion `X ∖ T ⟶ X` of
the open complement is quasi-compact, then the completion `X_{/T}` is locally adic*.

## Main results

* `AlgebraicGeometry.Space.isCompact_compl_preimage_pointsMap_of_isQuasiCompact_ι`: if
  `X ∖ T ⟶ X` is quasi-compact, then for every morphism `a : U ⟶ X` from a quasi-compact scheme
  `U` of the site the complement of the inverse image of `T` in `|U|` is quasi-compact.
* `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSheaf_of_isQuasiCompact`:
  **Stacks 0AQ1 (1)**.
* `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSheaf_and_isLocallyNoetherian`:
  **Stacks 0AQ1**, both parts.

## Implementation notes

The source's proof chooses an étale covering of `X` by affine schemes `U_i`, observes that
`U_i ∖ T_i ⟶ U_i` is quasi-compact when `X ∖ T ⟶ X` is, and concludes by the affine case. Here
the charts are those of `AlgebraicGeometry.FormalSpace.exists_affine_etale_charts`, the
set-theoretic condition of Stacks 0AIS for `X_{/T}` is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`, and the chart
statement is read on points: the open subspace `U ∖ T_U` of `U` is the base change of `X ∖ T` along
`a` (`AlgebraicGeometry.Space.isPullback_openComplementRestriction`), so it is a quasi-compact
algebraic space when `U` is, and its point set, the complement of the inverse image of `T`, is then
quasi-compact (Stacks 03E4). These feed the atlas argument
`AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSheaf`.

## References

* [Stacks Project, Tag 0AQ1](https://stacks.math.columbia.edu/tag/0AQ1)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Quasi-compactness of `X ∖ T ⟶ X` restricts to the charts.** Let `X` be an algebraic space
over `S`, let `T ⊆ |X|` be closed with `X ∖ T ⟶ X` quasi-compact, and let `a : U ⟶ X` be a
morphism from a scheme `U` of the site with quasi-compact underlying space. Then the complement
of the inverse image of `T` in `|U|` is quasi-compact.

The base change of `X ∖ T ⟶ X` along `a` is a quasi-compact algebraic space, hence has
quasi-compact point space (Stacks 03E4), and its points map onto the inverse image of `X ∖ T`
(Stacks 03H4). -/
theorem isCompact_compl_preimage_pointsMap_of_isQuasiCompact_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (hqc : IsQuasiCompact B S hS (openSubspaceOfPoints B S hS X Tᶜ).ι)
    (U : BigFppfOver B S hS) [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (a : yoneda.obj U ⟶ X) :
    IsCompact (pointsMap B S hS _ a ⁻¹' T)ᶜ := by
  let O := openSubspaceOfPoints B S hS X Tᶜ
  have hO : IsOpenSubspace B S hS O :=
    isOpenSubspace_openSubspaceOfPoints_compl_of_isClosed B S hS hX T hT
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hPqc : IsQuasiCompactSpace B S hS (pullback a O.ι) :=
    hqc (yoneda.obj U) hU (isQuasiCompact_yoneda_of_compact B S hS U inferInstance) a
  have : CompactSpace (points B S hS (pullback a O.ι)) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS
      (isAlgebraicSpace_pullback B S hS a O.ι hU hO.1 hX) hPqc
  have hsq : IsPullback (pullback.fst a O.ι) (pullback.snd a O.ι) a O.ι :=
    IsPullback.of_hasPullback _ _
  have hrange : Set.range (pointsMap B S hS _ (pullback.fst a O.ι)) =
      (pointsMap B S hS _ a ⁻¹' T)ᶜ := by
    rw [← Set.preimage_compl]
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [Set.mem_preimage, ← pointsMap_comp_apply, hsq.w, pointsMap_comp_apply,
        ← range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ]
      exact Set.mem_range_self _
    · intro hx
      rw [Set.mem_preimage, ← range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ] at hx
      obtain ⟨y, hy⟩ := hx
      obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS hsq x y hy.symm
      exact ⟨w, hw⟩
  rw [← hrange]
  exact isCompact_range (continuous_pointsMap B S hS (pullback.fst a O.ι))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0AQ1, part (1).** Let `S` be a scheme, let `X` be an algebraic space over `S` and
let `T ⊆ |X|` be a closed subset such that the inclusion `X ∖ T ⟶ X` of the open complement is
quasi-compact. Then the completion `X_{/T}` of `X` along `T` is locally adic*.

The affine étale charts `Spec A_k ⟶ X` are those of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_charts`; on each, the complement of the
inverse image of `T` is quasi-compact
(`AlgebraicGeometry.Space.isCompact_compl_preimage_pointsMap_of_isQuasiCompact_ι`), and the
set-theoretic condition of Stacks 0AIS is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`. With these the
atlas argument of `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSheaf` applies. -/
@[stacks 0AQ1 "part (1)"]
theorem isLocallyAdicStar_completionSheaf_of_isQuasiCompact
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hqc : Space.IsQuasiCompact B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) :
    IsLocallyAdicStar B S hS (Space.completionSheaf B S hS X T) := by
  obtain ⟨U₀, K, A, _, hA, str, a, -, -, het, hcov⟩ := exists_affine_etale_charts hX
  refine isLocallyAdicStar_completionSheaf hX T hT (Ix := ULift.{u + 1} K)
    (A := fun i ↦ A i.down) (fun i ↦ hA i.down) (fun i ↦ str i.down) (fun i ↦ a i.down)
    (fun i ↦ exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS _) hX (a i.down) (het i.down))
    hcov (fun i ↦ ?_) (satisfiesSetTheoreticCondition_completionSheaf hX T hT)
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (affineOver B S hS (hA i.down) (str i.down))) :=
    inferInstanceAs (CompactSpace (Spec (.of (A i.down))))
  exact Space.isCompact_compl_preimage_pointsMap_of_isQuasiCompact_ι hX hT hqc _ (a i.down)

/-- **Stacks 0AQ1.** Let `S` be a scheme, let `X` be an algebraic space over `S`, let `T ⊆ |X|`
be a closed subset and let `X_{/T}` be the completion of `X` along `T`.

1. If `X ∖ T ⟶ X` is quasi-compact, then `X_{/T}` is locally adic*.
2. If `X` is locally Noetherian, then `X_{/T}` is locally Noetherian.

The two parts are
`AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSheaf_of_isQuasiCompact` and
`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian`. -/
@[stacks 0AQ1]
theorem isLocallyAdicStar_completionSheaf_and_isLocallyNoetherian
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : @IsClosed _ (Space.pointTopology B S hS X) T) :
    (Space.IsQuasiCompact B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ).ι →
        IsLocallyAdicStar B S hS (Space.completionSheaf B S hS X T)) ∧
      (Space.IsLocallyNoetherian B S hS X →
        IsLocallyNoetherian B S hS (Space.completionSheaf B S hS X T)) :=
  ⟨isLocallyAdicStar_completionSheaf_of_isQuasiCompact hX T hT,
    fun hXN ↦ isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX hXN T hT⟩

end AlgebraicGeometry.FormalSpace

end
