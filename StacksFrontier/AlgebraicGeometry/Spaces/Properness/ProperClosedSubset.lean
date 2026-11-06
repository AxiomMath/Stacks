module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism

/-!
# Properness over a base of a closed subset of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, and let `T` be a closed subset of the points of `X`. Properness over `Y` of a closed
subspace of `X` supported on `T` does not depend on which closed subspace it is: the reduced
induced one is proper over `Y` exactly when some closed subspace with that support is, exactly
when every closed subspace with that support is. So
`AlgebraicGeometry.Space.IsProperOver`, which is defined through the reduced induced subspace,
may be tested on any closed subspace cut out on `T`; and conversely it transfers properness to
all of them.

The argument is a single reduction, isolated here as
`AlgebraicGeometry.Space.isProper_ι_comp_of_isProper_ι_comp`: both closed subspaces receive the
reduced induced one, by the factorization criterion of Stacks 03JJ, and both receiving morphisms
are proper and surjective enough that properness passes from the reduced induced subspace to each
of them by Stacks 08AJ.

Stacks 0CZE -- a closed subset of a closed subset proper over the base is itself proper over
the base -- follows by the same reduction and is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset`.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_ι_reducedClosedSubspace`,
  `AlgebraicGeometry.Space.universallyClosed_ι_reducedClosedSubspace` and
  `AlgebraicGeometry.Space.isProper_ι_reducedClosedSubspace`: the inclusion of the reduced
  closed subspace is locally of finite type, universally closed, and proper.
* `AlgebraicGeometry.Space.isProper_of_comp_eq_ι_reducedClosedSubspace`: a factorization of that
  inclusion through a monomorphism is proper.
* `AlgebraicGeometry.Space.isProperOver_of_isProper_ι_comp`: a closed set of points through
  which the reduced induced subspace factors into a subspace proper over the base is itself
  proper over the base.
* `AlgebraicGeometry.Space.isProper_reducedClosedSubspace_iff_exists`: **Stacks 0CZC**,
  conditions (1) and (2).
* `AlgebraicGeometry.Space.exists_isProper_closedSubspace_iff_forall`: **Stacks 0CZC**,
  conditions (2) and (3).

## Implementation notes

That the reduced induced subspace on a closed set of points is a *closed* subspace — that its
inclusion is representable by closed immersions — is the effective descent of a closed subscheme
along an étale chart, namely Stacks 02W8 at the closed immersions; it is
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent`
applied to
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`.
Only the two statements of Stacks 0CZC need it; the properness statements that precede them do
not, and are proved without any descent. Properness of a morphism is not a
representability condition: `AlgebraicGeometry.Space.IsSeparated` asks that the relative
diagonal be a closed immersion, and the relative diagonal of a monomorphism is an isomorphism;
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` is a condition on commuting squares of étale
charts, which Stacks 03MJ lets one check on a single surjective one; and
`AlgebraicGeometry.Space.UniversallyClosed` is a condition on the point sets of presheaf fibre
products, which Stacks 03IT lets one check after base change along a single surjective étale
chart. Over the chart `φ` of `X` the base change of the inclusion is the reduced induced closed
subscheme of the chart, a closed immersion of schemes, and that is all three clauses. The same
observation makes the inclusion of the reduction universally open, in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Reduction.lean`.

The two statements of Stacks 0CZC are the exception. Both of them *assert the existence* of a
closed subspace with point set `T` — condition (2) of the source — and no amount of properness
produces one: existence is exactly the clause of Stacks 03IQ that needs the descent. Each
therefore opens by discharging that clause from
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, so neither
carries a hypothesis the source does not have.

The factorization of the reduced induced subspace through an arbitrary closed subspace with the
same point set is `AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset`,
Stacks 03JJ; for a target which is itself a reduced induced subspace the unconditional form
`AlgebraicGeometry.Space.exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset` is used
instead.

## References

* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_ProperClosedSubset
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ProperClosedSubset :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### The inclusion of a reduced closed subspace, computed on a chart -/

section Chart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- **The reduced closed subspace computed from a chart has a surjective étale chart presented
by a closed immersion into the chart, cartesian over it.**

This is `AlgebraicGeometry.Space.exists_reducedChart` together with the two facts about the
presenting morphism of the site that the properness statements of this file use: that its
underlying morphism of schemes is a closed immersion, the reduced induced closed subscheme of
the chart being one, and that the square it sits in is cartesian. -/
theorem exists_isPullback_closedImmersion_reducedChart (T : Set (points B S hS X))
    (hT : IsClosed T) :
    ∃ (V : BigFppfOver B S hS) (i : V ⟶ U)
      (k : yoneda.obj V ⟶ (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
        IsPullback k (yoneda.map i) (reducedClosedSubspaceOfChart B S hS φ T hT).ι φ := by
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS (atlasReducedSubscheme B S hS φ T hT)
    (isImmersion_arrow_atlasReducedSubscheme B S hS φ T hT)
  obtain ⟨k, hk⟩ := exists_isPullback_yoneda_presentation B S hS hs
    (atlasReducedSubscheme B S hS φ T hT)
    (isInvariantSubscheme_atlasReducedSubscheme B S hS hs he T hT) i e hei
  refine ⟨V, i, k, ?_, hk⟩
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.respectsIso
  rw [← hei]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) e.hom
    (atlasReducedSubscheme B S hS φ T hT).arrow).2
    (isClosedImmersion_arrow_atlasReducedSubscheme B S hS φ T hT)

include hs he in
/-- **The inclusion of the reduced closed subspace computed from a chart is locally of finite
type**, with no descent hypothesis.

Being locally of finite type is a condition on commuting squares of étale charts, and by
Stacks 03MJ it suffices to exhibit one such square whose chart of the source is surjective. The
chart of `AlgebraicGeometry.Space.exists_isPullback_closedImmersion_reducedChart` is one, and the
morphism of the site it sits over is a closed immersion of schemes. -/
theorem isLocallyOfFiniteType_ι_reducedClosedSubspaceOfChart (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsLocallyOfFiniteType B S hS (reducedClosedSubspaceOfChart B S hS φ T hT).ι := by
  obtain ⟨V, i, k, hci, hk⟩ :=
    exists_isPullback_closedImmersion_reducedChart B S hS hs he T hT
  have hstabs := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hstabe := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_reducedClosedSubspaceOfChart B S hS hs he hX T hT) hX
    (reducedClosedSubspaceOfChart B S hS φ T hT).ι).2
    ⟨V, U, k, φ, i, MorphismProperty.of_isPullback hk.flip he, he,
      MorphismProperty.of_isPullback hk.flip hs, hk.w.symm, ?_⟩
  have _hci : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map i) := hci
  exact inferInstance

include hs he in
/-- **The inclusion of the reduced closed subspace computed from a chart is universally
closed**, with no descent hypothesis.

Universal closedness is a condition on the point sets of presheaf fibre products, so by
Stacks 03IT it may be checked after base change along the chart; there the inclusion becomes
the reduced induced closed subscheme of the chart, a closed immersion of schemes. -/
theorem universallyClosed_ι_reducedClosedSubspaceOfChart (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    UniversallyClosed B S hS (reducedClosedSubspaceOfChart B S hS φ T hT).ι := by
  obtain ⟨V, i, k, hci, hk⟩ :=
    exists_isPullback_closedImmersion_reducedChart B S hS hs he T hT
  have hR : IsAlgebraicSpace B S hS (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor :=
    isAlgebraicSpace_reducedClosedSubspaceOfChart B S hS hs he hX T hT
  refine universallyClosed_of_etale_atlas B S hS hX
    (reducedClosedSubspaceOfChart B S hS φ T hT).ι U φ
    (isSurjective_of_presheafSurjective B S hS φ hs)
    ((isEtale_iff_presheaf_of_yoneda B S hS φ).2 he) ?_
  have hUCi : UniversallyClosed B S hS (yoneda.map i) :=
    universallyClosed_of_isClosedImmersion B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS U) (yoneda.map i)
      (presheaf_yoneda_map_of_inverseImage B S hS inferInstance i hci)
  have hP : IsAlgebraicSpace B S hS
      (pullback φ (reducedClosedSubspaceOfChart B S hS φ T hT).ι) :=
    isAlgebraicSpace_pullback B S hS φ (reducedClosedSubspaceOfChart B S hS φ T hT).ι
      (isAlgebraicSpace_yoneda B S hS U) hR hX
  have heq : hk.flip.isoPullback.inv ≫ yoneda.map i =
      pullback.fst φ (reducedClosedSubspaceOfChart B S hS φ T hT).ι := by
    rw [Iso.inv_comp_eq]
    exact hk.flip.isoPullback_hom_fst.symm
  rw [← heq]
  exact universallyClosed_comp B S hS (isAlgebraicSpace_yoneda B S hS V)
    (isAlgebraicSpace_yoneda B S hS U) _ _ (universallyClosed_of_isIso B S hS _) hUCi

end Chart

/-! ### The inclusion of a reduced closed subspace is proper -/

section Inclusion

variable {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The inclusion of the reduced closed subspace on a closed set of points is locally of
finite type**, with no descent hypothesis. -/
theorem isLocallyOfFiniteType_ι_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsLocallyOfFiniteType B S hS (reducedClosedSubspace B S hS X hX T hT).ι :=
  isLocallyOfFiniteType_ι_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 hX T hT

/-- **The inclusion of the reduced closed subspace on a closed set of points is universally
closed**, with no descent hypothesis. -/
theorem universallyClosed_ι_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    UniversallyClosed B S hS (reducedClosedSubspace B S hS X hX T hT).ι :=
  universallyClosed_ι_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 hX T hT

/-- **A factorization of the inclusion of a reduced closed subspace through a monomorphism is
proper**, with no descent hypothesis.

The factoring morphism is a monomorphism, hence separated by Stacks 042N; it is universally
closed by Stacks 04NX, because the inclusion is universally closed and the monomorphism it is
factored through is separated; it is locally of finite type by Stacks 0462, because the
inclusion is; and it is quasi-compact by Stacks 04XW, being universally closed. -/
theorem isProper_of_comp_eq_ι_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hW : IsAlgebraicSpace B S hS W)
    (T : Set (points B S hS X)) (hT : IsClosed T) (n : W ⟶ X) (hn : Mono n)
    (v : (reducedClosedSubspace B S hS X hX T hT).toFunctor ⟶ W)
    (hv : v ≫ n = (reducedClosedSubspace B S hS X hX T hT).ι) :
    IsProper B S hS v := by
  have hRalg : IsAlgebraicSpace B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT
  have hmc : Mono (v ≫ n) := by rw [hv]; infer_instance
  have hUC : UniversallyClosed B S hS v :=
    universallyClosed_of_comp_of_isSeparated B S hS hRalg hW hX v n
      (by rw [hv]; exact universallyClosed_ι_reducedClosedSubspace B S hS X hX T hT)
      (isSeparated_of_mono B S hS n hn)
  exact ⟨isSeparated_of_mono B S hS v (mono_of_mono v n),
    ⟨isLocallyOfFiniteType_of_comp B S hS hRalg hW hX v n
      (by rw [hv]; exact isLocallyOfFiniteType_ι_reducedClosedSubspace B S hS X hX T hT),
      isQuasiCompact_of_universallyClosed B S hS hRalg hW v hUC⟩, hUC⟩

/-- **The inclusion of the reduced closed subspace on a closed set of points is proper**, with
no descent hypothesis. -/
theorem isProper_ι_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsProper B S hS (reducedClosedSubspace B S hS X hX T hT).ι :=
  isProper_of_comp_eq_ι_reducedClosedSubspace B S hS X hX hX T hT (𝟙 X) inferInstance _
    (Category.comp_id _)

end Inclusion

/-! ### Comparing two closed subspaces with the same point set -/

section Support

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A closed set of points is proper over the base as soon as it is cut out inside a subspace
proper over the base.** More precisely: if the reduced induced subspace on `T` factors through a
subfunctor `W` of `X` which is an algebraic space and is proper over `Y`, then `T` is proper
over `Y`. The factoring morphism is proper by
`AlgebraicGeometry.Space.isProper_of_comp_eq_ι_reducedClosedSubspace`, so the composite is.

The subfunctor `W` is not required to be a *closed* subspace, which is what makes this usable
on an inverse image of a reduced induced subspace. -/
theorem isProperOver_of_isProper_ι_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T) (W : Subfunctor X)
    (hW : IsAlgebraicSpace B S hS W.toFunctor) (hWproper : IsProper B S hS (W.ι ≫ f))
    (v : (reducedClosedSubspace B S hS X hX T hT).toFunctor ⟶ W.toFunctor)
    (hv : v ≫ W.ι = (reducedClosedSubspace B S hS X hX T hT).ι) :
    IsProperOver B S hS hX hY f hf T hT := by
  have h := isProper_comp B S hS
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT) hW hY v (W.ι ≫ f)
    (isProper_of_comp_eq_ι_reducedClosedSubspace B S hS X hX hW T hT W.ι inferInstance v hv)
    hWproper
  rwa [← Category.assoc, hv] at h

/-- The reduced induced closed subspace on a closed set of points factors through every closed
subspace with that same set of points, by Stacks 03JJ: its own set of points is that set, and it
is étale-locally reduced. -/
theorem exists_lift_reducedClosedSubspace_of_range_pointsMap_eq (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (Z : Subfunctor X)
    (hZ : IsClosedSubspace B S hS Z)
    (hZT : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T) :
    ∃ g : (reducedClosedSubspace B S hS X hX T hT).toFunctor ⟶ Z.toFunctor,
      g ≫ Z.ι = (reducedClosedSubspace B S hS X hX T hT).ι := by
  refine (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT) Z hZ
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT) _).2 ?_
  rw [range_pointsMap_ι_reducedClosedSubspace, hZT]

/-- **Properness over the base of a closed subspace depends only on its set of points.** If one
closed subspace of `X` with set of points `T` is proper over `Y`, then so is any other.

Both subspaces receive the reduced induced subspace on `T` by
`AlgebraicGeometry.Space.exists_lift_reducedClosedSubspace_of_range_pointsMap_eq`, and both
receiving morphisms are proper by
`AlgebraicGeometry.Space.isProper_of_comp_eq_ι_reducedClosedSubspace`. So the reduced induced
subspace is proper over `Y` through the first subspace, and the morphism to the second subspace
is surjective on points — the point sets of all three agree and the inclusion of the second is
injective on points by Stacks 06RV. Separatedness and quasi-compactness of the second subspace
over `Y` then follow from Stacks 05Z2 and Stacks 040W, local finite type from Stacks 03XG, and
universal closedness together with those from Stacks 08AJ. -/
theorem isProper_ι_comp_of_isProper_ι_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z)
    (hZT : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T)
    (hZproper : IsProper B S hS (Z.ι ≫ f))
    (W : Subfunctor X) (hW : IsClosedSubspace B S hS W)
    (hWT : Set.range (pointsMap B S hS W.toFunctor W.ι) = T) :
    IsProper B S hS (W.ι ≫ f) := by
  set R := reducedClosedSubspace B S hS X hX T hT with hRdef
  have hRalg : IsAlgebraicSpace B S hS R.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT
  obtain ⟨gZ, hgZ⟩ :=
    exists_lift_reducedClosedSubspace_of_range_pointsMap_eq B S hS hX T hT Z hZ hZT
  obtain ⟨gW, hgW⟩ :=
    exists_lift_reducedClosedSubspace_of_range_pointsMap_eq B S hS hX T hT W hW hWT
  have hRproper : IsProper B S hS (R.ι ≫ f) :=
    isProperOver_of_isProper_ι_comp B S hS hX hY f hf T hT Z hZ.1 hZproper gZ hgZ
  have hcomp : gW ≫ (W.ι ≫ f) = R.ι ≫ f := by rw [← Category.assoc, hgW]
  have hsurj : IsSurjective B S hS gW := by
    intro p
    obtain ⟨r, hr⟩ : pointsMap B S hS W.toFunctor W.ι p ∈
        Set.range (pointsMap B S hS R.toFunctor R.ι) := by
      rw [hRdef, range_pointsMap_ι_reducedClosedSubspace, ← hWT]
      exact ⟨p, rfl⟩
    refine ⟨r, pointsMap_injective_of_mono B S hS W.ι ?_⟩
    rw [← pointsMap_comp_apply B S hS gW W.ι r, hgW]
    exact hr
  have hgWproper : IsProper B S hS gW :=
    isProper_of_comp_eq_ι_reducedClosedSubspace B S hS X hX hW.1 T hT W.ι inferInstance gW hgW
  have hsep : IsSeparated B S hS (W.ι ≫ f) :=
    isSeparated_of_isSurjective_of_universallyClosed B S hS hRalg hW.1 hY gW (W.ι ≫ f)
      hsurj hgWproper.2.2 (by rw [hcomp]; exact hRproper.1)
  have hloc : IsLocallyOfFiniteType B S hS (W.ι ≫ f) :=
    isLocallyOfFiniteType_comp B S hS hW.1 hX hY W.ι f
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS W.ι hW.2) hf
  have hqc : IsQuasiCompact B S hS (W.ι ≫ f) :=
    isQuasiCompact_of_comp_surjective B S hS hRalg hW.1 hY gW (R.ι ≫ f) (W.ι ≫ f)
      hcomp.symm hsurj hRproper.2.1.2
  exact isProper_of_isSurjective_comp B S hS hRalg hW.1 hY gW (W.ι ≫ f)
    (by rw [hcomp]; exact hRproper.2.2) hsurj hsep ⟨hloc, hqc⟩

end Support

/-! ### Stacks 0CZC -/

section Equivalences

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CZC, conditions (1) and (2).** For a morphism of algebraic spaces over `S` locally
of finite type and a closed set `T` of points of the source, the reduced induced closed subspace
on `T` is proper over the target exactly when some closed subspace with set of points `T` is
proper over the target.

The forward implication must exhibit a closed subspace with set of points `T`, which is the
existence clause of Stacks 03IQ. That clause is now available unconditionally: the reduced
induced subspace *is* a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent`
applied to
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, which is
Stacks 02W8 at the closed immersions. -/
@[stacks 0CZC "conditions (1) and (2)", ega "II 5.4.10" "indep. of subscheme"]
theorem isProper_reducedClosedSubspace_iff_exists (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsProperOver B S hS hX hY f hf T hT ↔
      ∃ (Z : Subfunctor X) (_ : IsClosedSubspace B S hS Z),
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧ IsProper B S hS (Z.ι ≫ f) := by
  have hclT := isClosedSubspace_reducedClosedSubspace B S hS X hX T hT
  exact ⟨fun hR ↦ ⟨reducedClosedSubspace B S hS X hX T hT, hclT,
      range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT, hR⟩,
    fun ⟨Z, hZ, hZT, hZproper⟩ ↦
      isProper_ι_comp_of_isProper_ι_comp B S hS hX hY f hf T hT Z hZ hZT hZproper
        (reducedClosedSubspace B S hS X hX T hT) hclT
        (range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT)⟩

/-- **Stacks 0CZC, conditions (2) and (3).** If one closed subspace with a given closed set of
points is proper over the target, then every closed subspace with that set of points is.

The implication from (3) to (2) must exhibit a closed subspace with set of points `T`, which is
the existence clause of Stacks 03IQ. That clause is now available unconditionally: the reduced
induced subspace *is* a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent`
applied to
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, which is
Stacks 02W8 at the closed immersions. -/
@[stacks 0CZC "conditions (2) and (3)", ega "II 5.4.10" "indep. of subscheme"]
theorem exists_isProper_closedSubspace_iff_forall (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    (∃ (Z : Subfunctor X) (_ : IsClosedSubspace B S hS Z),
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧ IsProper B S hS (Z.ι ≫ f)) ↔
      ∀ (Z : Subfunctor X) (_ : IsClosedSubspace B S hS Z),
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T → IsProper B S hS (Z.ι ≫ f) := by
  have hclT := isClosedSubspace_reducedClosedSubspace B S hS X hX T hT
  exact ⟨fun ⟨Z, hZ, hZT, hZproper⟩ W hW hWT ↦
      isProper_ι_comp_of_isProper_ι_comp B S hS hX hY f hf T hT Z hZ hZT hZproper W hW hWT,
    fun hall ↦ ⟨reducedClosedSubspace B S hS X hX T hT, hclT,
      range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT,
      hall _ hclT (range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT)⟩⟩

end Equivalences

end AlgebraicGeometry.Space

end
