module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.GlueingSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification

/-!
# Clause (2) of Stacks 0EDM over an algebraic space

The morphism `X ⟶ X'` constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.GlueingSpace` is an isomorphism over the open complement
of the fibre `X'_y`.

The statement is checked over the chart: the complement of the fibre in `X'` pulls back to the
complement of the chart-level fibre in the chart-level pushout `P_U`, which is an open subscheme
of `P_U`, and over that open the morphism is the scheme-level `AlgebraicGeometry.glueingToSource`
restricted, an isomorphism by [Stacks Project, Tag 0E25].  Being an isomorphism is local on the
target for the fppf topology, so the space-level statement follows.

## Main definitions

* `AlgebraicGeometry.Space.glueingSpaceFibre` is the fibre `X'_y` as a set of points of `X'`.
* `AlgebraicGeometry.Space.glueingChartAwayOpen` is the complement of the chart-level fibre, an
  open subscheme of `P_U`, and `AlgebraicGeometry.Space.glueingAwaySite` is it as an object of
  the site.

## Main results

* `AlgebraicGeometry.Space.isIso_glueingSpaceRestrict`: **clause (2)**, the base change of
  `X ⟶ X'` to the open complement of `X'_y` is an isomorphism.
* `AlgebraicGeometry.Space.exists_glueingSpace_factorization`: **Stacks 0EDM** in full, under the
  source's hypotheses: the chart, the sheafification and the local Noetherianity of the chart are
  all produced inside the proof.

## References

* [Stacks Project, Tag 0EDM](https://stacks.math.columbia.edu/tag/0EDM)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme
  pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
  {Ky : BigFppfOver B S hS} {y : yoneda.obj Ky ⟶ Y.1} (hy : IsClosedImmersion B S hS y)
  (c : EtaleChartRelation B S hS Y.1)

/-! ### The complement of the chart-level fibre -/

/-- The open complement in the chart-level pushout `P_U` of the chart-level fibre: the preimage
of the open complement of the point which `Spec k ×_Y U ⟶ U` represents.  This is the open over
which the scheme-level clause (2),
`AlgebraicGeometry.isIso_glueingToSource_restrict`, is stated. -/
def glueingChartAwayOpen : (glueingChartPushout B S hS f hf hy c.u).Opens :=
  let := isIntegralHom_glueingChartSourceHom B S hS f hf c.u
  let := isClosedImmersion_glueingChartFibreHom B S hS hy c.u
  glueingChartPushoutToBase B S hS f hf hy c.u ⁻¹ᵁ
    glueingAwayOpen ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy c.u))

/-- The chart-level complement is exactly the complement of the chart-level fibre, by the
scheme-level clause (3), `AlgebraicGeometry.range_glueingPoint`. -/
theorem glueingChartAwayOpen_set :
    ((glueingChartAwayOpen B S hS f hf hy c :
        (glueingChartPushout B S hS f hf hy c.u).Opens) :
          Set (glueingChartPushout B S hS f hf hy c.u)) =
      (Set.range (pushoutInr (glueingChartSituation B S hS f hf hy c.u)))ᶜ := by
  let := isIntegralHom_glueingChartSourceHom B S hS f hf c.u
  let := isClosedImmersion_glueingChartFibreHom B S hS hy c.u
  change ⇑(glueingChartPushoutToBase B S hS f hf hy c.u) ⁻¹'
      (Set.range ⇑((BigFppfOver.toScheme B S hS).map
        (glueingChartFibreHom B S hS hy c.u)))ᶜ = _
  rw [Set.preimage_compl]
  exact congrArg (fun t ↦ tᶜ) (range_glueingPoint
    ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf c.u))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy c.u))).symm

/-- The chart-level complement is an object of the site: an open subscheme of a contained
scheme is contained. -/
theorem contains_glueingChartAwayOpen :
    B.Contains (glueingChartAwayOpen B S hS f hf hy c).toScheme :=
  Scheme.size_lt_of_isOpenImmersion (glueingChartAwayOpen B S hS f hf hy c).ι
    (contains_glueingChartPushout B S hS f hf hy c.u)

/-- The chart-level complement as an object of the site. -/
def glueingAwaySite : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_glueingChartAwayOpen B S hS f hf hy c)
    ((glueingChartAwayOpen B S hS f hf hy c).ι ≫
      (glueingChartPushoutToBase B S hS f hf hy c.u ≫ B.inclusion.map c.U.hom))

/-- Its open immersion into the chart-level pushout. -/
def glueingAwaySiteHom :
    glueingAwaySite B S hS f hf hy c ⟶ glueingChartSitePushout B S hS f hf hy c.u :=
  BigFppfOver.homMk B S hS (contains_glueingChartPushout B S hS f hf hy c.u)
    (glueingChartPushoutToBase B S hS f hf hy c.u ≫ B.inclusion.map c.U.hom)
    (glueingChartAwayOpen B S hS f hf hy c).ι rfl

/-- The underlying morphism of schemes of `glueingAwaySiteHom` is the open immersion of the
chart-level complement. -/
@[simp] theorem toScheme_map_glueingAwaySiteHom :
    (BigFppfOver.toScheme B S hS).map (glueingAwaySiteHom B S hS f hf hy c) =
      (glueingChartAwayOpen B S hS f hf hy c).ι := rfl

/-! ### The restriction of `X ×_Y U ⟶ P_U` to the complement -/

/-- The preimage of the chart-level complement in the chart-level source, as an object of the
site. -/
def glueingAwaySource : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_lt_of_isOpenImmersion
      (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ⁻¹ᵁ
        glueingChartAwayOpen B S hS f hf hy c).ι
      (glueingChartSource B S hS f hf c.u).left.property)
    ((pushoutInl (glueingChartSituation B S hS f hf hy c.u) ⁻¹ᵁ
        glueingChartAwayOpen B S hS f hf hy c).ι ≫
      B.inclusion.map (glueingChartSource B S hS f hf c.u).hom)

/-- Its open immersion into the chart-level source. -/
def glueingAwaySourceHom :
    glueingAwaySource B S hS f hf hy c ⟶ glueingChartSource B S hS f hf c.u :=
  BigFppfOver.homMk B S hS (glueingChartSource B S hS f hf c.u).left.property
    (B.inclusion.map (glueingChartSource B S hS f hf c.u).hom)
    (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ⁻¹ᵁ
      glueingChartAwayOpen B S hS f hf hy c).ι rfl

/-- The underlying morphism of schemes of `glueingAwaySourceHom` is the open immersion of the
preimage of the chart-level complement. -/
@[simp] theorem toScheme_map_glueingAwaySourceHom :
    (BigFppfOver.toScheme B S hS).map (glueingAwaySourceHom B S hS f hf hy c) =
      (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ⁻¹ᵁ
        glueingChartAwayOpen B S hS f hf hy c).ι := rfl

/-- The structure-morphism compatibility of the restriction, in the spelling in which the
composites are well typed without unfolding the site objects. -/
theorem glueingAwayRestrict_w :
    (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ∣_
        glueingChartAwayOpen B S hS f hf hy c) ≫
      ((glueingChartAwayOpen B S hS f hf hy c).ι ≫
        (glueingChartPushoutToBase B S hS f hf hy c.u ≫ B.inclusion.map c.U.hom)) =
      (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ⁻¹ᵁ
          glueingChartAwayOpen B S hS f hf hy c).ι ≫
        B.inclusion.map (glueingChartSource B S hS f hf c.u).hom := by
  rw [morphismRestrict_ι_assoc]
  refine congrArg (fun k ↦ (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ⁻¹ᵁ
    glueingChartAwayOpen B S hS f hf hy c).ι ≫ k) ?_
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫ B.inclusion.map c.U.hom)
      (pushoutToBase_inl (glueingChartSituation B S hS f hf hy c.u)))).trans
    (toScheme_map_comp_inclusion_hom B S hS (glueingChartSourceHom B S hS f hf c.u))

/-- The restriction of the canonical morphism `X ×_Y U ⟶ P_U` to the complement of the
chart-level fibre, as a morphism of the site. -/
def glueingAwayRestrict :
    glueingAwaySource B S hS f hf hy c ⟶ glueingAwaySite B S hS f hf hy c :=
  BigFppfOver.homMk B S hS (contains_glueingChartAwayOpen B S hS f hf hy c)
    ((glueingChartAwayOpen B S hS f hf hy c).ι ≫
      (glueingChartPushoutToBase B S hS f hf hy c.u ≫ B.inclusion.map c.U.hom))
    (pushoutInl (glueingChartSituation B S hS f hf hy c.u) ∣_
      glueingChartAwayOpen B S hS f hf hy c) (glueingAwayRestrict_w B S hS f hf hy c)

/-- The underlying morphism of schemes of `glueingAwayRestrict` is the restriction of
`X ×_Y U ⟶ P_U` to the chart-level complement. -/
@[simp] theorem toScheme_map_glueingAwayRestrict :
    (BigFppfOver.toScheme B S hS).map (glueingAwayRestrict B S hS f hf hy c) =
      pushoutInl (glueingChartSituation B S hS f hf hy c.u) ∣_
        glueingChartAwayOpen B S hS f hf hy c := rfl

/-- **Clause (2) of [Stacks Project, Tag 0EDM] over the chart.**  The restriction of
`X ×_Y U ⟶ P_U` to the complement of the chart-level fibre is an isomorphism of schemes.  This
is `AlgebraicGeometry.isIso_glueingToSource_restrict`. -/
theorem isIso_glueingAwayRestrict :
    IsIso ((BigFppfOver.toScheme B S hS).map (glueingAwayRestrict B S hS f hf hy c)) := by
  let := isIntegralHom_glueingChartSourceHom B S hS f hf c.u
  let := isClosedImmersion_glueingChartFibreHom B S hS hy c.u
  rw [toScheme_map_glueingAwayRestrict]
  exact isIso_glueingToSource_restrict
    ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf c.u))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy c.u))

/-- The restriction is cartesian over the open immersion: the preimage of an open is the fibre
product with it. -/
theorem isPullback_glueingAwayRestrict :
    IsPullback (glueingAwaySourceHom B S hS f hf hy c) (glueingAwayRestrict B S hS f hf hy c)
      (glueingChartSiteInl B S hS f hf hy c.u) (glueingAwaySiteHom B S hS f hf hy c) := by
  have := reflectsPullbacks_bigFppfOverToScheme B S hS
  refine IsPullback.of_map (BigFppfOver.toScheme B S hS) ?_ ?_
  · apply BigFppfOver.map_toScheme_injective B S hS
    change (BigFppfOver.toScheme B S hS).map
        (glueingAwaySourceHom B S hS f hf hy c ≫ glueingChartSiteInl B S hS f hf hy c.u) =
      (BigFppfOver.toScheme B S hS).map
        (glueingAwayRestrict B S hS f hf hy c ≫ glueingAwaySiteHom B S hS f hf hy c)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      toScheme_map_glueingAwaySourceHom, toScheme_map_glueingChartSiteInl,
      toScheme_map_glueingAwayRestrict, toScheme_map_glueingAwaySiteHom]
    exact (morphismRestrict_ι _ _).symm
  · rw [toScheme_map_glueingAwaySourceHom, toScheme_map_glueingChartSiteInl,
      toScheme_map_glueingAwayRestrict, toScheme_map_glueingAwaySiteHom]
    exact (isPullback_morphismRestrict (pushoutInl (glueingChartSituation B S hS f hf hy c.u))
      (glueingChartAwayOpen B S hS f hf hy c)).flip

/-! ### The open complement of the fibre in `X'`, and clause (2) -/

/-- The fibre `X'_y`, as a set of points of `X'`: the image of the distinguished closed
immersion `Spec k ⟶ X'`. -/
abbrev glueingSpaceFibre : Set (points B S hS (glueingSpaceSheaf B S hS f hf hy c).obj) :=
  Set.range (pointsMap B S hS (yoneda.obj Ky) (glueingSpacePoint B S hS f hf hy c))

/-- The open complement `X' ∖ X'_y`, as an open subspace of `X'`. -/
abbrev glueingSpaceAway : Subfunctor (glueingSpaceSheaf B S hS f hf hy c).obj :=
  openSubspaceOfPoints B S hS (glueingSpaceSheaf B S hS f hf hy c).obj
    (glueingSpaceFibre B S hS f hf hy c)ᶜ

/-- The points of the chart-level complement are exactly the points of the chart-level pushout
lying outside the fibre. -/
theorem range_pointsMap_glueingAwaySiteHom :
    Set.range (pointsMap B S hS (yoneda.obj (glueingAwaySite B S hS f hf hy c))
        (yoneda.map (glueingAwaySiteHom B S hS f hf hy c))) =
      pointsMap B S hS (yoneda.obj (glueingRelationBase B S hS f hf hy c))
        (glueingSpaceChart B S hS f hf hy c) ⁻¹'
        (glueingSpaceFibre B S hS f hf hy c)ᶜ := by
  have hR : pointsMap B S hS (yoneda.obj (glueingRelationBase B S hS f hf hy c))
        (glueingSpaceChart B S hS f hf hy c) ⁻¹'
        glueingSpaceFibre B S hS f hf hy c =
      Set.range (pointsMap B S hS (yoneda.obj (glueingChartFibre B S hS hy c.u))
        (yoneda.map (glueingChartSiteInr B S hS f hf hy c.u))) := by
    simpa only [Set.image_univ, Set.preimage_univ] using
      preimage_image_pointsMap_of_isPullback B S hS
        (isPullback_glueingSpacePoint B S hS f hf hy c).flip Set.univ
  rw [Set.preimage_compl, hR]
  ext π
  rw [mem_range_pointsMap_yoneda_iff, Set.mem_compl_iff, mem_range_pointsMap_yoneda_iff,
    toScheme_map_glueingAwaySiteHom, toScheme_map_glueingChartSiteInr]
  have hset : Set.range ⇑(glueingChartAwayOpen B S hS f hf hy c).ι =
      (Set.range ⇑(pushoutInr (glueingChartSituation B S hS f hf hy c.u)))ᶜ :=
    (glueingChartAwayOpen B S hS f hf hy c).range_ι.trans
      (glueingChartAwayOpen_set B S hS f hf hy c)
  exact Set.ext_iff.mp hset
    (pointsToScheme B S hS (glueingChartSitePushout B S hS f hf hy c.u) π)

/-- The chart-level complement maps into the open complement of the fibre. -/
theorem range_le_glueingSpaceAway :
    Subfunctor.range (yoneda.map (glueingAwaySiteHom B S hS f hf hy c) ≫
        glueingSpaceChart B S hS f hf hy c) ≤ glueingSpaceAway B S hS f hf hy c := by
  rw [range_le_openSubspaceOfPoints_iff]
  rintro p ⟨ω, rfl⟩
  rw [pointsMap_comp_apply]
  exact (range_pointsMap_glueingAwaySiteHom B S hS f hf hy c).subset ⟨ω, rfl⟩

/-- The chart of the open complement of the fibre: the chart-level complement maps to it, and
surjectively on points. -/
def glueingAwayChart :
    yoneda.obj (glueingAwaySite B S hS f hf hy c) ⟶
      (glueingSpaceAway B S hS f hf hy c).toFunctor :=
  Subfunctor.lift _ (range_le_glueingSpaceAway B S hS f hf hy c)

/-- `glueingAwayChart` followed by the inclusion of the open complement of the fibre is the open
immersion of the chart-level complement followed by the chart of `X'`. -/
@[simp] theorem glueingAwayChart_ι :
    glueingAwayChart B S hS f hf hy c ≫ (glueingSpaceAway B S hS f hf hy c).ι =
      yoneda.map (glueingAwaySiteHom B S hS f hf hy c) ≫ glueingSpaceChart B S hS f hf hy c :=
  rfl

/-- The open immersion of the chart-level complement is an open immersion of presheaves. -/
theorem isOpenImmersion_yoneda_map_glueingAwaySiteHom :
    IsOpenImmersion B S hS (yoneda.map (glueingAwaySiteHom B S hS f hf hy c)) := by
  have := MorphismProperty.inverseImage_isStableUnderBaseChange (BigFppfOver.toScheme B S hS)
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
  exact MorphismProperty.relative_map
    (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
      (glueingChartAwayOpen B S hS f hf hy c).ι))

/-- **The chart-level complement is the preimage of the open complement of the fibre.**  Both
are the open subspace of the chart-level pushout cut out by the points outside the fibre. -/
theorem preimage_glueingSpaceAway_eq :
    (glueingSpaceAway B S hS f hf hy c).preimage (glueingSpaceChart B S hS f hf hy c) =
      Subfunctor.range (yoneda.map (glueingAwaySiteHom B S hS f hf hy c)) := by
  rw [preimage_openSubspaceOfPoints,
    range_eq_openSubspaceOfPoints_of_isOpenImmersion B S hS _
      (isOpenImmersion_yoneda_map_glueingAwaySiteHom B S hS f hf hy c),
    range_pointsMap_glueingAwaySiteHom]

/-- The chart-level complement, viewed inside the preimage of the open complement of the fibre
under the chart of `X'`. -/
def glueingAwayLift :
    yoneda.obj (glueingAwaySite B S hS f hf hy c) ⟶
      ((glueingSpaceAway B S hS f hf hy c).preimage
        (glueingSpaceChart B S hS f hf hy c)).toFunctor :=
  Subfunctor.lift (yoneda.map (glueingAwaySiteHom B S hS f hf hy c))
    (le_of_eq (preimage_glueingSpaceAway_eq B S hS f hf hy c).symm)

/-- `glueingAwayLift` followed by the inclusion of the preimage is the open immersion of the
chart-level complement. -/
@[simp] theorem glueingAwayLift_ι :
    glueingAwayLift B S hS f hf hy c ≫
        ((glueingSpaceAway B S hS f hf hy c).preimage
          (glueingSpaceChart B S hS f hf hy c)).ι =
      yoneda.map (glueingAwaySiteHom B S hS f hf hy c) := rfl

/-- **The chart-level complement *is* the preimage of the open complement.**  The comparison is
an isomorphism: it is injective because the open immersion is a monomorphism, and surjective
because the two subfunctors are equal. -/
theorem isIso_glueingAwayLift : IsIso (glueingAwayLift B S hS f hf hy c) := by
  have hmono : Mono (yoneda.map (glueingAwaySiteHom B S hS f hf hy c)) :=
    mono_of_presheaf_isOpenImmersion
      (isOpenImmersion_yoneda_map_glueingAwaySiteHom B S hS f hf hy c)
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨fun a b hab => ?_, fun z => ?_⟩
  · exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hmono T)
      (congrArg Subtype.val hab)
  · have hset := congrArg (fun G : Subfunctor _ => G.obj T)
      (preimage_glueingSpaceAway_eq B S hS f hf hy c)
    obtain ⟨w, hw⟩ : z.val ∈ (Subfunctor.range
        (yoneda.map (glueingAwaySiteHom B S hS f hf hy c))).obj T := hset ▸ z.property
    exact ⟨w, Subtype.ext hw⟩

/-- The chart of the open complement is the base change of the chart of `X'`, read through the
isomorphism above. -/
theorem glueingAwayChart_eq :
    glueingAwayChart B S hS f hf hy c =
      glueingAwayLift B S hS f hf hy c ≫
        (glueingSpaceAway B S hS f hf hy c).fromPreimage
          (glueingSpaceChart B S hS f hf hy c) := by
  have : Mono (glueingSpaceAway B S hS f hf hy c).ι := inferInstance
  refine (cancel_mono (glueingSpaceAway B S hS f hf hy c).ι).1 ?_
  rw [glueingAwayChart_ι, Category.assoc,
    (Subfunctor.isPullback_preimage (glueingSpaceChart B S hS f hf hy c)
      (glueingSpaceAway B S hS f hf hy c)).w, ← Category.assoc, glueingAwayLift_ι]

/-- The open complement of the fibre is an open subspace of `X'`: the fibre is closed, being the
image of a closed immersion. -/
theorem isOpenSubspace_glueingSpaceAway :
    IsOpenSubspace B S hS (glueingSpaceAway B S hS f hf hy c) :=
  isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c) _
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c) _
      (isClosedImmersion_glueingSpacePoint B S hS f hf hy c)).isOpen_compl

/-- A property of the chart of `X'` which is stable under base change and respects isomorphisms
passes to the chart of the open complement of the fibre. -/
private theorem presheaf_glueingAwayChart (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.RespectsIso]
    (hP : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (glueingSpaceChart B S hS f hf hy c)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (glueingAwayChart B S hS f hf hy c) := by
  have := isIso_glueingAwayLift B S hS f hf hy c
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
    (F := yoneda (C := BigFppfOver B S hS))
  rw [glueingAwayChart_eq]
  exact MorphismProperty.RespectsIso.precomp _ (glueingAwayLift B S hS f hf hy c) _
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (Subfunctor.isPullback_preimage (glueingSpaceChart B S hS f hf hy c)
        (glueingSpaceAway B S hS f hf hy c)).flip hP)

/-- The chart of the open complement is surjective after every representable base change. -/
theorem surjective_glueingAwayChart :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingAwayChart B S hS f hf hy c) :=
  presheaf_glueingAwayChart B S hS f hf hy c _ (surjective_glueingSpaceChart B S hS f hf hy c)

/-- The chart of the open complement is étale after every representable base change. -/
theorem etale_glueingAwayChart :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (glueingAwayChart B S hS f hf hy c) :=
  presheaf_glueingAwayChart B S hS f hf hy c _ (etale_glueingSpaceChart B S hS f hf hy c)

/-- **The restriction of `X ⟶ X'` to the complement of the fibre.**  This is the morphism of
clause (2) of [Stacks Project, Tag 0EDM]: `X ∖ X_y ⟶ X' ∖ X'_y`. -/
abbrev glueingSpaceRestrict :
    (openSubspaceOfPoints B S hS X.1
        (pointsMap B S hS X.1 (glueingSpaceFromSource B S hS f hf hy c) ⁻¹'
          (glueingSpaceFibre B S hS f hf hy c)ᶜ)).toFunctor ⟶
      (glueingSpaceAway B S hS f hf hy c).toFunctor :=
  openComplementRestriction B S hS (glueingSpaceFromSource B S hS f hf hy c)
    (glueingSpaceFibre B S hS f hf hy c)

/-- The chart-level complement of the source maps into the chart-level complement of the
pushout, compatibly with `X ⟶ X'`. -/
theorem glueingAwaySourceHom_comp_fromSource :
    (yoneda.map (glueingAwaySourceHom B S hS f hf hy c) ≫
        glueingSourceChart B S hS f hf c) ≫ glueingSpaceFromSource B S hS f hf hy c =
      yoneda.map (glueingAwayRestrict B S hS f hf hy c) ≫
        (yoneda.map (glueingAwaySiteHom B S hS f hf hy c) ≫
          glueingSpaceChart B S hS f hf hy c) := by
  rw [Category.assoc, (isPullback_glueingSourceChart_chart B S hS f hf hy c).w.symm,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    (isPullback_glueingAwayRestrict B S hS f hf hy c).w, CategoryTheory.Functor.map_comp,
    Category.assoc]

/-- The chart-level complement of the source lands outside the fibre. -/
theorem range_le_glueingSpaceSourceAway :
    Subfunctor.range (yoneda.map (glueingAwaySourceHom B S hS f hf hy c) ≫
        glueingSourceChart B S hS f hf c) ≤
      openSubspaceOfPoints B S hS X.1
        (pointsMap B S hS X.1 (glueingSpaceFromSource B S hS f hf hy c) ⁻¹'
          (glueingSpaceFibre B S hS f hf hy c)ᶜ) := by
  rw [range_le_openSubspaceOfPoints_iff]
  rintro p ⟨α, rfl⟩
  rw [Set.mem_preimage, ← pointsMap_comp_apply,
    glueingAwaySourceHom_comp_fromSource B S hS f hf hy c, pointsMap_comp_apply,
    pointsMap_comp_apply]
  exact (range_pointsMap_glueingAwaySiteHom B S hS f hf hy c).subset ⟨_, rfl⟩

/-- The chart-level complement of the source, viewed inside the complement of the fibre in
`X`. -/
def glueingAwaySourceLift :
    yoneda.obj (glueingAwaySource B S hS f hf hy c) ⟶
      (openSubspaceOfPoints B S hS X.1
        (pointsMap B S hS X.1 (glueingSpaceFromSource B S hS f hf hy c) ⁻¹'
          (glueingSpaceFibre B S hS f hf hy c)ᶜ)).toFunctor :=
  Subfunctor.lift _ (range_le_glueingSpaceSourceAway B S hS f hf hy c)

/-- **The restriction of `X ⟶ X'` to the complement of the fibre becomes the chart-level
restriction after base change along the chart of the complement.** -/
theorem isPullback_glueingSpaceRestrict :
    IsPullback (glueingAwaySourceLift B S hS f hf hy c)
      (yoneda.map (glueingAwayRestrict B S hS f hf hy c))
      (glueingSpaceRestrict B S hS f hf hy c) (glueingAwayChart B S hS f hf hy c) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_openComplementRestriction B S hS
    (glueingSpaceFromSource B S hS f hf hy c) (glueingSpaceFibre B S hS f hf hy c))
  · have hrect := IsPullback.paste_horiz
      ((isPullback_glueingAwayRestrict B S hS f hf hy c).map yoneda)
      (isPullback_glueingSourceChart_chart B S hS f hf hy c).flip
    exact hrect
  · refine (cancel_mono (glueingSpaceAway B S hS f hf hy c).ι).1 ?_
    rw [Category.assoc, openComplementRestriction_ι, Category.assoc, glueingAwayChart_ι]
    exact glueingAwaySourceHom_comp_fromSource B S hS f hf hy c

/-- The complement of the fibre in `X` is an open subspace. -/
theorem isOpenSubspace_glueingSpaceSourceAway :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X.1
      (pointsMap B S hS X.1 (glueingSpaceFromSource B S hS f hf hy c) ⁻¹'
        (glueingSpaceFibre B S hS f hf hy c)ᶜ)) :=
  isOpenSubspace_openSubspaceOfPoints B S hS X.property _
    (((continuous_pointsMap B S hS (glueingSpaceFromSource B S hS f hf hy c)).isOpen_preimage _
      (isClosed_range_pointsMap_of_isClosedImmersion B S hS
        (isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c) _
        (isClosedImmersion_glueingSpacePoint B S hS f hf hy c)).isOpen_compl))

/-- The restriction to the complement of the fibre is an open immersion: it is one over the
chart, where it is the restricted `AlgebraicGeometry.glueingToSource`, and open immersions
descend along the surjective étale chart of the complement. -/
theorem isOpenImmersion_glueingSpaceRestrict :
    IsOpenImmersion B S hS (glueingSpaceRestrict B S hS f hf hy c) := by
  have := isIso_glueingAwayRestrict B S hS f hf hy c
  exact presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS)
    (isOpenSubspace_glueingSpaceSourceAway B S hS f hf hy c).1.isSheaf
    (isOpenSubspace_glueingSpaceAway B S hS f hf hy c).1.isSheaf
    (surjective_glueingAwayChart B S hS f hf hy c)
    (etale_glueingAwayChart B S hS f hf hy c)
    (presheaf_pullback_snd_of_isPullback
      (P := (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      (isPullback_glueingSpaceRestrict B S hS f hf hy c) inferInstance)

/-- The restriction to the complement of the fibre is surjective on points: the chart of the
complement is, and the chart-level restriction is an isomorphism. -/
theorem surjective_pointsMap_glueingSpaceRestrict :
    Function.Surjective (pointsMap B S hS _ (glueingSpaceRestrict B S hS f hf hy c)) := by
  have := isIso_glueingAwayRestrict B S hS f hf hy c
  have : IsIso (glueingAwayRestrict B S hS f hf hy c) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  have : IsIso (yoneda.map (glueingAwayRestrict B S hS f hf hy c)) := inferInstance
  intro v
  obtain ⟨ω, hω⟩ := isSurjective_of_presheafSurjective B S hS _
    (surjective_glueingAwayChart B S hS f hf hy c) v
  obtain ⟨α, hα⟩ := pointsMap_surjective_of_isIso B S hS
    (yoneda.map (glueingAwayRestrict B S hS f hf hy c)) ω
  refine ⟨pointsMap B S hS _ (glueingAwaySourceLift B S hS f hf hy c) α, ?_⟩
  rw [← pointsMap_comp_apply, (isPullback_glueingSpaceRestrict B S hS f hf hy c).w,
    pointsMap_comp_apply, hα, hω]

/-- **Clause (2) of [Stacks Project, Tag 0EDM].**  The morphism `X ⟶ X'` is an isomorphism over
the open complement `X' ∖ X'_y` of the fibre.

It is an open immersion, and surjective on points, hence an isomorphism by Stacks 03MD. Both
facts are checked over the chart `U` of `Y`, where the morphism is
`AlgebraicGeometry.glueingToSource` restricted to the complement of the chart-level fibre, an
isomorphism of schemes by `AlgebraicGeometry.isIso_glueingToSource_restrict`. -/
theorem isIso_glueingSpaceRestrict :
    IsIso (glueingSpaceRestrict B S hS f hf hy c) :=
  isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS _
    (isOpenImmersion_glueingSpaceRestrict B S hS f hf hy c)
    (surjective_pointsMap_glueingSpaceRestrict B S hS f hf hy c)

end Chart

/-! ### Stacks 0EDM -/

/-- **Stacks 0EDM.**  Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S`, and
let `y : Spec k ⟶ Y` be a closed immersion.  Then `f` factors as `X ⟶ X' ⟶ Y` with

1. `X' ⟶ Y` integral,
2. `X ⟶ X'` an isomorphism over the open complement `X' ∖ X'_y` of the fibre
   `X'_y = |h|⁻¹ {y}`,
3. `X'_y` a single point `p`, which is the point of a closed immersion `x' : Spec k ⟶ X'` over
   `y`, so that `κ(p) = k`,

and moreover `X' ⟶ Y` is finite when `f` is finite and `Y` is locally Noetherian.

The space `X'` is the quotient of the chart-level pushout over a separated étale chart of `Y`
(`AlgebraicGeometry.Space.EtaleChartRelation.exists_of_isAlgebraicSpace`) by the étale
equivalence relation induced by the chart's kernel pair; the sheafification it needs is
`AlgebraicGeometry.BigFppfOver.hasSheafify_type`.  "Locally Noetherian" is the source's
definition for algebraic spaces, a locally Noetherian surjective étale atlas
(`AlgebraicGeometry.Space.HasEtaleLocalProperty`, Stacks 03E6), and it gives local
Noetherianity of the chosen chart by Stacks 03E8. -/
@[stacks 0EDM]
theorem exists_glueingSpace_factorization {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom) {k : Type u} [Field k]
    (hk : B.Contains (Spec (CommRingCat.of k))) (σ : Spec (CommRingCat.of k) ⟶ S)
    (y : yoneda.obj (BigFppfOver.mk B S hS hk σ) ⟶ Y.1) (hy : IsClosedImmersion B S hS y) :
    ∃ (X' : AlgebraicSpaces B S hS) (g : X ⟶ X') (h : X' ⟶ Y),
      g ≫ h = f ∧
      IsIntegralHom B S hS h.hom ∧
      IsIso (openComplementRestriction B S hS g.hom
        (pointsMap B S hS X'.1 h.hom ⁻¹'
          Set.range (pointsMap B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ)) y))) ∧
      (∃ (x' : yoneda.obj (BigFppfOver.mk B S hS hk σ) ⟶ X'.1) (p : points B S hS X'.1),
        IsClosedImmersion B S hS x' ∧ x' ≫ h.hom = y ∧
        pointsMap B S hS X'.1 h.hom ⁻¹'
            Set.range (pointsMap B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ)) y) = {p} ∧
        Set.range (pointsMap B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ)) x') = {p}) ∧
      (IsFinite B S hS f.hom →
        HasEtaleLocalProperty B S hS Y.1
          (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T) →
        IsFinite B S hS h.hom) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := BigFppfOver.hasSheafify_type B S hS
  obtain ⟨c⟩ := EtaleChartRelation.exists_of_isAlgebraicSpace Y.property
  have hfib := preimage_range_pointsMap_glueingSpaceToBase B S hS f hf hy c
  let X' : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_glueingSpaceSheaf B S hS f hf hy c⟩
  let g : X ⟶ X' := ObjectProperty.homMk (glueingSpaceFromSource B S hS f hf hy c)
  let h : X' ⟶ Y := ObjectProperty.homMk (glueingSpaceToBase B S hS f hf hy c)
  -- the source of `y` has exactly one point
  obtain ⟨q⟩ : Nonempty (points B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ))) :=
    ⟨(schemePointsHomeomorph B S hS _).symm
      (show Spec (CommRingCat.of k) from default)⟩
  have hq : ∀ q' : points B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ)), q' = q := fun q' ↦
    (schemePointsHomeomorph B S hS _).injective
      (Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _)
  have hrange : Set.range (pointsMap B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ))
      (glueingSpacePoint B S hS f hf hy c)) =
      {pointsMap B S hS _ (glueingSpacePoint B S hS f hf hy c) q} := by
    ext z
    constructor
    · rintro ⟨q', rfl⟩
      rw [hq q']
      rfl
    · rintro rfl
      exact ⟨q, rfl⟩
  refine ⟨X', g, h, ?_, isIntegralHom_glueingSpaceToBase B S hS f hf hy c, ?_,
    ⟨glueingSpacePoint B S hS f hf hy c, _, isClosedImmersion_glueingSpacePoint B S hS f hf hy c,
      glueingSpacePoint_comp_toBase B S hS f hf hy c, hfib.trans hrange, hrange⟩, ?_⟩
  · exact ObjectProperty.hom_ext _ (glueingSpaceFromSource_comp_toBase B S hS f hf hy c)
  · change IsIso (openComplementRestriction B S hS (glueingSpaceFromSource B S hS f hf hy c)
      (pointsMap B S hS _ (glueingSpaceToBase B S hS f hf hy c) ⁻¹'
        Set.range (pointsMap B S hS (yoneda.obj (BigFppfOver.mk B S hS hk σ)) y)))
    rw [hfib]
    exact isIso_glueingSpaceRestrict B S hS f hf hy c
  · intro hfin hnoeth
    have : _root_.AlgebraicGeometry.IsLocallyNoetherian
        ((BigFppfOver.toScheme B S hS).obj c.U) :=
      (exists_atlas_iff_forall_etale B S hS Y.1
        (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T)
        Y.property).mp hnoeth c.U c.u c.etale_u
    exact isFinite_glueingSpaceToBase B S hS f hf hy c hfin

end AlgebraicGeometry.Space

end
