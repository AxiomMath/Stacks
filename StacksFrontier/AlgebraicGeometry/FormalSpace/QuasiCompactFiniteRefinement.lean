module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleOpenPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints

/-!
# Shrinking an atlas of a formal algebraic space with quasi-compact reduction

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an fppf sheaf on the big fppf
site of `S` carrying an atlas as in Definition 0AIM, and let `i : Xred ⟶ X` be a reduction of
`X` whose source is a quasi-compact algebraic space. Then finitely many members of the atlas
are already jointly surjective on the points of Stacks 03BU. This is the point-set content of
the implication (1) ⇒ (2) of **Stacks 0AJ9**.

The cover that compactness is applied to lives on an *affine* chart of `Xred`, not on `Xred`
itself: Stacks 03H6 in the larger value universe
(`AlgebraicGeometry.Space.exists_affine_chart_of_isQuasiCompactSpaceULift`) supplies an object
`U` of the site with affine underlying scheme and a morphism `a : U ⟶ Xred` which is surjective
after every represented base change, and the point space of the universe-lifted presheaf `U`
represents is quasi-compact because the scheme is. For each member `Xᵢ ⟶ X` of the atlas the
fibre product `Xᵢ ×_X U` is an algebraic space, by representability of that member, and an étale
scheme chart of it composed with the projection to `U` is a morphism which is étale after every
represented base change, hence open on points by clause (3) of Stacks 03BX. Those images cover,
because the atlas is jointly surjective on the points of `X` and points of a cartesian square
lift (Stacks 03H4); finitely many of them therefore suffice, and a point of `X` comes from a
point of `Xred`, hence from a point of `U`, hence from a member of the finite subfamily.

## Main results

* `AlgebraicGeometry.Space.surjective_pointsMapULift_of_relative_surjective`: a morphism into an
  algebraic space from a universe-lifted represented presheaf which is surjective after every
  represented base change is surjective on points. This is
  `AlgebraicGeometry.Space.surjective_pointsMap_of_presheaf_surjective` in a value universe
  independent of the universe of the schemes.
* `AlgebraicGeometry.Space.exists_etale_chart_surjective_pointsULift`: an algebraic space in
  such a value universe receives a scheme chart which is étale after every represented base
  change and surjective on points.
* `AlgebraicGeometry.FormalSpace.exists_finite_jointly_surjective_of_isQuasiCompactSpaceULift`:
  the point-set content of the implication (1) ⇒ (2) of Stacks 0AJ9.

## Implementation notes

The transfer of `AlgebraicGeometry.Space.surjective_pointsMap_of_presheaf_surjective` to the
larger value universe is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType`: the target is isomorphic to the
universe lift of a presheaf of `Type u`, the morphism composed with that isomorphism is the
universe lift of a morphism of presheaves of `Type u`, relative surjectivity of a universe lift
is relative surjectivity of the morphism, and so is surjectivity on points. This is why the
statement carries the algebraic-space hypothesis on the target, which the statement in the value
universe of the site does not need.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Relative surjectivity and surjectivity on points, in a larger value universe -/

/-- **A morphism into an algebraic space from a universe-lifted represented presheaf which is
surjective after every represented base change is surjective on the points of Stacks 03BU.**
This is `AlgebraicGeometry.Space.surjective_pointsMap_of_presheaf_surjective` for a value
universe `max w u` independent of the universe `u` of the schemes.

The target is isomorphic to the universe lift of a presheaf of `Type u`; the morphism followed
by that isomorphism is the universe lift of a morphism of presheaves of `Type u`, which is
surjective after every represented base change, hence surjective on points, hence so is its
universe lift. -/
theorem surjective_pointsMapULift_of_relative_surjective
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    {T : BigFppfOver B S hS} (a : (uliftYoneda.{w}).obj T ⟶ F)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a) :
    Function.Surjective (pointsMapULift.{w} B S hS ((uliftYoneda.{w}).obj T) a) := by
  obtain ⟨F', -, ⟨e⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  obtain ⟨a', ha'⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj T) (a ≫ e.inv)
  have hrel : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        (Functor.whiskerRight a' uliftFunctor.{w}) := by
    rw [ha']
    exact MorphismProperty.RespectsIso.postcomp _ e.inv a ha
  have hs : Function.Surjective (pointsMapULift.{w} B S hS
      ((uliftYoneda.{w}).obj T) (Functor.whiskerRight a' uliftFunctor.{w})) :=
    (isSurjectiveULift_whiskerRight_iff B S hS a').mpr
      (surjective_pointsMap_of_presheaf_surjective B S hS a'
        ((relative_uliftYoneda_whiskerRight_iff' B S hS _ a').mp hrel))
  have hbs : Function.Surjective
      (pointsMapULift.{w} B S hS ((uliftYoneda.{w}).obj T) (a ≫ e.inv)) := ha' ▸ hs
  have hinj : Function.Injective (pointsMapULift.{w} B S hS F e.inv) :=
    (bijective_pointsMapULift_of_iso B S hS e.symm).1
  intro z
  obtain ⟨x, hx⟩ := hbs (pointsMapULift.{w} B S hS F e.inv z)
  exact ⟨x, hinj ((pointsMapULift_comp_apply B S hS a e.inv x).symm.trans hx)⟩

/-- **An algebraic space over `S` with values in a universe `max w u` independent of the
universe `u` of the schemes receives a scheme chart which is étale after every represented base
change and surjective on points.** The chart is the one the algebraic-space condition provides;
what is added is that relative surjectivity of it gives surjectivity on points. -/
theorem exists_etale_chart_surjective_pointsULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hF : IsAlgebraicSpaceULift.{w} B S hS F) :
    ∃ (V : BigFppfOver B S hS) (β : (uliftYoneda.{w}).obj V ⟶ F),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) β ∧
      Function.Surjective (pointsMapULift.{w} B S hS ((uliftYoneda.{w}).obj V) β) := by
  obtain ⟨V, β, hsurj, hetale⟩ := hF.exists_atlas
  exact ⟨V, β, hetale, surjective_pointsMapULift_of_relative_surjective B S hS hF β hsurj⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopologyULift

/-! ### The finite subfamily -/

/-- **Finitely many members of an atlas of a formal algebraic space with quasi-compact reduction
are already jointly surjective on points.** This is the point-set content of the implication
(1) ⇒ (2) of Stacks 0AJ9.

An affine chart `U ⟶ Xred` of the quasi-compact algebraic space `Xred`, which Stacks 03H6
supplies, has quasi-compact point space. For each `j` the fibre product `Xⱼ ×_X U` is an
algebraic space, since `Xⱼ ⟶ X` is representable by algebraic spaces, and an étale scheme chart
of it followed by the projection to `U` is étale after every represented base change, hence open
on points. Those open images cover the point space of `U`, because the family `{Xⱼ ⟶ X}` is
jointly surjective on the points of `X` and a compatible pair of points of a cartesian square
lifts, so finitely many of them cover it. A point of `X` is the image of a point of `Xred`,
because the inclusion of a reduction is bijective on points, hence of a point of `U`; that point
lies in one of the finitely many images, and pushing its preimage along the other projection of
the fibre product exhibits it as the image of a point of the corresponding `Xⱼ`. -/
theorem exists_finite_jointly_surjective_of_isQuasiCompactSpaceULift
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (h : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj)
    {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} {f : ∀ j, Xi j ⟶ X}
    (hetale : ∀ j, IsRepresentableEtale B S hS (f j))
    (hsurjective : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    ∃ t : Finset I, ∀ p : Space.pointsULift.{u + 1} B S hS X.obj,
      ∃ j ∈ t, ∃ z : Space.pointsULift.{u + 1} B S hS (Xi j).obj,
        Space.pointsMapULift.{u + 1} B S hS (Xi j).obj (f j).hom z = p := by
  classical
  -- an affine chart of the quasi-compact reduction, and the induced point of `X`
  obtain ⟨U, a, hUaff, hasurj, -⟩ :=
    Space.exists_affine_chart_of_isQuasiCompactSpaceULift B S hS hi.algebraic h
  set ξ : (uliftYoneda.{u + 1}).obj U ⟶ X.obj := a ≫ i.hom with hξ
  -- an étale chart of each fibre product `Xⱼ ×_X U`, surjective on points
  choose V β hβetale hβsurj using fun j ↦
    Space.exists_etale_chart_surjective_pointsULift B S hS ((hetale j).1 U ξ)
  -- those charts are open on the points of `U`
  set C : I → Set (Space.pointsULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)) := fun j ↦
    Set.range (Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj (V j))
      (β j ≫ pullback.fst ξ (f j).hom))
  have hCopen : ∀ j, IsOpen (C j) := fun j ↦
    (Space.isOpenMap_pointsMapULift_of_relativeEtale B S hS _
      ((hetale j).2 U ξ (V j) (β j) (hβetale j))).isOpen_range
  -- and they cover, the atlas being jointly surjective on the points of `X`
  have hCcover : ∀ q, q ∈ ⋃ j, C j := by
    intro q
    obtain ⟨j, z, hz⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS f
      hsurjective (Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U) ξ q)
    obtain ⟨v, hv, -⟩ := Space.exists_pointsULift_of_isPullback B S hS
      (IsPullback.of_hasPullback ξ (f j).hom) q z hz.symm
    obtain ⟨w, hw⟩ := hβsurj j v
    refine Set.mem_iUnion.2 ⟨j, w, ?_⟩
    rw [Space.pointsMapULift_comp_apply, hw, hv]
  -- the point space of an affine chart is quasi-compact
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have _ : CompactSpace (Space.pointsULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)) :=
    Space.compactSpace_pointsULift_uliftYoneda B S hS U inferInstance
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C hCopen fun q _ ↦ hCcover q
  -- a point of `X` comes from a point of `U`, hence from a member of the finite subfamily
  refine ⟨t, fun p ↦ ?_⟩
  obtain ⟨pred, hpred⟩ := hi.bijective_pointsMapULift.2 p
  obtain ⟨q, hq⟩ := Space.surjective_pointsMapULift_of_relative_surjective B S hS
    hi.algebraic a hasurj pred
  have hqp : Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U) ξ q = p := by
    rw [hξ, Space.pointsMapULift_comp_apply, hq, hpred]
  obtain ⟨j, hjt, v, hv⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
  set r : Space.pointsULift.{u + 1} B S hS (pullback ξ (f j).hom) :=
    Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj (V j)) (β j) v
  have hrq : Space.pointsMapULift.{u + 1} B S hS (pullback ξ (f j).hom)
      (pullback.fst ξ (f j).hom) r = q :=
    (Space.pointsMapULift_comp_apply B S hS (β j) (pullback.fst ξ (f j).hom) v).symm.trans hv
  refine ⟨j, hjt, Space.pointsMapULift.{u + 1} B S hS (pullback ξ (f j).hom)
    (pullback.snd ξ (f j).hom) r, ?_⟩
  have hfin : Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U) ξ
      (Space.pointsMapULift.{u + 1} B S hS (pullback ξ (f j).hom)
        (pullback.fst ξ (f j).hom) r) = p := by rw [hrq]; exact hqp
  exact (Space.pointsMapULift_apply_comm B S hS pullback.condition r).symm.trans hfin

end AlgebraicGeometry.FormalSpace

end
