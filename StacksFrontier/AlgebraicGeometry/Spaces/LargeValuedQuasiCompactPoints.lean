module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# Quasi-compactness and the point space, for a value universe larger than the schemes

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 03E4** says that an algebraic
space over `S` is quasi-compact, in the sense of Stacks 03E3, exactly when its space of points
is quasi-compact, **Stacks 040W**, part (1), says that the target of a surjective morphism of
algebraic spaces with quasi-compact source is quasi-compact, and **Stacks 03H6** says that a
quasi-compact algebraic space receives a surjective étale morphism from an *affine* object of
the site. All three are proved in this library
for presheaves with values in `Type u`, the value universe of the site. This file carries them
to a value universe `max w u` independent of the universe `u` of the schemes, which is the form
needed for the reduction of a formal algebraic space: a formal algebraic space is a sheaf of
`Type (u + 1)`, so its reduction is an algebraic space with values in that larger universe.

The transfer is the one of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType`: an
algebraic space with values in `Type (max w u)` is isomorphic to the universe lift of a presheaf
of `Type u`, quasi-compactness of a universe lift is quasi-compactness of the presheaf, and the
point space of a universe lift is homeomorphic to the point space of the presheaf.

## Main definitions

* `AlgebraicGeometry.Space.pointsULiftHomeomorphOfIso`: isomorphic presheaves have homeomorphic
  point spaces; `AlgebraicGeometry.Space.bijective_pointsMapULift_of_iso` is the underlying
  bijection, stated without reference to the topologies.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpaceULift_uliftYoneda`: a universe-lifted Yoneda
  presheaf with quasi-compact underlying scheme is quasi-compact.
* `AlgebraicGeometry.Space.compactSpace_pointsULift_uliftYoneda`: the point space of a
  universe-lifted represented presheaf is quasi-compact when the representing scheme is.
* `AlgebraicGeometry.Space.isQuasiCompactSpaceULift_iff_compactSpace_pointsULift`:
  **Stacks 03E4** for a value universe independent of the universe of the schemes.
* `AlgebraicGeometry.Space.isQuasiCompactSpaceULift_of_surjective_pointsMapULift`: an algebraic
  space over `S` receiving a morphism surjective on points from a presheaf with quasi-compact
  point space is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiCompactSpaceULift_of_isSurjectiveULift`: **Stacks 040W**,
  part (1), for a value universe independent of the universe of the schemes.
* `AlgebraicGeometry.Space.exists_affine_chart_of_isQuasiCompactSpaceULift`: **Stacks 03H6**,
  the forward implication, for a value universe independent of the universe of the schemes.

## Implementation notes

The point topologies are the `@[instance_reducible]` definitions
`AlgebraicGeometry.Space.pointTopology` and `AlgebraicGeometry.Space.pointTopologyULift`, which
are not global instances; they are local instances here, as they are in the files proving
Stacks 03E4 and Stacks 03BX.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology pointTopologyULift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point space of a universe-lifted Yoneda presheaf -/

/-- A universe-lifted Yoneda presheaf whose underlying scheme is quasi-compact is a
quasi-compact algebraic space over `S`: its identity is a surjective étale atlas. -/
theorem isQuasiCompactSpaceULift_uliftYoneda (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T : Type u)) :
    IsQuasiCompactSpaceULift.{w} B S hS ((uliftYoneda.{w}).obj T) :=
  ⟨T, 𝟙 _, hT,
    relative_id_of_isomorphisms B S hS _
      (fun _ _ φ hφ ↦ by
        have := hφ
        change AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map φ)
        infer_instance) T,
    fun _ φ hφ ↦ by simpa using hφ⟩

/-! ### Point spaces of isomorphic presheaves -/

/-- An isomorphism of presheaves on the big fppf site of `S` with values in a universe
`max w u` independent of the universe `u` of the schemes is bijective on points, the two
induced maps on points being mutually inverse because the point space is functorial. -/
theorem bijective_pointsMapULift_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G) :
    Function.Bijective (pointsMapULift.{w} B S hS F e.hom) := by
  have key : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G) (x),
      pointsMapULift.{w} B S hS G e.inv (pointsMapULift.{w} B S hS F e.hom x) = x := by
    intro F G e x
    have h : pointsMapULift.{w} B S hS F (e.hom ≫ e.inv) x = x := by
      rw [e.hom_inv_id, pointsMapULift_id]; rfl
    rwa [pointsMapULift_comp, Function.comp_apply] at h
  exact ⟨Function.LeftInverse.injective (key e),
    Function.RightInverse.surjective (key e.symm)⟩

/-- Isomorphic presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes have homeomorphic point spaces: the two induced
maps on points are mutually inverse, and every morphism is continuous on points. -/
noncomputable def pointsULiftHomeomorphOfIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G) :
    pointsULift.{w} B S hS F ≃ₜ pointsULift.{w} B S hS G where
  toFun := pointsMapULift B S hS F e.hom
  invFun := pointsMapULift B S hS G e.inv
  left_inv x := by
    have h := congrFun (pointsMapULift_comp B S hS F e.hom e.inv) x
    rw [e.hom_inv_id, pointsMapULift_id] at h
    exact h.symm
  right_inv x := by
    have h := congrFun (pointsMapULift_comp B S hS G e.inv e.hom) x
    rw [e.inv_hom_id, pointsMapULift_id] at h
    exact h.symm
  continuous_toFun := continuous_pointsMapULift B S hS e.hom
  continuous_invFun := continuous_pointsMapULift B S hS e.inv

/-- The point space of a universe-lifted represented presheaf on the big fppf site of `S` is
quasi-compact when the representing scheme is: it is the point space of the represented
presheaf, which is homeomorphic to the scheme by clause (1) of Stacks 03BX. -/
theorem compactSpace_pointsULift_uliftYoneda (U : BigFppfOver B S hS)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    CompactSpace (pointsULift.{w} B S hS ((uliftYoneda.{w}).obj U)) :=
  have _ : CompactSpace (points B S hS (yoneda.obj U)) :=
    @compactSpace_points_yoneda B S hS U hU
  (pointsHomeomorphPointsULift.{w} B S hS (yoneda.obj U)).compactSpace

/-! ### Stacks 03E4 in a larger value universe -/

/-- **Stacks 03E4**, the forward implication, for a value universe `max w u` independent of the
universe `u` of the schemes: the point space of a quasi-compact algebraic space over `S` is
quasi-compact. -/
theorem compactSpace_pointsULift_of_isQuasiCompactSpaceULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (h : IsQuasiCompactSpaceULift.{w} B S hS F) :
    CompactSpace (pointsULift.{w} B S hS F) := by
  obtain ⟨F', hF', ⟨e⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  have hqc : IsQuasiCompactSpace B S hS F' :=
    (isQuasiCompactSpaceULift_comp_uliftFunctor_iff.{w} B S hS F').mp
      (isQuasiCompactSpaceULift_of_iso B S hS e.symm h)
  have hpts : CompactSpace (points B S hS F') :=
    compactSpace_points_of_isQuasiCompactSpace B S hS hF' hqc
  have := (pointsHomeomorphPointsULift.{w} B S hS F').compactSpace
  exact (pointsULiftHomeomorphOfIso.{w} B S hS e).compactSpace

/-- **Stacks 03E4**, the reverse implication, for a value universe `max w u` independent of the
universe `u` of the schemes: an algebraic space over `S` whose point space is quasi-compact is
quasi-compact. -/
theorem isQuasiCompactSpaceULift_of_compactSpace_pointsULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (h : CompactSpace (pointsULift.{w} B S hS F)) :
    IsQuasiCompactSpaceULift.{w} B S hS F := by
  obtain ⟨F', hF', ⟨e⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  have h' : CompactSpace (pointsULift.{w} B S hS (F' ⋙ uliftFunctor.{w})) :=
    (pointsULiftHomeomorphOfIso.{w} B S hS e).symm.compactSpace
  have hpts : CompactSpace (points B S hS F') :=
    (pointsHomeomorphPointsULift.{w} B S hS F').symm.compactSpace
  exact isQuasiCompactSpaceULift_of_iso B S hS e
    ((isQuasiCompactSpaceULift_comp_uliftFunctor_iff.{w} B S hS F').mpr
      (isQuasiCompactSpace_of_compactSpace_points B S hS hF' hpts))

/-- **Stacks 03E4** for a value universe `max w u` independent of the universe `u` of the
schemes: an algebraic space over `S` is quasi-compact if and only if its space of points is
quasi-compact. -/
@[stacks 03E4 "for a value universe independent of the universe of the schemes"]
theorem isQuasiCompactSpaceULift_iff_compactSpace_pointsULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) :
    IsQuasiCompactSpaceULift.{w} B S hS F ↔ CompactSpace (pointsULift.{w} B S hS F) :=
  ⟨compactSpace_pointsULift_of_isQuasiCompactSpaceULift B S hS hF,
    isQuasiCompactSpaceULift_of_compactSpace_pointsULift B S hS hF⟩

/-- An algebraic space over `S` with values in a universe `max w u` independent of the
universe `u` of the schemes which receives a morphism surjective on points from a presheaf
with quasi-compact point space is quasi-compact: the induced map of point spaces is continuous
and surjective, so the target point space is quasi-compact, and Stacks 03E4 in that value
universe turns that back into quasi-compactness. -/
theorem isQuasiCompactSpaceULift_of_surjective_pointsMapULift
    {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (hE : CompactSpace (pointsULift.{w} B S hS E)) (g : E ⟶ F)
    (hg : Function.Surjective (pointsMapULift.{w} B S hS E g)) :
    IsQuasiCompactSpaceULift.{w} B S hS F :=
  (isQuasiCompactSpaceULift_iff_compactSpace_pointsULift.{w} B S hS hF).mpr
    (@Function.Surjective.compactSpace _ _ _ _ _ (continuous_pointsMapULift B S hS g) hE hg)

/-! ### Stacks 040W, part (1), in a larger value universe -/

/-- **Stacks 040W**, part (1), for a value universe `max w u` independent of the universe `u` of
the schemes: if `f : F ⟶ G` is a surjective morphism of algebraic spaces over `S` and `F` is
quasi-compact, then `G` is quasi-compact. The point space of `G` is the image of the
quasi-compact point space of `F` under a continuous surjection. -/
@[stacks 040W "part (1), for a value universe independent of the universe of the schemes"]
theorem isQuasiCompactSpaceULift_of_isSurjectiveULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (f : F ⟶ G) (hf : IsSurjectiveULift.{w} B S hS f)
    (h : IsQuasiCompactSpaceULift.{w} B S hS F) :
    IsQuasiCompactSpaceULift.{w} B S hS G :=
  isQuasiCompactSpaceULift_of_surjective_pointsMapULift B S hS hG
    (compactSpace_pointsULift_of_isQuasiCompactSpaceULift B S hS hF h) f hf

/-! ### Stacks 03H6 in the larger value universe -/

/-- **Stacks 03H6**, the forward implication, for a presheaf with values in a universe
`max w u` independent of the universe `u` of the schemes: a quasi-compact algebraic space over
`S` admits a surjective étale chart whose source is an object of the site with *affine*
underlying scheme, not merely a quasi-compact one.

The presheaf is isomorphic to the universe lift of a presheaf of `Type u`, which is a
quasi-compact algebraic space; Tag 03H6 supplies an affine surjective étale chart of it, and
the universe lift of that chart composed with the isomorphism is the required one. -/
@[stacks 03H6 "the affine chart of a quasi-compact algebraic space, in a value universe \
independent of the universe of the schemes"]
theorem exists_affine_chart_of_isQuasiCompactSpaceULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (h : IsQuasiCompactSpaceULift.{w} B S hS F) :
    ∃ (U : BigFppfOver B S hS) (a : (uliftYoneda.{w}).obj U ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a ∧
      IsEtaleULift.{w} B S hS a := by
  obtain ⟨F', ⟨e⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift.{w} B S hS hF
  have hF' : IsAlgebraicSpace B S hS F' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff.{w} B S hS F').mp
      (isAlgebraicSpaceULift_of_iso B S hS e.symm hF)
  have h' : IsQuasiCompactSpace B S hS F' :=
    (isQuasiCompactSpaceULift_comp_uliftFunctor_iff.{w} B S hS F').mp
      (isQuasiCompactSpaceULift_of_iso B S hS e.symm h)
  obtain ⟨U, a', hUaff, hsurj, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F' hF').mp h'
  have hsurjL : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        (Functor.whiskerRight a' uliftFunctor.{w}) :=
    (relative_comp_map_iff yoneda
      ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
        (Type (max w u))).obj uliftFunctor.{w}) _ a').mpr hsurj
  have hetaleL : IsEtaleULift.{w} B S hS (Functor.whiskerRight a' uliftFunctor.{w}) :=
    (isEtaleULift_whiskerRight_iff B S hS a').mpr hetale
  refine ⟨U, Functor.whiskerRight a' uliftFunctor.{w} ≫ e.hom, hUaff,
    MorphismProperty.RespectsIso.postcomp _ e.hom _ hsurjL, ?_⟩
  intro V φ hφ
  have hassoc : (φ ≫ Functor.whiskerRight a' uliftFunctor.{w}) ≫ e.hom
      = φ ≫ Functor.whiskerRight a' uliftFunctor.{w} ≫ e.hom := Category.assoc _ _ _
  exact hassoc ▸ MorphismProperty.RespectsIso.postcomp _ e.hom
    (φ ≫ Functor.whiskerRight a' uliftFunctor.{w}) (hetaleL V φ hφ)

end AlgebraicGeometry.Space

end
