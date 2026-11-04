module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Surjectivity, scheme properties and étale-local properties in a larger value universe

An algebraic space over a scheme `S` of a big fppf site `B` is a presheaf on the big fppf site
of `S` with values in `Type u`, the universe of the schemes. A formal algebraic space is a sheaf
of `Type (u + 1)`, so the notions attached to a morphism of algebraic spaces have to be
available for a value universe `max w u` with `w` independent of `u`. This file carries three
of them: surjectivity on points, having a property of morphisms of schemes after every
represented base change, and having an étale-local property of schemes.

Nothing is weakened by the move. Surjectivity is surjectivity of the map on points of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints`, and the two relative conditions are
the same conditions tested against the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`
rather than out of `CategoryTheory.yoneda.obj U`. At `w = u` the notions below are the ones
already in the library, since `CategoryTheory.uliftYoneda.{u}` and `CategoryTheory.yoneda` are
isomorphic.

## Main definitions

* `AlgebraicGeometry.Space.IsSurjectiveULift` is `AlgebraicGeometry.Space.IsSurjective` for a
  morphism of presheaves of `Type (max w u)`.
* `AlgebraicGeometry.Space.HasSchemePropertyULift` is
  `AlgebraicGeometry.Space.HasSchemeProperty` for such a morphism.
* `AlgebraicGeometry.Space.IsRepresentableThickeningULift` is that condition at the property of
  being a thickening of schemes.
* `AlgebraicGeometry.Space.HasEtaleLocalPropertyULift` is
  `AlgebraicGeometry.Space.HasEtaleLocalProperty` for a presheaf of `Type (max w u)`.

## Main results

* `AlgebraicGeometry.Space.exists_point_of_isPullbackULift`: a compatible pair of points of a
  cartesian square of presheaves of `Type (max w u)` lifts to a point of the upper left corner.

## Implementation notes

The relative conditions are stated with `CategoryTheory.MorphismProperty.relative` along
`CategoryTheory.uliftYoneda.{w}` rather than with
`CategoryTheory.MorphismProperty.presheaf`, which is that relative property along
`CategoryTheory.yoneda` and so is only available in the value universe of the site. This is the
convention of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`.

`AlgebraicGeometry.Space.IsRepresentableThickeningULift` is a condition on a *morphism* of
presheaves, namely that each of its represented base changes is a thickening of schemes in the
sense of Stacks 04EX. It is therefore not a counterpart of
`AlgebraicGeometry.Space.IsThickening`, which is the condition of Stacks 05ZK on a *subfunctor*
of an algebraic space, and it is named accordingly.

`AlgebraicGeometry.Space.exists_point_of_isPullbackULift` is proved exactly as
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf` is: the two given points agree in
the lower right corner, so their field-valued representatives admit a common extension over the
spectrum of a single field of the site, the two restricted sections are two morphisms out of
`CategoryTheory.uliftYoneda.{w}.obj A` agreeing over the lower right corner, and the universal
property of the square turns them into a morphism to the upper left corner whose value at the
identity is the point looked for. The algebraic-space axioms are never used.

## References

* [Stacks Project, Tag 025V](https://stacks.math.columbia.edu/tag/025V)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes is *surjective* when the induced map on their
sets of points is surjective. This is `AlgebraicGeometry.Space.IsSurjective` for such a
morphism. -/
abbrev IsSurjectiveULift {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : X ⟶ Y) : Prop :=
  Function.Surjective (pointsMapULift.{w} B S hS X f)

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes *has a property `P` of morphisms of schemes* when
it is representable relative to the universe-lifted Yoneda embedding and the morphism of schemes
underlying every represented base change of it has `P`. This is
`AlgebraicGeometry.Space.HasSchemeProperty` with the scheme-valued points taken to be the
morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
abbrev HasSchemePropertyULift (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes is a *representable thickening* when it is
representable relative to the universe-lifted Yoneda embedding and the morphism of schemes
underlying every represented base change of it is a thickening, that is a surjective closed
immersion. -/
abbrev IsRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) : Prop :=
  HasSchemePropertyULift.{w} B S hS
    (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u}) a

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u))
variable (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]

/-- A presheaf on the big fppf site of `S` with values in a universe `max w u` independent of
the universe `u` of the schemes *has an étale-local property `P` of schemes* when it admits a
surjective étale atlas by a scheme with `P`. This is
`AlgebraicGeometry.Space.HasEtaleLocalProperty` with the scheme-valued points taken to be the
morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
abbrev HasEtaleLocalPropertyULift : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : (uliftYoneda.{w}).obj U ⟶ F),
    HasSchemePropertyULift.{w} B S hS
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) f ∧
    HasSchemePropertyULift.{w} B S hS
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) f ∧
    P ((BigFppfOver.toScheme B S hS).obj U)

/-- Compatible points of the two middle terms of a cartesian square of presheaves on the big
fppf site of `S` with values in a universe `max w u` independent of the universe `u` of the
schemes lift to a point of its upper left corner. This is
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf` for such presheaves. -/
theorem exists_point_of_isPullbackULift
    {W Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (z : pointsULift.{w} B S hS Z) (x : pointsULift.{w} B S hS X)
    (h : pointsMapULift B S hS Z g z = pointsMapULift B S hS X f x) :
    ∃ v : pointsULift.{w} B S hS W,
      pointsMapULift B S hS W p v = z ∧ pointsMapULift B S hS W q v = x := by
  classical
  obtain ⟨z₀, rfl⟩ := Quot.exists_rep z
  obtain ⟨x₀, rfl⟩ := Quot.exists_rep x
  rw [pointsMapULift_class, pointsMapULift_class] at h
  obtain ⟨r, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    (FieldValuedPointULift.class_eq_class_iff B S hS Y
      (FieldValuedPointULift.map B S hS Z g z₀)
      (FieldValuedPointULift.map B S hS X f x₀)).mp h
  let A := r.siteObject B S hS Y
  let z' := Z.map i.op z₀.value
  let x' := X.map j.op x₀.value
  let yZ : (uliftYoneda.{w}).obj A ⟶ Z := uliftYonedaEquiv.symm z'
  let yX : (uliftYoneda.{w}).obj A ⟶ X := uliftYonedaEquiv.symm x'
  have hcompat : yZ ≫ g = yX ≫ f := by
    apply (uliftYonedaEquiv.{w} (X := A) (F := Y)).injective
    simpa only [uliftYonedaEquiv_comp, yZ, yX, Equiv.apply_symm_apply] using calc
      g.app (Opposite.op A) z' = Y.map i.op (g.app
          (Opposite.op (z₀.siteObject B S hS Z)) z₀.value) :=
        g.naturality_apply i.op z₀.value
      _ = r.value := hi
      _ = Y.map j.op (f.app (Opposite.op (x₀.siteObject B S hS X)) x₀.value) := hj.symm
      _ = f.app (Opposite.op A) x' := (f.naturality_apply j.op x₀.value).symm
  have hp : p.app (Opposite.op A) (uliftYonedaEquiv.{w} (sq.lift yZ yX hcompat)) = z' := by
    rw [← uliftYonedaEquiv_comp, sq.lift_fst]
    simp only [yZ, Equiv.apply_symm_apply]
  have hq : q.app (Opposite.op A) (uliftYonedaEquiv.{w} (sq.lift yZ yX hcompat)) = x' := by
    rw [← uliftYonedaEquiv_comp, sq.lift_snd]
    simp only [yX, Equiv.apply_symm_apply]
  refine ⟨FieldValuedPointULift.class B S hS W
    ⟨r.carrier, r.contained, r.toBase, uliftYonedaEquiv.{w} (sq.lift yZ yX hcompat)⟩, ?_, ?_⟩
  all_goals
    rw [pointsMapULift_class]
    apply FieldValuedPointULift.class_eq_class_of_hasCommonExtension
    refine ⟨_, FieldValuedPointULift.dominates_refl B S hS _ _, ?_⟩
    first
      | exact ⟨i, hp.symm⟩
      | exact ⟨j, hq.symm⟩

end AlgebraicGeometry.Space

end
