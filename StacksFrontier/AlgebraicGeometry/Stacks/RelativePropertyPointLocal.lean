module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent

/-!
# A relative property is local on the scheme-valued points of the target

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. The relative property `P` of
**Stacks 03YK** is tested on the algebraic spaces representing the base changes of `f` along
scheme-valued points `y` of `𝒴` with values in `U`. This file proves that the test may be run
locally on `U`: if every point of `U` lies in the image of a flat morphism `W ⟶ U` locally of
finite presentation such that the test succeeds for the restricted point `W ⟶ U ⟶ 𝒴`, then it
succeeds for `y`.

This is the local half of the proof of **Stacks 045D**
(`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`), with the covering family supplied
point by point instead of being extracted from a covering sieve; the restricted points need not
come from any single 1-morphism into `𝒴`. That is the form needed when the local information
lives on a family of open substacks of `𝒴` rather than on one chart.

## Main results

* `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_of_forall_point_local`: the test of
  Stacks 03YK at a scheme-valued point succeeds as soon as it succeeds locally on that point.

## Implementation notes

The proof is that of Stacks 045D up to the point where the restriction of the representing
algebraic space `F` to a member `W ⟶ U` of the covering has been identified with a representing
algebraic space of the base change along the restricted point
(`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_relocalizeRestrict`): there the
hypothesis applies directly. The covering family is indexed by the points of `U`, one member per
point, so its index type lives in `Type u` and the locality of `P` is used at the fppf
precoverage of index universe `u`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u

/-- **The test of Stacks 03YK is local on the scheme-valued point.** Let `P` be stable under base
change and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism over
the big fppf site of `S` and let `y` be a scheme-valued point of `𝒴` with values in `U`. Suppose
that every point `t` of `U` lies in the image of a flat morphism `m : W ⟶ U` locally of finite
presentation such that every algebraic space representing the base change of `f` along
`W ⟶ U ⟶ 𝒴` has structural morphism with `P`. Then every algebraic space representing the base
change of `f` along `y` has structural morphism with `P`. -/
theorem prop_algebraicSpaceMap_of_forall_point_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (hloc : ∀ t : (BigFppfOver.toScheme B S hS).obj U,
      ∃ (W : B.Schemes) (m : W ⟶ U.left), Flat (B.inclusion.map m) ∧
        LocallyOfFinitePresentation (B.inclusion.map m) ∧ t ∈ Set.range (B.inclusion.map m) ∧
        ∀ (F : (BigFppfOver B W.1 W.2)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W.1 W.2 F),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map (m ≫ U.hom)) 𝒳.val.p 𝒴.val.p (Over.map m ⋙ y)
              f.toFunctor)
            (presheafOfCategories (F ⋙ typeToCat)).p) →
          P (algebraicSpaceMap B S hS (Over.mk (m ≫ U.hom))
            ((spacesOverSmallerBaseFunctor B W.1 S W.2 hS (m ≫ U.hom)).obj ⟨F, hF⟩)))
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  classical
  obtain ⟨E⟩ := hE
  choose W m hflat hlfp hsurj hP using hloc
  -- the covering family, one member per point of the underlying scheme of `U`
  let V' : (B.inclusion.obj U.left) → BigFppfOver B S hS := fun x => Over.mk (m x ≫ U.hom)
  let k' : ∀ x, V' x ⟶ U := fun x => Over.homMk (m x)
  have hcov := Space.ofArrows_yoneda_mem_fppfPrecoverage.{u, u} B S hS (U := U) V' k'
    (fun x => hflat x) (fun x => hlfp x) (fun x => by
      obtain ⟨z, hz⟩ := hsurj x
      exact ⟨x, z, hz⟩)
  refine (Space.prop_relocalizeToYoneda_iff B S hS P U F hF).1 ?_
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := P) (K := Space.Topology.fppf.precoverage.{u, u} B S hS) hcov).2 ?_
  intro T q hpb hq
  obtain ⟨x⟩ := hq
  have hFx : IsAlgebraicSpace B (W x).1 (W x).2 ((relocalizeRestrict (m x)).obj F) :=
    isAlgebraicSpace_relocalizeRestrict B (W x).1 U.left.1 (W x).2 U.left.2 (m x) F hF
  have hΛF := Space.isAlgebraicSpace_relocalizePresheaf B S hS U F hF
  have hΛFx := Space.isAlgebraicSpace_relocalizePresheaf B S hS (V' x)
    ((relocalizeRestrict (m x)).obj F) hFx
  have hc := OverShriek.isPullback_relocalizeRestrictMap U.hom (m x) F
  have hsq : IsPullback
      (ObjectProperty.homMk (relocalizeRestrictMap U.hom (m x) F) :
        (⟨_, hΛFx⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hΛF⟩)
      (ObjectProperty.homMk
          (relocalizeToYoneda (m x ≫ U.hom) ((relocalizeRestrict (m x)).obj F)) :
        (⟨_, hΛFx⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (V' x), isAlgebraicSpace_yoneda B S hS (V' x)⟩)
      (ObjectProperty.homMk (relocalizeToYoneda U.hom F) :
        (⟨_, hΛF⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk (yoneda.map (k' x))) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
  rw [← P.cancel_left_of_respectsIso hsq.isoPullback.hom, hsq.isoPullback_hom_snd]
  refine (Space.prop_relocalizeToYoneda_iff B S hS P (V' x) _ hFx).2 ?_
  exact hP x _ hFx (nonempty_equivalenceOver_relocalizeRestrict U.hom (m x) F y f.toFunctor hy
    f.w 𝒳.property 𝒴.property E)

end AlgebraicGeometry.Stack

end
