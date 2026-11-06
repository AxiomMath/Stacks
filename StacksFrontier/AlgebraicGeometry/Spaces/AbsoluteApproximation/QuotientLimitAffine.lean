module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientSystem

/-!
# The limit of a system of étale quotients is affine over every stage

Let `E` be an inverse system of étale equivalence relations `(V_j, R_j)` on objects of the big
fppf site with cartesian source squares and affine transition morphisms `V_i ⟶ V_j`
(`AlgebraicGeometry.Space.EtaleRelationSystem`), and let `V = lim V_j` be a limit in schemes
lying in the site. If the presheaf limit `lim_j V_j / R_j` of the quotient system is an algebraic
space, then each projection `lim_j V_j / R_j ⟶ V_i / R_i` is an affine morphism.

This is the statement, used in the proof of Stacks 07SU and in every application of a
Noetherian approximation built there, that the morphisms `X ⟶ X_i` from the limit to the stages
are affine (Stacks 07SF, part (1), for the systems of the proof of Stacks 07SU).

## Main results

* `AlgebraicGeometry.Space.EtaleRelationSystem.isAffineHom_limit_π`: the projections from the
  limit of the quotient system are affine.
* `AlgebraicGeometry.Space.EtaleRelationSystem.exists_iso_limit_quotient_isAffineHom`: the
  same for an algebraic space presented by the limit of the objects with kernel pair the limit of
  the relations.

## Implementation notes

The base change of the projection `lim_j V_j / R_j ⟶ V_i / R_i` along the surjective étale
quotient map `V_i ⟶ V_i / R_i` is the projection `V ⟶ V_i`
(`AlgebraicGeometry.Space.EtaleRelationSystem.isPullback_limitToQuotient`), which is an affine
morphism of schemes because the transition morphisms are affine
(`AlgebraicGeometry.isAffineHom_π_app`). Affineness of a morphism of algebraic spaces is étale
local on the target (Stacks 03WG), which gives the claim.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_QuotientLimitAffine :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_QuotientLimitAffine
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace EtaleRelationSystem

variable {J : Type u} [Category.{u} J] [IsCofiltered J] (E : EtaleRelationSystem B S hS J)

/-- **The projections from the limit of a system of étale quotients are affine.** For an
inverse system of étale equivalence relations with affine transition morphisms on the objects,
whose objects have a limit `V` in schemes lying in the site, each projection from the presheaf
limit of the quotients to a stage is an affine morphism, provided that limit is an algebraic
space. -/
theorem isAffineHom_limit_π
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (hL : IsAlgebraicSpace B S hS (limit E.quotient)) (i : J) :
    IsAffineHom B S hS (limit.π E.quotient i) := by
  have : IsConnected J := IsCofiltered.isConnected J
  have hV' : IsLimit cV := BigFppfOver.isLimit_of_isLimit_toScheme B S hS hV
  have sq := E.isPullback_limitToQuotient cV hV' i
  have hπ : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (cV.π.app i)) := by
    have : ∀ {i j : J} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
        ((E.obj ⋙ BigFppfOver.toScheme B S hS).map g) := fun g => hobj g
    exact AlgebraicGeometry.isAffineHom_π_app (E.obj ⋙ BigFppfOver.toScheme B S hS) _ hV i
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (limit.π E.quotient i) hL
    (E.isAlgebraicSpace_quotient_obj i)).out 4 2).mp ?_
  refine ⟨E.obj.obj i, E.toQuotient.app i,
      isSurjective_of_presheafSurjective B S hS _
        (quotientMap_surjective_unconditional B S hS (E.s.app i) (E.t.app i)),
      isEtale_of_presheaf_etale B S hS
        (quotientMap_etale_unconditional B S hS (E.s.app i) (E.t.app i)), ?_⟩
  refine IsAffineHom.of_isPullback (f := yoneda.map (cV.π.app i)) (g := 𝟙 _)
    (k := sq.isoPullback.inv) ?_ (isAffineHom_yoneda_map_of_isAffineHom _ hπ)
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩

/-- **The projections from a sheaf presented by a limit of étale relations are affine.** If an
algebraic space `X` receives a surjective étale morphism from the limit `V` of the objects whose
kernel pair is the limit `R` of the relations, then `X` is the limit of the quotient system
(`AlgebraicGeometry.Space.EtaleRelationSystem.exists_iso_limit_quotient`) and each of the
resulting projections `X ⟶ V_i / R_i` is affine. -/
theorem exists_iso_limit_quotient_isAffineHom
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (cR : Cone E.rel) (hR : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cR))
    (sL tL : cR.pt ⟶ cV.pt) (hs : ∀ j, sL ≫ cV.π.app j = cR.π.app j ≫ E.s.app j)
    (ht : ∀ j, tL ≫ cV.π.app j = cR.π.app j ≫ E.t.app j)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : yoneda.obj cV.pt ⟶ X) (hf : IsPullback (yoneda.map tL) (yoneda.map sL) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ e : X ≅ limit E.quotient, f ≫ e.hom = E.limitToQuotient cV ∧
      ∀ i, IsAffineHom B S hS (e.hom ≫ limit.π E.quotient i) := by
  have : IsConnected J := IsCofiltered.isConnected J
  have hV' : IsLimit cV := BigFppfOver.isLimit_of_isLimit_toScheme B S hS hV
  have hR' : IsLimit cR := BigFppfOver.isLimit_of_isLimit_toScheme B S hS hR
  obtain ⟨e, he⟩ := E.exists_iso_limit_quotient cV hV' cR hR' sL tL hs ht hX.isSheaf f hf
    hsurj hetale
  exact ⟨e, he, fun i => isAffineHom_iso_comp e.hom
    (E.isAffineHom_limit_π hobj cV hV (hX.of_iso e) i)⟩

end EtaleRelationSystem

end AlgebraicGeometry.Space

end
