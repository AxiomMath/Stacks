module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional

/-!
# The étale atlas criterion in an arbitrary value universe, and locality on the target

**Stacks 0BGR** says that a sheaf on the big fppf site of `S` receiving a morphism from an
algebraic space over `S` which is representable by objects of the site, surjective and étale is
itself an algebraic space over `S`. It is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional` for presheaves with
values in `Type u`, the value universe of the site. This file carries it over to the value
universe `max w u` with `w` independent of `u`, which is the generality in which a formal
algebraic space — a sheaf of `Type (u + 1)` — lives, and draws from it the two statements that
make representability by algebraic spaces an étale-local condition on the target.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale`:
  **Stacks 0BGR** for presheaves with values in `Type (max w u)`.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_comp_of_surjective_etale`:
  if `a` is representable by objects of the site, surjective and étale and the composite
  `a ≫ b` is representable by algebraic spaces, then so is `b`.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_forall_surjective_etale_cover`:
  **representability by algebraic spaces is local on the target.** A morphism of fppf sheaves
  is representable by algebraic spaces as soon as every scheme-valued point of its target
  admits a surjective étale covering by one object of the site over which the base change of
  the morphism is an algebraic space.

## Implementation notes

*Why the étale case and not Stacks 0AMP.* The source closes locality on the target with Stacks
0AMP, which asks of the covering morphism only that it be representable by algebraic spaces,
surjective, flat and locally of finite presentation. This library does not have Stacks 0AMP:
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective` proves it
from the bootstrap theorem Stacks 04S6, part (3), and
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_iff` shows the two
statements are equivalent, so nothing short of the bootstrap theorem discharges that input. The
étale case is not in that situation, because Stacks 0BGR is proved outright — but only for a
morphism representable by *objects of the site*. That is a genuine strengthening and not a
convenience: a base change of a morphism representable by algebraic spaces and étale along a
scheme-valued point is an algebraic space étale over a scheme, which need not be a scheme, so
the weaker hypothesis does not give Stacks 0BGR its atlas. The covering morphisms the statements
below are applied to — base changes of morphisms of the site — satisfy the stronger hypothesis
on the nose.

*The descent to the value universe of the site.* Both presheaves are pointwise `u`-small, so
they are universe lifts of presheaves of `Type u` and the three conditions transport along the
lift, exactly as in
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift`. For
the source this is `AlgebraicGeometry.Space.small_of_isAlgebraicSpaceULift`; for the target it
is `AlgebraicGeometry.Space.small_of_relative_surjective_etale`, which is the same argument with
the atlas replaced by the covering morphism — a section of the target lifts to the source after
a surjective étale base change, and restriction along that base change is injective on a sheaf.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0AMP](https://stacks.math.columbia.edu/tag/0AMP)
* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property of being surjective on underlying schemes, read on the big fppf site. -/
abbrev surjectiveOnSite : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

/-- The property of being étale on underlying schemes, read on the big fppf site. -/
abbrev etaleOnSite : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

/-- **Stacks 0BGR** for presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes. A sheaf `F` on the big fppf site of `S` admitting a morphism
`a : G ⟶ F` from an algebraic space `G` over `S` which is representable by objects of the site,
surjective and étale is an algebraic space over `S`.

Both presheaves are pointwise `u`-small — the source because it is an algebraic space, the
target because its sections lift along `a` after a surjective étale base change — so they are
universe lifts of presheaves of `Type u` and the statement is the one in the value universe of
the site transported along the lift. -/
@[stacks 0BGR "in an arbitrary value universe"]
theorem isAlgebraicSpaceULift_of_relative_surjective_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : IsAlgebraicSpaceULift.{w} B S hS G) (a : G ⟶ F)
    (hs : (surjectiveOnSite B S hS).relative (uliftYoneda.{w}) a)
    (he : (etaleOnSite B S hS).relative (uliftYoneda.{w}) a) :
    IsAlgebraicSpaceULift.{w} B S hS F := by
  have hGsmall := small_of_isAlgebraicSpaceULift B S hS hG
  have hFsmall := small_of_relative_surjective_etale B S hS hF a hs he
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  let F' := FunctorToTypes.shrink.{u} F
  let G' := FunctorToTypes.shrink.{u} G
  let eF : H.obj F' ≅ F := shrinkCompUliftFunctorIso F
  let eG : H.obj G' ≅ G := shrinkCompUliftFunctorIso G
  let a' : G' ⟶ F' := H.preimage (eG.hom ≫ a ≫ eF.inv)
  have hmap : H.map a' = eG.hom ≫ a ≫ eF.inv := H.map_preimage _
  have hG' : IsAlgebraicSpace B S hS G' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS G').mp
      (isAlgebraicSpaceULift_of_iso B S hS eG.symm hG)
  have hF'sheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F' := by
    have h1 : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F' ⋙ uliftFunctor.{w}) :=
      (Presheaf.isSheaf_of_iso_iff eF).mpr hF
    simpa only [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff] using h1
  have key : ∀ (P : MorphismProperty C), P.relative (uliftYoneda.{w}) a →
      P.relative yoneda a' := by
    intro P hP
    refine (relative_comp_map_iff yoneda H P a').mp ?_
    rw [hmap]
    exact MorphismProperty.RespectsIso.postcomp _ eF.inv _
      (MorphismProperty.RespectsIso.precomp _ eG.hom a hP)
  exact isAlgebraicSpaceULift_of_iso B S hS eF
    ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F').mpr
      (isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS hG' hF'sheaf a'
        (key _ hs) (key _ he)))

/-- Stacks 0BGR applied to a sheaf `P` and the base change `s` of a morphism `a` which is
representable by objects of the site, surjective and étale. -/
private theorem isAlgebraicSpaceULift_of_isPullback_of_relative_surjective_etale
    {F G P X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {a : G ⟶ F} {t : P ⟶ F}
    {r : X ⟶ G} {s : X ⟶ P}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P)
    (hX : IsAlgebraicSpaceULift.{w} B S hS X) (hpb : IsPullback r s a t)
    (hs : (surjectiveOnSite B S hS).relative (uliftYoneda.{w}) a)
    (he : (etaleOnSite B S hS).relative (uliftYoneda.{w}) a) :
    IsAlgebraicSpaceULift.{w} B S hS P := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{w} (C := BigFppfOver B S hS)) (surjectiveOnSite B S hS)
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{w} (C := BigFppfOver B S hS)) (etaleOnSite B S hS)
  exact isAlgebraicSpaceULift_of_relative_surjective_etale B S hS hP hX s
    (MorphismProperty.of_isPullback hpb hs) (MorphismProperty.of_isPullback hpb he)

/-- **Representability by algebraic spaces descends along a surjective étale morphism
representable by objects of the site.** If `a : F ⟶ G` is representable by objects of the site,
surjective and étale, `G` and `H` are sheaves and the composite `a ≫ b` is representable by
algebraic spaces, then `b : G ⟶ H` is representable by algebraic spaces.

At a scheme-valued point `ξ` of `H` the fibre product `T ×_H F` is an algebraic space, being a
base change of `a ≫ b`, and `T ×_H G` is a sheaf; the morphism between them is a base change of
`a`, so Stacks 0BGR applies.

This is the étale case of Stacks 0AMP with the hypothesis on `a` strengthened from
representability by algebraic spaces to representability by objects of the site, and it carries
no attribute for that tag: Stacks 0AMP in its own generality is equivalent to the bootstrap
theorem Stacks 04S6, part (3), which this library does not prove. -/
theorem isRepresentableByAlgebraicSpacesULift_of_comp_of_surjective_etale
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) (b : G ⟶ H)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hs : (surjectiveOnSite B S hS).relative (uliftYoneda.{w}) a)
    (he : (etaleOnSite B S hS).relative (uliftYoneda.{w}) a)
    (hcomp : IsRepresentableByAlgebraicSpacesULift.{w} B S hS (a ≫ b)) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS b := by
  intro U ξ
  have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ b) :=
    Presheaf.isSheaf_pullback _ ξ b
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U).isSheaf hG hH
  have hX : IsAlgebraicSpaceULift.{w} B S hS (pullback (pullback.snd ξ b) a) :=
    isAlgebraicSpaceULift_of_iso B S hS (pullbackLeftPullbackSndIso ξ b a).symm (hcomp U ξ)
  exact isAlgebraicSpaceULift_of_isPullback_of_relative_surjective_etale B S hS hsheaf hX
    (IsPullback.of_hasPullback (pullback.snd ξ b) a).flip hs he

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes has a
base-change stable property `P` satisfies the relative form of `P` along the universe-lifted
Yoneda embedding: the universe lift is a fully faithful functor preserving fibre products, so
the relative property is the one along the Yoneda embedding itself. -/
theorem relative_uliftYoneda_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {T' T : BigFppfOver B S hS} (q : T' ⟶ T)
    (hq : P ((BigFppfOver.toScheme B S hS).map q)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (uliftYoneda.{w}) ((uliftYoneda.{w}).map q) :=
  (relative_comp_map_iff yoneda
    ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (max w u))).obj
      uliftFunctor.{w}) _ (yoneda.map q)).mpr
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P q).2 hq)

/-- **Representability by algebraic spaces is local on the target.** A morphism `f : X ⟶ Y` of
sheaves on the big fppf site of `S` is representable by algebraic spaces as soon as every
scheme-valued point `ξ : T ⟶ Y` admits a morphism `q : T' ⟶ T` of the site which is surjective
and étale on underlying schemes and over which the base change of `f` is an algebraic space.

The base change of `f` along `ξ` is a sheaf, its base change along `q` is the algebraic space
supplied by the hypothesis, and the morphism between them is a base change of the universe
lifted Yoneda image of `q`, hence representable by objects of the site, surjective and étale;
so Stacks 0BGR applies.

An affine open covering of `T` whose disjoint union is again an object of the site supplies
such a `q`, which is the form in which Zariski locality on the target is used: representability
of `f` follows from representability after base change along the members of an affine open
covering of each scheme-valued point of the target. -/
theorem isRepresentableByAlgebraicSpacesULift_of_forall_surjective_etale_cover
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : X ⟶ Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (h : ∀ (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj T ⟶ Y),
      ∃ (T' : BigFppfOver B S hS) (q : T' ⟶ T),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        IsAlgebraicSpaceULift.{w} B S hS (pullback ((uliftYoneda.{w}).map q ≫ ξ) f)) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS f := by
  intro T ξ
  obtain ⟨T', q, hqs, hqe, halg⟩ := h T ξ
  have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ f) :=
    Presheaf.isSheaf_pullback _ ξ f
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS T).isSheaf hX hY
  have halg' : IsAlgebraicSpaceULift.{w} B S hS
      (pullback ((uliftYoneda.{w}).map q) (pullback.fst ξ f)) :=
    isAlgebraicSpaceULift_of_iso B S hS
      (pullbackRightPullbackFstIso ξ f ((uliftYoneda.{w}).map q)).symm halg
  exact isAlgebraicSpaceULift_of_isPullback_of_relative_surjective_etale B S hS hsheaf halg'
    (IsPullback.of_hasPullback _ _) (relative_uliftYoneda_map B S hS _ q hqs)
    (relative_uliftYoneda_map B S hS _ q hqe)

end AlgebraicGeometry.Space

end
