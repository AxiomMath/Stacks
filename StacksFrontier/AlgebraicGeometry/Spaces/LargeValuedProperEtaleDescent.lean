module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget

/-!
# Properness over a scheme of the site descends along a surjective étale morphism

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0422** says that properness of
morphisms of algebraic spaces over `S` is local on the base for the fppf topology; in the value
universe of the site that is `AlgebraicGeometry.Space.proper_isLocalAtTarget_fppf`. This file
carries the one-member case of that statement — the base being covered by a single surjective
étale morphism of the site — over to the value universe `Type (u + 1)` in which a formal
algebraic space lives, where properness is `AlgebraicGeometry.Space.IsProperULift`.

The transport is `AlgebraicGeometry.Space.isProperULift_whiskerRight_iff`: an algebraic space
over `S` with values in `Type (u + 1)` is the universe lift of a presheaf in the value universe
of the site, properness of the lift is properness of that presheaf, and over there Stacks 0422
applies.

## Main results

* `AlgebraicGeometry.Space.isProperULift_of_isPullback_uliftYoneda_map`: properness of a
  morphism of large-valued algebraic spaces whose target is a scheme of the site descends along
  a surjective étale morphism of the site.

## Implementation notes

The covering morphism is taken to be a morphism of the *site*, not of algebraic spaces. That is
what makes the fppf covering family available: a surjective étale morphism of the site induces a
one-member covering family of the fppf precoverage of Stacks 03YH by
`AlgebraicGeometry.Space.ofArrows_atlas_mem_fppf_precoverage`, through
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`, which is the form in which a property
local at the target is tested on a scheme atlas. It is also the hypothesis
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale` — Stacks 0BGR —
needs, so the same covering morphism serves to see that the source is an algebraic space.

The cartesian square is a hypothesis rather than the canonical fibre product, so that a caller
who has exhibited the base change in some other shape need not transport along a comparison
isomorphism; inside, the square is compared with the canonical fibre product by
`CategoryTheory.IsPullback.isoIsPullback`, and properness is carried across that isomorphism by
`AlgebraicGeometry.Space.isProperULift_precomp`. For the same reason no hypothesis is placed on
the source of the base change: it is isomorphic to a fibre product of algebraic spaces, hence an
algebraic space.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0422 for a family of morphisms of the site, in the value universe `Type (u + 1)`.**
Let `p : F ⟶ U` be a morphism of presheaves on the big fppf site of `S` with values in
`Type (u + 1)` whose source is an algebraic space over `S` and whose target is the
universe-lifted representable sheaf of an object `U` of the site, and let `{qᵢ : Vᵢ ⟶ U}` be a
family of morphisms of the site whose Yoneda images form an fppf covering family of `U` in the
sense of **Stacks 03Y8**. If some base change of `p` along each `qᵢ` is proper, then `p` is
proper.

The source and the base changes are algebraic spaces, hence universe lifts of presheaves in the
value universe of the site; there properness of a lift is properness of the presheaf
(`AlgebraicGeometry.Space.isProperULift_whiskerRight_iff`) and the covering family generates a
covering family of the fpqc precoverage of Stacks 03YH, at which properness is local on the
base by **Stacks 0422**. -/
@[stacks 0422 "for a family of morphisms of the site, in the value universe of a formal \
algebraic space", sga "1 VIII 4.8" "partial"]
theorem isProperULift_of_isPullback_uliftYoneda_family
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U : BigFppfOver B S hS}
    {p : F ⟶ (uliftYoneda.{u + 1}).obj U} {Idx : Type (u + 1)}
    {V : Idx → BigFppfOver B S hS} {q : ∀ i, V i ⟶ U}
    {F' : Idx → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))}
    {p' : ∀ i, F' i ⟶ (uliftYoneda.{u + 1}).obj (V i)} {k : ∀ i, F' i ⟶ F}
    (sq : ∀ i, IsPullback (k i) (p' i) p ((uliftYoneda.{u + 1}).map (q i)))
    (hF : IsAlgebraicSpaceULift.{u + 1} B S hS F)
    (hcov : IsFppfCovering B S hS (fun i => yoneda.obj (V i)) (fun i => yoneda.map (q i)))
    (hp' : ∀ i, IsProperULift.{u + 1} B S hS (p' i)) :
    IsProperULift.{u + 1} B S hS p := by
  classical
  have hLT : (properProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, u + 1} .fpqc B S hS) := proper_isLocalAtTarget_fpqc B S hS
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  -- the source is the universe lift of a presheaf in the value universe of the site
  obtain ⟨F₀, ⟨e⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : F₀ ⟶ yoneda.obj U,
      Functor.whiskerRight p₀ uliftFunctor.{u + 1} = e.hom ≫ p := H.map_surjective _
  have hF₀L : IsAlgebraicSpaceULift.{u + 1} B S hS (F₀ ⋙ uliftFunctor.{u + 1}) :=
    isAlgebraicSpaceULift_of_iso B S hS e.symm hF
  have hF₀ : IsAlgebraicSpace B S hS F₀ :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F₀).mp hF₀L
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hV (i : Idx) : IsAlgebraicSpace B S hS (yoneda.obj (V i)) :=
    isAlgebraicSpace_yoneda B S hS (V i)
  have hsq₀ (i : Idx) :
      IsPullback (pullback.fst (yoneda.map (q i)) p₀) (pullback.snd (yoneda.map (q i)) p₀)
        (yoneda.map (q i)) p₀ := IsPullback.of_hasPullback _ _
  have hP₀ (i : Idx) : IsAlgebraicSpace B S hS (pullback (yoneda.map (q i)) p₀) :=
    isAlgebraicSpace_pullback B S hS (yoneda.map (q i)) p₀ (hV i) hF₀ hU
  -- transport each hypothesis to the canonical fibre product in the value universe of the site
  have hiso : IsPullback e.inv p (e.hom ≫ p) (𝟙 ((uliftYoneda.{u + 1}).obj U)) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hmem (i : Idx) : IsProper B S hS (pullback.fst (yoneda.map (q i)) p₀) := by
    have hP₀L : IsAlgebraicSpaceULift.{u + 1} B S hS
        (pullback (yoneda.map (q i)) p₀ ⋙ uliftFunctor.{u + 1}) :=
      (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr (hP₀ i)
    have sq2 : IsPullback (k i ≫ e.inv) (p' i)
        (Functor.whiskerRight p₀ uliftFunctor.{u + 1})
        ((uliftYoneda.{u + 1}).map (q i)) := by
      rw [hp₀]
      have hpaste := (sq i).paste_horiz hiso
      rw [Category.comp_id] at hpaste
      exact hpaste
    have h0 : IsPullback
        (Functor.whiskerRight (pullback.snd (yoneda.map (q i)) p₀) uliftFunctor.{u + 1})
        (Functor.whiskerRight (pullback.fst (yoneda.map (q i)) p₀) uliftFunctor.{u + 1})
        (Functor.whiskerRight p₀ uliftFunctor.{u + 1})
        (Functor.whiskerRight (yoneda.map (q i)) uliftFunctor.{u + 1}) :=
      (isPullback_whiskerRight.{u + 1} B S hS (hsq₀ i)).flip
    have hF'L : IsAlgebraicSpaceULift.{u + 1} B S hS (F' i) :=
      isAlgebraicSpaceULift_of_iso B S hS (sq2.isoIsPullback _ _ h0).symm hP₀L
    refine (isProperULift_whiskerRight_iff.{u + 1} B S hS _).mp ?_
    have h1 : IsProperULift.{u + 1} B S hS ((sq2.isoIsPullback _ _ h0).inv ≫ p' i) :=
      isProperULift_precomp B S hS (sq2.isoIsPullback _ _ h0).symm (p' i) hP₀L hF'L
        (isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (V i)) (hp' i)
    rw [sq2.isoIsPullback_inv_snd _ _ h0] at h1
    exact h1
  -- descend along the covering family, properness being local on the base
  set Y : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hU⟩ with hY
  set X : AlgebraicSpaces B S hS := ⟨F₀, hF₀⟩ with hX
  set f₀ : X ⟶ Y := ObjectProperty.homMk p₀ with hf₀
  set Vi : Idx → AlgebraicSpaces B S hS := fun i => ⟨yoneda.obj (V i), hV i⟩ with hVi
  set g : ∀ i, Vi i ⟶ Y := fun i => ObjectProperty.homMk (yoneda.map (q i)) with hg
  have hR : Presieve.ofArrows Vi g ∈
      (Topology.precoverage.{u, u + 1} .fpqc B S hS).coverings Y :=
    ⟨Idx, Vi, g, rfl, Y.property, (fun i => (Vi i).property),
      isFpqcCovering_of_isFppfCovering B S hS _ _ hcov⟩
  have hPf : properProperty B S hS f₀ := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR ?_
    intro A a _ ha
    obtain ⟨i⟩ := ha
    have sqA : IsPullback
        (ObjectProperty.homMk (pullback.snd (yoneda.map (q i)) p₀) :
          (⟨pullback (yoneda.map (q i)) p₀, hP₀ i⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (ObjectProperty.homMk (pullback.fst (yoneda.map (q i)) p₀) :
          (⟨pullback (yoneda.map (q i)) p₀, hP₀ i⟩ : AlgebraicSpaces B S hS) ⟶ Vi i)
        f₀ (g i) :=
      IsPullback.of_map_of_faithful
        (ObjectProperty.ι
          (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS T))
        (hsq₀ i).flip
    rw [← sqA.isoPullback_inv_snd]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr (hmem i)
  have hp₀proper : IsProper B S hS p₀ := hPf
  -- and lift the conclusion back
  have h1 : IsProperULift.{u + 1} B S hS (Functor.whiskerRight p₀ uliftFunctor.{u + 1}) :=
    (isProperULift_whiskerRight_iff.{u + 1} B S hS p₀).mpr hp₀proper
  rw [hp₀] at h1
  have h2 : IsProperULift.{u + 1} B S hS (e.symm.hom ≫ e.hom ≫ p) :=
    isProperULift_precomp B S hS e.symm (e.hom ≫ p) hF hF₀L
      (isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U) h1
  rwa [Iso.symm_hom, Iso.inv_hom_id_assoc] at h2

/-- **Stacks 0422 for a single surjective étale morphism of the site, in the value universe
`Type (u + 1)`.** Let `p : F ⟶ U` be a morphism of presheaves on the big fppf site of `S` with
values in `Type (u + 1)` whose source is an algebraic space over `S` and whose target is the
universe-lifted representable sheaf of an object `U` of the site, and let `q : U' ⟶ U` be a
morphism of the site which is surjective and étale on underlying schemes. If some base change
of `p` along `q` is proper, then `p` is proper.

The one-member family consisting of the Yoneda image of `q` is an fppf covering family of its
target by `AlgebraicGeometry.Space.isFppfCovering_atlas`, so this is the family statement at
that family. -/
@[stacks 0422 "for one surjective étale morphism of the site, in the value universe of a formal \
algebraic space"]
theorem isProperULift_of_isPullback_uliftYoneda_map
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U U' : BigFppfOver B S hS}
    {p : F ⟶ (uliftYoneda.{u + 1}).obj U} {p' : F' ⟶ (uliftYoneda.{u + 1}).obj U'}
    {k : F' ⟶ F} (q : U' ⟶ U)
    (sq : IsPullback k p' p ((uliftYoneda.{u + 1}).map q))
    (hF : IsAlgebraicSpaceULift.{u + 1} B S hS F)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (hp' : IsProperULift.{u + 1} B S hS p') :
    IsProperULift.{u + 1} B S hS p :=
  isProperULift_of_isPullback_uliftYoneda_family B S hS
    (V := fun _ : PUnit.{u + 2} => U') (q := fun _ => q) (F' := fun _ => F')
    (p' := fun _ => p') (k := fun _ => k) (fun _ => sq) hF
    (isFppfCovering_atlas.{u, u + 1} B S hS (isAlgebraicSpace_yoneda B S hS U)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe))
    (fun _ => hp')

end AlgebraicGeometry.Space

end
