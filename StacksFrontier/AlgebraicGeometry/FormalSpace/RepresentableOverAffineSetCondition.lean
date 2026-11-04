module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableCancellation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine

/-!
# The set-theoretic condition for a sheaf representable over an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `Y` be an affine formal algebraic
space over `S` and let `f : X ⟶ Y` be a morphism of fppf sheaves representable by algebraic
spaces. **Stacks 0AJH** says that `X` is then a formal algebraic space over `S`, and imposes no
condition on `X` beyond that.

Being a formal algebraic space (Stacks 0AIM, Definition 87.11.1) is, in the source as in this
library, the conjunction of the set-theoretic condition of **Stacks 0AIS** and the existence of
an atlas by affine formal algebraic spaces. So the set-theoretic condition on `X` is part of
the conclusion of Stacks 0AJH, not of its hypotheses, and carrying it as a hypothesis — as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_affineFormal` does
in the binder `hXset` — proves less than the tag asserts. This file proves that condition; the
unconditional Stacks 0AJH that consumes it is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_isAffineFormal`.

## Main results

* `satisfiesSetTheoreticCondition_of_representable_over_affineFormal`:
  the set-theoretic condition of **Stacks 0AIS** holds for the source of a morphism to an affine
  formal algebraic space which is representable by algebraic spaces.

## Implementation notes

*Why the condition is available here and not for Stacks 0AJ1.* Observation (3) of Stacks 0AIS
is explicit that an atlas by affine formal algebraic spaces produces the condition only when
the index set is "not too large" and the diagonal is "not too wild", which is why Stacks 0AJ1
keeps the condition as the hypothesis `hXset` in
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`. The hypotheses of Stacks
0AJH are stronger in exactly the way that closes the gap: the target `Y`, being an *affine*
formal algebraic space, already satisfies the condition, so it supplies a *single* object `U`
of the site with `h_U ⟶ Y` a surjection of sheaves, and it has representable relative products
by Stacks 0AI8. Nothing has to be assembled out of a family, so no bound on an index set is
needed.

*The argument.* Write `W = h_U ×_Y X`. It is an algebraic space over `S` because `f` is
representable by algebraic spaces, and `W ⟶ X` is a surjection of sheaves because `h_U ⟶ Y` is
one and epimorphisms of sheaves of sets are stable under base change. An algebraic space has an
étale atlas by an *object of the site* (Definition 025Y), and that atlas is a surjection of
sheaves by Stacks 05VM, so composing gives the required surjection `a : h_V ⟶ X` from a
representable.

For the relation, no second application of the condition on `Y` is needed, because `h_V ×_X h_V`
turns out to be an algebraic space and so has an atlas of its own. The morphism `a` is
representable by algebraic spaces: the atlas `h_V ⟶ W` is representable by objects of the site,
and `W ⟶ X` is a base change of `h_U ⟶ Y`, which is representable by objects of the site since
`Y` has representable relative products. Hence `h_V ×_X h_V` is an algebraic space by Stacks
03XY, and its étale atlas is the required `R`.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf isomorphic to a universe-lifted representable presheaf is an algebraic space. -/
private theorem isAlgebraicSpaceULift_of_iso_uliftYoneda {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (T : BigFppfOver B S hS) (e : uliftYoneda.{u + 1}.obj T ≅ G) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS G :=
  Space.isAlgebraicSpaceULift_of_iso B S hS e
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)

/-- An isomorphism of presheaves on the big fppf site of `S` is representable by algebraic
spaces: its base change along a universe-lifted scheme-valued point is again an isomorphism,
so the base change is a universe-lifted representable presheaf. -/
private theorem isRepresentableByAlgebraicSpacesULift_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ⟶ G) (he : IsIso e) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS e := by
  intro T ξ
  have _ : IsIso e := he
  have _ : IsIso (pullback.fst ξ e) :=
    (IsPullback.of_hasPullback ξ e).flip.isIso_snd_of_isIso
  exact isAlgebraicSpaceULift_of_iso_uliftYoneda B S hS T (asIso (pullback.fst ξ e)).symm

/-- A morphism of presheaves on the big fppf site of `S` which is representable by objects of
the site is representable by algebraic spaces: a represented base change is a universe-lifted
representable presheaf, which is an algebraic space. -/
private theorem isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (c : F ⟶ G)
    (hc : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable c) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c := by
  intro T ξ
  obtain ⟨V, snd, fst, hpb⟩ := hc ξ
  exact isAlgebraicSpaceULift_of_iso_uliftYoneda B S hS V hpb.flip.isoPullback

/-- The sheafified Yoneda embedding of the big fppf site of `S`, followed by the forgetful
functor to presheaves, is the universe-lifted Yoneda embedding. -/
private noncomputable def sheafifiedYonedaCompSheafToPresheafIso :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
        sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅ uliftYoneda.{u + 1} :=
  haveI := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS))
      (sheafToPresheaf _ _) ≪≫
    GrothendieckTopology.uliftYonedaCompSheafToPresheaf (BigFppfOver.topology B S hS)

/-- **An algebraic space over `S` receives a surjection of fppf sheaves from an object of the
site, and that surjection is representable by objects of the site.** This is the étale scheme
atlas of Definition 025Y, read as a surjection of sheaves by Stacks 05VM; relative
representability is part of the datum, since the atlas of an algebraic space is required to be
surjective and étale after every represented base change. -/
private theorem exists_representable_epi_of_isAlgebraicSpaceULift (A : FppfSheaf B S hS)
    (hA : Space.IsAlgebraicSpaceULift.{u + 1} B S hS A.obj) :
    ∃ (V : BigFppfOver B S hS)
      (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ A),
      Epi α ∧ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS α.hom := by
  let J := BigFppfOver.topology B S hS
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let ee := sheafifiedYonedaCompSheafToPresheafIso B S hS
  obtain ⟨V, cc, hccS, _⟩ := hA.exists_atlas
  have hls : Presheaf.IsLocallySurjective J cc :=
    isLocallySurjective_of_surjective_etale_uliftYoneda B S hS cc hccS ‹_›
  refine ⟨V, ⟨(ee.app V).hom ≫ cc⟩, ?_, ?_⟩
  · rw [← Sheaf.isLocallySurjective_iff_epi]
    exact Presheaf.isLocallySurjective_comp J _ cc
  · exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (isRepresentableByAlgebraicSpacesULift_of_isIso B S hS (ee.app V).hom inferInstance)
      (isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS cc hccS.rep)

/-- **The set-theoretic condition of Stacks 0AIS for the source of a morphism to an affine
formal algebraic space representable by algebraic spaces.** This is the first conjunct of the
conclusion of **Stacks 0AJH**, discharged.

The condition on `Y` supplies one object `U` of the site with `h_U ⟶ Y` a surjection of
sheaves. The fibre product `W = h_U ×_Y X` is then an algebraic space over `S`, and `W ⟶ X` is
a surjection of sheaves, so the étale scheme atlas `h_V ⟶ W` of `W` composes to a surjection
`a : h_V ⟶ X` from a representable. That atlas is representable by objects of the site and
`W ⟶ X` is a base change of `h_U ⟶ Y`, which is representable by objects of the site because an
affine formal algebraic space has representable relative products (Stacks 0AI8); so `a` is
representable by algebraic spaces, `h_V ×_X h_V` is an algebraic space by Stacks 03XY, and the
étale scheme atlas of `h_V ×_X h_V` is the second half of the condition. -/
@[stacks 0AIS "the condition for the source of a morphism to an affine formal algebraic space \
which is representable by algebraic spaces, which is the first conjunct of the conclusion of \
Stacks 0AJH"]
theorem satisfiesSetTheoreticCondition_of_representable_over_affineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    SatisfiesSetTheoreticCondition B S hS X := by
  let J := BigFppfOver.topology B S hS
  let Fy := Sheaf.sheafifiedYoneda J
  let Gp := sheafToPresheaf J (Type (u + 1))
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let ee : Fy ⋙ Gp ≅ uliftYoneda.{u + 1} := sheafifiedYonedaCompSheafToPresheafIso B S hS
  -- A representable surjection onto `Y`, from the set-theoretic condition on `Y`.
  obtain ⟨U, -, hU, -, hUrep, -, p, hp, -⟩ := hY.1
  let eU : hU ≅ Fy.obj U := (Functor.FullyFaithful.ofFullyFaithful Gp).preimageIso
    (Classical.choice hUrep ≪≫ (Gp.mapIso ((Sheaf.sheafifiedYonedaIsoUliftYoneda' J).app U)).symm)
  let p' : Fy.obj U ⟶ Y := eU.inv ≫ p
  -- `h_U ⟶ Y` is representable by objects of the site, hence by algebraic spaces.
  -- `W = h_U ×_Y X` is an algebraic space, and `W ⟶ X` is a surjection of sheaves.
  let W := pullback p' f
  let w₂ : W ⟶ X := pullback.snd p' f
  have hw₂ : Epi w₂ := Sheaf.epi_pullback_snd p' f (inferInstanceAs (Epi (eU.inv ≫ p)))
  have h0 : IsPullback (pullback.fst p' f).hom w₂.hom p'.hom f.hom :=
    (IsPullback.of_hasPullback p' f).map Gp
  have hw₂rep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w₂.hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
      (pullback.fst p' f).hom w₂.hom p'.hom f.hom h0
      (isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable B S hS p'
        (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hY p'))
  have hWalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj := by
    let ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj := ee.inv.app U ≫ p'.hom
    have hbot : IsPullback p'.hom (ee.hom.app U) (𝟙 Y.obj) ξ :=
      IsPullback.of_vert_isIso ⟨by simp [ξ]⟩
    have hv := h0.flip.paste_vert hbot
    rw [Category.comp_id] at hv
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hv.flip.isoPullback.symm (hf U ξ)
  -- The étale scheme atlas of `W`, composed into `X`.
  obtain ⟨V, c, hc, hcrep⟩ := exists_representable_epi_of_isAlgebraicSpaceULift B S hS W hWalg
  let a : Fy.obj V ⟶ X := c ≫ w₂
  -- The relation `h_V ×_X h_V` is an algebraic space, so it too has an atlas.
  have hKalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback a a).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (((IsPullback.of_hasPullback a a).map Gp).isoIsPullback _ _
        (IsPullback.of_hasPullback a.hom a.hom)).symm
      (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS a.hom a.hom
        (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS c.hom w₂.hom hcrep hw₂rep)
        (isAlgebraicSpaceULift_of_iso_uliftYoneda B S hS V (ee.app V).symm))
  obtain ⟨R, g, hg, -⟩ :=
    exists_representable_epi_of_isAlgebraicSpaceULift B S hS (pullback a a) hKalg
  exact ⟨V, R, Fy.obj V, Fy.obj R, ⟨ee.app V⟩, ⟨ee.app R⟩, a,
    inferInstanceAs (Epi (c ≫ w₂)), g, hg⟩

end AlgebraicGeometry.FormalSpace

end
