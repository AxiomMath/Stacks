module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# The set-theoretic condition along morphisms representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The set-theoretic condition of
**Stacks 0AIS** asks of an fppf sheaf `X` over `S` for an object `U` of the site with a
surjection `h_U ⟶ X` and an object `R` with a surjection `h_R ⟶ h_U ×_X h_U`. This file shows
that it passes from the target to the source of a morphism `f : X ⟶ Y` representable by
algebraic spaces, provided morphisms from objects of the site to `Y` are representable (as they
are when `Y` is a formal algebraic space, by the representability clause of Stacks 0AIP).

## Main results

* `satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift`: the condition
  passes to the source of a morphism representable by algebraic spaces whose target satisfies it
  and has representable relative products. The variant with the further suffix
  `_of_isFormalAlgebraicSpace` states the same with a formal algebraic space as target.

## Implementation notes

Let `h_U ⟶ Y` be the surjection of the condition on `Y`. Its base change `P = h_U ×_Y X` is an
algebraic space, `f` being representable by algebraic spaces, so it receives a surjection
`h_{U'} ⟶ P` from its étale scheme atlas, an object of the site; that map is representable,
the diagonal of an algebraic space being representable. The projection `P ⟶ X` is a surjection,
as a base change of one, and representable, as a base change of `h_U ⟶ Y`. So the composite
`h_{U'} ⟶ X` is a representable surjection, and its kernel pair is itself represented by an
object of the site; the second surjection of the condition may be taken to be an isomorphism.
No size bound on an index is involved.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Relative representability along the sheafified Yoneda embedding of the big fppf site of `S`
gives relative representability along the universe-lifted Yoneda embedding into sheaves. -/
theorem relativelyRepresentable_sheafUliftYoneda_of_sheafifiedYoneda
    {X Y : FppfSheaf B S hS} (p : X ⟶ Y)
    (hp : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable p) :
    (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.relativelyRepresentable p := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)
  intro a g
  obtain ⟨b, snd, fst, hpb⟩ := hp ((eG.app a).hom ≫ g)
  refine ⟨b, snd, (eG.app b).inv ≫ fst, ?_⟩
  refine hpb.of_iso (eG.app b) (Iso.refl _) (eG.app a) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.app_hom, Iso.app_inv, Iso.hom_inv_id_app_assoc]
    exact Category.comp_id fst
  · simp only [Iso.app_hom]
    exact eG.hom.naturality snd
  · simp
  · simp

/-- **The set-theoretic condition of Stacks 0AIS passes to the source of a morphism
representable by algebraic spaces.** Let `f : X ⟶ Y` be a morphism of fppf sheaves over `S`
which is representable by algebraic spaces, where `Y` satisfies the set-theoretic condition and
every morphism to `Y` from an object of the site is representable. Then `X` satisfies the
set-theoretic condition. -/
theorem satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hYset : SatisfiesSetTheoreticCondition B S hS Y)
    (hYrep : HasRepresentableRelativeProducts B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X := by
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let L := J.uliftYoneda.{u + 1}
  let F := sheafToPresheaf J (Type (u + 1))
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  obtain ⟨U, -, hU, -, hUrep, -, p, hp, -⟩ := hYset
  let eU : hU ≅ G.obj U := (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
    (Classical.choice hUrep ≪≫ (F.mapIso (eG.app U)).symm)
  let p' : G.obj U ⟶ Y := eU.inv ≫ p
  -- the base change `π : h_U ×_Y X ⟶ X` of `p'` along `f`
  let π := pullback.snd p' f
  have hπ : Epi π := Sheaf.epi_pullback_snd p' f (epi_comp _ _)
  have hπrep : L.relativelyRepresentable π :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p' f)
      (relativelyRepresentable_sheafUliftYoneda_of_sheafifiedYoneda B S hS p' (hYrep p'))
  -- `h_U ×_Y X` is an algebraic space
  let ξ : uliftYoneda.{u + 1}.obj U ⟶ Y.obj := (F.mapIso (eG.app U)).inv ≫ p'.hom
  have hpre : IsPullback (F.map (pullback.fst p' f)) (F.map π) p'.hom f.hom :=
    (IsPullback.of_hasPullback p' f).map F
  have hpre' : IsPullback (F.map (pullback.fst p' f) ≫ (F.mapIso (eG.app U)).hom) (F.map π)
      ξ f.hom := by
    refine hpre.of_iso (Iso.refl _) (F.mapIso (eG.app U)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp]
    · simp
    · rw [Iso.refl_hom, Category.comp_id]
      exact (Iso.hom_inv_id_assoc (F.mapIso (eG.app U)) p'.hom).symm
    · simp
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback p' f).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (hpre'.isoIsPullback _ _ (IsPullback.of_hasPullback ξ f.hom)).symm (hf U ξ)
  -- its atlas, a representable surjection from an object of the site
  obtain ⟨R, α, hα⟩ := exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS _ hPalg
  have hαrep : L.relativelyRepresentable α :=
    (relativelyRepresentable_uliftYoneda_iff B S hS α).2
      (hPalg.diagonal_representable.of_diag (F.map α))
  -- the composite is a representable surjection; its kernel pair is represented
  obtain ⟨R', snd, fst, hpb⟩ := MorphismProperty.comp_mem _ _ _ hαrep hπrep (α ≫ π)
  exact ⟨R, R', L.obj R, L.obj R', ⟨J.uliftYonedaCompSheafToPresheaf.app R⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.app R'⟩, α ≫ π, epi_comp _ _, hpb.isoPullback.hom,
    inferInstance⟩

/-- **The set-theoretic condition of Stacks 0AIS for a source representable over a formal
algebraic space.** If `f : X ⟶ Y` is a morphism of fppf sheaves over `S` representable by
algebraic spaces and `Y` is a formal algebraic space, then `X` satisfies the set-theoretic
condition. -/
theorem satisfiesSetTheoreticCondition_of_isRepresentableByAlgSpacesULift_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X :=
  satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift B S hS f hf hY.1
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)

end AlgebraicGeometry.FormalSpace

end
