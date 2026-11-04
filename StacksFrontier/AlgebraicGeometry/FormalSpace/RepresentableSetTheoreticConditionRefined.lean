module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSetTheoreticCondition
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas

/-!
# The set-theoretic condition along morphisms representable by algebraic spaces, refined

Let `S` be a scheme contained in a big fppf site `B` and `f : X ⟶ Y` a morphism of fppf sheaves
over `S` which is representable by algebraic spaces. The set-theoretic condition of
**Stacks 0AIS** asks for an object `U` of the site with a surjection `h_U ⟶ Y` and an object `R`
with a surjection `h_R ⟶ h_U ×_Y h_U`. This file shows that the condition passes from `Y` to `X`
with no further hypothesis on `Y`:
`satisfiesSetTheoreticCondition_of_isRepresentableByAlgebraicSpacesULift`
asks in addition that every morphism to `Y` from an object of the site be representable, which
is not available for the target of the charts in the proof of **Stacks 0AIU** before that
target is known to be a formal algebraic space.

## Main results

* `satisfiesSetTheoreticCondition_source_of_isRepresentableByAlgebraicSpacesULift`: the
  set-theoretic condition passes to the source of a morphism representable by algebraic spaces.

## Implementation notes

Let `p : h_U ⟶ Y` and `q : h_R ⟶ h_U ×_Y h_U` be the surjections of the condition on `Y`. The
base change `P = h_U ×_Y X` is an algebraic space, so it receives a surjection `α : h_{U'} ⟶ P`
out of an object of the site, and `α` is representable, the diagonal of an algebraic space
being representable. The composite `a : h_{U'} ⟶ P ⟶ X` is a surjection. Its kernel pair is
`h_{U'} ×_P (P ×_X h_{U'})`, and `P ×_X h_{U'} = h_U ×_Y h_{U'}` is the base change of
`h_U ×_Y h_U` along `h_{U'} ⟶ h_U`; so the base change `h_{R ×_U U'}` of `q` surjects onto it,
and the base change of that surjection along `α`, represented because `α` is, surjects onto the
kernel pair. No relative product over `Y` other than those of the condition is used.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The set-theoretic condition of Stacks 0AIS passes to the source of a morphism
representable by algebraic spaces.** Let `f : X ⟶ Y` be a morphism of fppf sheaves over `S`
which is representable by algebraic spaces. If `Y` satisfies the set-theoretic condition, so
does `X`. -/
theorem satisfiesSetTheoreticCondition_source_of_isRepresentableByAlgebraicSpacesULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hYset : SatisfiesSetTheoreticCondition B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let L := J.uliftYoneda.{u + 1}
  let F := sheafToPresheaf J (Type (u + 1))
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let gl := J.uliftYonedaCompSheafToPresheaf.{u + 1}
  -- a base change of an epimorphism of sheaves is an epimorphism
  have epi_of_isPullback : ∀ {P' X' Y' Z' : FppfSheaf B S hS} {f' : P' ⟶ X'} {g' : P' ⟶ Y'}
      {g : X' ⟶ Z'} {f₀ : Y' ⟶ Z'}, IsPullback f' g' g f₀ → Epi g → Epi g' := by
    intro P' X' Y' Z' f' g' g f₀ sq hg
    have : Epi (pullback.snd g f₀) := Sheaf.epi_pullback_snd g f₀ hg
    have he : sq.isoPullback.hom ≫ pullback.snd g f₀ = g' := sq.isoPullback_hom_snd
    rw [← he]
    infer_instance
  obtain ⟨U, R, hU, hR, ⟨eU⟩, ⟨eR⟩, p, hp, q, hq⟩ := hYset
  let eU' : hU ≅ L.obj U :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso (eU ≪≫ (gl.app U).symm)
  let eR' : hR ≅ L.obj R :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso (eR ≪≫ (gl.app R).symm)
  let p' : L.obj U ⟶ Y := eU'.inv ≫ p
  have hp' : Epi p' := by
    dsimp only [p']
    infer_instance
  let q' : L.obj R ⟶ pullback p' p' :=
    eR'.inv ≫ q ≫ pullback.map p p p' p' eU'.hom eU'.hom (𝟙 Y)
      (by simp [p']) (by simp [p'])
  have hq' : Epi q' := by
    dsimp only [q']
    infer_instance
  -- the base change `P = h_U ×_Y X` is an algebraic space
  let π := pullback.snd p' f
  have hπ : Epi π := Sheaf.epi_pullback_snd p' f hp'
  let ξ : uliftYoneda.{u + 1}.obj U ⟶ Y.obj := (gl.app U).inv ≫ p'.hom
  have hpre : IsPullback (F.map (pullback.fst p' f)) (F.map π) p'.hom f.hom :=
    (IsPullback.of_hasPullback p' f).map F
  have hpre' : IsPullback (F.map (pullback.fst p' f) ≫ (gl.app U).hom) (F.map π) ξ f.hom := by
    refine hpre.of_iso (Iso.refl _) (gl.app U) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp]
    · simp
    · rw [Iso.refl_hom, Category.comp_id]
      exact (Iso.hom_inv_id_assoc (gl.app U) p'.hom).symm
    · simp
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback p' f).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (hpre'.isoIsPullback _ _ (IsPullback.of_hasPullback ξ f.hom)).symm (hf U ξ)
  -- its atlas `α`, a representable surjection out of an object of the site
  obtain ⟨U', α, hα⟩ := exists_epi_uliftYoneda_of_isAlgebraicSpaceULift B S hS _ hPalg
  have hαrep : L.relativelyRepresentable α :=
    (relativelyRepresentable_uliftYoneda_iff B S hS α).2
      (hPalg.diagonal_representable.of_diag (F.map α))
  let a : L.obj U' ⟶ X := α ≫ π
  let s : L.obj U' ⟶ L.obj U := α ≫ pullback.fst p' f
  have has : a ≫ f = s ≫ p' := by
    simp only [a, s, π, Category.assoc, pullback.condition]
  -- `P ×_X h_{U'}` is the base change of `h_U ×_Y h_U` along `s`
  let sqP := IsPullback.of_hasPullback p' f
  let sqPP := IsPullback.of_hasPullback p' p'
  let sqA := IsPullback.of_hasPullback π a
  have hout : IsPullback (pullback.fst π a ≫ pullback.fst p' f) (pullback.snd π a) p' (s ≫ p') := by
    rw [← has]
    exact sqA.paste_horiz sqP
  let w : pullback π a ⟶ pullback p' p' :=
    pullback.lift (pullback.fst π a ≫ pullback.fst p' f) (pullback.snd π a ≫ s) (by
      simpa only [Category.assoc] using hout.w)
  have hw : IsPullback w (pullback.snd π a) (pullback.snd p' p') s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) sqPP
    simpa only [w, pullback.lift_fst] using hout
  -- the representable base change `h_{R₁}` of `q` along `s`, surjecting onto `P ×_X h_{U'}`
  obtain ⟨g, hg⟩ := L.map_surjective (q' ≫ pullback.snd p' p')
  obtain ⟨R₁, snd₁, fst₁, sq₁⟩ := Functor.relativelyRepresentable.map L g s
  rw [hg] at sq₁
  have h1 : fst₁ ≫ q' ≫ pullback.snd p' p' = L.map snd₁ ≫ s := by
    simpa only [Category.assoc] using sq₁.w
  let l₁ : L.obj R₁ ⟶ pullback p' f :=
    sqP.lift (fst₁ ≫ q' ≫ pullback.fst p' p') (L.map snd₁ ≫ a) (by
      simp only [Category.assoc, pullback.condition (f := p') (g := p')]
      rw [reassoc_of% h1, has])
  let e₁ : L.obj R₁ ⟶ pullback π a := pullback.lift l₁ (L.map snd₁) (sqP.lift_snd _ _ _)
  have he₁ : IsPullback fst₁ e₁ q' w := by
    refine IsPullback.of_bot ?_ ?_ hw
    · simpa only [e₁, pullback.lift_snd] using sq₁
    · apply pullback.hom_ext
      · simp only [e₁, w, l₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          IsPullback.lift_fst]
      · simp only [e₁, w, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, h1]
  have he₁epi : Epi e₁ := epi_of_isPullback he₁ hq'
  -- the kernel pair of `a` is `h_{U'} ×_P (P ×_X h_{U'})`
  let k : pullback a a ⟶ pullback π a :=
    pullback.lift (pullback.snd a a ≫ α) (pullback.fst a a) (by
      rw [Category.assoc]
      exact pullback.condition.symm)
  have hK : IsPullback k (pullback.snd a a) (pullback.fst π a) α := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) sqA.flip
    have hks : k ≫ pullback.snd π a = pullback.fst a a := pullback.lift_snd _ _ _
    rw [hks]
    exact IsPullback.of_hasPullback a a
  obtain ⟨R'', snd'', fst'', sq''⟩ := hαrep (e₁ ≫ pullback.fst π a)
  let g'' : L.obj R'' ⟶ pullback a a := hK.lift (L.map snd'' ≫ e₁) fst'' (by
    rw [Category.assoc]
    exact sq''.w.symm)
  have hg'' : IsPullback (L.map snd'') g'' e₁ k := by
    refine IsPullback.of_bot ?_ (hK.lift_fst _ _ _).symm hK
    have hgs : g'' ≫ pullback.snd a a = fst'' := hK.lift_snd _ _ _
    rw [hgs]
    exact sq''.flip
  have hg''epi : Epi g'' := epi_of_isPullback hg'' he₁epi
  have haepi : Epi a := by
    dsimp only [a]
    infer_instance
  exact ⟨U', R'', L.obj U', L.obj R'', ⟨gl.app U'⟩, ⟨gl.app R''⟩, a, haepi, g'', hg''epi⟩

end AlgebraicGeometry.FormalSpace

end
