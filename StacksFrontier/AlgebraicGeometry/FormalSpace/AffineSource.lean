module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts

/-!
# Affine source of a representable affine morphism (Stacks 0AKP, part (1))

Let `S` be a scheme in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf sheaves on
the big fppf site of `S` which is representable and affine. If `Y` is an affine formal algebraic
space over `S` then so is `X`. This is **Stacks 0AKP part (1)**.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_relative_isAffineHom`: the
  set-theoretic condition of **Stacks 0AIS** passes to the source of a representable affine
  morphism.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_relative_isAffineHom`:
  **Stacks 0AKP part (1)**.

## Implementation notes

Being an affine formal algebraic space is the conjunction of the set-theoretic condition of
Stacks 0AIS and the existence of a directed presentation by affine schemes with thickening
transition morphisms, and the two halves are proved separately. The presentation half is
`AlgebraicGeometry.FormalSpace.exists_affine_pullback_presentation` together with
`AlgebraicGeometry.FormalSpace.isThickening_of_cartesian_presentation`, which pull a
presentation of `Y` back along `f`.

The set-theoretic half is the first result above and is where the work is. The condition on `Y`
supplies a representable `h_U` surjecting onto `Y` and a representable `h_R` surjecting onto the
kernel pair of that surjection; what has to be produced is the same datum for `X`. Over the
subcanonical big fppf site (`AlgebraicGeometry.bigFppfOver_subcanonical`) a sheaf whose
underlying presheaf is isomorphic to a universe-lifted Yoneda presheaf is isomorphic, as a
sheaf, to a sheafified representable: that is
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'` together with full faithfulness of
`CategoryTheory.sheafToPresheaf`. So `h_U` and `h_R` may be replaced by sheafified
representables, and then representability of `f` supplies represented pullbacks `T = U ×_Y X`
and `V = R ×_Y X`.

The surjection onto `X` is the projection `T ⟶ X`, an epimorphism because epimorphisms of
sheaves of sets are stable under base change (`Sheaf.epi_pullback_snd`). For the kernel pair of
that projection, the square expressing `V` as the base change of `X` along `R ⟶ Y` is shown to
be cartesian over the comparison morphism `R ⟶ U ×_Y U`, which exhibits `V ⟶ T ×_X T` as a base
change of the surjection `h_R ⟶ U ×_Y U` and hence as an epimorphism by the same lemma. Only
the set-theoretic condition on `Y` is used, not the full affine formal algebraic space
structure, so the first result is stated at that weaker hypothesis.

## References

* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-- Let `T = X ×_Y U` be cartesian and let `V = X ×_Y R` be the base change of `f` along
`q ≫ pullback.fst p p ≫ p` for some `q : R ⟶ U ×_Y U`. Then `V ⟶ R` is the base change of `q`
along the induced morphism `T ×_X T ⟶ U ×_Y U`. -/
private theorem exists_isPullback_pullbackMap {C : Type*} [Category C]
    {T X U Y R V : C} {a : T ⟶ X} {t : T ⟶ U} {f : X ⟶ Y} {p : U ⟶ Y}
    (hpb : IsPullback a t f p) [HasPullback a a] [HasPullback p p] {q : R ⟶ pullback p p}
    {vX : V ⟶ X} {vR : V ⟶ R} (hv : IsPullback vX vR f (q ≫ pullback.fst p p ≫ p)) :
    ∃ m : V ⟶ pullback a a, IsPullback m vR (pullback.map a a p p t t f hpb.w hpb.w) q := by
  have hk₁ : pullback.map a a p p t t f hpb.w hpb.w ≫ pullback.fst p p =
      pullback.fst a a ≫ t := pullback.lift_fst _ _ _
  have hk₂ : pullback.map a a p p t t f hpb.w hpb.w ≫ pullback.snd p p =
      pullback.snd a a ≫ t := pullback.lift_snd _ _ _
  have hcomp₁ : vX ≫ f = (vR ≫ q ≫ pullback.fst p p) ≫ p := by simpa using hv.w
  have hcomp₂ : vX ≫ f = (vR ≫ q ≫ pullback.snd p p) ≫ p :=
    hcomp₁.trans (by simp only [Category.assoc, pullback.condition])
  let m : V ⟶ pullback a a := pullback.lift (hpb.lift vX _ hcomp₁) (hpb.lift vX _ hcomp₂)
    ((hpb.lift_fst _ _ _).trans (hpb.lift_fst _ _ _).symm)
  have hm₁ : m ≫ pullback.fst a a = hpb.lift vX _ hcomp₁ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd a a = hpb.lift vX _ hcomp₂ := pullback.lift_snd _ _ _
  have hX₁ : m ≫ pullback.fst a a ≫ a = vX := by
    rw [reassoc_of% hm₁]
    exact hpb.lift_fst _ _ _
  have hX₂ : m ≫ pullback.snd a a ≫ a = vX := by
    rw [reassoc_of% hm₂]
    exact hpb.lift_fst _ _ _
  have hU₁ : m ≫ pullback.fst a a ≫ t = vR ≫ q ≫ pullback.fst p p := by
    rw [reassoc_of% hm₁]
    exact hpb.lift_snd _ _ _
  have hU₂ : m ≫ pullback.snd a a ≫ t = vR ≫ q ≫ pullback.snd p p := by
    rw [reassoc_of% hm₂]
    exact hpb.lift_snd _ _ _
  refine ⟨m, IsPullback.mk' (pullback.hom_ext (by simp only [Category.assoc, hk₁, hU₁])
    (by simp only [Category.assoc, hk₂, hU₂])) ?_ ?_⟩
  · intro Z φ ψ hφ hψ
    exact hv.hom_ext (by rw [← hX₁, reassoc_of% hφ]) hψ
  · intro Z cK cR hc
    have hx : (cK ≫ pullback.fst a a ≫ a) ≫ f = cR ≫ q ≫ pullback.fst p p ≫ p := by
      rw [Category.assoc, Category.assoc, hpb.w, ← reassoc_of% hk₁, reassoc_of% hc]
    obtain ⟨l, hlX, hlR⟩ : ∃ l, l ≫ vX = cK ≫ pullback.fst a a ≫ a ∧ l ≫ vR = cR :=
      ⟨hv.lift _ _ hx, hv.lift_fst _ _ _, hv.lift_snd _ _ _⟩
    refine ⟨l, ?_, hlR⟩
    apply pullback.hom_ext <;> apply hpb.hom_ext <;>
      simp only [Category.assoc, hX₂, hU₁, hU₂, hlX, reassoc_of% hlR,
        ← reassoc_of% hc, hk₁, hk₂, pullback.condition]

/-- The set-theoretic condition of **Stacks 0AIS** passes to the source of a representable
affine morphism of fppf sheaves: a representable surjection onto the target, and a
representable surjection onto its kernel pair, base change to the same data over the source. -/
theorem satisfiesSetTheoreticCondition_of_relative_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : SatisfiesSetTheoreticCondition B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X := by
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  obtain ⟨U, R, hU, hR, hUrep, hRrep, p, hp, q, hq⟩ := hY
  let F := sheafToPresheaf J (Type (u + 1))
  let eU : hU ≅ G.obj U :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
      (Classical.choice hUrep ≪≫ (F.mapIso (eG.app U)).symm)
  let eR : hR ≅ G.obj R :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
      (Classical.choice hRrep ≪≫ (F.mapIso (eG.app R)).symm)
  let p' : G.obj U ⟶ Y := eU.inv ≫ p
  let q' : G.obj R ⟶ pullback p' p' :=
    eR.inv ≫ q ≫ pullback.map p p p' p' eU.hom eU.hom (𝟙 Y)
      (by simp [p']) (by simp [p'])
  have hp' : Epi p' := by
    dsimp [p']
    infer_instance
  have hq' : Epi q' := by
    dsimp [q']
    infer_instance
  let hrep : Functor.relativelyRepresentable G f := hf.1
  have hpb := hrep.isPullback p'
  have ha : Epi (hrep.fst p') := by
    have := Sheaf.epi_pullback_snd p' f hp'
    rw [← hpb.flip.isoPullback_hom_snd]
    infer_instance
  obtain ⟨m, hsq⟩ := exists_isPullback_pullbackMap hpb
    (hrep.isPullback (q' ≫ pullback.fst p' p' ≫ p'))
  have hm : Epi m := by
    have := Sheaf.epi_pullback_snd q' (pullback.map _ _ _ _ _ _ _ hpb.w hpb.w) hq'
    rw [← hsq.flip.isoPullback_hom_snd]
    infer_instance
  exact ⟨hrep.pullback p', hrep.pullback (q' ≫ pullback.fst p' p' ≫ p'), _, _,
    ⟨F.mapIso (eG.app _)⟩, ⟨F.mapIso (eG.app _)⟩, _, ha, m, hm⟩

/-- **Stacks 0AKP, part (1).** The source of a representable affine morphism of fppf sheaves
whose target is an affine formal algebraic space is itself an affine formal algebraic space. -/
@[stacks 0AKP "affine_source"]
theorem isAffineFormalAlgebraicSpace_of_relative_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  obtain ⟨I, pre, hI, hd, D, hD, ⟨hYcol⟩⟩ := hY.2
  obtain ⟨E, p, hX, hcart⟩ :=
    exists_affine_pullback_presentation B S hS f hf D hYcol
  exact ⟨satisfiesSetTheoreticCondition_of_relative_isAffineHom B S hS f hf hY.1,
    I, pre, hI, hd, E,
    isThickening_of_cartesian_presentation B S hS f D E p hYcol hX hcart hD,
    ⟨hX⟩⟩

end AlgebraicGeometry.FormalSpace

end
