module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSupplement

/-!
# Representable affine morphisms to an affine formal algebraic space

Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf site of `S` which is representable
by schemes and whose representable base changes are affine. If `Y` is an affine formal
algebraic space then so is `X`, and if `Y` is countably indexed then so is `X`.

## Main results

* `AlgebraicGeometry.hasThickeningPresentation_of_affine`: the source of a representable affine
  morphism to a sheaf presented by affine thickenings is presented in the same way -- the
  geometric half of the statement, with no set-theoretic condition on either side.
* `AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine`: the source of a representable
  affine morphism to an affine formal algebraic space is an affine formal algebraic space.
* `AlgebraicGeometry.isCountablyIndexed_of_affine`: the source of a representable affine
  morphism to a countably indexed sheaf is countably indexed.

## Implementation notes

The hypothesis on `f` is the relative morphism property along the sheafified Yoneda
embedding: it asks both that `f` be representable and that each represented base change be
an affine morphism of schemes.

In both statements the presentation of the source is produced by pulling the presentation of
the target back along `f`. For the first statement the set-theoretic condition has to be
pulled back as well: the two representable surjections presenting `Y` give, after base
change along `f`, a representable surjection onto `X` and a representable surjection onto
its kernel pair. Transporting them requires identifying a representable sheaf for the
chosen big fppf site with a sheafified representable, which is where subcanonicity of the
topology enters.

The second statement needs no affine-formal-space hypothesis: countable indexing already
supplies the presentation the argument pulls back. Its sequential presentation is converted
to a countable directed one and back, which is how the index category stays fixed while the
stages change.

## References

* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The source of a representable affine map of fppf sheaves to a sheaf presented as a directed
colimit of affine schemes along thickenings is presented in the same way: the presentation of
the target is pulled back along the morphism, which is affine, and the base change of a
thickening along an affine morphism is again a thickening.

This is the geometric half of Stacks 0AKP, part (1). It assumes neither set-theoretic condition
and produces neither, so it applies to a formal spectrum over a site which is not large enough
to contain the coproduct of its quotient spectra. -/
theorem hasThickeningPresentation_of_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : X ⟶ Y)
    (hY : FormalSpace.HasThickeningPresentation B S hS Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    FormalSpace.HasThickeningPresentation B S hS X := by
  obtain ⟨I, pre, hI, hd, D, hD, ⟨hYcol⟩⟩ := hY
  let _ : Preorder I := pre
  let _ : Nonempty I := hI
  let _ : IsDirected I (· ≤ ·) := hd
  obtain ⟨E, p, hX, hcart⟩ :=
    exists_affine_pullback_presentation B S hS f hf D hYcol
  exact ⟨I, pre, hI, hd, E,
    isThickening_of_cartesian_presentation B S hS f D E p hYcol hX hcart hD, ⟨hX⟩⟩

/-- The source of a representable affine map of fppf sheaves to an affine
formal algebraic space is an affine formal algebraic space. -/
@[stacks 0AKP "affine_source"]
theorem isAffineFormalAlgebraicSpace_of_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : X ⟶ Y)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  have hSet : SatisfiesSetTheoreticCondition B S hS X := by
    let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
    let _ : J.Subcanonical := inferInstance
    let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
    obtain ⟨U, R, hU, hR, hUrep, hRrep, p, hp, q, hq⟩ := hY.1
    let F := sheafToPresheaf J (Type (u + 1))
    let eU : hU ≅ G.obj U :=
      (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
        (Classical.choice hUrep ≪≫ (F.mapIso (eG.app U)).symm)
    let eR : hR ≅ G.obj R :=
      (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
        (Classical.choice hRrep ≪≫ (F.mapIso (eG.app R)).symm)
    let p' : G.obj U ⟶ Y := eU.inv ≫ p
    let _ : Epi q := hq
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
    have hV := hrep.isPullback (q' ≫ pullback.fst p' p' ≫ p')
    obtain ⟨m, hsq⟩ : ∃ m, IsPullback m (G.map (hrep.snd (q' ≫ pullback.fst p' p' ≫ p')))
        (pullback.map _ _ _ _ _ _ f hpb.w hpb.w) q' := by
      have hc₁ : hrep.fst (q' ≫ pullback.fst p' p' ≫ p') ≫ f =
          (G.map (hrep.snd (q' ≫ pullback.fst p' p' ≫ p')) ≫ q' ≫ pullback.fst p' p') ≫ p' := by
        simpa only [Category.assoc] using hV.w
      have hc₂ : hrep.fst (q' ≫ pullback.fst p' p' ≫ p') ≫ f =
          (G.map (hrep.snd (q' ≫ pullback.fst p' p' ≫ p')) ≫ q' ≫ pullback.snd p' p') ≫ p' := by
        simpa only [Category.assoc, pullback.condition] using hV.w
      refine ⟨pullback.lift (hpb.lift _ _ hc₁) (hpb.lift _ _ hc₂)
        ((hpb.lift_fst _ _ _).trans (hpb.lift_fst _ _ _).symm), ?_⟩
      refine IsPullback.mk' (by apply pullback.hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            pullback.lift_snd_assoc, IsPullback.lift_snd])
        (fun _ φ ψ hφ hψ => hV.hom_ext ?_ hψ) (fun _ cK cR hc => ?_)
      · simpa only [Category.assoc, pullback.lift_fst_assoc, IsPullback.lift_fst] using
          hφ =≫ pullback.fst (hrep.fst p') (hrep.fst p') ≫ hrep.fst p'
      · have hx : (cK ≫ pullback.fst (hrep.fst p') (hrep.fst p') ≫ hrep.fst p') ≫ f =
            cR ≫ q' ≫ pullback.fst p' p' ≫ p' := by
          rw [Category.assoc, Category.assoc, hpb.w, ← reassoc_of% hc, pullback.lift_fst_assoc,
            Category.assoc]
        refine ⟨hV.lift _ cR hx, ?_, hV.lift_snd _ _ _⟩
        apply pullback.hom_ext <;> apply hpb.hom_ext <;>
          simp only [Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd,
            IsPullback.lift_snd_assoc, pullback.condition, ← reassoc_of% hc, pullback.lift_fst,
            pullback.lift_snd]
    have ha : Epi (hrep.fst p') := by
      have := Sheaf.epi_pullback_snd p' f hp'
      rw [← hpb.flip.isoPullback_hom_snd]
      infer_instance
    have hm : Epi m := by
      have := Sheaf.epi_pullback_snd q' (pullback.map _ _ _ _ _ _ f hpb.w hpb.w) hq'
      rw [← hsq.flip.isoPullback_hom_snd]
      infer_instance
    exact ⟨_, _, _, _, ⟨F.mapIso (eG.app _)⟩, ⟨F.mapIso (eG.app _)⟩, _, ha, m, hm⟩
  exact ⟨hSet, hasThickeningPresentation_of_affine B S hS f hY.2 hf⟩

/-- The source of a representable affine map to a countably indexed sheaf is
countably indexed. -/
theorem isCountablyIndexed_of_affine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY_countable : IsCountablyIndexed B S hS Y) :
    IsCountablyIndexed B S hS X := by
  obtain ⟨I, pre, hI, hd, hc, D, hD, ⟨hY⟩⟩ :=
    (exists_sequential_presentation_iff_exists_countable_presentation
      B S hS Y).1 hY_countable
  let _ : Preorder I := pre
  let _ : Nonempty I := hI
  let _ : IsDirected I (· ≤ ·) := hd
  obtain ⟨E, p, hX, hcart⟩ :=
    exists_affine_pullback_presentation B S hS f hf D hY
  exact (exists_sequential_presentation_iff_exists_countable_presentation B S hS X).2
    ⟨I, pre, hI, hd, hc, E, isThickening_of_cartesian_presentation
      B S hS f D E p hY hX hcart hD, ⟨hX⟩⟩

/-- The source of a representable affine map to a countably indexed sheaf is
countably indexed. -/
@[stacks 0AKP "countably_indexed_source"]
theorem isCountablyIndexed_of_affine'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY_countable : FormalSpace.IsCountablyIndexed B S hS Y) :
    FormalSpace.IsCountablyIndexed B S hS X :=
  isCountablyIndexed_of_affine B S hS f hf hY_countable

end AlgebraicGeometry
