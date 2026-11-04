module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic

/-!
# The étale analogue of the glueing criterion: a family of étale charts

Stacks 02WR glues an fppf sheaf `F` from a family of subfunctors `Fᵢ ⊂ F` which are algebraic
spaces and whose inclusions are representable **open immersions**. This file proves the variant
in which the legs `Fᵢ ⟶ F` are only required to be representable and **étale** — they need not
be monomorphisms, and the `Fᵢ` need not be subfunctors of `F`. It is the family form of Stacks
0BGR, which is the one-leg case.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_sigma_of_etaleCover`: the represented base change
  of the desc map along a section of `F` is the coproduct, in the site, of the represented base
  changes of the individual legs.
* `AlgebraicGeometry.Space.presheafEtale_of_etaleCover`: the desc map `∐ Fᵢ ⟶ F` of a family of
  representable étale legs is itself representable and étale.
* `AlgebraicGeometry.isAlgebraicSpace_coproduct_of_admitsCoproductIndex`: Stacks 02WQ with its
  set-theoretic condition supplied by `AdmitsCoproductIndex`.
* `AlgebraicGeometry.isAlgebraicSpace_of_etale_cover`: **the criterion.** An fppf sheaf covered
  by a family of algebraic spaces along representable étale legs is an algebraic space.

## Implementation notes

The index type carries `Small.{u} I` together with
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which is exactly what makes a coproduct
`∐ Xᵢ` of objects of the site an object of the site. Every finite index type satisfies both.

Hypothesis (2)(e) of Stacks 02WR — that `∐ Fᵢ` be an algebraic space — is *not* a hypothesis
here: it is Stacks 02WQ, and at an admissible index type it follows from the members being
algebraic spaces.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type v} [Small.{u} I]
  [B.AdmitsCoproductIndex I] {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}

/-- **The represented base change of a desc map is a coproduct of the legs' base changes.**

Let `G` be the coproduct of a family `Fᵢ` of fppf sheaves over `S`, let `g : G ⟶ F` be a
morphism to a sheaf `F` whose composite `(ι i) ≫ g` with each coproduct inclusion is
representable, and let `γ : h_V ⟶ F` be a section of `F` over an object `V` of the site.

Then the fibre product `G ×_F h_V` is represented by a coproduct `∐ Xᵢ` of the site, whose
structure morphism `σ : ∐ Xᵢ ⟶ V` restricts on the `i`-th summand to a represented base change
of the `i`-th leg — the last clause being recorded as a cartesian square, so that any property
of morphisms of the site stable under isomorphism transfers from the legs to the summands. -/
theorem exists_isPullback_sigma_of_etaleCover
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (ι : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G ι)) (g : G.obj ⟶ F)
    (hrep : ∀ i, yoneda.relativelyRepresentable ((ι i).hom ≫ g))
    {V : BigFppfOver B S hS} (γ : yoneda.obj V ⟶ F) :
    ∃ (X : I → BigFppfOver B S hS) (σ : BigFppfOver.sigmaObj B S hS X ⟶ V)
      (fst : yoneda.obj (BigFppfOver.sigmaObj B S hS X) ⟶ G.obj)
      (c : ∀ i, yoneda.obj (X i) ⟶ (Fi i).obj),
      IsPullback fst (yoneda.map σ) g γ ∧
        ∀ i, IsPullback (c i)
          (yoneda.map (BigFppfOver.sigmaIncl B S hS X i ≫ σ)) ((ι i).hom ≫ g) γ := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  let Fs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF⟩
  let γs : (BigFppfOver.topology B S hS).yoneda.obj V ⟶ Fs := ⟨γ⟩
  let gs : G ⟶ Fs := ⟨g⟩
  let H := pullback γs gs
  let fstH : H.obj ⟶ yoneda.obj V := (pullback.fst γs gs).hom
  let sndH : H.obj ⟶ G.obj := (pullback.snd γs gs).hom
  have hH : IsPullback fstH sndH γ g :=
    (IsPullback.of_hasPullback γs gs).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
  have hdata : ∀ i, ∃ p : yoneda.obj ((hrep i).pullback γ) ⟶ H.obj,
      IsPullback p ((hrep i).fst γ) sndH (ι i).hom ∧
        p ≫ fstH = yoneda.map ((hrep i).snd γ) := by
    intro i
    have hsq : IsPullback ((hrep i).fst γ) (yoneda.map ((hrep i).snd γ))
        ((ι i).hom ≫ g) γ := (hrep i).isPullback γ
    have hc : yoneda.map ((hrep i).snd γ) ≫ γ = ((hrep i).fst γ ≫ (ι i).hom) ≫ g :=
      hsq.w.symm.trans (Category.assoc _ _ _).symm
    have hl := hH.lift_fst (yoneda.map ((hrep i).snd γ)) ((hrep i).fst γ ≫ (ι i).hom) hc
    refine ⟨_, ?_, hl⟩
    rw [← hl] at hsq
    exact (IsPullback.of_bot hsq (hH.lift_snd _ _ _).symm hH.flip).flip
  choose p hp hpfst using hdata
  set X : I → BigFppfOver B S hS := fun i => (hrep i).pullback γ
  let pS : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (X i) ⟶ H := fun i => ⟨p i⟩
  let qS : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (X i) ⟶ Fi i :=
    fun i => ⟨(hrep i).fst γ⟩
  obtain ⟨hcolim⟩ := nonempty_isColimit_cofanMk_of_isPullback B S hS ι hcoprod
    (pullback.snd γs gs) pS qS fun i => isPullback_sheaf_of_hom (hp i)
  let e : H ≅ (BigFppfOver.topology B S hS).yoneda.obj (BigFppfOver.sigmaObj B S hS X) :=
    hcolim.coconePointUniqueUpToIso (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS X)
  let eP : H.obj ≅ yoneda.obj (BigFppfOver.sigmaObj B S hS X) :=
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso e
  have he : ∀ i, p i ≫ eP.hom = yoneda.map (BigFppfOver.sigmaIncl B S hS X i) := fun i =>
    congrArg (fun φ => φ.hom) (hcolim.comp_coconePointUniqueUpToIso_hom
      (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS X) (Discrete.mk i))
  have hσ : ∀ i, BigFppfOver.sigmaIncl B S hS X i ≫ yoneda.preimage (eP.inv ≫ fstH) =
      (hrep i).snd γ := fun i => yoneda.map_injective <| by
    rw [Functor.map_comp, Functor.map_preimage, ← he i, Category.assoc,
      Iso.hom_inv_id_assoc, hpfst i]
  refine ⟨X, yoneda.preimage (eP.inv ≫ fstH), eP.inv ≫ sndH, fun i => (hrep i).fst γ, ?_,
    fun i => ?_⟩
  · rw [Functor.map_preimage]
    exact IsPullback.of_iso hH.flip eP (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  · rw [hσ i]
    exact (hrep i).isPullback γ

/-- **A desc map of representable étale legs is representable and étale.**

If `G` is the coproduct of fppf sheaves `Fᵢ` over `S` and each composite `Fᵢ ⟶ G ⟶ F` is
representable and étale, then `g : G ⟶ F` is representable and étale. -/
theorem presheafEtale_of_etaleCover
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (ι : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G ι)) (g : G.obj ⟶ F)
    (hetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) ((ι i).hom ≫ g)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) g := by
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun V γ => ?_
  obtain ⟨X, σ, fst, c, hsq, hsqi⟩ := exists_isPullback_sigma_of_etaleCover B S hS hF ι hcoprod g
    (fun i => (hetale i).rep) γ
  exact ⟨_, fst, σ, hsq, etale_toScheme_of_sigmaIncl B S hS X σ fun i =>
    (hetale i).property γ (c i) _ (hsqi i)⟩

end Space

/-- **The sheaf coproduct of an admissible family of algebraic spaces is an algebraic
space.** This is Stacks 02WQ with its set-theoretic condition supplied by
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which every finite index type satisfies. -/
theorem isAlgebraicSpace_coproduct_of_admitsCoproductIndex
    {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    IsAlgebraicSpace B S hS G.obj := by
  choose U a hsurj hetale using fun i => (hF i).exists_atlas
  exact isAlgebraicSpace_coproduct B S hS F hF G ι hG U a hsurj hetale
    (BigFppfOver.sigmaObj B S hS U) (BigFppfOver.sigmaIncl B S hS U)
    (BigFppfOver.isColimit_sigmaCofan B S hS U)

/-- **The étale glueing criterion for algebraic spaces.**

Let `F` be an fppf sheaf on the big fppf site over `S`, let `Fᵢ` be a family of algebraic
spaces over `S` indexed by an admissible `u`-small type and let `G` be their coproduct as fppf
sheaves. If `g : G ⟶ F` is locally surjective and each composite `Fᵢ ⟶ G ⟶ F` is representable
and étale, then `F` is an algebraic space over `S`.

This is the family form of Stacks 0BGR, which is the case of a one-element family, and the
étale analogue of Stacks 02WR, whose legs are required to be open immersions. -/
theorem isAlgebraicSpace_of_etale_cover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
    {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hFi : ∀ i, IsAlgebraicSpace B S hS (Fi i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G ι)) (g : G.obj ⟶ F)
    (hetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) ((ι i).hom ≫ g))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g) :
    IsAlgebraicSpace B S hS F := by
  have hG : IsAlgebraicSpace B S hS G.obj :=
    isAlgebraicSpace_coproduct_of_admitsCoproductIndex B S hS (fun i => (Fi i).obj) hFi G ι
      hcoprod
  have het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) g :=
    Space.presheafEtale_of_etaleCover B S hS hF ι hcoprod g hetale
  exact isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS hG hF g
    (Space.presheaf_surjective_of_isLocallySurjective B S hS het.rep hsurj) het

end AlgebraicGeometry

end
