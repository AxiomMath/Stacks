module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic

/-!
# The atlas of an open covering by algebraic spaces

Let `F` be an algebraic space covered by open subspaces `Fᵢ` (Stacks 02WR, in the form of
`AlgebraicGeometry.isAlgebraicSpace_of_open_cover`): `g : ∐ Fᵢ ⟶ F` is locally surjective and
each `Fᵢ ⟶ F` is an open immersion. Then every surjective étale atlas of the coproduct `∐ Fᵢ`,
followed by `g`, is a surjective étale atlas of `F`
(`AlgebraicGeometry.C1590Private.atlas_comp_of_open_cover`). This is the atlas the proof of
`AlgebraicGeometry.isAlgebraicSpace_of_open_cover` produces, for a prescribed atlas of the
coproduct, so that a bound on its size passes to the atlas of `F`.
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A surjective étale atlas of the coproduct of an open covering is one of the covered
space.** -/
theorem atlas_comp_of_open_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFalg : IsAlgebraicSpace B S hS F)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ((ι i).hom ≫ g))
    (hsurj : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS) g)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ G.obj)
    (hfSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hfEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f ≫ g) ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f ≫ g) := by
  classical
  let J := BigFppfOver.topology B S hS
  let Tfun := BigFppfOver.toScheme B S hS
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : PreservesLimitsOfShape WalkingCospan Tfun := comp_preservesLimitsOfShape _ _
  have hdiag := hFalg.diagonal_representable
  obtain ⟨Uᵢ, q, hqOpen, hqSec, -, hqCov, hqUniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hcoprod U (yonedaEquiv f)
  choose z hz using hqSec
  let fᵢ : ∀ i, yoneda.obj (Uᵢ i) ⟶ (Fᵢ i).obj := fun i => yonedaEquiv.symm (z i)
  have hUi : ∀ i, IsPullback (yoneda.map (q i)) (fᵢ i) f (ι i).hom := fun i => by
    simpa only [Equiv.symm_apply_apply] using
      isPullback_yoneda_clopen_piece ι hcoprod (q i) (hqOpen i) (yonedaEquiv f) (z i) (hz i)
        (hqUniv i)
  -- the pieces of the atlas are surjective étale charts of the members
  have hfiEtale : ∀ i, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf (fᵢ i) := fun i => by
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hUi i) hfEtale
  -- and the composite with the inclusion of the member is étale over `F`
  have hlocalEtale : ∀ i, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf
      (yoneda.map (q i) ≫ f ≫ g) := fun i => by
    have hcomp : fᵢ i ≫ (ι i).hom ≫ g = yoneda.map (q i) ≫ f ≫ g := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ g) (hUi i).w.symm
    rw [← hcomp]
    have ho : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf ((ι i).hom ≫ g) :=
      MorphismProperty.relative_monotone (fun _ _ k hk => by
        have _ : IsOpenImmersion (Tfun.map k) := hk
        exact (inferInstance : Etale (Tfun.map k))) _ (hopen i)
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).IsStableUnderComposition := by
      refine ⟨fun {_ _ _} a b ha hb => ?_⟩
      show Etale (Tfun.map (a ≫ b))
      rw [Functor.map_comp]
      have _ : Etale (Tfun.map a) := ha
      have _ : Etale (Tfun.map b) := hb
      infer_instance
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        Tfun).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ _ _ (hfiEtale i) ho
  -- `f ≫ g` is locally surjective
  have hfgLoc : Presheaf.IsLocallySurjective J (f ≫ g) := by
    have _ := Space.isLocallySurjective_of_presheafSurjective_etale f hfSurj hfEtale
    have _ := hsurj
    infer_instance
  -- assemble
  have hfgRep : yoneda.relativelyRepresentable (f ≫ g) :=
    Functor.relativelyRepresentable.of_diag hdiag _
  refine ⟨?_, ?_⟩
  · exact Space.presheafSurjective_of_relativelyRepresentable (f ≫ g) hfgRep hfgLoc
  · have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage _ _
    refine MorphismProperty.relative_of_snd hfgRep fun T t => ?_
    set V := hfgRep.pullback t
    set p : V ⟶ T := hfgRep.snd t with hp
    set r : V ⟶ U := yoneda.preimage (hfgRep.fst t) with hr
    have hrp : IsPullback (yoneda.map r) (yoneda.map p) (f ≫ g) t := by
      simpa only [hr, hp, Functor.map_preimage] using hfgRep.isPullback t
    have hsq : ∀ i, IsPullback (Tfun.map (pullback.fst (q i) r))
        (Tfun.map (pullback.snd (q i) r)) (Tfun.map (q i)) (Tfun.map r) := fun i =>
      (IsPullback.of_hasPullback (q i) r).map Tfun
    have hbOpen : ∀ i, IsOpenImmersion (Tfun.map (pullback.snd (q i) r)) := fun i =>
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsOpenImmersion.{u}) (hsq i) (hqOpen i)
    have hbEtale : ∀ i, Etale (Tfun.map (pullback.snd (q i) r ≫ p)) := fun i => by
      have hpb : IsPullback (yoneda.map (pullback.fst (q i) r))
          (yoneda.map (pullback.snd (q i) r) ≫ yoneda.map p)
          (yoneda.map (q i) ≫ (f ≫ g)) t :=
        ((IsPullback.of_hasPullback (q i) r).map yoneda).paste_vert hrp
      exact (hlocalEtale i).property t (yoneda.map (pullback.fst (q i) r))
        (pullback.snd (q i) r ≫ p)
        (by simpa only [Functor.map_comp, Category.assoc] using hpb)
    have hbCover : iSup (fun i : I => (Tfun.map (pullback.snd (q i) r)).opensRange) = ⊤ := by
      refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
      rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
      obtain ⟨i, y, hy⟩ := hqCov (Tfun.map r x)
      obtain ⟨c, hc⟩ : x ∈ Set.range (pullback.snd (Tfun.map (q i)) (Tfun.map r)) :=
        (IsOpenImmersion.range_pullbackSnd (Tfun.map (q i)) (Tfun.map r)).ge ⟨y, hy⟩
      refine ⟨i, (hsq i).isoPullback.inv c, ?_⟩
      calc (Tfun.map (pullback.snd (q i) r)) ((hsq i).isoPullback.inv c)
          = (pullback.snd (Tfun.map (q i)) (Tfun.map r))
            ((hsq i).isoPullback.hom ((hsq i).isoPullback.inv c)) := by
            simpa only [← Scheme.Hom.comp_apply, Category.assoc] using
              congrArg (fun φ : Tfun.obj (pullback (q i) r) ⟶ Tfun.obj V =>
                φ ((hsq i).isoPullback.inv c)) (hsq i).isoPullback_hom_snd.symm
        _ = (pullback.snd (Tfun.map (q i)) (Tfun.map r)) c := by simp
        _ = x := hc
    have _ : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top
      (fun i : I => (Tfun.map (pullback.snd (q i) r)).opensRange) hbCover fun i => ?_
    set e : ((Tfun.map (pullback.snd (q i) r)).opensRange).toScheme ≅
        Tfun.obj (pullback (q i) r) :=
      IsOpenImmersion.isoOfRangeEq ((Tfun.map (pullback.snd (q i) r)).opensRange).ι
        (Tfun.map (pullback.snd (q i) r)) (by simp)
    have hfac : e.hom ≫ Tfun.map (pullback.snd (q i) r ≫ p) =
        ((Tfun.map (pullback.snd (q i) r)).opensRange).ι ≫ Tfun.map p := by
      rw [Functor.map_comp, ← Category.assoc]
      exact congrArg (fun y => y ≫ Tfun.map p)
        (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _)
    have hcomp : Etale (e.hom ≫ Tfun.map (pullback.snd (q i) r ≫ p)) := by
      have _ := hbEtale i
      infer_instance
    rwa [hfac] at hcomp

end AlgebraicGeometry.C1590Private

end
