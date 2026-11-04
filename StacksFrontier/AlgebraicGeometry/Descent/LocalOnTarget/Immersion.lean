module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage

/-!
# Quasi-compact immersions are fpqc local on the base

A morphism of schemes is a quasi-compact immersion precisely when its base changes along the
members of an fpqc covering of the target are.

## Main results

* `AlgebraicGeometry.ker_pullback_snd_eq_comap_of_flat`: the kernel ideal sheaf of a quasi-compact
  morphism pulls back to the kernel ideal sheaf of its flat base change.
* `AlgebraicGeometry.isImmersion_inf_quasiCompact_descendsAlong`: quasi-compact immersions
  satisfy fpqc descent.
* `AlgebraicGeometry.isLocalAtTarget_isImmersion_inf_quasiCompact_fpqc`: being a quasi-compact
  immersion is fpqc local on the base.

## Implementation notes

A quasi-compact immersion factors as an open immersion onto its scheme-theoretic image followed
by the closed immersion of that image (`AlgebraicGeometry.isOpenImmersion_toImage`), and closed
immersions are already known to be fpqc local on the base. The descent step therefore reduces to
descending the open immersion, and that in turn to identifying the scheme-theoretic image of the
base change with the base change of the scheme-theoretic image.

That identification is the content of `ker_pullback_snd_eq_comap_of_flat`: for `f` quasi-compact
and `g` flat the kernel ideal sheaf of `pullback.snd f g` is the pullback of the kernel ideal
sheaf of `f`. Its proof factors `f` through its image, notes that the first factor is
scheme-theoretically dominant and that scheme-theoretic dominance is preserved by the flat base
change, and reads the kernel of the resulting composite off the closed immersion.

## References

* [Stacks Project, Tag 02L8](https://stacks.math.columbia.edu/tag/02L8)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

universe u

/-- For `f` quasi-compact and `g` flat, the kernel ideal sheaf of the base change of `f` along
`g` is the pullback along `g` of the kernel ideal sheaf of `f`. -/
theorem ker_pullback_snd_eq_comap_of_flat {X Y V : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) [Flat g] [QuasiCompact f] :
    (pullback.snd f g).ker = f.ker.comap g := by
  conv_lhs => rw [← f.toImage_imageι]
  set i := f.imageι with hi
  set h := f.toImage
  have hdom : IsSchemeTheoreticallyDominant h := by
    rw [isSchemeTheoreticallyDominant_iff]
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : Y.affineOpens ↦ ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩)
      (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) i.base.hom) fun U ↦ ?_
    simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U
  have hp : IsSchemeTheoreticallyDominant (pullback.snd h (pullback.fst i g)) := inferInstance
  have he : (pullbackRightPullbackFstIso i g h).hom ≫ pullback.snd (h ≫ i) g =
      pullback.snd h (pullback.fst i g) ≫ pullback.snd i g := by
    rw [pullbackRightPullbackFstIso_hom_snd]
  calc (pullback.snd (h ≫ i) g).ker
      = ((pullbackRightPullbackFstIso i g h).hom ≫ pullback.snd (h ≫ i) g).ker :=
        (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (pullback.snd h (pullback.fst i g) ≫ pullback.snd i g).ker := congrArg Scheme.Hom.ker he
    _ = (pullback.snd i g).ker := by
        rw [Scheme.Hom.ker_comp, hp.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    _ = i.ker.comap g := by
        rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry g i).hom (pullback.snd i g),
          pullbackSymmetry_hom_comp_snd, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    _ = f.ker.comap g := by rw [hi, Scheme.IdealSheafData.ker_subschemeι]

/-- If the base change of `f` along a surjective flat quasi-compact morphism `g` is a
quasi-compact immersion, then so is `f`. -/
@[sga "4 IV 8.5.5" "special case"]
private lemma isImmersion_of_pullbackSnd {S S' X : Scheme.{u}} (g : S' ⟶ S)
    [Surjective g] [Flat g] [QuasiCompact g] (f : X ⟶ S)
    (hf : IsImmersion (pullback.snd f g)) (hqc : QuasiCompact (pullback.snd f g)) :
    IsImmersion f ∧ QuasiCompact f := by
  have := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  let 𝒰 : Precoverage.ZeroHypercover.{0} Scheme.fpqcPrecoverage S :=
    .singleton g g.singleton_mem_fpqcPrecoverage
  have _ : QuasiCompact f :=
    MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := @QuasiCompact) 𝒰
      fun i ↦ by cases i; exact hqc
  have _ : IsImmersion (pullback.snd f g) := hf
  have _ : QuasiCompact (pullback.snd f g) := hqc
  have _ : IsOpenImmersion (pullback.snd f g).toImage :=
    isOpenImmersion_toImage _ (Or.inl hqc)
  -- The scheme-theoretic image of the base change is the base change of the image, because the
  -- two closed subschemes of `S'` are cut out by the same ideal sheaf.
  have hsame : (pullback.snd f g).ker = (pullback.snd f.imageι g).ker := by
    rw [ker_pullback_snd_eq_comap_of_flat f g, ker_pullback_snd_eq_comap_of_flat f.imageι g,
      Scheme.IdealSheafData.ker_subschemeι]
  let j := IsClosedImmersion.lift (pullback.snd f.imageι g) (pullback.snd f g).imageι
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hsame.symm.le)
  have hj : j ≫ pullback.snd f.imageι g = (pullback.snd f g).imageι :=
    IsClosedImmersion.lift_fac _ _ _
  have _ : IsIso j :=
    IsClosedImmersion.isIso_of_ker_eq (pullback.snd f g).imageι (pullback.snd f.imageι g) j hj
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hsame)
  -- Paste the two cartesian squares to compare the two descriptions of `X ×_S S'`.
  have hpb : IsPullback (pullback.fst f.toImage (pullback.fst f.imageι g))
      (pullback.snd f.toImage (pullback.fst f.imageι g) ≫ pullback.snd f.imageι g) f g := by
    have h := (IsPullback.of_hasPullback f.toImage (pullback.fst f.imageι g)).paste_vert
      (IsPullback.of_hasPullback f.imageι g)
    rwa [Scheme.Hom.toImage_imageι] at h
  have hfac : hpb.isoPullback.hom ≫ (pullback.snd f g).toImage ≫ j =
      pullback.snd f.toImage (pullback.fst f.imageι g) := by
    refine (cancel_mono (pullback.snd f.imageι g)).mp ?_
    calc (hpb.isoPullback.hom ≫ (pullback.snd f g).toImage ≫ j) ≫ pullback.snd f.imageι g
        = hpb.isoPullback.hom ≫ (pullback.snd f g).toImage ≫ (pullback.snd f g).imageι := by
          simp only [Category.assoc, hj]
      _ = hpb.isoPullback.hom ≫ pullback.snd f g := by rw [Scheme.Hom.toImage_imageι]
      _ = _ := hpb.isoPullback_hom_snd
  have hpOpen : IsOpenImmersion (pullback.snd f.toImage (pullback.fst f.imageι g)) := by
    rw [← hfac]; infer_instance
  have _ : IsOpenImmersion f.toImage :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsOpenImmersion)
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hpOpen
  refine ⟨?_, inferInstance⟩
  rw [← Scheme.Hom.toImage_imageι f]
  infer_instance

/-- Quasi-compact immersions satisfy fpqc descent. -/
@[ega "IV 2.7.1" "(xi)", sga "4 IV 8.5.5" "Target"]
instance isImmersion_inf_quasiCompact_descendsAlong :
    MorphismProperty.DescendsAlong
      (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {_ _ _ _ _ _ g f} h hg hfst := by
    obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := hg
    have _ : Surjective g := hsurj
    have _ : Flat g := hflat
    have _ : QuasiCompact g := hqc
    have : MorphismProperty.IsStableUnderBaseChange
        (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := .inf
    have : (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}).RespectsIso :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have key : (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (pullback.snd f g) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso
        (P := (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
        h.flip.isoPullback.hom, h.flip.isoPullback_hom_snd]
      exact hfst
    exact isImmersion_of_pullbackSnd g f key.1 key.2

/-- **Stacks Project, Tag 02L8.** Quasi-compact immersions are fpqc local on the target. -/
@[stacks 02L8, ega "IV 2.7.1" "more general", sga "4 IV 8.5.5"]
instance isLocalAtTarget_isImmersion_inf_quasiCompact_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc.of_le
      Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  have : IsZariskiLocalAtTarget
      (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := .inf _ _
  have : MorphismProperty.IsStableUnderBaseChange
      (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := .inf
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end AlgebraicGeometry

end
