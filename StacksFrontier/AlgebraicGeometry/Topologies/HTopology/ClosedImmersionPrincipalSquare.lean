module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AffineAlmostBlowUpInterludeB
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ClosedImmersionAlmostBlowUp
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSquareGluing
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.OneGeneratorSquareRefinement

/-!
# Squares with a closed-immersion modification and a locally principal centre

The second step of the proof of Stacks 0EVI reads: "if we have a blow up square such that
`b : X' → X` is a closed immersion and `Z` is a locally principal closed subscheme, then we see
that `F(X) = F(X') ×_{F(E)} F(Z)`.  Namely, affine locally on `X` we obtain an almost blow up
square as in (3)."

This file proves that, for an almost blowup square of the site whose modification is a closed
immersion and whose centre is locally principal, under conditions (1) and (3) of Stacks 0EVI.

## Main results

* `AlgebraicGeometry.BigHOver.isPullback_of_isClosedImmersion_of_restrict_isIso`: the second step
  of the proof of Stacks 0EVI, at the hypotheses the induction has available.
* `AlgebraicGeometry.BigHOver.isPullback_of_isClosedImmersion_of_isLocallyPrincipal`: the same for
  an almost blowup square.

## Implementation notes

The gluing is `AlgebraicGeometry.BigHOver.isPullback_of_isLocallyCartesianSquare`, so all that
happens here is the exhibition of its hypothesis: over every base change of the square there is a
Zariski covering of the new base — by the affine opens on which the inverse-image centre becomes
principal, which is what `Stacks.Divisors.IsLocallyPrincipal` provides at every point — over whose
members the image of the restricted square is cartesian.  On such a member condition (3) applies
verbatim, by
`AlgebraicGeometry.BigHOver.isPullback_of_isOneGeneratorAlmostBlowUpSheaf_of_isClosedImmersion`.

The restricted square is taken to be the fibre product in the site, exactly as in Interlude B of
the proof of the sufficiency direction of Stacks 0EVF
(`AlgebraicGeometry.BigHOver.isPullback_of_isAffineAlmostBlowUpSheaf`), and the three hypotheses
condition (3) asks of it are checked the same way, with two additions: the restricted
modification is again a closed immersion, closed immersions being stable under base change, and
the ideal of the restricted centre over the whole of the member is principal, by
`AlgebraicGeometry.isPrincipal_comap_ideal_top_of_isPrincipal`.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- **The second step of the proof of Stacks 0EVI.** A presheaf on the big h category over `S`
which is a sheaf for the Zariski topology and satisfies condition (3) of Stacks 0EVI sends every
square of the site whose modification is a closed immersion of finite presentation which is an
isomorphism away from a locally principal centre to a cartesian square of sets.

The square is *not* assumed to be an almost blowup square, and neither the base nor any other
corner is assumed affine.  Affine locally on the base the square is recognized as one by
`AlgebraicGeometry.isAlmostBlowUpSquare_of_restrict_isIso`, which is all condition (3) needs; that
is what makes this statement available to the induction of Stacks 0EVI for the closed immersion
between the modifications of two almost blowup squares with the same centre. -/
public theorem isPullback_of_isClosedImmersion_of_restrict_isIso
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    (h1 : BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F)
    (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hci : IsClosedImmersion ((BigHOver.toScheme B S hS).map b))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map b))
    (hprin : Stacks.Divisors.IsLocallyPrincipal I)
    (hiso : IsIso ((BigHOver.toScheme B S hS).map b ∣_
      (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ :
        ((BigHOver.toScheme B S hS).obj X).Opens)))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hsq : IsPullback ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map d)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) := by
  classical
  have : HasPullbacks B.Schemes := inferInstance
  let _ := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let _ : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
    inferInstance
  have := hci
  have : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map b) := hfp.1
  have : QuasiCompact ((BigHOver.toScheme B S hS).map b) := hfp.2.1
  have : QuasiSeparated ((BigHOver.toScheme B S hS).map b) := hfp.2.2
  obtain ⟨ez⟩ := hZ
  have hsqsite : IsPullback e d z b := hsq.of_map_of_faithful (BigHOver.toScheme B S hS)
  have hwsite : e ≫ z = d ≫ b := hsqsite.w
  refine isPullback_of_isLocallyCartesianSquare B S hS F hzar b z d e hwsite ?_
  intro W w
  set wS := (BigHOver.toScheme B S hS).map w
  choose Uo hUoMem hUoPrin using Stacks.Divisors.isLocallyPrincipal_comap wS I hprin
  let U0 : ((BigHOver.toScheme B S hS).obj W).OpenCover.{u} :=
    Scheme.openCoverOfIsOpenCover _ (fun y ↦ (Uo y).1)
      (TopologicalSpace.IsOpenCover.mk (TopologicalSpace.Opens.ext
        (Set.eq_univ_of_forall fun y ↦ by
          rw [TopologicalSpace.Opens.coe_iSup]
          exact Set.mem_iUnion.2 ⟨y, hUoMem y⟩)))
  let U : Scheme.OpenCover.{u + 1, u} ((BigHOver.toScheme B S hS).obj W) :=
    U0.reindex (Equiv.ulift.{u + 1, u})
  refine ⟨preZeroHypercoverOfOpenCover U,
    (by simpa [preZeroHypercoverOfOpenCover, PreZeroHypercover.presieve₀, PreZeroHypercover.map]
      using U.mem₀), fun i => ?_⟩
  set x : (BigHOver.toScheme B S hS).obj W := Equiv.ulift.{u + 1, u} i
  have hAffine :
      IsAffine ((BigHOver.toScheme B S hS).obj ((preZeroHypercoverOfOpenCover U).X i)) :=
    (Uo x).2
  set h : (preZeroHypercoverOfOpenCover U).X i ⟶ X :=
    (preZeroHypercoverOfOpenCover U).f i ≫ w with hh
  have hmapeq : (BigHOver.toScheme B S hS).map h = (Uo x).1.ι ≫ wS := by
    rw [hh, Functor.map_comp]
    rfl
  refine ⟨pullback h b, pullback h z, pullback h (d ≫ b), pullback.fst h b, pullback.fst h z,
    restrictExcToMod B S hS b d h, restrictExcToCen B S hS b z d e hwsite h,
    pullback.snd h b, pullback.snd h z, pullback.snd h (d ≫ b),
    (IsPullback.of_hasPullback h b).flip, (IsPullback.of_hasPullback h z).flip,
    pullback.lift_snd _ _ _, pullback.lift_snd _ _ _, ?_⟩
  set εb := Limits.PreservesPullback.iso (BigHOver.toScheme B S hS) h b
  set εz := Limits.PreservesPullback.iso (BigHOver.toScheme B S hS) h z
  have hεfst : ∀ {Y : BigHOver B S hS} (g : Y ⟶ X),
      (Limits.PreservesPullback.iso (BigHOver.toScheme B S hS) h g).hom ≫
        pullback.fst ((BigHOver.toScheme B S hS).map h) ((BigHOver.toScheme B S hS).map g) =
      (BigHOver.toScheme B S hS).map (pullback.fst h g) := fun g ↦
    Limits.PreservesPullback.iso_hom_fst _ _ _
  have hεbfst := hεfst b
  have hεzfst := hεfst z
  have := hAffine
  have hcomapeq : I.comap ((BigHOver.toScheme B S hS).map h) = (I.comap wS).comap (Uo x).1.ι := by
    rw [hmapeq]
    exact Scheme.IdealSheafData.comap_comp ..
  obtain ⟨t, ht0⟩ :=
    isPrincipal_comap_ideal_top_of_isPrincipal (I.comap wS) (Uo x) (hUoPrin x)
  have ht : (I.comap ((BigHOver.toScheme B S hS).map h)).ideal ⟨⊤, isAffineOpen_top _⟩
      = Ideal.span {t} := by
    rw [hcomapeq]
    exact ht0
  have hciR : IsClosedImmersion ((BigHOver.toScheme B S hS).map (pullback.fst h b)) := by
    rw [← hεbfst]
    infer_instance
  have hfpR : FinitePresentation ((BigHOver.toScheme B S hS).map (pullback.fst h b)) := by
    rw [← hεbfst]
    have := finitePresentation_pullback_fst ((BigHOver.toScheme B S hS).map b)
      ((BigHOver.toScheme B S hS).map h) hfp
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hisoR : IsIso ((BigHOver.toScheme B S hS).map (pullback.fst h b) ∣_
      (⟨(I.comap ((BigHOver.toScheme B S hS).map h)).supportᶜ,
        (I.comap ((BigHOver.toScheme B S hS).map h)).support.isClosed.isOpen_compl⟩ :
          ((BigHOver.toScheme B S hS).obj ((preZeroHypercoverOfOpenCover U).X i)).Opens)) :=
    isIso_restrict_of_over_iso
      (pullback.fst ((BigHOver.toScheme B S hS).map h) ((BigHOver.toScheme B S hS).map b))
      ((BigHOver.toScheme B S hS).map (pullback.fst h b))
      (Over.isoMk εb.symm
        (show εb.inv ≫ (BigHOver.toScheme B S hS).map (pullback.fst h b) =
            pullback.fst ((BigHOver.toScheme B S hS).map h)
              ((BigHOver.toScheme B S hS).map b) by
          rw [← hεbfst, Iso.inv_hom_id_assoc])) _
      (isIso_restrict_compl_support_comap I ((BigHOver.toScheme B S hS).map b)
        ((BigHOver.toScheme B S hS).map h) hiso)
  refine isPullback_of_isOneGeneratorAlmostBlowUpSheaf_of_isClosedImmersion B S hS F h1
    ((preZeroHypercoverOfOpenCover U).X i) (pullback h b) (pullback h z) (pullback h (d ≫ b))
    (pullback.fst h b) (pullback.fst h z) (restrictExcToMod B S hS b d h)
    (restrictExcToCen B S hS b z d e hwsite h)
    (I.comap ((BigHOver.toScheme B S hS).map h)) hAffine
    (isAlmostBlowUpSquare_of_restrict_isIso _ _ hfpR hisoR t ht) hciR ?_ ?_ t ht
  · have e1 : Over.mk ((BigHOver.toScheme B S hS).map (pullback.fst h z)) ≅
        Over.mk (pullback.fst ((BigHOver.toScheme B S hS).map h)
          ((BigHOver.toScheme B S hS).map z)) :=
      Over.isoMk εz hεzfst
    have e3 : Over.mk (I.comap ((BigHOver.toScheme B S hS).map h)).subschemeι ≅
        Over.mk (pullback.fst ((BigHOver.toScheme B S hS).map h) I.subschemeι) :=
      Over.isoMk (I.comapIso ((BigHOver.toScheme B S hS).map h))
        (Scheme.IdealSheafData.comapIso_hom_fst I _)
    exact ⟨e1 ≪≫ pullbackOverIso ((BigHOver.toScheme B S hS).map h)
      ((BigHOver.toScheme B S hS).map z) I.subschemeι ez ≪≫ e3.symm⟩
  · exact (isPullback_restrictExc B S hS hwsite hsqsite h).map (BigHOver.toScheme B S hS)

/-- **The second step of the proof of Stacks 0EVI for an almost blowup square.** A presheaf on the
big h category over `S` which is a sheaf for the Zariski topology and satisfies condition (3) of
Stacks 0EVI sends every almost blowup square of the site whose modification is a closed immersion
and whose centre is locally principal to a cartesian square of sets.

This is the source's "in particular, if we have a blow up square such that `b : X' → X` is a
closed immersion and `Z` is a locally principal closed subscheme, then
`F(X) = F(X') ×_{F(E)} F(Z)`"; an almost blowup square supplies the two requirements
`AlgebraicGeometry.BigHOver.isPullback_of_isClosedImmersion_of_restrict_isIso` asks of the
modification. -/
public theorem isPullback_of_isClosedImmersion_of_isLocallyPrincipal
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    (h1 : BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F)
    (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hci : IsClosedImmersion ((BigHOver.toScheme B S hS).map b))
    (hprin : Stacks.Divisors.IsLocallyPrincipal I)
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hsq : IsPullback ((BigHOver.toScheme B S hS).map e) ((BigHOver.toScheme B S hS).map d)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) :=
  isPullback_of_isClosedImmersion_of_restrict_isIso B S hS F hzar h1 X X' Z E b z d e I hci
    hb.finitePresentation hprin
    (isIso_restrict_compl_support I ((BigHOver.toScheme B S hS).map b) hb) hZ hsq

end BigHOver

end AlgebraicGeometry

end
