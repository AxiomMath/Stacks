module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackRestrict
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSectionsDisjointOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleSquare

/-!
# The strict transform over the admissible open is the pullback

Let `f : X ⟶ S` be a morphism, `I` a centre on `S` supported away from an open `U ⊆ S`, and `F`
a module on `X`. Over the inverse image of `U` in the base change `X ×_S S'` the exceptional
divisor is absent, so the quotient defining the strict transform divides out nothing: the strict
transform of `F` *is* the pullback of `F` there.

Consequently the two properties of `F` that [Stacks, Tag 0815] assumes over `U` — finite
presentation and flatness over the base — are inherited by the strict transform over the inverse
image of `U`. That is what makes the induction of 0815 able to re-enter itself after a blowup:
the hypotheses on the open survive the blowup.

## Main results

* `AlgebraicGeometry.isIso_pullback_π_strictTransformSheaf_of_disjoint_support`: the quotient map
  onto the strict transform is an isomorphism over the inverse image of `U`.
* `AlgebraicGeometry.isFinitePresentation_strictTransformSheaf_on_admissible_open`: the strict
  transform is of finite presentation there.
* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_on_admissible_open`: the strict transform is
  flat over the blowup there.
* `AlgebraicGeometry.isFiniteType_strictTransformSheaf`: the strict transform of a module of
  finite type is of finite type, over the whole blowup.

## Implementation notes

The disjointness used is `Disjoint U (Supp I)`, one of the two conditions making the blowup
`U`-admissible; the other, finite presentation of the centre, plays no role here.

The vanishing of the supported sections over an open disjoint from the support is
`Stacks.Modules.isIso_pullback_supportedSections_quotient`, which is stated for
`AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule`; the strict transform is built from
`AlgebraicGeometry.Scheme.Modules.supportedSectionsι`, and the two submodules are the same
submodule — the sections whose germs vanish off the subset — so that statement applies
directly.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData) (F : X.Modules)

/-- The strict transform of a module of finite type is of finite type: it is a quotient of the
pullback of the module to the base change. -/
theorem isFiniteType_strictTransformSheaf [F.IsFiniteType] :
    (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F).IsFiniteType := by
  have _ : ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType
      (pullback.fst f (blowUpToBase I)).toLRSHom.toShHom F
  exact @Stacks.SheafOfModules.isFiniteType_of_epi'.{u} _ _ _ _ _ _ _ _ _
    (Stacks.StrictTransform.π f (blowUpToBase I) (exceptionalIdeal I) F) inferInstance
    (coequalizer.π_epi)

/-- The inverse image in the base change of an open of `S` disjoint from the support of the
centre is disjoint from the inverse image of the exceptional divisor. -/
theorem disjoint_preimage_exceptionalPreimage (U : S.Opens)
    (hUI : Disjoint (U : Set S) (I.support : Set S)) :
    Disjoint
      (((pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U) :
        (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens)) :
          Set (Stacks.StrictTransform.baseChange f (blowUpToBase I)))
      (Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I)) := by
  have hE : ((exceptionalIdeal I).support : Set (blowUp I)) =
      (blowUpToBase I).base ⁻¹' (I.support : Set S) := by
    show ((I.comap (blowUpToBase I)).support : Set (blowUp I)) = _
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
  show Disjoint ((pullback.snd f (blowUpToBase I)).base ⁻¹'
      ((blowUpToBase I).base ⁻¹' (U : Set S)))
    ((pullback.snd f (blowUpToBase I)).base ⁻¹'
      ((exceptionalIdeal I).support : Set (blowUp I)))
  rw [hE]
  exact ((hUI.preimage (blowUpToBase I).base).preimage
    (pullback.snd f (blowUpToBase I)).base)

/-- **Over the inverse image of an open disjoint from the centre, the strict transform is the
pullback.** The quotient map `pr_X^* F ⟶ F'` becomes an isomorphism there, because the sections
divided out are supported on the inverse image of the exceptional divisor, which that open
misses. -/
theorem isIso_pullback_π_strictTransformSheaf_of_disjoint_support (U : S.Opens)
    (hUI : Disjoint (U : Set S) (I.support : Set S)) :
    IsIso ((Scheme.Modules.pullback
        (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U)).ι).map
      (Stacks.StrictTransform.π f (blowUpToBase I) (exceptionalIdeal I) F)) :=
  Stacks.Modules.isIso_pullback_supportedSections_quotient
    ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F)
    (Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I))
    (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U))
    (disjoint_preimage_exceptionalPreimage f I U hUI)

/-- The two inverse images of an open `U ⊆ S` in the base change `X ×_S S'` agree. -/
private theorem preimage_fst_eq_preimage_snd (U : S.Opens) :
    pullback.fst f (blowUpToBase I) ⁻¹ᵁ (f ⁻¹ᵁ U) =
      pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]

/-- **The strict transform is of finite presentation over the admissible open.** There it is the
pullback of `F`, which is of finite presentation over the inverse image of `U` by hypothesis. -/
theorem isFinitePresentation_strictTransformSheaf_on_admissible_open (U : S.Opens)
    (hUI : Disjoint (U : Set S) (I.support : Set S))
    (hfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation) :
    ((Scheme.Modules.pullback
        (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U)).ι).obj
      (Stacks.StrictTransform.sheaf f (blowUpToBase I)
        (exceptionalIdeal I) F)).IsFinitePresentation := by
  have hP : ((Scheme.Modules.pullback
        (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U)).ι).obj
      ((Scheme.Modules.pullback
        (pullback.fst f (blowUpToBase I))).obj F)).IsFinitePresentation := by
    rw [← preimage_fst_eq_preimage_snd]
    exact Stacks.Modules.isFinitePresentation_pullback_on_preimage
      (pullback.fst f (blowUpToBase I)) F (f ⁻¹ᵁ U) hfp
  have hiso := isIso_pullback_π_strictTransformSheaf_of_disjoint_support f I F U hUI
  exact (SheafOfModules.isFinitePresentation
    (pullback.snd f (blowUpToBase I) ⁻¹ᵁ
      (blowUpToBase I ⁻¹ᵁ U)).toScheme.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ _ hiso) hP

/-- Flatness over the base, on the preimage of an open of the target, transports along a map of
modules which becomes an isomorphism there.

Stated for an arbitrary morphism and an arbitrary map of modules rather than for the quotient
map onto a strict transform: specialising the statement makes the elaborator unfold the strict
transform while checking the `whnf` of the restricted morphism, which exhausts the heartbeat
budget. -/
theorem isFlatOver_restrict_of_isIso_pullback_map {Y T : Scheme.{u}} (g : Y ⟶ T)
    {M N : Y.Modules} (α : M ⟶ N) (V : T.Opens)
    (hiso : IsIso ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).map α))
    (h : IsFlatOver (g ∣_ V).toLRSHom.toShHom
      ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M)) :
    IsFlatOver (g ∣_ V).toLRSHom.toShHom
      ((Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj N) :=
  fun x ↦ isFlatOverAt_of_moduleIso (g ∣_ V).toLRSHom.toShHom (@asIso _ _ _ _ _ hiso) x (h x)

/-- **The strict transform is flat over the blowup over the admissible open.** There it is the
pullback of `F`, which is flat over `U` by hypothesis, and flatness over the base is stable
under base change. -/
theorem isFlatOver_strictTransformSheaf_on_admissible_open (hF : F.IsQuasicoherent)
    (U : S.Opens) (hUI : Disjoint (U : Set S) (I.support : Set S))
    (hflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F)) :
    IsFlatOver (pullback.snd f (blowUpToBase I) ∣_ (blowUpToBase I ⁻¹ᵁ U)).toLRSHom.toShHom
      ((Scheme.Modules.pullback
          (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U)).ι).obj
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) := by
  let : F.IsQuasicoherent := hF
  let : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F)
  have hPqc : ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj
      F).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (pullback.fst f (blowUpToBase I)).toLRSHom.toShHom F hF
  have hPflat : IsFlatOver
      (pullback.snd f (blowUpToBase I) ∣_ (blowUpToBase I ⁻¹ᵁ U)).toLRSHom.toShHom
      ((Scheme.Modules.pullback
          (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U)).ι).obj
        ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F)) := by
    refine @isFlatOver_restrict_of_flatOnPreimage _ _ (pullback.snd f (blowUpToBase I))
      _ hPqc (blowUpToBase I ⁻¹ᵁ U) fun x hx ↦ ?_
    have hpx : f (pullback.fst f (blowUpToBase I) x) ∈ U := by
      have : x ∈ pullback.fst f (blowUpToBase I) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
        rw [preimage_fst_eq_preimage_snd]; exact hx
      simpa using this
    exact modulePullback_isFlatOverAt (IsPullback.of_hasPullback f (blowUpToBase I)) F x
      (isFlatOverAt_of_open_restriction f F U (pullback.fst f (blowUpToBase I) x) hpx hflat)
  exact isFlatOver_restrict_of_isIso_pullback_map (pullback.snd f (blowUpToBase I))
    (Stacks.StrictTransform.π f (blowUpToBase I) (exceptionalIdeal I) F)
    (blowUpToBase I ⁻¹ᵁ U)
    (isIso_pullback_π_strictTransformSheaf_of_disjoint_support f I F U hUI) hPflat

end AlgebraicGeometry

end
