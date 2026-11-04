module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FinitePresentationTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleSquare

/-!
# Transporting the hypotheses on the open across an elementary dévissage

The induction of [Stacks, Tag 0815] replaces the module `F` on `X/S` by the direct image
`π_* G` on the smooth scheme `Y` over the étale neighbourhood `V` of the base, where
`(Z, Y, π, i, h)` is an elementary dévissage ([Stacks, Tag 057S]) of `F` at a point. For the
induction to continue, the two hypotheses carried over the quasi-compact open `U ⊆ S` — finite
presentation of `F` there and flatness of `F` over `U` — must be inherited by `π_* G` over the
inverse image `W` of `U` in `V`.

They are, because both are insensitive to the two moves that relate the two modules: direct
image along an affine morphism, and the dévissage's identification of `i_* G` with the pullback
of `F` to the source neighbourhood.

## Main results

* `AlgebraicGeometry.isFinitePresentation_pullback_iff_finitePushforward`: over an open of the
  target, finite presentation of a module passes to and from its direct image along a finite
  morphism of finite presentation there.
* `AlgebraicGeometry.isFlatOver_restrict_iff_affinePushforward`: over an open of the base,
  flatness over the base passes to and from the direct image along an affine morphism.
* `AlgebraicGeometry.ElementaryDevissage.pushforward_isFinitePresentation_onOpen` and
  `AlgebraicGeometry.ElementaryDevissage.pushforward_isFlatOver_onOpen`: the two transports.

## Implementation notes

Finite presentation of `π`, which both transports need, is
`AlgebraicGeometry.ElementaryDevissage.finitePresentation_π`
(`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/FinitePresentationTransfer.lean`), where it
carries the clause registration for Tag 057T, "finite presentation of π".

The flatness transport uses the direct-image criterion [Stacks, Tag 0FLM]
(`AlgebraicGeometry.isFlatOver_pushforward_iff`) over the restricted morphisms; the restriction
of an affine morphism to the preimage of an open is affine, being a base change of it.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
* [Stacks Project, Tag 057T](https://stacks.math.columbia.edu/tag/057T)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Direct image along a finite morphism, over an open -/

/-- **Finite presentation over an open passes to and from the direct image along a finite
morphism.** The restriction of the direct image to an open of the target is the direct image of
the restriction, so this is [Stacks, Tag 01XZ] for the restricted morphism, which is of finite
presentation by hypothesis. -/
theorem isFinitePresentation_pullback_iff_finitePushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (V : Y.Opens) (hfV : FinitePresentation (f ∣_ V)) (F : X.Modules)
    [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F).IsFinitePresentation ↔
      ((Scheme.Modules.pullback V.ι).obj
        ((Scheme.Modules.pushforward f).obj F)).IsFinitePresentation := by
  have : (F.restrict (f ⁻¹ᵁ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ V).ι F
  have eF : F.restrict (f ⁻¹ᵁ V).ι ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F :=
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F
  have eG : (Scheme.Modules.pushforward (f ∣_ V)).obj (F.restrict (f ⁻¹ᵁ V).ι) ≅
      (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward f).obj F) :=
    (Stacks.LocalCohomology.schemePushforwardRestrictIso f V).app F ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        ((Scheme.Modules.pushforward f).obj F)
  have hfin := isFinitePresentation_iff_pushforward_isFinitePresentation (f ∣_ V) hfV
    (F.restrict (f ⁻¹ᵁ V).ι)
  exact ((SheafOfModules.isFinitePresentation
      (f ⁻¹ᵁ V).toScheme.ringCatSheaf).prop_iff_of_iso eF).symm.trans
    (hfin.trans ((SheafOfModules.isFinitePresentation
      V.toScheme.ringCatSheaf).prop_iff_of_iso eG))

/-! ### Direct image along an affine morphism, over an open -/

/-- **Flatness over the base, on the preimage of an open, passes to and from the direct image
along an affine morphism.** This is [Stacks, Tag 0FLM] applied to the restricted morphisms,
whose composite is the restriction of the composite. -/
theorem isFlatOver_restrict_iff_affinePushforward {X Y S : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)
    [IsAffineHom g] (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) :
    IsFlatOver ((g ≫ f) ∣_ U).toLRSHom.toShHom
        ((Scheme.Modules.pullback ((g ≫ f) ⁻¹ᵁ U).ι).obj F) ↔
      IsFlatOver (f ∣_ U).toLRSHom.toShHom
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
          ((Scheme.Modules.pushforward g).obj F)) := by
  have : IsAffineHom (g ∣_ (f ⁻¹ᵁ U)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict g (f ⁻¹ᵁ U)).flip inferInstance
  let : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F)
  have : ((Scheme.Modules.pullback (g ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).obj F).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (g ⁻¹ᵁ (f ⁻¹ᵁ U)).ι.toLRSHom.toShHom F inferInstance
  have e : (Scheme.Modules.pushforward (g ∣_ (f ⁻¹ᵁ U))).obj
        ((Scheme.Modules.pullback (g ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).obj F) ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pushforward g).obj F) :=
    (Scheme.Modules.pushforward (g ∣_ (f ⁻¹ᵁ U))).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).app F).symm ≪≫
      (Stacks.LocalCohomology.schemePushforwardRestrictIso g (f ⁻¹ᵁ U)).app F ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
        ((Scheme.Modules.pushforward g).obj F)
  have h := isFlatOver_pushforward_iff (g ∣_ (f ⁻¹ᵁ U)) (f ∣_ U)
    ((Scheme.Modules.pullback (g ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).obj F)
  have hcomp : (g ∣_ (f ⁻¹ᵁ U)) ≫ (f ∣_ U) = (g ≫ f) ∣_ U := (morphismRestrict_comp g f U).symm
  rw [hcomp] at h
  exact h.trans (forall_congr' fun x ↦ isFlatOverAt_iff_of_moduleIso (f ∣_ U).toLRSHom.toShHom e x)

/-! ### The two transports across a dévissage -/

namespace ElementaryDevissage

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
  (hx : f.asFiber x ∈
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))

/-- **Finite presentation over the open survives the dévissage.** If the pullback of `F` to the
source neighbourhood is of finite presentation over the preimage of an open `W` of the base
neighbourhood, then so is the direct image `π_* G` over the preimage of `W` in the smooth
scheme. -/
theorem pushforward_isFinitePresentation_onOpen [LocallyOfFinitePresentation f]
    (D : ElementaryDevissage f F x hx) (W : D.V.scheme.Opens)
    (hfp : ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ W).ι).obj
      ((Scheme.Modules.pullback D.U.toBase).obj F)).IsFinitePresentation) :
    ((Scheme.Modules.pullback (D.h ⁻¹ᵁ W).ι).obj
      ((Scheme.Modules.pushforward D.π).obj D.G)).IsFinitePresentation := by
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  have : IsClosedImmersion D.i := D.closedImmersion
  have : IsFinite D.i := inferInstance
  have : IsFinite D.π := D.finite_π
  have hfp_restrict : ∀ {A B : Scheme.{u}} (g : A ⟶ B) [LocallyOfFinitePresentation g]
      [IsFinite g] (V : B.Opens), FinitePresentation (g ∣_ V) :=
    by intros; exact ⟨inferInstance, inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation D.i := D.finitePresentation.1
  have : LocallyOfFinitePresentation D.π := D.finitePresentation_π.1
  have hpushI : ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ W).ι).obj
      ((Scheme.Modules.pushforward D.i).obj D.G)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation
      (D.toBase ⁻¹ᵁ W).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ W).ι).mapIso D.sheafIso).symm hfp
  have hG : ((Scheme.Modules.pullback (D.i ⁻¹ᵁ (D.toBase ⁻¹ᵁ W)).ι).obj
      D.G).IsFinitePresentation :=
    (isFinitePresentation_pullback_iff_finitePushforward D.i (D.toBase ⁻¹ᵁ W) (hfp_restrict _ _)
      D.G).mpr hpushI
  have heq : D.i ⁻¹ᵁ (D.toBase ⁻¹ᵁ W) = D.π ⁻¹ᵁ (D.h ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, D.commutes_closed]
  rw [heq] at hG
  exact (isFinitePresentation_pullback_iff_finitePushforward D.π (D.h ⁻¹ᵁ W)
    (hfp_restrict _ _) D.G).mp hG

/-- **Flatness over the open survives the dévissage.** If the pullback of `F` to the source
neighbourhood is flat over an open `W` of the base neighbourhood, then so is the direct image
`π_* G` over `W`. -/
theorem pushforward_isFlatOver_onOpen (D : ElementaryDevissage f F x hx)
    (W : D.V.scheme.Opens)
    (hflat : IsFlatOver (D.toBase ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ W).ι).obj
        ((Scheme.Modules.pullback D.U.toBase).obj F))) :
    IsFlatOver (D.h ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.h ⁻¹ᵁ W).ι).obj
        ((Scheme.Modules.pushforward D.π).obj D.G)) := by
  have : IsClosedImmersion D.i := D.closedImmersion
  have : IsFinite D.π := D.finite_π
  have : D.G.IsQuasicoherent := D.quasicoherent_G
  have hpush : IsFlatOver (D.toBase ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ W).ι).obj
        ((Scheme.Modules.pushforward D.i).obj D.G)) := fun y ↦
    isFlatOverAt_of_moduleIso (D.toBase ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.toBase ⁻¹ᵁ W).ι).mapIso D.sheafIso).symm y (hflat y)
  have hG : IsFlatOver ((D.i ≫ D.toBase) ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback ((D.i ≫ D.toBase) ⁻¹ᵁ W).ι).obj D.G) :=
    (isFlatOver_restrict_iff_affinePushforward D.i D.toBase D.G W).mpr hpush
  rw [D.commutes_closed] at hG
  exact (isFlatOver_restrict_iff_affinePushforward D.π D.h D.G W).mp hG

end ElementaryDevissage

end AlgebraicGeometry

end
