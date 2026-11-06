module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismAgreementNearClosedSubset
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumOfAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# A proper modification and the algebraization over the spectrum of an adic completion agree

Let `V` be an object of the big fppf site of `S` whose underlying scheme `X` is affine with
Noetherian ring of global sections `A`, let `I ⊆ A` be an ideal with zero locus `T`, let
`f : X' ⟶ X` be a proper morphism of algebraic spaces, and let `w' : X' ⟶ W` and
`ŵ : X_{/T} ⟶ W` be morphisms to an algebraic space `W` inducing the same morphism
`X'_{/T} ⟶ W`. Let `h : Spec Â ⟶ W` be a morphism agreeing with `ŵ` on every morphism into the
spectrum of the `I`-adic completion `Â` with image in `V(I)` (as produced by
`AlgebraicGeometry.Space.exists_adicCompletionObj_hom_app_eq`). Then `h` and `w'` agree on the
fibre product `Y = X' ×_X Spec Â`. This is step F2 of the existence half of Stacks 0GI3: on the
part of `Y` over `X ∖ T`, where `f` is an isomorphism, it identifies `h` with the given morphism.

## Main results

* `AlgebraicGeometry.Space.comp_eq_comp_of_isProper_of_adicCompletionObj`: for morphisms
  `g₁ : Z ⟶ X'` and `g₂ : Z ⟶ Spec Â` agreeing over `X`, `g₁ ≫ w' = g₂ ≫ h`.

## Implementation notes

The two composites `Y ⟶ W` agree on the completion of `Y` along the inverse image `T_Y` of `T`:
a section of `Y` with image in `T_Y` projects to a morphism into `Spec Â` with image in `V(I)`,
on which `h` is the value of `ŵ`, and to a section of `X'` with image in `|f|⁻¹ T`, on which
`w'` is the value of `ŵ` by the compatibility of `w'` and `ŵ`. So
`AlgebraicGeometry.Space.eq_of_completion_eq_of_closed_meets` applies once `Y` is locally
Noetherian and `T_Y` meets every nonempty closed subset of `|Y|`. The first holds because `Y` is
of finite type over the Noetherian scheme `Spec Â` (Stacks 0316 for `Â`). For the second, the
image of a nonempty closed subset of `|Y|` in `Spec Â` is closed, `Y ⟶ Spec Â` being proper; it
contains a closed point, which lies in `V(I Â)` because `I Â` is contained in the Jacobson
radical of the complete ring `Â` (Mathlib's `IsAdicComplete.le_jacobson_bot`), and so lies over
`T`.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_modificationAgreement
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Over `Spec Â`, the closed subset of `X' ×_V Spec Â` lying over `T` meets every nonempty
closed subset: its image in `Spec Â` is closed and contains a closed point, which lies over
`V(I)` since `I Â` is contained in the Jacobson radical of `Â`. -/
theorem inter_preimage_nonempty_of_isProper_adicCompletionObj
    {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    {T : Set (points B S hS (yoneda.obj V))}
    (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (f : X' ⟶ yoneda.obj V) (hf : IsProper B S hS f)
    (C : Set (points B S hS (pullback (yoneda.map (adicCompletionObjHom B S hS V I)) f)))
    (hC : IsClosed C) (hCne : C.Nonempty) :
    (C ∩ pointsMap B S hS _ (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f) ⁻¹'
      (pointsMap B S hS X' f ⁻¹' T)).Nonempty := by
  have hXh : IsAlgebraicSpace B S hS (yoneda.obj (adicCompletionObj B S hS V I)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hpr : IsProper B S hS (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f) :=
    isProper_pullback_fst B S hS hX' (isAlgebraicSpace_yoneda B S hS V) hXh f _ hf
  have hclosed : IsClosedMap (pointsMap B S hS _
      (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f)) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS _
      ((IsProper.universallyClosed B S hS hpr) _ hXh (𝟙 _))
  have hK : IsClosed (pointsToScheme B S hS (adicCompletionObj B S hS V I) ''
      (pointsMap B S hS _ (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f) ''
        C) : Set (PrimeSpectrum
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) :=
    (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS
      (adicCompletionObj B S hS V I) _).mp (hclosed C hC)
  obtain ⟨c₀, hc₀⟩ := hCne
  obtain ⟨M, ⟨_, ⟨c, hc, rfl⟩, hcM⟩, hMcl⟩ := hK.exists_closed_singleton
    ⟨_, ⟨_, ⟨c₀, hc₀, rfl⟩, rfl⟩⟩
  refine ⟨c, hc, ?_⟩
  have hIM : I ≤ Ideal.comap (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) M.asIdeal := by
    have := AdicCompletion.isAdicComplete_self I (Ideal.fg_of_isNoetherianRing I)
    exact Ideal.map_le_iff_le_comap.mp ((IsAdicComplete.le_jacobson_bot _).trans
      (sInf_le ⟨bot_le, (PrimeSpectrum.isClosed_singleton_iff_isMaximal M).mp hMcl⟩))
  show pointsMap B S hS X' f (pointsMap B S hS _ (pullback.snd _ f) c) ∈ T
  rw [← Function.comp_apply (f := pointsMap B S hS X' f), ← pointsMap_comp,
    ← pullback.condition, pointsMap_comp, Function.comp_apply, hTI,
    pointsToScheme_pointsMap_yoneda, hcM]
  exact (Set.ext_iff.mp (Scheme.isoSpec_inv_preimage_zeroLocus _
    (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) M)).mpr hIM

/-- The composites `X' ×_V Spec Â ⟶ Spec Â ⟶ W` (through `h`) and `X' ×_V Spec Â ⟶ X' ⟶ W`
(through `w'`) agree on the completion of `X' ×_V Spec Â` along the inverse image of `T`. -/
theorem completion_comp_pullback_fst_eq_snd_of_adicCompletionObj
    {X' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    {T : Set (points B S hS (yoneda.obj V))} (f : X' ⟶ yoneda.obj V) (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    (h : yoneda.obj (adicCompletionObj B S hS V I) ⟶ W)
    (hh : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ adicCompletionObj B S hS V I)
      (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ adicCompletionObjHom B S hS V I)),
      h.app (op Zo) z =
        (ŵ.app (op Zo) ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).down) :
    (completionSubfunctor B S hS _ (pointsMap B S hS _
      (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f) ⁻¹'
        (pointsMap B S hS X' f ⁻¹' T))).ι ≫
      Functor.whiskerRight (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f ≫ h)
        uliftFunctor.{u + 1} =
    (completionSubfunctor B S hS _ (pointsMap B S hS _
      (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f) ⁻¹'
        (pointsMap B S hS X' f ⁻¹' T))).ι ≫
      Functor.whiskerRight (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f ≫ w')
        uliftFunctor.{u + 1} := by
  ext Zo s
  obtain ⟨Zo⟩ := Zo
  obtain ⟨⟨y⟩, hy⟩ := s
  show ULift.up (h.app (op Zo)
      ((pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f).app (op Zo) y)) =
    ULift.up (w'.app (op Zo)
      ((pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f).app (op Zo) y))
  congr 1
  have hy' : HasImageIn B S hS _ (pointsMap B S hS _
      (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f ≫
        yoneda.map (adicCompletionObjHom B S hS V I)) ⁻¹' T) Zo y := by
    rwa [pullback.condition, pointsMap_comp]
  have hz : HasImageIn B S hS (yoneda.obj V) T Zo
      ((pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f).app (op Zo) y ≫
        adicCompletionObjHom B S hS V I) := ((completionMap B S hS (pullback.fst (yoneda.map
    (adicCompletionObjHom B S hS V I)) f ≫ yoneda.map (adicCompletionObjHom B S hS V I)) T).app
      (op Zo) ⟨ULift.up y, hy'⟩).2
  have hx' : HasImageIn B S hS X' (pointsMap B S hS X' f ⁻¹' T) Zo
      ((pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f).app (op Zo) y) :=
    ((completionMap B S hS (pullback.snd (yoneda.map
    (adicCompletionObjHom B S hS V I)) f) (pointsMap B S hS X' f ⁻¹' T)).app
      (op Zo) ⟨ULift.up y, hy⟩).2
  have hfy : (pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f).app (op Zo) y ≫
      adicCompletionObjHom B S hS V I =
      f.app (op Zo) ((pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f).app
        (op Zo) y) := by
    have := congrArg (fun α => α.app (op Zo) y)
      (pullback.condition (f := yoneda.map (adicCompletionObjHom B S hS V I)) (g := f))
    simp only [NatTrans.comp_app_apply] at this
    exact this
  have hs : (⟨ULift.up ((pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f).app
        (op Zo) y ≫ adicCompletionObjHom B S hS V I), hz⟩ :
        (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor.obj (op Zo)) =
      (completionMap B S hS f T).app (op Zo)
        ⟨ULift.up ((pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f).app
          (op Zo) y), hx'⟩ :=
    Subtype.ext (congrArg ULift.up hfy)
  rw [hh Zo _ hz, hs]
  exact congrArg ULift.down (congrArg (fun α => α.app (op Zo)
    ⟨ULift.up ((pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f).app
      (op Zo) y), hx'⟩) hcompat)

/-- **Step F2 of Stacks 0GI3.** Let `V` be an affine object of the site with Noetherian ring of
global sections `A`, let `T ⊆ |V|` be the zero locus of an ideal `I ⊆ A`, let `f : X' ⟶ V` be a
proper morphism from an algebraic space, and let `w' : X' ⟶ W` and `ŵ : V_{/T} ⟶ W` be morphisms
to an algebraic space inducing the same morphism `X'_{/T} ⟶ W`. If `h : Spec Â ⟶ W` agrees with
`ŵ` on every morphism into `Spec Â` with image in `V(I)`, then `h` and `w'` agree on
`X' ×_V Spec Â`: for all `g₁ : Z ⟶ X'` and `g₂ : Z ⟶ Spec Â` with `g₁ ≫ f = g₂ ≫ κ`, one has
`g₁ ≫ w' = g₂ ≫ h`. -/
theorem comp_eq_comp_of_isProper_of_adicCompletionObj
    {X' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hW : IsAlgebraicSpace B S hS W)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    {T : Set (points B S hS (yoneda.obj V))}
    (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (f : X' ⟶ yoneda.obj V) (hf : IsProper B S hS f)
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    (h : yoneda.obj (adicCompletionObj B S hS V I) ⟶ W)
    (hh : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ adicCompletionObj B S hS V I)
      (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ adicCompletionObjHom B S hS V I)),
      h.app (op Zo) z =
        (ŵ.app (op Zo) ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).down)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g₁ : Z ⟶ X')
    (g₂ : Z ⟶ yoneda.obj (adicCompletionObj B S hS V I))
    (hg : g₁ ≫ f = g₂ ≫ yoneda.map (adicCompletionObjHom B S hS V I)) :
    g₁ ≫ w' = g₂ ≫ h := by
  have hXh : IsAlgebraicSpace B S hS (yoneda.obj (adicCompletionObj B S hS V I)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hY : IsAlgebraicSpace B S hS
      (pullback (yoneda.map (adicCompletionObjHom B S hS V I)) f) :=
    isAlgebraicSpace_pullback B S hS _ f hXh hX' hV
  have hXhnoeth : HasEtaleLocalProperty B S hS (yoneda.obj (adicCompletionObj B S hS V I))
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
    hasEtaleLocalProperty_of_representable B S hS _ (fun V : Scheme.{u} => IsLocallyNoetherian V)
      (adicCompletionObj B S hS V I) (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian
        (Spec (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))))
  have hYnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hY hXh _
    (IsProper.isFiniteType B S hS (isProper_pullback_fst B S hS hX' hV hXh f _ hf)).1 hXhnoeth
  have hTclosed : IsClosed T := by
    rw [isClosed_pointTopology_yoneda_iff_isClosed_image]
    convert Scheme.zeroLocus_isClosed ((BigFppfOver.toScheme B S hS).obj V)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) using 1
    ext y
    obtain ⟨x, rfl⟩ := surjective_pointsToScheme B S hS V y
    rw [(injective_pointsToScheme B S hS V).mem_set_image, hTI]
  have hTYclosed : IsClosed (pointsMap B S hS _
      (pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f) ⁻¹'
        (pointsMap B S hS X' f ⁻¹' T)) :=
    (hTclosed.preimage (continuous_pointsMap B S hS f)).preimage (continuous_pointsMap B S hS _)
  calc g₁ ≫ w' = pullback.lift g₂ g₁ hg.symm ≫
        pullback.snd (yoneda.map (adicCompletionObjHom B S hS V I)) f ≫ w' := by
        rw [pullback.lift_snd_assoc]
    _ = pullback.lift g₂ g₁ hg.symm ≫
        pullback.fst (yoneda.map (adicCompletionObjHom B S hS V I)) f ≫ h := by
      rw [eq_of_completion_eq_of_closed_meets B S hS hY hW hYnoeth hTYclosed
        (inter_preimage_nonempty_of_isProper_adicCompletionObj B S hS hX' V I hTI f hf) _ _
        (completion_comp_pullback_fst_eq_snd_of_adicCompletionObj B S hS V I f w' ŵ hcompat h hh)]
    _ = g₂ ≫ h := by rw [pullback.lift_fst_assoc]

end Space

end AlgebraicGeometry

end
