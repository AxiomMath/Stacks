module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectCompatibility
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerTorsion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerIdeal
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModificationMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperTowerAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismSmallerBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubsetReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.RingTheory.LocalRing.AdicCompleteRingEquiv
public import StacksFrontier.RingTheory.AdicCompletion.Basic

/-!
# From the tower form of Stacks 0A4Z to the completion form

Let `V = Spec R` for a Noetherian complete local ring `R`, let `Z = V(I) ⊆ |V|` be closed and
contain the closed point, and let `p : Y ⟶ V` be proper. A morphism `μ : Y_{/|p|⁻¹Z} ⟶ X'_{/T'}`
restricts to compatible morphisms `g_n : Y ×_V Spec(R/Iⁿ⁺¹) ⟶ X'`; if these come from one
`y : Y ⟶ X'` (the tower form of Stacks 0A4Z over spectra,
`AlgebraicGeometry.Space.HasProperTowerAlgebraizationOverSpec`), then `y` carries `|p|⁻¹ Z`
into `T'` and its completion is `μ`: over an affine test object every section of
`Y_{/|p|⁻¹Z}` factors through some thickening (`I` is finitely generated), and morphisms out of a
completion are determined over affine objects.

## Main results

The elided prefix is `AlgebraicGeometry.Artin.ContractionSituation`.

* `hasCompletionAlgebraization_of_hasProperTowerAlgebraizationOverSpec`: the completion form of
  0A4Z for `X'` from the tower form.
* `hasEffectiveFormalObjects_of_hasProperTowerAlgebraizationOverSpec`: Stacks 0GI8 from the tower
  form.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing Deformation.Artin

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace Space

/-- Two morphisms out of the completion `F_{/T}` of a presheaf agree as soon as they agree on
the sections given by sections of `F` over affine objects with image in `T`. -/
theorem completionSheaf_hom_ext_of_forall_isAffine {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (points B S hS F)} {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {φ ψ : completionSheaf B S hS F T ⟶ G}
    (H : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (t : F.obj (op U)) (ht : HasImageIn B S hS F T U t),
        φ.hom.app (op U) (FormalSpace.presheafSection B S hS t ht) =
          ψ.hom.app (op U) (FormalSpace.presheafSection B S hS t ht)) :
    φ = ψ := by
  apply Sheaf.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _ G.property
  ext U ⟨⟨x⟩, hx⟩
  change φ.hom.app U (FormalSpace.presheafSection B S hS x hx) =
    ψ.hom.app U (FormalSpace.presheafSection B S hS x hx)
  have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  refine Functor.IsCoverDense.ext (BigAffineFppf.inclusion B S hS) G U.unop fun V f => ?_
  have hx' : HasImageIn B S hS F T _ (F.map f.op x) :=
    ((completionSubfunctor B S hS F T).map f.op hx :)
  have key : ∀ θ : completionSheaf B S hS F T ⟶ G,
      G.obj.map f.op (θ.hom.app U (FormalSpace.presheafSection B S hS x hx)) =
        θ.hom.app (op ((BigAffineFppf.inclusion B S hS).obj V))
          (FormalSpace.presheafSection B S hS (F.map f.op x) hx') := by
    intro θ
    rw [← FormalSpace.presheafSection_map (F := F) (TF := T) B S hS f x hx hx']
    exact (NatTrans.naturality_apply θ.hom f.op _).symm
  rw [key φ, key ψ]
  exact H _ V.property _ hx'

end Space

namespace Artin.ContractionSituation

variable (c : ContractionSituation B S hS)

attribute [local instance] Space.pointTopology

/-- **The completion form of Stacks 0A4Z from its tower form.** If compatible morphisms on the
thickenings of proper algebraic spaces into `X'` algebraize, then so do morphisms from their
completions into `X'_{/T'}`. -/
theorem hasCompletionAlgebraization_of_hasProperTowerAlgebraizationOverSpec
    (h : Space.HasProperTowerAlgebraizationOverSpec c.X') : c.HasCompletionAlgebraization := by
  intro A hA Z hZ hZ0 Y hY p hp μ
  let V := baseOver B S hS A (A.contains_spec_of_contains_truncation hA)
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    inferInstanceAs (IsAffine (Spec (.of A.R)))
  obtain ⟨I, hTI⟩ := Space.exists_ideal_mem_iff_mem_zeroLocus B S hS V hZ
  -- the ring of global sections of `V` is a Noetherian `I`-adically complete local ring
  let e : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ≃+* A.R :=
    (Scheme.ΓSpecIso (CommRingCat.of A.R)).commRingCatIsoToRingEquiv
  have := A.noetherian
  have hN : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    isNoetherianRing_of_ringEquiv A.R e.symm
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) := e.toEquiv.nontrivial
  have : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  have : IsAdicComplete (maximalIdeal A.R) A.R := A.complete
  have hmΓ : IsAdicComplete (maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    isAdicComplete_maximalIdeal_of_ringEquiv e.symm
  have hcl := (hTI _).1 (closedPoint_mem_of_hasImageIn A hA hZ0)
  have hIm : I ≤ maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) := by
    intro f hf
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [Scheme.mem_zeroLocus_iff] at hcl
    exact hcl f hf (by rw [Scheme.basicOpen_of_isUnit _ hu]; trivial)
  have hIc : IsAdicComplete I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete hIm hmΓ (IsNoetherian.noetherian I)
  -- the thickenings `Y_n = Y ×_V Spec(A/Iⁿ⁺¹)` map into `Y_{/|p|⁻¹Z}`
  let ιn : ∀ n : ℕ, Space.adicCompletionQuotientObj B S hS V I (n + 1) ⟶ V := fun n =>
    Space.adicCompletionQuotientObjHom B S hS V I (n + 1)
  let F := Space.pointsMap B S hS Y p ⁻¹' Z
  have hYn : ∀ (n : ℕ) (U : (BigFppfOver B S hS)ᵒᵖ)
      (s : (pullback p (yoneda.map (ιn n))).obj U),
      Space.HasImageIn B S hS Y F U.unop ((pullback.fst p (yoneda.map (ιn n))).app U s) := by
    intro n U s
    refine (FormalSpace.hasImageIn_preimage_iff B S hS p Z U.unop _).2 ?_
    have hc : p.app U ((pullback.fst p (yoneda.map (ιn n))).app U s) =
        (pullback.snd p (yoneda.map (ιn n))).app U s ≫ ιn n :=
      congrFun (congrArg (fun φ => φ.app U) (pullback.condition (f := p)
        (g := yoneda.map (ιn n)))) s
    rw [hc]
    exact ((Space.completionSubfunctor B S hS (yoneda.obj V) Z).map
      ((pullback.snd p (yoneda.map (ιn n))).app U s).op
      (Space.hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI (n + 1)) :)
  let κ : ∀ n : ℕ, pullback p (yoneda.map (ιn n)) ⋙ uliftFunctor.{u + 1} ⟶
      (Space.completionSubfunctor B S hS Y F).toFunctor := fun n =>
    Subfunctor.lift (Functor.whiskerRight (pullback.fst p (yoneda.map (ιn n))) uliftFunctor)
      (by
        rintro U _ ⟨s, rfl⟩
        exact hYn n U s.down)
  have hX'u : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (c.X' ⋙ uliftFunctor.{u + 1}) :=
    FormalSpace.isSheaf_comp_uliftFunctor B S hS c.isAlgebraicSpace_X'
  let g' : ∀ n : ℕ, pullback p (yoneda.map (ιn n)) ⋙ uliftFunctor.{u + 1} ⟶
      c.X' ⋙ uliftFunctor.{u + 1} := fun n =>
    κ n ≫ (BigFppfOver.topology B S hS).toSheafify _ ≫ μ.hom ≫
      (Space.completionSheafInclusion B S hS c.X' c.T').hom ≫
        ((BigFppfOver.topology B S hS).isoSheafify hX'u).inv
  choose g hg using fun n => Space.exists_whiskerRight_eq B S hS (g' n)
  have hκ : ∀ n, Functor.whiskerRight (Space.properThickeningTransition I p n) uliftFunctor ≫
      κ (n + 1) = κ n := by
    intro n
    ext U s
    refine Subtype.ext (ULift.ext ?_)
    change (pullback.fst p _).app U ((Space.properThickeningTransition I p n).app U s.down) =
      (pullback.fst p _).app U s.down
    rw [← NatTrans.comp_app_apply, Space.properThickeningTransition, pullback.lift_fst]
  have hcompat : ∀ n, Space.properThickeningTransition I p n ≫ g (n + 1) = g n := by
    intro n
    apply ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (u + 1))).obj uliftFunctor.{u + 1}).map_injective
    change Functor.whiskerRight _ _ = Functor.whiskerRight _ _
    rw [Functor.whiskerRight_comp, hg, hg]
    simp only [g', ← Category.assoc, hκ]
  obtain ⟨y, hy⟩ := h A.R (A.contains_spec_of_contains_truncation hA)
    (ObjectProperty.homMk A.toS) I A.noetherian hIc Y hY p hp g hcompat
  -- over affine objects, sections of `Y_{/|p|⁻¹Z}` come from thickenings
  have key : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (t : Y.obj (op U)) (ht : Space.HasImageIn B S hS Y F U t),
        (Space.completionSheafInclusion B S hS c.X' c.T').hom.app (op U)
          (μ.hom.app (op U) (FormalSpace.presheafSection B S hS t ht)) =
        ((BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1})).app (op U)
          (ULift.up (y.app (op U) t)) := by
    intro U hU t ht
    have ht' : Space.HasImageIn B S hS (yoneda.obj V) Z U (p.app _ t) :=
      (FormalSpace.hasImageIn_preimage_iff B S hS p Z U t).1 ht
    obtain ⟨N, hN'⟩ := Scheme.exists_pow_le_ker_appTop ((BigFppfOver.toScheme B S hS).map
      (p.app _ t)) I (IsNoetherian.noetherian I)
      (Space.toScheme_map_mem_zeroLocus_of_hasImageIn hTI ht')
    obtain ⟨t', ht''⟩ := (Space.exists_comp_adicCompletionQuotientObjHom_iff V I (p.app _ t)
      (N + 1)).2 ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN')
    let σ : yoneda.obj U ⟶ pullback p (yoneda.map (ιn N)) :=
      pullback.lift (yonedaEquiv.symm t) (yoneda.map t') (by
        rw [← Functor.map_comp, ht'', yonedaEquiv_symm_naturality_right]
        exact (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map _).symm)
    let s : (pullback p (yoneda.map (ιn N))).obj (op U) := yonedaEquiv σ
    have hs : (pullback.fst p (yoneda.map (ιn N))).app _ s = t := by
      change yonedaEquiv (σ ≫ pullback.fst _ _) = t
      rw [pullback.lift_fst, Equiv.apply_symm_apply]
    have hys : y.app _ t = (g N).app _ s := by
      rw [← hs, ← hy N]
      rfl
    have hg's : (g' N).app (op U) (ULift.up s) = ULift.up ((g N).app _ s) := by
      rw [← hg N]
      rfl
    have hps : ((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS Y F).toFunctor).app (op U) ((κ N).app _ (ULift.up s)) =
        FormalSpace.presheafSection B S hS t ht := by
      change ((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS Y F).toFunctor).app (op U)
        ⟨ULift.up ((pullback.fst p (yoneda.map (ιn N))).app _ s), _⟩ = _
      exact FormalSpace.presheafSection_congr B S hS hs _ ht
    have h1 : ((BigFppfOver.topology B S hS).isoSheafify hX'u).inv.app (op U)
        ((Space.completionSheafInclusion B S hS c.X' c.T').hom.app (op U)
          (μ.hom.app (op U) (FormalSpace.presheafSection B S hS t ht))) =
        ULift.up (y.app (op U) t) := by
      rw [hys, ← hg's, ← hps]
      rfl
    rw [← h1]
    change _ = (((BigFppfOver.topology B S hS).isoSheafify hX'u).inv ≫
      ((BigFppfOver.topology B S hS).isoSheafify hX'u).hom).app (op U) _
    rw [Iso.inv_hom_id]
    rfl
  -- the completion of `y` on a section given by a section of `Y`
  have hsec : ∀ (U : BigFppfOver B S hS) (t : Y.obj (op U)) (ht : Space.HasImageIn B S hS Y F U t),
      (Space.sheafifiedULiftMap B S hS y).hom.app (op U)
        ((Space.completionSheafInclusion B S hS Y F).hom.app (op U)
          (FormalSpace.presheafSection B S hS t ht)) =
        ((BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1})).app (op U)
          (ULift.up (y.app (op U) t)) := by
    intro U t ht
    rw [FormalSpace.inclusion_presheafSection]
    exact congrFun (congrArg (fun φ => φ.app (op U))
      ((BigFppfOver.topology B S hS).toSheafify_naturality
        (Functor.whiskerRight y uliftFunctor.{u + 1}))).symm (ULift.up t)
  -- the completion of `y` agrees with `μ` after the inclusion into `X'`
  have hincl : Space.completionSheafInclusion B S hS Y F ≫ Space.sheafifiedULiftMap B S hS y =
      μ ≫ Space.completionSheafInclusion B S hS c.X' c.T' :=
    Space.completionSheaf_hom_ext_of_forall_isAffine fun U hU t ht =>
      (hsec U t ht).trans (key U hU t ht).symm
  -- `y` carries `|p|⁻¹ Z` into `T'`
  have hT : F ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T' := by
    intro x hx
    obtain ⟨pK, rfl⟩ := Quot.exists_rep x
    have hv : Space.HasImageIn B S hS Y F pK.siteObject pK.value := by
      rw [Space.hasImageIn_iff_range_subset, Space.range_pointsMap_yonedaEquiv_symm]
      exact Set.singleton_subset_iff.2 hx
    have hyv : Space.HasImageIn B S hS c.X' c.T' pK.siteObject (y.app _ pK.value) :=
      hasImageIn_of_completionSheafInclusion_app_eq c.isAlgebraicSpace_X'.isSheaf
        hX'u (μ.hom.app _ (FormalSpace.presheafSection B S hS pK.value hv)) _
        (congrFun (congrArg (fun φ => φ.hom.app (op pK.siteObject)) hincl.symm)
          (FormalSpace.presheafSection B S hS pK.value hv) |>.trans (hsec _ _ hv))
    rw [Space.hasImageIn_iff_range_subset] at hyv
    have hr := Space.range_pointsMap_yonedaEquiv_symm B S hS
      (Space.FieldValuedPoint.map B S hS Y y pK)
    exact hyv (hr.symm.subset (Set.mem_singleton _))
  refine ⟨y, hT, ?_⟩
  refine (Space.mono_completionSheafInclusion B S hS c.X' c.T').right_cancellation _ _ ?_
  rw [Space.completionSheafRestrict_comp_inclusion]
  exact hincl

/-- **Stacks 0GI8, reduced to the tower form of Stacks 0A4Z for `X'`.** -/
theorem hasEffectiveFormalObjects_of_hasProperTowerAlgebraizationOverSpec
    (h : Space.HasProperTowerAlgebraizationOverSpec c.X') :
    LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) :=
  c.hasEffectiveFormalObjects_of_hasCompletionAlgebraization
    (c.hasCompletionAlgebraization_of_hasProperTowerAlgebraizationOverSpec h)

end Artin.ContractionSituation

end AlgebraicGeometry

end
