module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModulesRaised
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# Quasi-coherence *reflects* along restriction to a dense cocontinuous subsite

`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction` carries quasi-coherence *to* a
subsite: the restriction of a quasi-coherent module along a continuous cocontinuous functor,
taken over the restricted structure sheaf, is quasi-coherent. This file proves the converse
for a dense subsite inclusion: if the restriction of `𝓜` to the subsite is quasi-coherent, then
`𝓜` is quasi-coherent. Together the two make quasi-coherence an intrinsic property of the ringed
topos presented by either site.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_of_restriction`: **a global presentation reflects
  along restriction to a dense subsite**, at module sections independent of the ring sections.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction`: **quasi-coherence reflects along
  restriction to a dense cocontinuous subsite.**

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m

namespace Stacks.SheafOfModules

open Stacks.DenseSubsiteModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (v : D ⥤ C) [v.IsDenseSubsite K J] [v.IsCocontinuous K J]
  (R : Sheaf J RingCat.{r})

/-- **A global presentation reflects along restriction to a dense subsite.** If the restriction
of `𝓜` to a dense subsite, taken over the restricted sheaf of rings, admits a global
presentation in the sense of Stacks 03DE (6), then so does `𝓜`. -/
theorem hasGlobalPresentation_of_restriction
    [HasSheafify J AddCommGrpCat.{max u v r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m}]
    [HasSheafify K AddCommGrpCat.{max u v r m}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max u v r m}]
    (M : SheafOfModules.{m} R)
    (h : ((moduleRestrictionRaised.{r, m} K J v R).obj M).HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  classical
  set S : Sheaf K RingCat.{r} := ringRestriction K J v R with hS
  set F := moduleRestrictionRaised.{r, max u v r m} K J v R with hF
  have hfull : F.Full := full_moduleRestrictionRaised K J v R
  have hfaithful : F.Faithful := faithful_moduleRestrictionRaised K J v R
  have hpc : PreservesColimitsOfSize.{max u v r m, max u v r m} F :=
    pushforward_preservesColimits v (𝟙 S)
  have hz : F.PreservesZeroMorphisms := ⟨fun _ _ => by ext X x; rfl⟩
  have hunit : ∀ (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{r} K J).obj R) [IsIso φ],
      IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit φ) := by
    intro φ _
    have : IsIso ((sheafToPresheaf K AddCommGrpCat.{r}).map
        ((_root_.SheafOfModules.toSheaf S).map
          (_root_.SheafOfModules.unitToPushforwardObjUnit φ))) := by
      show IsIso (Functor.whiskerRight φ.hom (forget₂ RingCat.{r} AddCommGrpCat.{r}))
      infer_instance
    have : IsIso ((_root_.SheafOfModules.toSheaf S).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit φ)) :=
      isIso_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{r})
    exact isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf S)
  have := hunit (𝟙 S)
  obtain ⟨I, L, P', Q', ι', κ', ⟨hP'⟩, ⟨hQ'⟩, a', b', hab', ⟨hc'⟩⟩ := h
  set UR := _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m}
    (_root_.SheafOfModules.unit R) with hUR
  set UM := _root_.SheafOfModules.uliftForPresentation.{u, v, r, m, max u v r} M with hUM
  have η₁ : F.obj UR ≅ _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m}
      (_root_.SheafOfModules.unit S) :=
    (pushforwardUliftForPresentationIso.{u, v, r, r, max u v m} (𝟙 S)
        (_root_.SheafOfModules.unit R)).trans
      (_root_.SheafOfModules.uliftForPresentationMapIso
        (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit (𝟙 S))).symm)
  have ηM : F.obj UM ≅ _root_.SheafOfModules.uliftForPresentation.{u, v, r, m, max u v r}
      ((moduleRestrictionRaised.{r, m} K J v R).obj M) :=
    pushforwardUliftForPresentationIso.{u, v, r, m, max u v r} (𝟙 S) M
  have mkIso : ∀ (T : Type (max u v r m)) (Z : _root_.SheafOfModules.{max u v r m} S)
      (ζ : ∀ _ : T, _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m}
        (_root_.SheafOfModules.unit S) ⟶ Z),
      IsColimit (Cofan.mk Z ζ) → (F.obj (∐ (fun _ : T => UR)) ≅ Z) := by
    intro T Z ζ hZ
    exact IsColimit.coconePointUniqueUpToIso
      (GlobalPresentationTransport.isColimitCofanPrecompose η₁.symm
        (fun i => F.map (Sigma.ι (fun _ : T => UR) i))
        ((Cofan.isColimitMapCoconeEquiv F _
          (Cofan.mk (∐ (fun _ : T => UR)) (Sigma.ι (fun _ : T => UR)))).toFun
          (isColimitOfPreserves F (coproductIsCoproduct _)))) hZ
  obtain ⟨θP⟩ : Nonempty (F.obj (∐ (fun _ : I => UR)) ≅ P') := ⟨mkIso I P' ι' hP'⟩
  obtain ⟨θQ⟩ : Nonempty (F.obj (∐ (fun _ : L => UR)) ≅ Q') := ⟨mkIso L Q' κ' hQ'⟩
  set a : (∐ (fun _ : L => UR)) ⟶ (∐ (fun _ : I => UR)) :=
    F.preimage (θQ.hom ≫ a' ≫ θP.inv) with ha
  set b : (∐ (fun _ : I => UR)) ⟶ UM := F.preimage (θP.hom ≫ b' ≫ ηM.inv) with hb
  have hFa : F.map a = θQ.hom ≫ a' ≫ θP.inv := F.map_preimage _
  have hFb : F.map b = θP.hom ≫ b' ≫ ηM.inv := F.map_preimage _
  have hFa' : a' ≫ θP.inv = θQ.inv ≫ F.map a := by rw [hFa]; simp
  have hFb' : b' ≫ ηM.inv = θP.inv ≫ F.map b := by rw [hFb]; simp
  have hab : a ≫ b = 0 := by
    apply F.map_injective
    rw [F.map_comp, hFa, hFb, Functor.map_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc a' b', hab', zero_comp, comp_zero]
  have hkey : ∀ (T : _root_.SheafOfModules.{max u v r m} R) (π : (∐ (fun _ : I => UR)) ⟶ T),
      a ≫ π = 0 → a' ≫ (θP.inv ≫ F.map π) = 0 := by
    intro T π hπ
    rw [← Category.assoc, hFa', Category.assoc, ← F.map_comp, hπ, Functor.map_zero, comp_zero]
  refine ⟨I, L, ∐ (fun _ : I => UR), ∐ (fun _ : L => UR),
    fun i => Sigma.ι (fun _ : I => UR) i, fun l => Sigma.ι (fun _ : L => UR) l,
    ⟨coproductIsCoproduct _⟩, ⟨coproductIsCoproduct _⟩, a, b, hab, ⟨?_⟩⟩
  have hcond : ∀ s : Cofork a 0, a ≫ s.π = 0 := fun s => by rw [s.condition, zero_comp]
  have hdesc : ∀ s : Cofork a 0, b' ≫ hc'.desc
      (CokernelCofork.ofπ (θP.inv ≫ F.map s.π) (hkey _ s.π (hcond s))) =
        θP.inv ≫ F.map s.π := fun s => Cofork.IsColimit.π_desc hc'
  refine Cofork.IsColimit.mk _
    (fun s => F.preimage (ηM.hom ≫ hc'.desc
      (CokernelCofork.ofπ (θP.inv ≫ F.map s.π) (hkey _ s.π (hcond s))))) ?_ ?_
  · intro s
    apply F.map_injective
    show F.map (b ≫ _) = F.map s.π
    rw [F.map_comp, hFb, F.map_preimage, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc, hdesc s, Iso.hom_inv_id_assoc]
  · intro s n hn
    apply F.map_injective
    have hbn : b ≫ n = s.π := hn
    have hζ : b' ≫ (ηM.inv ≫ F.map n) = θP.inv ≫ F.map s.π := by
      rw [← Category.assoc, hFb', Category.assoc, ← F.map_comp, hbn]
    have hunique : ηM.inv ≫ F.map n = hc'.desc
        (CokernelCofork.ofπ (θP.inv ≫ F.map s.π) (hkey _ s.π (hcond s))) :=
      Cofork.IsColimit.hom_ext hc' (by
        show b' ≫ (ηM.inv ≫ F.map n) = b' ≫ _
        rw [hζ, hdesc s])
    rw [F.map_preimage, ← hunique, Iso.hom_inv_id_assoc]

omit [v.IsCocontinuous K J] in
/-- **Quasi-coherence reflects along restriction to a dense cocontinuous subsite.** If the
restriction of `𝓜` to a dense subsite, taken over the restricted sheaf of rings, is
quasi-coherent in the sense of Stacks 03DL (6), then `𝓜` is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_restriction [v.Full] [v.Faithful]
    [∀ W : D, (Over.post (X := W) v).IsCocontinuous (K.over W) (J.over (v.obj W))]
    (M : SheafOfModules.{m} R)
    (hM : ((moduleRestrictionRaised.{r, m} K J v R).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  classical
  have := Functor.IsDenseSubsite.isCoverDense K J v
  have hstep : ∀ W : D,
      (((moduleRestrictionRaised.{r, m} K J v R).obj M).over W).HasGlobalPresentation →
        (M.over (v.obj W)).HasGlobalPresentation := by
    intro W hW
    have := Stacks.Sites.overPost_isDenseSubsite (J := K) (K := J) v W
    have inst : ∀ (E : Type (max u v)) [Category.{v} E] (L : GrothendieckTopology E),
        HasSheafify L AddCommGrpCat.{max u v r m} ∧
          L.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} := fun E _ L =>
      ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} L,
        AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
          max u v, v} L⟩
    have := (inst _ (J.over (v.obj W))).1
    have := (inst _ (J.over (v.obj W))).2
    have := (inst _ (K.over W)).1
    have := (inst _ (K.over W)).2
    exact hasGlobalPresentation_of_restriction.{max u v, v, r, m}
      (Over.post (X := W) v) (R.over (v.obj W)) (M.over (v.obj W)) hW
  refine ⟨fun X => ?_⟩
  choose Idx Vv ff hcov hpres using fun Y : D =>
    _root_.SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation
      (M := (moduleRestrictionRaised.{r, m} K J v R).obj M) Y
  refine ⟨Σ (Y : D) (_ : v.obj Y ⟶ X), Idx Y,
    fun l => v.obj (Vv l.1 l.2.2), fun l => v.map (ff l.1 l.2.2) ≫ l.2.1, ?_,
    fun l => hstep _ (hpres l.1 l.2.2)⟩
  refine J.transitive (v.is_cover_of_isCoverDense J X) _ ?_
  rintro Z h ⟨⟨Y, lift, map, hfac⟩⟩
  have hY : Sieve.functorPushforward v (Sieve.ofArrows (Vv Y) (ff Y)) ∈ J (v.obj Y) :=
    (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := K) (K := J) (G := v)).mpr (hcov Y)
  refine J.superset_covering ?_ (J.pullback_stable lift hY)
  rintro W g ⟨W₀, p, q, hp, hgq⟩
  obtain ⟨i, e, he⟩ := (Sieve.mem_ofArrows_iff (Vv Y) (ff Y) p).mp hp
  show Sieve.ofArrows _ _ (g ≫ h)
  have heq : g ≫ h = (q ≫ v.map e) ≫ (v.map (ff Y i) ≫ map) := by
    rw [← hfac, ← Category.assoc, hgq, he]
    simp
  rw [heq]
  exact (Sieve.ofArrows
      (fun l : (Σ (Y : D) (_ : v.obj Y ⟶ X), Idx Y) => v.obj (Vv l.1 l.2.2))
      (fun l => v.map (ff l.1 l.2.2) ≫ l.2.1)).downward_closed
    (Sieve.ofArrows_mk
      (fun l : (Σ (Y : D) (_ : v.obj Y ⟶ X), Idx Y) => v.obj (Vv l.1 l.2.2))
      (fun l => v.map (ff l.1 l.2.2) ≫ l.2.1) ⟨Y, map, i⟩) (q ≫ v.map e)

end Stacks.SheafOfModules

end
