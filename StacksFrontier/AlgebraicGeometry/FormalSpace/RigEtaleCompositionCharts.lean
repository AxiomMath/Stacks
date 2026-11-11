module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts

/-!
# Composition and cancellation of rig-étale morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and `g` are rig-étale then
so is `g ∘ f`, and if `g ∘ f` and `g` are rig-étale then so is `f`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_comp_of_isNoetherian` and
  `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_comp_of_isNoetherian`:
  composition and right cancellation of rig-étaleness for morphisms of fppf sheaves whose
  presentations by Noetherian adic rings are rig-étale, the middle, respectively last, member
  being Noetherian.
* `AlgebraicGeometry.FormalSpace.exists_isAffineEtaleCover_of_isRepresentableEtale`: a sheaf
  representable étale over a locally Noetherian formal algebraic space has an affine étale
  covering.
* `AlgebraicGeometry.FormalSpace.exists_isAffineEtaleCover_chartFactorization_comp`: an affine
  étale covering of `X` whose members factor through affine étale charts of `Y` and `Z`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_comp_of_isLocallyNoetherian`: rig-étale morphisms of
  locally Noetherian formal algebraic spaces are stable under composition.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_comp_of_isLocallyNoetherian`: if `g ∘ f` and `g`
  are rig-étale then so is `f`.

## References

* [Stacks Project, Tag 0GD2](https://stacks.math.columbia.edu/tag/0GD2)
* [Stacks Project, Tag 0GD3](https://stacks.math.columbia.edu/tag/0GD3)
* [Stacks Project, Tag 0GCX](https://stacks.math.columbia.edu/tag/0GCX)
* [Stacks Project, Tag 0GCY](https://stacks.math.columbia.edu/tag/0GCY)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBP](https://stacks.math.columbia.edu/tag/0GBP)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Composition and cancellation on charts -/

/-- Let `t : U ⟶ W` and `s : W ⟶ V` be morphisms of fppf sheaves all
of whose presentations by Noetherian adic rings are rig-étale, with `W` Noetherian. Then every
presentation of `t ≫ s` by Noetherian adic rings is rig-étale. -/
theorem hasPropertyOnAffineChartMap_comp_of_isNoetherian {U W V : FppfSheaf B S hS}
    (t : U ⟶ W) (s : W ⟶ V) (hW : IsNoetherian B S hS W)
    (ht : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom t)
    (hs : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom s) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom (t ≫ s) := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  obtain ⟨M, _, _, _, _, F, hCM, ⟨eW⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hW
  have hMw := hCM.1.isWeaklyAdmissible
  have hRw := hCR.1.isWeaklyAdmissible
  obtain ⟨h, hh, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hMw hRw
    (eU.inv ≫ t ≫ eW.hom)
  obtain ⟨k, hk, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hMw
    (eW.inv ≫ s ≫ eV.hom)
  have htP : IsRigEtaleHom h.toRingHom := ht M R hCM hCR hMw F E eU eW h (by simp [hh])
  have hsP : IsRigEtaleHom k.toRingHom := hs A M hCA hCM hA D F eW eV k (by simp [hk])
  have hspf : formalSpectrumMap hA g =
      formalSpectrumMap hA (ContinuousHom.comp hMw hA h k) := by
    have h1 : formalSpectrumMap hA g = eU.inv ≫ (t ≫ s) ≫ eV.hom := by simp [hg]
    rw [← formalSpectrumMap_comp_eq hMw hA, hh, hk, h1]
    simp
  have hring : g.toRingHom = h.toRingHom.comp k.toRingHom := by
    rw [toRingHom_eq_of_formalSpectrumMap_eq B S hS hA hRw hspf]
    rfl
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have : IsNoetherianRing M := hCM.2
  intro _ _ _ _
  obtain ⟨hhc, hhr⟩ := htP
  obtain ⟨hkc, hkr⟩ := hsP
  exact hring ▸ ⟨hhc.comp hkc, Rig.rigEtale_comp hCR.1 hCM.1 hCA.1 _ _ hhc hkc hhr hkr⟩

/-- Let `t : U ⟶ W` and `s : W ⟶ V` be morphisms of fppf sheaves
with `V` Noetherian, such that every presentation of `s` and of `t ≫ s` by Noetherian adic
rings is rig-étale. Then every presentation of `t` by Noetherian adic rings is rig-étale. -/
theorem hasPropertyOnAffineChartMap_of_comp_of_isNoetherian {U W V : FppfSheaf B S hS}
    (t : U ⟶ W) (s : W ⟶ V) (hV : IsNoetherian B S hS V)
    (hts : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom (t ≫ s))
    (hs : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom s) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom t := by
  intro M R _ _ _ _ _ _ _ _ hCM hCR hMw F E eU eW h hh
  obtain ⟨A, _, _, _, _, D, hCA, ⟨eV⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hV
  have hA := hCA.1.isWeaklyAdmissible
  obtain ⟨k, hk, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hMw
    (eW.inv ≫ s ≫ eV.hom)
  have hsP : IsRigEtaleHom k.toRingHom := hs A M hCA hCM hA D F eW eV k (by simp [hk])
  have htsP : IsRigEtaleHom (ContinuousHom.comp hMw hA h k).toRingHom :=
    hts A R hCA hCR hA D E eU eV _ (by
      rw [← formalSpectrumMap_comp_eq hMw hA, hk, hh]
      simp)
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have : IsNoetherianRing M := hCM.2
  intro _ _ _ _
  exact Rig.rigEtale_hasNoetherianCancellationProperty h.toRingHom k.toRingHom hCR hCM hCA
    h.continuous k.continuous ⟨hsP, htsP⟩

/-! ### The covering -/

/-- Affine étale coverings of the base changes `Vⱼ ×_Z Y` of a representable étale covering
`{Vⱼ ⟶ Z}` compose to an affine étale covering of `Y`. -/
private theorem isAffineEtaleCover_sigma_comp_pullback_snd {Y Z : FppfSheaf B S hS}
    (g : Y ⟶ Z) {J : Type (u + 1)} {V : J → FppfSheaf B S hS} (v : ∀ j, V j ⟶ Z)
    (hv : ∀ j, IsRepresentableEtale B S hS (v j))
    (hvsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc v))
    {K : J → Type (u + 1)} {W : ∀ j, K j → FppfSheaf B S hS}
    (w : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (w j)) :
    IsAffineEtaleCover B S hS (fun x : Σ j, K j ↦ W x.1 x.2)
      (fun x ↦ w x.1 x.2 ≫ pullback.snd (v x.1) g) :=
  ⟨fun x ↦ (hW x.1).1 x.2, fun x ↦ ((hW x.1).2.1 x.2).comp B S hS
    (isRepresentableEtale_pullback_snd B S hS (v x.1) g (hv x.1)),
    isLocallySurjective_sigmaDesc_comp_sigma B S hS (fun j ↦ pullback.snd (v j) g)
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd g v hvsurj)
      (fun x : Σ j, K j ↦ w x.1 x.2) (fun j ↦ (hW j).2.2)⟩

/-- A sheaf `P` with a representable étale morphism to a locally Noetherian formal algebraic space
`X` has an affine étale covering. -/
theorem exists_isAffineEtaleCover_of_isRepresentableEtale {X P : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) (φ : P ⟶ X) (hφ : IsRepresentableEtale B S hS φ) :
    ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS) (w : ∀ k, W k ⟶ P),
      IsAffineEtaleCover B S hS W w := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, IX, Xi, ui, -, hXet, hXsurj, hXnoeth⟩ := hX
  have hcharts : ∀ i : IX, ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS)
      (w : ∀ k, W k ⟶ pullback (ui i) φ), IsAffineEtaleCover B S hS W w := by
    intro i
    obtain ⟨R, _, _, _, _, E, hCR, ⟨eXi⟩⟩ :=
      exists_iso_formalSpectrum_of_isNoetherian B S hS (hXnoeth i)
    have hψ : IsRepresentableEtale B S hS (pullback.fst (ui i) φ ≫ eXi.hom) :=
      (isRepresentableEtale_pullback_fst B S hS (ui i) φ hφ).comp B S hS
        (isRepresentableEtale_of_isIso B S hS _)
    obtain ⟨K, C, _, fk, -, Q, g, -, w, -, hwet, hWaff, -, hsurj⟩ :=
      exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCR E _ hψ
    exact ⟨K, fun k ↦ formalSpectrum (Q k), w, hWaff, hwet, hsurj⟩
  choose K W w hW using hcharts
  exact ⟨(i : IX) × K i, _, _, isAffineEtaleCover_sigma_comp_pullback_snd B S hS φ ui hXet
    hXsurj w hW⟩

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of fppf sheaves with `X` locally Noetherian and
`g` corresponding to a rig-étale map after an affine étale covering of `Z`. Then there is an
affine étale covering `{Uᵢ ⟶ X}` together with factorizations `Uᵢ ⟶ Wᵢ ⟶ Y` and
`Wᵢ ⟶ Vᵢ ⟶ Z` through affine representable étale charts `Wᵢ` of `Y` and `Vᵢ` of `Z`, with each
`Wᵢ ⟶ Vᵢ` corresponding to a rig-étale map in `WAdm^{Noeth}`. -/
theorem exists_isAffineEtaleCover_chartFactorization_comp {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X)
    (hg : CorrespondsToRigEtaleMapAfterTargetCover B S hS g) :
    ∃ (I : Type (u + 1)) (U W V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X)
      (t : ∀ i, U i ⟶ W i) (s : ∀ i, W i ⟶ V i) (c : ∀ i, W i ⟶ Y) (v : ∀ i, V i ⟶ Z),
      IsAffineEtaleCover B S hS U u ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) ∧
        (∀ i, IsRepresentableEtale B S hS (c i)) ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) ∧
        (∀ i, IsRepresentableEtale B S hS (v i)) ∧
        (∀ i, u i ≫ f = t i ≫ c i) ∧ (∀ i, c i ≫ g = s i ≫ v i) ∧
        ∀ i, CorrespondsToRigEtaleMap B S hS (s i) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, ⟨hVaff, hVet, hVsurj⟩, hcharts⟩ := hg
  choose I W w hWcover hWcorr using hcharts
  have hcov := isAffineEtaleCover_sigma_comp_pullback_snd B S hS g v hVet hVsurj w hWcover
  let c : (x : Σ j, I j) → W x.1 x.2 ⟶ Y := fun x ↦ w x.1 x.2 ≫ pullback.snd (v x.1) g
  have hc : ∀ x, IsRepresentableEtale B S hS (c x) := hcov.2.1
  choose K U m hUcover using fun x ↦
    exists_isAffineEtaleCover_of_isRepresentableEtale B S hS hX (pullback.snd (c x) f)
      (isRepresentableEtale_pullback_snd B S hS (c x) f (hc x))
  refine ⟨Σ x, K x, fun y ↦ U y.1 y.2, fun y ↦ W y.1.1 y.1.2, fun y ↦ V y.1.1,
    fun y ↦ m y.1 y.2 ≫ pullback.snd (c y.1) f, fun y ↦ m y.1 y.2 ≫ pullback.fst (c y.1) f,
    fun y ↦ w y.1.1 y.1.2 ≫ pullback.fst (v y.1.1) g, fun y ↦ c y.1, fun y ↦ v y.1.1,
    isAffineEtaleCover_sigma_comp_pullback_snd B S hS f c hc hcov.2.2 m hUcover,
    fun y ↦ (hWcover y.1.1).1 y.1.2, fun y ↦ hc y.1, fun y ↦ hVaff y.1.1, fun y ↦ hVet y.1.1,
    fun y ↦ ?_, fun y ↦ ?_, fun y ↦ hWcorr y.1.1 y.1.2⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition]
  · simp only [c, Category.assoc, pullback.condition]

/-! ### Composition and cancellation -/

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `f` and `g` are rig-étale, then so is `g ∘ f`. -/
@[stacks 0GD2]
theorem isRigEtale_comp_of_isLocallyNoetherian {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z) (hf : IsRigEtale B S hS f)
    (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS (f ≫ g) := by
  obtain ⟨I, U, W, V, u, t, s, c, v, hUcover, hWaff, hc, hVaff, hv, hsq₁, hsq₂, hs⟩ :=
    exists_isAffineEtaleCover_chartFactorization_comp B S hS f g hX
      (correspondsToRigEtaleMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram B S hS
        g hY hZ ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))
  have hf5 : HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom f :=
    (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf
  refine (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS
      (f ≫ g) ⟨I, U, u, hUcover, fun i ↦ ⟨V i, v i, t i ≫ s i, hVaff i, hv i, ?_, ?_⟩⟩)
  · rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]
  obtain ⟨R, _, _, _, _, E, hCR, ⟨eU⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX (u i)
      (hUcover.1 i) (hUcover.2.1 i))
  obtain ⟨A, _, _, _, _, D, hCA, ⟨eV⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hZ (v i) (hVaff i)
      (hv i))
  exact correspondsToRigEtaleMap_of_hasPropertyOnAffineChartMap B S hS
    (hasPropertyOnAffineChartMap_comp_of_isNoetherian B S hS (t i) (s i)
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY (c i) (hWaff i)
        (hc i))
      (hf5 (U i) (W i) (u i) (c i) (t i) (hUcover.1 i) (hWaff i) (hUcover.2.1 i) (hc i)
        (hsq₁ i))
      (hasPropertyOnAffineChartMap_of_correspondsToRigEtaleMap B S hS (hs i)))
    hCA hCR D E eU eV

/-- **Stacks 0GD3.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian
formal algebraic spaces over `S`. If `g ∘ f` and `g` are rig-étale, then so is `f`.

The proof is unconditional and works on affine étale charts: an affine étale cover of `X`
is factored through affine étale charts of `Y` and `Z` adapted to `g`, and rig-étaleness of
`f` is checked chart by chart from that of `g ∘ f` and `g`. -/
@[stacks 0GD3 "f, g morphisms of locally Noetherian formal algebraic spaces over S; \
g ∘ f and g rig-étale implies f rig-étale"]
theorem isRigEtale_of_comp_of_isLocallyNoetherian {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z) (hfg : IsRigEtale B S hS (f ≫ g))
    (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS f := by
  obtain ⟨I, U, W, V, u, t, s, c, v, hUcover, hWaff, hc, hVaff, hv, hsq₁, hsq₂, hs⟩ :=
    exists_isAffineEtaleCover_chartFactorization_comp B S hS f g hX
      (correspondsToRigEtaleMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram B S hS
        g hY hZ ((isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS g).mp hg))
  have hfg5 : HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom
      (f ≫ g) := (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS (f ≫ g)).mp hfg
  refine (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS f
      ⟨I, U, u, hUcover, fun i ↦ ⟨W i, c i, t i, hWaff i, hc i, hsq₁ i, ?_⟩⟩)
  obtain ⟨R, _, _, _, _, E, hCR, ⟨eU⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX (u i)
      (hUcover.1 i) (hUcover.2.1 i))
  obtain ⟨M, _, _, _, _, F, hCM, ⟨eW⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY (c i) (hWaff i)
      (hc i))
  have hsq : u i ≫ f ≫ g = (t i ≫ s i) ≫ v i := by
    rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]
  exact correspondsToRigEtaleMap_of_hasPropertyOnAffineChartMap B S hS
    (hasPropertyOnAffineChartMap_of_comp_of_isNoetherian B S hS (t i) (s i)
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hZ (v i) (hVaff i)
        (hv i))
      (hfg5 (U i) (V i) (u i) (v i) (t i ≫ s i) (hUcover.1 i) (hVaff i) (hUcover.2.1 i) (hv i)
        hsq)
      (hasPropertyOnAffineChartMap_of_correspondsToRigEtaleMap B S hS (hs i)))
    hCM hCR F E eU eW

end AlgebraicGeometry.FormalSpace

end
