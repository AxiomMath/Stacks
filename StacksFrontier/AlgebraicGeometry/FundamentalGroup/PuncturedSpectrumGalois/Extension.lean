module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEssSurj
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverTorsor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumGalois.FormalNeighbourhood
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumGalois.PowerSeriesChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.SplitLocal
public import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Galois covers over the punctured spectrum of the base extend

Let `A` be a Noetherian local normal domain of dimension at least two, `U ⊆ Spec A` its punctured
spectrum and `f : X ⟶ Spec A` smooth with geometrically connected fibres and a section `σ`. A
finite étale Galois cover of `X_U = f⁻¹(U)` with group `G` having a `U`-point over `σ|_U` is the
restriction of a finite étale Galois cover of `X` with group `G`. This is the claim proved in the
proof of [Stacks, Tag 0EYJ] at a point of codimension at least two of the base.

## Main results

* `AlgebraicGeometry.etaleAt_extendedEtale_of_isSplitCover` — the local calculation: the
  extension of [Stacks, Tag 0EY6] of a cover of `X_U` that splits along `σ|_U` is étale above
  `σ(𝔪)`.
* `AlgebraicGeometry.Abhyankar.exists_finiteEtaleGaloisCover_extending_puncturedSpectrum` — the
  claim.

## Implementation notes

The source shows that the extension `Y'` of [Stacks, Tag 0EY6] is étale over the generic point of
the closed fibre and then appeals to [Stacks, Tag 0EYB]. Here the local calculation gives
étaleness above `σ(𝔪)`, so `Y'` is finite étale over an open `V ⊇ X_U` meeting the closed fibre,
which is irreducible; [Stacks, Tag 0EYB] for `V` then gives a finite étale cover of `X` whose
restriction to `V`, hence to `X_U`, is the given one. The `U`-point enters only through the
splitting of the cover along `σ|_U`
(`AlgebraicGeometry.Abhyankar.isIso_sigmaDesc_translateSection`).

## References

* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 05D5](https://stacks.math.columbia.edu/tag/05D5)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup Stacks.FundamentalGroup.ExtendedEtaleFold Stacks.RelativeSpec
open Stacks.Algebraization (IsInfinitesimalSectionsComplete
  CompletionFullyFaithfulOnFiniteLocallyFree)

universe v u

namespace AlgebraicGeometry

/-- The canonical map `Spec Γ(Spec A, ⊤) ⟶ Spec A` sends the closed point to the closed point. -/
private theorem IsAffineOpen.fromSpec_top_closedPoint {A : Type u} [CommRing A] [IsLocalRing A]
    (hU : IsAffineOpen (⊤ : (Spec (.of A)).Opens)) [IsLocalRing Γ(Spec (.of A), ⊤)] :
    hU.fromSpec (closedPoint Γ(Spec (.of A), ⊤)) = closedPoint A := by
  obtain ⟨t, ht⟩ : closedPoint A ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    trivial
  have hsp : closedPoint A ⤳ hU.fromSpec (closedPoint Γ(Spec (.of A), ⊤)) := by
    rw [← ht]
    exact (IsLocalRing.specializes_closedPoint t).map hU.fromSpec.continuous
  exact PrimeSpectrum.ext
    ((IsLocalRing.le_maximalIdeal (hU.fromSpec (closedPoint _)).isPrime.ne_top).antisymm
    ((PrimeSpectrum.le_iff_specializes _ _).2 hsp))

/-- Depth at least two of the local rings of a finite `E ⟶ X` off an open `U` is preserved by flat
base change. -/
private theorem two_le_depth_stalk_pullback_of_finite_of_flat {E X T : Scheme.{u}}
    [IsLocallyNoetherian T] (g : E ⟶ X) [IsFinite g] (U : X.Opens)
    (hg : ∀ y : E, g y ∉ U →
      (2 : ℕ∞) ≤ Module.depth (E.presheaf.stalk y) (maximalIdeal (E.presheaf.stalk y))
        (E.presheaf.stalk y))
    (φ : T ⟶ X) [Flat φ] (e : (pullback g φ : Scheme.{u}))
    (he : pullback.snd g φ e ∉ φ ⁻¹ᵁ U) :
    (2 : ℕ∞) ≤ Module.depth ((pullback g φ).presheaf.stalk e)
      (maximalIdeal ((pullback g φ).presheaf.stalk e)) ((pullback g φ).presheaf.stalk e) := by
  have hP := IsPullback.of_hasPullback g φ
  have : IsFinite (pullback.snd g φ) := MorphismProperty.of_isPullback hP inferInstance
  have : Flat (pullback.fst g φ) := MorphismProperty.of_isPullback hP.flip inferInstance
  have : IsLocallyNoetherian (pullback g φ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g φ)
  refine (hg _ fun h => he ?_).trans (depth_stalk_le_depth_stalk_of_flat (pullback.fst g φ) e)
  show φ (pullback.snd g φ e) ∈ U
  rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]

/-- Commuting squares of schemes commute pointwise. -/
private theorem apply_eq_of_comp_eq {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W}
    {d : W ⟶ Z} (h : a ≫ b = c ≫ d) (x : X) : b (a x) = d (c x) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun h => h x) h

/-- A section `σ` of `f` satisfies `f (σ s) = s` pointwise. -/
private theorem apply_section_apply {S X : Scheme.{u}} {f : X ⟶ S} {σ : S ⟶ X}
    (hσ : σ ≫ f = 𝟙 S) (s : S) : f (σ s) = s := by
  rw [← Scheme.Hom.comp_apply, hσ]
  rfl

/-- A finite étale cover that is a split covering is the base change of a finite étale cover along
any morphism to its base. -/
private theorem exists_iso_finiteEtaleBaseChange_of_isSplitCover {S U : Scheme.{u}} (k : U ⟶ S)
    (H : FiniteEtaleOver U) (hH : Stacks.Etale.IsSplitCover H.hom) :
    ∃ F₀ : FiniteEtaleOver S, Nonempty (H ≅ (finiteEtaleBaseChange k).obj F₀) := by
  obtain ⟨ι, hι, eS, heS⟩ := hH
  have hP := (Stacks.Etale.isPullback_sigmaDesc_id (ι := ι) k).flip
  have hK : IsPullback (finiteEtaleBaseChangeProj k (splitCover S ι))
      ((finiteEtaleBaseChange k).obj (splitCover S ι)).hom
      (Sigma.desc fun _ : ι => 𝟙 S) k := IsPullback.of_hasPullback _ k
  exact ⟨splitCover S ι, ⟨MorphismProperty.Over.isoMk (eS ≪≫ (hK.isoIsPullback _ _ hP).symm) (by
    refine Eq.trans ?_ heS
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    exact congrArg (eS.hom ≫ ·) (hK.isoIsPullback_inv_snd _ _ hP))⟩⟩

/-- Let `Y` be a finite étale cover of `f⁻¹(U)` that splits along a section `σU` over `U` of
`f : X ⟶ S`. If `s₀ ≫ φ = α ≫ σ`, the base change of `Y` along `φ`, restricted along `s₀`, is the
base change of a finite étale cover of `S'`. -/
private theorem exists_iso_finiteEtaleBaseChange_of_isSplitCover_section {S X T S' : Scheme.{u}}
    (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (U : S.Opens)
    (Yobj : FiniteEtaleOver (f ⁻¹ᵁ U).toScheme) (σU : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme)
    (hσU : σU ≫ (f ⁻¹ᵁ U).ι = U.ι ≫ σ)
    (htriv : Stacks.Etale.IsSplitCover (pullback.snd Yobj.hom σU))
    (φ : T ⟶ X) (s₀ : S' ⟶ T) (α : S' ⟶ S) (hφs : s₀ ≫ φ = α ≫ σ) :
    ∃ F₀ : FiniteEtaleOver S',
      Nonempty ((finiteEtaleBaseChange (s₀ ∣_ (φ ⁻¹ᵁ f ⁻¹ᵁ U))).obj
          ((finiteEtaleBaseChange (φ ∣_ f ⁻¹ᵁ U)).obj Yobj) ≅
        (finiteEtaleBaseChange (s₀ ⁻¹ᵁ φ ⁻¹ᵁ f ⁻¹ᵁ U).ι).obj F₀) := by
  let XU := f ⁻¹ᵁ U
  let φV := φ ∣_ XU
  let W := (finiteEtaleBaseChange φV).obj Yobj
  let i := s₀ ∣_ (φ ⁻¹ᵁ XU)
  let k := (s₀ ⁻¹ᵁ φ ⁻¹ᵁ XU).ι
  have hφV : φV ≫ XU.ι = (φ ⁻¹ᵁ XU).ι ≫ φ := morphismRestrict_ι φ XU
  have hfφs : ∀ t, f (φ (s₀ t)) = α t := fun t => by
    rw [apply_eq_of_comp_eq hφs, apply_section_apply hσ]
  have hrange : Set.range (k ≫ α) ⊆ U.ι.opensRange := by
    rintro _ ⟨t', rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    have h1 : k t' ∈ s₀ ⁻¹ᵁ φ ⁻¹ᵁ XU := t'.2
    change f (φ (s₀ (k t'))) ∈ U at h1
    rwa [hfφs] at h1
  let m := IsOpenImmersion.lift U.ι (k ≫ α) hrange
  have hm : m ≫ U.ι = k ≫ α := IsOpenImmersion.lift_fac _ _ _
  have hiφ : i ≫ φV = m ≫ σU := by
    rw [← cancel_mono XU.ι, Category.assoc, Category.assoc, hφV, hσU, ← Category.assoc i,
      morphismRestrict_ι, Category.assoc, hφs, reassoc_of% hm]
  have hsqφ : IsPullback (finiteEtaleBaseChangeProj φV Yobj) W.hom Yobj.hom φV :=
    IsPullback.of_hasPullback Yobj.hom φV
  have hsqi : IsPullback (finiteEtaleBaseChangeProj i W) ((finiteEtaleBaseChange i).obj W).hom
      W.hom i := IsPullback.of_hasPullback W.hom i
  refine exists_iso_finiteEtaleBaseChange_of_isSplitCover k _ ?_
  rw [Stacks.Etale.isSplitCover_snd_of_isPullback (hsqi.paste_horiz hsqφ), hiφ,
    ← Stacks.Etale.isSplitCover_pullback_snd_comp]
  exact Stacks.Etale.isSplitCover_pullback_snd htriv m

/-- **The extension of a cover of `X_U` is étale over a power series chart along `σ`.** For a flat
`φ : Spec A'[[x]] ⟶ X` whose zero section lies over `σ ∘ α`, with `α` meeting the closed point
exactly at the closed point, the base change along `φ` of the extension of [Stacks, Tag 0EY6] of a
cover of `X_U` that splits along `σ|_U` is étale. -/
private theorem etale_pullback_snd_extendedEtale_of_powerSeries_chart
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (Yobj : FiniteEtaleOver (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    [IsFinite Yobj.hom] [Etale Yobj.hom]
    (σU : (Stacks.puncturedSpectrum A).toScheme ⟶ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    (hσU : σU ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι = (Stacks.puncturedSpectrum A).ι ≫ σ)
    (htriv : Stacks.Etale.IsSplitCover (pullback.snd Yobj.hom σU))
    [IsLocallyNoetherian X]
    (hd : ∀ x : X, x ∉ ((f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))
    (A' : CommRingCat.{u}) [IsLocalRing A'] [IsNoetherianRing A']
    (hdepthA' : (2 : ℕ∞) ≤ Module.depth A' (maximalIdeal A') A')
    (α : Spec (.of A') ⟶ Spec (.of A)) (hα : ∀ t, α t = closedPoint A ↔ t = closedPoint A')
    (d : ℕ) (φ : Spec (.of (MvPowerSeries (Fin d) A')) ⟶ X) [Flat φ]
    (hφs : Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A' →+* A')) ≫ φ = α ≫ σ) :
    Etale (pullback.snd (gluedSpectrum (extendedEtaleSituation
      (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι Yobj.hom hd)).toBase φ) := by
  classical
  let XU := f ⁻¹ᵁ Stacks.puncturedSpectrum A
  let E := gluedSpectrum (extendedEtaleSituation XU.ι Yobj.hom hd)
  let g : E.scheme ⟶ X := E.toBase
  have : IsFinite g := isFinite_relativeSpectrum_extendedEtaleSituation XU.ι Yobj.hom hd
  let cW := extendedEtaleCoverMap XU.ι Yobj.hom hd
  have hE : IsPullback Yobj.hom cW XU.ι g := extendedEtaleCoverMap_isPullback XU.ι Yobj.hom hd
  -- the power series scheme `T`, its zero section and the inverse image `V` of `X_U`
  let T : Scheme.{u} := Spec (.of (MvPowerSeries (Fin d) A'))
  let s₀ : Spec (.of A') ⟶ T := Spec.map (CommRingCat.ofHom
    (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A' →+* A'))
  let VT : T.Opens := φ ⁻¹ᵁ XU
  have hfφs : ∀ t, f (φ (s₀ t)) = α t := fun t => by
    rw [apply_eq_of_comp_eq hφs, apply_section_apply hσ]
  have hV : (s₀ ⁻¹ᵁ VT : Set (Spec (.of A'))) = {closedPoint A'}ᶜ := by
    refine Set.ext fun t => ⟨fun h h' => ?_, fun h => ?_⟩
    · have h1 : f (φ (s₀ t)) ∈ Stacks.puncturedSpectrum A := h
      rw [hfφs, (hα t).2 h'] at h1
      exact Stacks.notMem_puncturedSpectrum_closedPoint A h1
    · show f (φ (s₀ t)) ∈ Stacks.puncturedSpectrum A
      rw [hfφs]
      exact fun h' => h ((hα t).1 h')
  have hdepthT : ∀ q : T, q ∉ VT →
      (2 : ℕ∞) ≤ Module.depth (T.presheaf.stalk q) (maximalIdeal (T.presheaf.stalk q))
        (T.presheaf.stalk q) := fun q hq =>
    (hd (φ q) (by rwa [Scheme.Opens.opensRange_ι])).trans (depth_stalk_le_depth_stalk_of_flat φ q)
  -- the base change `E ×_X T`
  have hET : IsPullback (pullback.fst g φ) (pullback.snd g φ) g φ := IsPullback.of_hasPullback g φ
  have : IsFinite (pullback.snd g φ) := MorphismProperty.of_isPullback hET inferInstance
  -- its restriction over `V` is the base change `W` of `Y`
  let φV := φ ∣_ XU
  let W := (finiteEtaleBaseChange φV).obj Yobj
  have hφV : φV ≫ XU.ι = VT.ι ≫ φ := morphismRestrict_ι φ XU
  have hbig : IsPullback (finiteEtaleBaseChangeProj φV Yobj ≫ cW) W.hom g (φV ≫ XU.ι) :=
    (IsPullback.of_hasPullback Yobj.hom φV).paste_horiz hE.flip
  let c : W.left ⟶ pullback g φ := pullback.lift (finiteEtaleBaseChangeProj φV Yobj ≫ cW)
    (W.hom ≫ VT.ι) (by rw [hbig.w, hφV, Category.assoc])
  have hc' : IsPullback c W.hom (pullback.snd g φ) VT.ι := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hET
    rwa [pullback.lift_fst, ← hφV]
  -- along the zero section, `W` is a split covering
  obtain ⟨F₀, ⟨e₀⟩⟩ := exists_iso_finiteEtaleBaseChange_of_isSplitCover_section f σ hσ
    (Stacks.puncturedSpectrum A) Yobj σU hσU htriv φ s₀ α hφs
  exact etale_of_isPullback_of_zeroSection_iso A' d hdepthA' VT hV hdepthT (pullback.snd g φ)
    (two_le_depth_stalk_pullback_of_finite_of_flat g XU (fun y hy =>
      extendedEtale_depth_ge_two XU.ι Yobj.hom hd y (by rwa [Scheme.Opens.opensRange_ι])) φ)
    W c hc'.flip F₀ e₀

/-- **The extension of a cover of `X_U` is étale above `σ(𝔪)`.** Let `(A, 𝔪)` be a Noetherian
local ring of depth at least two with punctured spectrum `U`, `f : X ⟶ Spec A` smooth with a
section `σ`, and `Y` a finite étale cover of `X_U = f⁻¹(U)` whose base change along
`σ|_U : U ⟶ X_U` is a split covering. Then the finite extension `E ⟶ X` of `Y` given by
[Stacks, Tag 0EY6] is étale at every point above `σ(𝔪)`.

This is the local calculation of the proof of [Stacks, Tag 0EYJ]. The power series chart
`φ : T = Spec A'[[x]] ⟶ X` along `σ` (`exists_flat_powerSeries_chart_of_section`, with
`A' = Γ(Spec A, ⊤)`) is flat, so `E ×_X T ⟶ T` restricts over `V = φ⁻¹(X_U)` to the base change
`W` of `Y` and has depth at least two above `T ∖ V`. Along the zero section `W` is the base change
of `Y` along `σ|_U`, a split covering, which extends to the split covering of `Spec A'`. So
`E ×_X T ⟶ T` is étale by `etale_of_isPullback_of_zeroSection_iso`, and étaleness descends along
the flat `φ` to the points of `E` above `φ(𝔪_T) = σ(𝔪)`. -/
theorem etaleAt_extendedEtale_of_isSplitCover
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepthA : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Smooth f] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (Yobj : FiniteEtaleOver (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    [IsFinite Yobj.hom] [Etale Yobj.hom]
    (σU : (Stacks.puncturedSpectrum A).toScheme ⟶ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    (hσU : σU ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι = (Stacks.puncturedSpectrum A).ι ≫ σ)
    (htriv : Stacks.Etale.IsSplitCover (pullback.snd Yobj.hom σU))
    [IsLocallyNoetherian X]
    (hd : ∀ x : X, x ∉ ((f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))
    (e : (gluedSpectrum (extendedEtaleSituation (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι
      Yobj.hom hd)).scheme)
    (he : (gluedSpectrum (extendedEtaleSituation (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι
      Yobj.hom hd)).toBase e = σ (closedPoint A)) :
    EtaleAt (gluedSpectrum (extendedEtaleSituation (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι
      Yobj.hom hd)).toBase e := by
  classical
  let XU := f ⁻¹ᵁ Stacks.puncturedSpectrum A
  let E := gluedSpectrum (extendedEtaleSituation XU.ι Yobj.hom hd)
  let g : E.scheme ⟶ X := E.toBase
  have : IsFinite g := isFinite_relativeSpectrum_extendedEtaleSituation XU.ι Yobj.hom hd
  have : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian g
  -- the chart along `σ`
  obtain ⟨U₀, hU₀, hsU₀, d, φ, hφflat, -, hφs⟩ :=
    exists_flat_powerSeries_chart_of_section f σ hσ (closedPoint A)
  have hU₀top : U₀ = ⊤ := eq_top_iff.mpr fun t _ =>
    (IsLocalRing.specializes_closedPoint t).mem_open U₀.isOpen hsU₀
  subst hU₀top
  -- the ring `A' = Γ(Spec A, ⊤)` of the chart
  let A' := Γ(Spec (.of A), ⊤)
  let eΓ : A' ≃+* A := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have : Nontrivial A' := eΓ.toEquiv.nontrivial
  have : IsLocalRing A' := IsLocalRing.of_surjective' eΓ.symm.toRingHom eΓ.symm.surjective
  have : IsNoetherianRing A' := isNoetherianRing_of_ringEquiv A eΓ.symm
  have hdepthA' : (2 : ℕ∞) ≤ Module.depth A' (maximalIdeal A') A' := by
    rwa [Module.depth_self_eq_of_ringEquiv eΓ]
  let α := hU₀.fromSpec
  have hαc : α (closedPoint A') = closedPoint A := IsAffineOpen.fromSpec_top_closedPoint hU₀
  let T : Scheme.{u} := Spec (.of (MvPowerSeries (Fin d) A'))
  let s₀ : Spec (.of A') ⟶ T := Spec.map (CommRingCat.ofHom
    (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A' →+* A'))
  have hφs' := apply_eq_of_comp_eq hφs
  have hetT := etale_pullback_snd_extendedEtale_of_powerSeries_chart A f σ hσ Yobj σU hσU htriv
    hd A' hdepthA' α
    (fun t => ⟨fun ht => α.isOpenEmbedding.injective (ht.trans hαc.symm), fun ht => ht ▸ hαc⟩)
    d φ hφs
  -- étaleness descends along the flat `φ`
  let pA' : Spec (.of A') := closedPoint (CommRingCat.of A')
  have hφpT : φ (s₀ pA') = σ (closedPoint A) := (hφs' pA').trans (congrArg σ hαc)
  have : LocallyOfFinitePresentation g := inferInstance
  obtain ⟨e', he'1, -⟩ := Scheme.Pullback.exists_preimage_pullback e (s₀ pA')
    (he.trans hφpT.symm)
  exact (congrArg (fun x => EtaleAt g x) he'1).mp
    ((etaleAt_iff_of_isPullback (IsPullback.of_hasPullback g φ) (Or.inr hφflat) e').2
      ((etale_iff_forall_etaleAt _).1 hetT e'))

/-- A Galois cover `Y ⟶ S` splits after base change along `t ≫ Y ⟶ S`, for any `t : W ⟶ Y`. -/
private theorem Abhyankar.isSplitCover_pullback_snd_comp_hom {S W : Scheme.{u}} {G : Type v}
    [Group G] [Finite G] (Y : FiniteEtaleGaloisCover S G) (t : W ⟶ Y.obj.left) :
    Stacks.Etale.IsSplitCover (pullback.snd Y.obj.hom (t ≫ Y.obj.hom)) := by
  let aY := ((MorphismProperty.Over.forget _ ⊤ _).mapAut Y.obj).comp Y.action
  have := Abhyankar.isIso_sigmaDesc_translateSection Y.obj.hom aY t
  obtain ⟨n, ⟨eG⟩⟩ := Finite.exists_equiv_fin G
  let eι : ULift.{u} (Fin n) ≃ G := Equiv.ulift.trans eG.symm
  let E1 : (∐ fun _ : G ↦ W) ≅ pullback (t ≫ Y.obj.hom) Y.obj.hom :=
    asIso (Limits.Sigma.desc (Abhyankar.translateSection Y.obj.hom aY t))
  let E2 : (∐ fun _ : ULift.{u} (Fin n) ↦ W) ≅ ∐ fun _ : G ↦ W :=
    Sigma.whiskerEquiv eι (fun _ ↦ Iso.refl W)
  have hE1 : E1.hom ≫ pullback.fst (t ≫ Y.obj.hom) Y.obj.hom =
      Limits.Sigma.desc (fun _ ↦ 𝟙 _) := by
    refine Sigma.hom_ext _ _ fun _ => ?_
    simp only [E1, asIso_hom, Sigma.ι_desc_assoc, Abhyankar.translateSection,
      pullback.lift_fst, Limits.Sigma.ι_desc]
  have hE2 : E2.inv ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 W) = Limits.Sigma.desc (fun _ ↦ 𝟙 _) :=
    Sigma.hom_ext _ _ fun _ => by simp [E2, Sigma.whiskerEquiv]
  refine (Stacks.Etale.isSplitCover_iff_of_iso (pullbackSymmetry Y.obj.hom (t ≫ Y.obj.hom))
    (pullbackSymmetry_hom_comp_fst _ _)).2
    ⟨ULift.{u} (Fin n), inferInstance, E1.symm ≪≫ E2.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc, hE2, ← hE1,
    Iso.inv_hom_id_assoc]

/-- Over a Noetherian local ring of depth at least two, the fibre of `f : X ⟶ Spec A` over a point
whose local ring has depth at most one lies over the punctured spectrum. -/
private theorem preimage_singleton_subset_puncturedSpectrum_of_depth_le_one
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hdepthA : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (s : Spec (.of A))
    (hs : Module.depth ((Spec (.of A)).presheaf.stalk s)
      (maximalIdeal ((Spec (.of A)).presheaf.stalk s)) ((Spec (.of A)).presheaf.stalk s) ≤ 1) :
    f.base ⁻¹' {s} ⊆ (f ⁻¹ᵁ Stacks.puncturedSpectrum A : Set X) := by
  intro x hx
  by_cases hsc : s = closedPoint A
  · exfalso
    have hloc : IsLocalRing ((Spec (.of A)).presheaf.stalk s) := inferInstance
    have eA : (Spec (.of A)).presheaf.stalk s ≃+* A := by
      subst hsc
      exact (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv
    rw [@Module.depth_self_eq_of_ringEquiv _ _ _ _ hloc _ eA] at hs
    exact absurd (hdepthA.trans hs) (by norm_num)
  · show f x ∈ Stacks.puncturedSpectrum A
    rw [show f x = s from hx]
    exact hsc

/-- Under a flat morphism to the spectrum of a local domain of dimension at least two, every point
is a specialization of a point over the punctured spectrum. -/
private theorem exists_specializes_mem_preimage_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] (hdim : 2 ≤ ringKrullDim A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] (x : X) :
    ∃ x' : X, x' ⤳ x ∧ x' ∈ f ⁻¹ᵁ Stacks.puncturedSpectrum A := by
  let η : Spec (.of A) := ⟨⊥, Ideal.isPrime_bot⟩
  have hηx : η ⤳ f x := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x', hx'x, hx'η⟩ := Flat.generalizingMap f hηx
  refine ⟨x', hx'x, ?_⟩
  show f x' ∈ Stacks.puncturedSpectrum A
  rw [hx'η]
  intro hηc
  have hbot : maximalIdeal A = ⊥ := (congrArg PrimeSpectrum.asIdeal hηc).symm
  have := ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot)
  rw [this] at hdim
  norm_num at hdim

/-- The extension of [Stacks, Tag 0EY6] of a cover of `X_U` that splits along `σ|_U` is étale over
an open of `X` containing `X_U` and `σ(𝔪)`. -/
private theorem exists_opens_etaleAt_extendedEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepthA : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Smooth f] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (Yobj : FiniteEtaleOver (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    [IsFinite Yobj.hom] [Etale Yobj.hom]
    (σU : (Stacks.puncturedSpectrum A).toScheme ⟶ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    (hσU : σU ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι = (Stacks.puncturedSpectrum A).ι ≫ σ)
    (htriv : Stacks.Etale.IsSplitCover (pullback.snd Yobj.hom σU))
    [IsLocallyNoetherian X]
    (hd : ∀ x : X, x ∉ ((f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) :
    ∃ V : X.Opens, f ⁻¹ᵁ Stacks.puncturedSpectrum A ≤ V ∧ σ (closedPoint A) ∈ V ∧
      ∀ e, (gluedSpectrum (extendedEtaleSituation (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι
        Yobj.hom hd)).toBase e ∈ V → EtaleAt (gluedSpectrum (extendedEtaleSituation
          (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι Yobj.hom hd)).toBase e := by
  let XU := f ⁻¹ᵁ Stacks.puncturedSpectrum A
  let E := gluedSpectrum (extendedEtaleSituation XU.ι Yobj.hom hd)
  let g : E.scheme ⟶ X := E.toBase
  have : IsFinite g := isFinite_relativeSpectrum_extendedEtaleSituation XU.ι Yobj.hom hd
  have : LocallyOfFinitePresentation g := inferInstance
  let cW := extendedEtaleCoverMap XU.ι Yobj.hom hd
  have hE : IsPullback Yobj.hom cW XU.ι g := extendedEtaleCoverMap_isPullback XU.ι Yobj.hom hd
  have : IsOpenImmersion cW := MorphismProperty.of_isPullback hE inferInstance
  let Bad : Set X := g.base '' {e | ¬ EtaleAt g e}
  have hBad : IsClosed Bad := g.isClosedMap _ (isOpen_setOf_etaleAt g).isClosed_compl
  refine ⟨⟨Badᶜ, hBad.isOpen_compl⟩, ?_, ?_, fun e he => by_contra fun h => he ⟨e, h, rfl⟩⟩
  · rintro x hx ⟨e, he, rfl⟩
    obtain ⟨w, -, rfl⟩ := Scheme.exists_preimage_of_isPullback hE (⟨g e, hx⟩ : XU.toScheme) e rfl
    refine he (etaleAt_of_etaleAt_isOpenImmersion_comp cW g w ?_)
    rw [← hE.w]
    exact (etale_iff_forall_etaleAt _).1 inferInstance w
  · rintro ⟨e, he, hge⟩
    exact he (etaleAt_extendedEtale_of_isSplitCover A hdepthA f σ hσ Yobj σU hσU htriv hd e hge)

/-- Let `F` and `Y` be the restrictions of `g : E ⟶ X` to opens `V ⊇ U`. If `F` is the base change
of `Y₁` to `V`, then `Y` is the base change of `Y₁` to `U`. -/
private theorem nonempty_iso_finiteEtaleBaseChange_of_isPullback {X E : Scheme.{u}} {U V : X.Opens}
    (hle : U ≤ V) (g : E ⟶ X) (Y : FiniteEtaleOver U.toScheme) (cY : Y.left ⟶ E)
    (hY : IsPullback Y.hom cY U.ι g) (F : FiniteEtaleOver V.toScheme) (cF : F.left ⟶ E)
    (hF : IsPullback F.hom cF V.ι g) (Y₁ : FiniteEtaleOver X)
    (β : (finiteEtaleBaseChange V.ι).obj Y₁ ≅ F) :
    Nonempty ((finiteEtaleBaseChange U.ι).obj Y₁ ≅ Y) := by
  let c := hF.lift (Y.hom ≫ X.homOfLE hle) cY (by rw [Category.assoc, Scheme.homOfLE_ι, hY.w])
  have hsq1 : IsPullback c Y.hom F.hom (X.homOfLE hle) := by
    refine IsPullback.of_right ?_ (hF.lift_fst _ _ _) hF.flip
    rw [hF.lift_snd, Scheme.homOfLE_ι]
    exact hY.flip
  have hK2 : IsPullback (finiteEtaleBaseChangeProj V.ι Y₁)
      ((finiteEtaleBaseChange V.ι).obj Y₁).hom Y₁.hom V.ι := IsPullback.of_hasPullback _ _
  have hsq2 : IsPullback (β.inv.left ≫ finiteEtaleBaseChangeProj V.ι Y₁) F.hom Y₁.hom
      V.ι := by
    let βL : ((finiteEtaleBaseChange V.ι).obj Y₁).left ≅ F.left :=
      { hom := β.hom.left
        inv := β.inv.left
        hom_inv_id := congrArg (fun φ ↦ φ.left) β.hom_inv_id
        inv_hom_id := congrArg (fun φ ↦ φ.left) β.inv_hom_id }
    refine hK2.of_iso βL (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id]
      exact (βL.hom_inv_id_assoc _).symm
    · rw [Iso.refl_hom, Category.comp_id]
      exact (MorphismProperty.Over.w β.hom).symm
    · simp
    · simp
  have hsq : IsPullback (c ≫ β.inv.left ≫ finiteEtaleBaseChangeProj V.ι Y₁) Y.hom
      Y₁.hom U.ι := by
    convert hsq1.paste_horiz hsq2 using 1
    exact (Scheme.homOfLE_ι X hle).symm
  have hK1 : IsPullback (finiteEtaleBaseChangeProj U.ι Y₁)
      ((finiteEtaleBaseChange U.ι).obj Y₁).hom Y₁.hom U.ι := IsPullback.of_hasPullback _ _
  exact ⟨MorphismProperty.Over.isoMk (hK1.isoIsPullback _ _ hsq)
    (hK1.isoIsPullback_hom_snd _ _ hsq)⟩

/-- **A cover of `X_U` that splits along `σ|_U` extends to `X`.** Over a Noetherian local ring of
depth at least two, a finite étale cover of `X_U` whose base change along `σ|_U` is a split
covering is the restriction of a finite étale cover of `X` ([Stacks, Tags 0EY6, 0EYB]). -/
private theorem exists_finiteEtaleOver_extending_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepthA : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Smooth f] [GeometricallyConnected f]
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (Yobj : FiniteEtaleOver (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    [IsFinite Yobj.hom] [Etale Yobj.hom]
    (σU : (Stacks.puncturedSpectrum A).toScheme ⟶ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme)
    (hσU : σU ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι = (Stacks.puncturedSpectrum A).ι ≫ σ)
    (htriv : Stacks.Etale.IsSplitCover (pullback.snd Yobj.hom σU)) :
    ∃ Y₁ : FiniteEtaleOver X,
      Nonempty ((finiteEtaleBaseChange (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι).obj Y₁ ≅ Yobj) := by
  classical
  let U := Stacks.puncturedSpectrum A
  let XU := f ⁻¹ᵁ U
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hfibS := preimage_singleton_subset_puncturedSpectrum_of_depth_le_one A hdepthA f
  have hdX := two_le_depth_stalk_of_notMem_of_fibre_subset f XU hfibS
  have hd : ∀ x : X, x ∉ (XU.ι.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) := fun x hx => hdX x (by rwa [Scheme.Opens.opensRange_ι] at hx)
  -- the open `Good` above which `E` is étale
  obtain ⟨Good, hle, hσGood, hgood⟩ :=
    exists_opens_etaleAt_extendedEtale A hdepthA f σ hσ Yobj σU hσU htriv hd
  have hXUGood : ∀ x : X, x ∈ XU → x ∈ Good := fun x hx => hle hx
  -- the extension `E` of `Y`
  let E := gluedSpectrum (extendedEtaleSituation XU.ι Yobj.hom hd)
  let g : E.scheme ⟶ X := E.toBase
  have hgfin : IsFinite g := isFinite_relativeSpectrum_extendedEtaleSituation XU.ι Yobj.hom hd
  have : LocallyOfFinitePresentation g := inferInstance
  -- the hypotheses of [Stacks, Tag 0EYB] for `Good`
  have hfibG : ∀ s : Spec (.of A), Module.depth ((Spec (.of A)).presheaf.stalk s)
      (maximalIdeal ((Spec (.of A)).presheaf.stalk s)) ((Spec (.of A)).presheaf.stalk s) ≤ 1 →
        f.base ⁻¹' {s} ⊆ (Good : Set X) := fun s hs x hx => hXUGood x (hfibS s hs hx)
  have hirr : IsIrreducible (f.base ⁻¹' {closedPoint A}) :=
    Abhyankar.isIrreducible_preimage_of_smooth f (closedPoint A : Spec (.of A))
  have hdenseG : ∀ s : Spec (.of A),
      f.base ⁻¹' {s} ⊆ closure ((Good : Set X) ∩ f.base ⁻¹' {s}) := by
    intro s
    by_cases hsc : s = closedPoint A
    · subst hsc
      rw [Set.inter_comm]
      refine subset_closure_inter_of_isPreirreducible_of_isOpen hirr.2 Good.isOpen
        ⟨σ (closedPoint A), apply_section_apply hσ _, hσGood⟩
    · intro x hx
      refine subset_closure ⟨hXUGood x ?_, hx⟩
      show f x ∈ U
      rw [show f x = s from hx]
      exact hsc
  -- `E` over `Good`
  have hres : IsPullback (g ⁻¹ᵁ Good).ι (g ∣_ Good) g Good.ι :=
    (isPullback_morphismRestrict g Good).flip
  have : IsFinite (g ∣_ Good) := MorphismProperty.of_isPullback hres hgfin
  have : Etale (g ∣_ Good) := (etale_iff_forall_etaleAt _).2 fun e' =>
    (etaleAt_iff_of_isPullback hres (Or.inr inferInstance) e').1 (hgood _ e'.2)
  let EGood : FiniteEtaleOver Good.toScheme :=
    MorphismProperty.Over.mk ⊤ (g ∣_ Good) ⟨inferInstance, inferInstance⟩
  have := essSurj_finiteEtaleBaseChange_of_smooth f Good hfibG hdenseG
  -- `Y₁` restricts to `Y` over `X_U`
  exact ⟨_, nonempty_iso_finiteEtaleBaseChange_of_isPullback hle g Yobj _
    (extendedEtaleCoverMap_isPullback XU.ι Yobj.hom hd) EGood _ hres.flip _
    ((finiteEtaleBaseChange Good.ι).objObjPreimageIso EGood)⟩

/-- A finite étale cover of `X` is connected if its base change to an open `U` is, provided every
point of `X` specializes from a point of `U`. -/
private theorem connectedSpace_left_of_finiteEtaleBaseChange_iso {X : Scheme.{u}} (U : X.Opens)
    (hU : ∀ x : X, ∃ x' : X, x' ⤳ x ∧ x' ∈ U) (Y₁ : FiniteEtaleOver X)
    (Y : FiniteEtaleOver U.toScheme) [ConnectedSpace Y.left]
    (e : (finiteEtaleBaseChange U.ι).obj Y₁ ≅ Y) : ConnectedSpace Y₁.left := by
  have : IsFinite Y₁.hom := Y₁.prop.1
  have : Etale Y₁.hom := Y₁.prop.2
  have hK1 : IsPullback (finiteEtaleBaseChangeProj U.ι Y₁)
      ((finiteEtaleBaseChange U.ι).obj Y₁).hom Y₁.hom U.ι := IsPullback.of_hasPullback _ _
  let a := e.inv.left ≫ finiteEtaleBaseChangeProj U.ι Y₁
  have hdense : Dense (Set.range a) := by
    intro y
    obtain ⟨x', hx'y, hx'⟩ := hU (Y₁.hom y)
    obtain ⟨y', hy'y, hy'x'⟩ := Flat.generalizingMap Y₁.hom hx'y
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback hK1 y' (⟨x', hx'⟩ : U.toScheme)
      hy'x'
    refine hy'y.mem_closed isClosed_closure (subset_closure ⟨e.hom.left p, ?_⟩)
    show (e.hom.left ≫ e.inv.left ≫ finiteEtaleBaseChangeProj U.ι Y₁) p = y'
    rw [← Category.assoc, ← MorphismProperty.Comma.comp_left, e.hom_inv_id]
    exact hp
  exact connectedSpace_iff_univ.mpr
    (hdense.closure_eq ▸ (isConnected_range a.continuous).closure)

/-- **[Stacks, Tag 0EYJ], the local claim at a point of codimension at least two.** Let `A` be a
Noetherian local normal domain of dimension at least two with punctured spectrum `U`, and let
`f : X ⟶ Spec A` be smooth with geometrically connected fibres and a section `σ`. Let `Y` be a
finite étale Galois cover of `X_U = f⁻¹(U)` with group `G` having a `U`-point `t` lying over
`σ|_U`. Then `Y` is the restriction of a finite étale Galois cover of `X` with group `G`,
equivariantly.

This is the claim in the proof of [Stacks, Tag 0EYJ] for `dim 𝒪_{S, s} ≥ 2`. `A` has depth at least
two ([Stacks, Tag 031S]), hence so do the local rings of `X` outside `X_U` ([Stacks, Tag 0337]).
Let `E ⟶ X` be the finite extension of `Y` of [Stacks, Tag 0EY6]. Since `Y` has a section over
`σ|_U` it splits there, and the local calculation `etaleAt_extendedEtale_of_isSplitCover`
([Stacks, Tags 05D5, 00MB, 0EY9]) shows that `E` is étale above `σ(𝔪)`. So `E` is finite étale over
an open `V ⊇ X_U` meeting the irreducible closed fibre, and [Stacks, Tag 0EYB] extends `E|_V` to a
finite étale cover `Y'` of `X`. Restriction `FÉt_X ⟶ FÉt_{X_U}` is fully faithful
([Stacks, Tags 0BQF, 0BLR]) and `Y'` is connected, so the Galois structure of `Y` comes from one on
`Y'` (`exists_finiteEtaleGaloisCover_of_fullyFaithful`).

The order of `G` is not used: the source needs it only for codimension-one points.
[Stacks, Tags 0EY9 and 0EYB] are used in their unconditional forms. -/
theorem Abhyankar.exists_finiteEtaleGaloisCover_extending_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] (hdim : 2 ≤ ringKrullDim A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Smooth f] [GeometricallyConnected f]
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (G : Type v) [Group G] [Finite G] (_hG : IsUnit (Nat.card G : A))
    (Y : FiniteEtaleGaloisCover (f ⁻¹ᵁ Stacks.puncturedSpectrum A).toScheme G)
    (t : (Stacks.puncturedSpectrum A).toScheme ⟶ Y.obj.left)
    (ht : t ≫ Y.obj.hom ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι =
      (Stacks.puncturedSpectrum A).ι ≫ σ) :
    ∃ (Y' : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι).obj Y'.obj ≅ Y.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι).map
        (Y'.action g).asIso.hom ≫ e.hom = e.hom ≫ (Y.action g).asIso.hom := by
  classical
  let U := Stacks.puncturedSpectrum A
  let XU := f ⁻¹ᵁ U
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsFinite Y.obj.hom := Y.obj.prop.1
  have : Etale Y.obj.hom := Y.obj.prop.2
  -- depth
  have hdepthA : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed A hdim
  -- the section `σ` over `U`
  have hσrange : Set.range (U.ι ≫ σ) ⊆ XU.ι.opensRange := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    show f (σ (U.ι u)) ∈ U
    rw [apply_section_apply hσ]
    exact u.2
  let σU := IsOpenImmersion.lift XU.ι (U.ι ≫ σ) hσrange
  have hσU : σU ≫ XU.ι = U.ι ≫ σ := IsOpenImmersion.lift_fac _ _ _
  -- `Y` splits along `σ|_U`, because the torsor `Y` has the section `t` there
  have htσ : t ≫ Y.obj.hom = σU := by rw [← cancel_mono XU.ι, Category.assoc, ht, hσU]
  have htriv := Abhyankar.isSplitCover_pullback_snd_comp_hom Y t
  rw [htσ] at htriv
  obtain ⟨Y₁, ⟨e⟩⟩ :=
    exists_finiteEtaleOver_extending_puncturedSpectrum A hdepthA f σ hσ Y.obj σU hσU htriv
  -- full faithfulness of restriction to `X_U`
  have hη := exists_specializes_mem_preimage_puncturedSpectrum A hdim f
  have hdenseXU : Dense (XU : Set X) := fun x => by
    obtain ⟨x', hx'x, hx'⟩ := hη x
    exact hx'x.mem_closed isClosed_closure (subset_closure hx')
  have hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite := by
    intro V hV
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV
    have : IsNoetherian V := { __ := isLocallyNoetherian_of_isOpenImmersion V.ι }
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  obtain ⟨hff⟩ := fullyFaithful_finiteEtaleBaseChange_of_finite_irreducibleComponents X XU
    hfinite hdenseXU fun x hx => isConnectedPuncturedStrictHenselization_of_two_le_depth _
      (two_le_depth_stalk_of_notMem_of_fibre_subset f XU
        (preimage_singleton_subset_puncturedSpectrum_of_depth_le_one A hdepthA f) x hx)
  -- `Y₁` is connected
  exact exists_finiteEtaleGaloisCover_of_fullyFaithful XU.ι hff G Y₁
    (connectedSpace_left_of_finiteEtaleBaseChange_iso XU hη Y₁ Y.obj e) Y e

end AlgebraicGeometry

end
