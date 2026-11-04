module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesEssSurj
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SmoothPowerSeriesChart
public import StacksFrontier.AlgebraicGeometry.Properties.Specialization
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential surjectivity of finite étale restriction for a smooth morphism

Let `f : X ⟶ S` be smooth with `S` Noetherian and `U ⊆ X` an open such that `X_s = U_s` whenever
`depth 𝒪_{S, s} ≤ 1` and `U_s` is dense in `X_s` for every `s ∈ S`. Then every finite étale cover
of `U` is the restriction of a finite étale cover of `X`. This is the essential surjectivity half
of [Stacks, Tag 0EYB].

## Main results

* `Stacks.FundamentalGroup.mem_of_forall_specializes_fiber` — a point of `X` with no strict
  generalization in its fibre lies in `U`.
* `Stacks.FundamentalGroup.isClosed_asFiber_of_isClosed_preimage`,
  `Stacks.FundamentalGroup.exists_isClosed_asFiber_specializes` — closed points of the fibres.
* `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_of_smooth` — essential surjectivity.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EYA](https://stacks.math.columbia.edu/tag/0EYA)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Topology

universe u

namespace Stacks.FundamentalGroup

/-! ### Generic points of the fibres lie in `U` -/

/-- **A point with no strict generalization in its fibre lies in an open that is dense in every
fibre.** Let `f : X ⟶ S` be locally of finite type and `U ⊆ X` an open with `U ∩ f⁻¹(s)` dense
in `f⁻¹(s)` for every `s`. If no point of `f⁻¹(f(y))` other than `y` specializes to `y`, then
`y ∈ U`. -/
@[sga "3 VIB 5.4.1" "special case"]
public theorem mem_of_forall_specializes_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (U : X.Opens)
    (hdense : ∀ s : S, f.base ⁻¹' {s} ⊆ closure ((U : Set X) ∩ f.base ⁻¹' {s}))
    (y : X) (hy : ∀ w : X, w ⤳ y → f w = f y → w = y) : y ∈ U := by
  let s := f y
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  let ι := f.fiberι s
  have hind : Topology.IsInducing ι.base := ι.isEmbedding.isInducing
  have hrange : Set.range ι.base = f.base ⁻¹' {s} := f.range_fiberι s
  have hιy : ι (f.asFiber y) = y := f.fiberι_asFiber y
  have hD : Dense (ι.base ⁻¹' (U : Set X)) := by
    intro w
    rw [hind.closure_eq_preimage_closure_image, Set.mem_preimage]
    have himage : ι.base '' (ι.base ⁻¹' (U : Set X)) = (U : Set X) ∩ f.base ⁻¹' {s} := by
      rw [Set.image_preimage_eq_inter_range, hrange]
    rw [himage]
    exact hdense s (hrange ▸ Set.mem_range_self w)
  have hgen : f.asFiber y ∈ genericPoints (f.fiber s) := by
    refine ⟨isIrreducible_singleton.closure, fun Z hZ hsub => ?_⟩
    have hZc := hZ.closure
    let η := hZ.genericPoint
    have hη : closure ({η} : Set (f.fiber s)) = closure Z := hZ.genericPoint_closure_eq
    have hηy : η ⤳ f.asFiber y := by
      rw [specializes_iff_mem_closure, hη]
      exact subset_closure (hsub (subset_closure (Set.mem_singleton _)))
    have hιη : ι η = y := by
      refine hy (ι η) ?_ ?_
      · have := hηy.map ι.continuous
        rwa [hιy] at this
      · have : ι η ∈ f.base ⁻¹' {s} := hrange ▸ Set.mem_range_self η
        exact this
    have hηeq : η = f.asFiber y :=
      ι.isEmbedding.injective (hιη.trans (f.fiberι_asFiber y).symm)
    rw [← hηeq, hη]
    exact subset_closure
  have := Scheme.mem_of_mem_genericPoints_of_dense (f.fiber s)
    (U.isOpen.preimage ι.continuous) hD hgen
  rw [Set.mem_preimage, hιy] at this
  exact this

/-! ### Closed points of the fibres -/

/-- **A point closed in the subspace `f⁻¹(f(z))` is closed in the scheme-theoretic fibre.** If `z`
is closed in `f⁻¹(f(z)) ⊆ X`, then the corresponding point `f.asFiber z` is closed in the fibre
`X_{f(z)}`. -/
public theorem isClosed_asFiber_of_isClosed_preimage {X S : Scheme.{u}} (f : X ⟶ S) (z : X)
    (hz : IsClosed ({⟨z, rfl⟩} : Set (f.base ⁻¹' {f z}))) :
    IsClosed ({f.asFiber z} : Set (f.fiber (f z))) := by
  have hpre : (f.fiberHomeo (f z)) ⁻¹' {⟨z, rfl⟩} = {f.asFiber z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply (f.fiberι (f z)).isEmbedding.injective
      rw [f.fiberι_asFiber, ← f.fiberHomeo_apply, h]
    · rintro rfl
      exact Subtype.ext (f.fiberι_asFiber z)
  rw [← hpre]
  exact hz.preimage (f.fiberHomeo (f z)).continuous

/-- **Every point of a fibre of a morphism locally of finite type specializes, inside the fibre,
to a point closed in the fibre.** -/
public theorem exists_isClosed_asFiber_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    ∃ z : X, f z = f x ∧ x ⤳ z ∧ IsClosed ({f.asFiber z} : Set (f.fiber (f z))) := by
  let F := f.base ⁻¹' {f x}
  have : JacobsonSpace F :=
    .of_isClosedEmbedding (f.fiberHomeo (f x)).symm.isClosedEmbedding
  let x' : F := ⟨x, rfl⟩
  have hne : (closure ({x'} : Set F) ∩ closedPoints F).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := closure_inter_closedPoints (X := F) (isClosed_closure (s := {x'}))
    rw [h, closure_empty] at this
    exact (this ▸ subset_closure (Set.mem_singleton x') : x' ∈ (∅ : Set F))
  obtain ⟨⟨z, hzF⟩, hzx, hzc⟩ := hne
  have hfz : f z = f x := hzF
  refine ⟨z, hfz, ?_, ?_⟩
  · exact (specializes_iff_mem_closure.mpr hzx).map continuous_subtype_val
  · have hset : F = f.base ⁻¹' {f z} := by rw [hfz]
    let e := Homeomorph.setCongr hset
    have hpre : e ⁻¹' {⟨z, rfl⟩} = {⟨z, hzF⟩} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      rfl
    refine isClosed_asFiber_of_isClosed_preimage f z ?_
    rw [← e.isClosed_preimage, hpre]
    exact hzc

/-! ### Essential surjectivity -/

open ExtendedEtaleFold Stacks.RelativeSpec Stacks.Algebraization in
/-- **Essential surjectivity in [Stacks, Tag 0EYB].** Let `f : X ⟶ S` be smooth with `S`
Noetherian, and `U ⊆ X` an open with `X_s = U_s` whenever `depth 𝒪_{S, s} ≤ 1` and with `U_s`
dense in `X_s` for every `s`. Then every finite étale cover of `U` is the restriction of a finite
étale cover of `X`. -/
public theorem essSurj_finiteEtaleBaseChange_of_smooth {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsNoetherian S] (U : X.Opens)
    (hfib : ∀ s : S, Module.depth (S.presheaf.stalk s) (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s) ≤ 1 → f.base ⁻¹' {s} ⊆ (U : Set X))
    (hdense : ∀ s : S, f.base ⁻¹' {s} ⊆ closure ((U : Set X) ∩ f.base ⁻¹' {s})) :
    (finiteEtaleBaseChange U.ι).EssSurj := by
  classical
  refine ⟨fun W => ?_⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  have hdU := two_le_depth_stalk_of_notMem_of_fibre_subset f U hfib
  have hd : ∀ x : X, x ∉ (U.ι.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) := fun x hx => hdU x (by rwa [Scheme.Opens.opensRange_ι] at hx)
  let E := gluedSpectrum (extendedEtaleSituation U.ι W.hom hd)
  let g : E.scheme ⟶ X := E.toBase
  have hgfin : IsFinite g := isFinite_relativeSpectrum_extendedEtaleSituation U.ι W.hom hd
  have : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian g
  let cW := extendedEtaleCoverMap U.ι W.hom hd
  have hE : IsPullback W.hom cW U.ι g := extendedEtaleCoverMap_isPullback U.ι W.hom hd
  have : IsOpenImmersion cW := MorphismProperty.of_isPullback hE inferInstance
  have hetU : ∀ e : E.scheme, g e ∈ U → EtaleAt g e := by
    intro e he
    obtain ⟨w, -, rfl⟩ :=
      Scheme.exists_preimage_of_isPullback hE (⟨g e, he⟩ : U.toScheme) e rfl
    refine etaleAt_of_etaleAt_isOpenImmersion_comp cW g w ?_
    rw [← hE.w]
    exact (etale_iff_forall_etaleAt _).1 inferInstance w
  let Bad : Set X := g.base '' {e | ¬ EtaleAt g e}
  have hBad : IsClosed Bad := g.isClosedMap _ (isOpen_setOf_etaleAt g).isClosed_compl
  have hnotBad : ∀ x : X, x ∉ Bad → ∀ e : E.scheme, g e = x → EtaleAt g e :=
    fun x hx e he => by_contra fun h => hx ⟨e, h, he⟩
  have hUBad : ∀ x : X, x ∈ U → x ∉ Bad := by
    rintro x hx ⟨e, he, rfl⟩
    exact he (hetU e hx)
  let Good : X.Opens := ⟨Badᶜ, hBad.isOpen_compl⟩
  have : LocallyOfFinitePresentation g := inferInstance
  have key : ∀ s : S, ∀ e : E.scheme, f (g e) = s → EtaleAt g e := by
    intro s
    induction s using (InvImage.wf (fun s : S => Order.coheight s) wellFounded_lt).induction with
    | h s ih =>
    intro e₀ he₀
    by_contra hne
    have hx₀ : g e₀ ∈ Bad := ⟨e₀, hne, rfl⟩
    have hx₀U : g e₀ ∉ U := fun h => hne (hetU e₀ h)
    have hdepthS : (2 : ℕ∞) ≤ Module.depth (S.presheaf.stalk s)
        (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) := by
      have hnot : ¬ Module.depth (S.presheaf.stalk s) (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s) ≤ 1 := fun hle => hx₀U (hfib s hle he₀)
      exact Order.add_one_le_of_lt (by simpa using not_le.1 hnot)
    obtain ⟨z, hfz, hxz, hzc⟩ := exists_isClosed_asFiber_specializes f (g e₀)
    have hzBad : z ∈ Bad := hxz.mem_closed hBad hx₀
    have hfzs : f z = s := hfz.trans he₀
    obtain ⟨A, _, _, _, d, α, φ, hαflat, hφflat, hαc, hαq, hφα, hφc⟩ :=
      exists_flat_powerSeries_chart f z hzc
    rw [hfzs] at hαc hαq
    have hdepthA : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A := by
      let pA : Spec (.of A) := IsLocalRing.closedPoint A
      have h1 := depth_stalk_le_depth_stalk_of_flat α pA
      rw [hαc] at h1
      have hloc : IsLocalRing ((Spec (.of A)).presheaf.stalk pA) := inferInstance
      rw [@Module.depth_self_eq_of_ringEquiv _ _ _ _ hloc _
        (AlgebraicGeometry.stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv] at h1
      exact hdepthS.trans h1
    let T : Scheme.{u} := Spec (.of (MvPowerSeries (Fin d) A))
    have hET : IsPullback (Limits.pullback.fst g φ) (Limits.pullback.snd g φ) g φ :=
      IsPullback.of_hasPullback g φ
    let gT := Limits.pullback.snd g φ
    have : IsFinite gT := MorphismProperty.of_isPullback hET inferInstance
    have : Flat (Limits.pullback.fst g φ) := MorphismProperty.of_isPullback hET.flip hφflat
    have : IsLocallyNoetherian (Limits.pullback g φ) := LocallyOfFiniteType.isLocallyNoetherian gT
    let VT : T.Opens := φ ⁻¹ᵁ Good
    have hgfst (e' : (Limits.pullback g φ : Scheme.{u})) :
        g (Limits.pullback.fst g φ e') = φ (gT e') := by
      exact congr($(hET.w) e')
    have hφf (q : T) : f (φ q) = α ((Spec.map (CommRingCat.ofHom MvPowerSeries.C)) q) := by
      exact congr($(hφα) q)
    let pT : T := IsLocalRing.closedPoint (MvPowerSeries (Fin d) A)
    have hV₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
        q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
          q ∈ VT := by
      intro q hq
      let qT : T := q
      let t : Spec (.of A) := (Spec.map (CommRingCat.ofHom MvPowerSeries.C)) qT
      have ht : t ≠ IsLocalRing.closedPoint A := fun h => hq (congrArg PrimeSpectrum.asIdeal h)
      have hts : α t ≠ s := fun h => ht (hαq t h)
      have hsp : α t ⤳ s := by
        rw [← hαc]
        exact (IsLocalRing.specializes_closedPoint t).map α.continuous
      have hlt := coheight_lt_coheight_of_specializes S hsp hts
      have ih' := ih (α t) hlt
      show φ qT ∉ Bad
      rintro ⟨e, he, hge⟩
      exact he (ih' e (by rw [hge, hφf]))
    have hV₂ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
        q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
          (maximalIdeal A) → q ∈ VT := by
      intro q hq
      let qT : T := q
      have hqA : (Spec.map (CommRingCat.ofHom MvPowerSeries.C)) qT =
          IsLocalRing.closedPoint A := by
        refine PrimeSpectrum.ext ?_
        show q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) = _
        rw [hq]
        exact ((maximalIdeal.isMaximal A).eq_of_le
          (by rw [← hq]; exact (Ideal.IsPrime.comap _).ne_top) Ideal.le_comap_map).symm
      refine hUBad _ (mem_of_forall_specializes_fiber f U hdense (φ qT) fun w hw hfw => ?_)
      obtain ⟨q', hq'q, rfl⟩ := Flat.generalizingMap φ hw
      have hq'A : (Spec.map (CommRingCat.ofHom MvPowerSeries.C)) q' =
          IsLocalRing.closedPoint A := hαq _ (by rw [← hφf, hfw, hφf, hqA, hαc])
      have hle : q'.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hq'q
      have hge : q.asIdeal ≤ q'.asIdeal := by
        rw [hq, Ideal.map_le_iff_le_comap]
        exact (congrArg PrimeSpectrum.asIdeal hq'A).ge
      rw [show q' = q from PrimeSpectrum.ext (hle.antisymm hge)]
    have hiff := etaleAt_iff_of_isPullback hET (Or.inr hφflat)
    have hetT : Etale gT := by
      refine etale_of_etaleAt_of_two_le_depth_mvPowerSeries A d hdepthA VT hV₁ hV₂ gT
        (fun e' he' => ?_) (fun e' he' => ?_)
      · exact (hiff e').1 (hnotBad _ he' _ (hgfst e'))
      · refine le_trans ?_ (depth_stalk_le_depth_stalk_of_flat (Limits.pullback.fst g φ) e')
        refine extendedEtale_depth_ge_two U.ι W.hom hd _ ?_
        rw [Scheme.Opens.opensRange_ι]
        show g (Limits.pullback.fst g φ e') ∉ U
        rw [hgfst]
        exact fun h => he' (hUBad _ h)
    obtain ⟨e, he, hez⟩ := hzBad
    obtain ⟨e', he'1, he'2⟩ := Scheme.Pullback.exists_preimage_pullback e pT (hez.trans hφc.symm)
    exact he (he'1 ▸ (hiff e').2 ((etale_iff_forall_etaleAt gT).1 hetT e'))
  have hetE : Etale g := (etale_iff_forall_etaleAt g).2 fun e => key _ e rfl
  let F : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ g ⟨hgfin, hetE⟩
  exact ⟨F, ⟨MorphismProperty.Over.isoMk hE.flip.isoPullback.symm hE.flip.isoPullback_inv_snd⟩⟩

end Stacks.FundamentalGroup

end
