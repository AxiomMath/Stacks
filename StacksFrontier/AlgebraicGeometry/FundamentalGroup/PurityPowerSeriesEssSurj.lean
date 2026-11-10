module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.MvPowerSeries
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Permanence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionDepth
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.LocalCohomology.HartshorneConnectednessHenselian

/-!
# Essential surjectivity of finite étale restriction over a power series ring

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two and let `B = A[[x_1, …, x_d]]` with
`d ≥ 1`. For an open `V ⊆ Y = Spec B` which contains every prime `𝔮` of `B` with `𝔮 ∩ A ≠ 𝔪`
and contains the prime `𝔪B`, every finite étale cover of `V` is the restriction of a finite
étale cover of `Y`. As a consequence, a finite morphism to `Spec A[[x_1, …, x_d]]` which is étale
above such an open `V`, and whose local rings above the complement of `V` have depth at least two,
is étale.

## Main results

* `Stacks.FundamentalGroup.dense_of_comap_ne_maximalIdeal_mem_of_flat` — such an open is dense,
  along any flat map from a local ring of positive depth.
* `Stacks.FundamentalGroup.exists_isPullback_of_isPullback_restrict` — a finite extension of the
  restriction of a cover to a smaller open, with depth at least two off that open, is an extension
  of the cover itself.
* `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_mvPowerSeries` — essential surjectivity.
* `Stacks.FundamentalGroup.etale_of_etaleAt_of_two_le_depth_mvPowerSeries` — the étaleness
  criterion.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
* [Stacks Project, Tag 0EYA](https://stacks.math.columbia.edu/tag/0EYA)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.FundamentalGroup

/-! ### Density of the open `V` -/

/-- **An open containing the primes not over the closed point is dense, along a flat map.** Let
`(A, 𝔪)` be a local ring of positive depth, `B` a flat `A`-algebra, and `V` an open of `Spec B`
containing every prime `𝔮` with `𝔮 ∩ A ≠ 𝔪`. Then `V` is dense. -/
public theorem dense_of_comap_ne_maximalIdeal_mem_of_flat (A B : Type u) [CommRing A]
    [IsLocalRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V) :
    Dense (V : Set (Spec (.of B))) := by
  obtain ⟨a, ha, hreg⟩ := exists_regular_of_depth_pos (R := A) (M := A)
    (by
      rw [← AlgebraicGeometry.depth_eq_depthSup_of_isLocalRing]
      exact lt_of_lt_of_le zero_lt_one hdepth)
  have hreg' : IsSMulRegular B (algebraMap A B a) := hreg.of_flat
  have hCa : algebraMap A B a ∈ nonZeroDivisors B :=
    mem_nonZeroDivisors_iff_right.mpr fun x hx =>
      hreg'.right_eq_zero_of_smul (by rw [smul_eq_mul, mul_comm]; exact hx)
  intro y
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨q, hq, hqy⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ y.asIdeal)
  have : q.IsPrime := hq.1.1
  have hqV : (⟨q, this⟩ : PrimeSpectrum B) ∈ V := by
    refine hV₁ _ fun h => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ?_ hq hCa
    change algebraMap A B a ∈ q
    rw [← Ideal.mem_comap, show q.comap (algebraMap A B) = maximalIdeal A from h]
    exact ha
  exact closure_mono (Set.singleton_subset_iff.2 hqV)
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 hqy)

/-! ### Identifying a finite extension over a larger open -/

open ExtendedEtaleFold Stacks.RelativeSpec in
/-- **A finite extension of the restriction of a cover is an extension of the cover itself.** Let
`Y` be a locally Noetherian scheme, `V' ≤ V` two opens of `Y`, and suppose that `𝒪_{Y, y}` has
depth at least two at every point `y` outside `V'`. Let `W` be a finite étale cover of `V` and let
`f : G ⟶ Y` be finite, with `G ×_Y V'` identified with the restriction `W'` of `W` to `V'`, and
with local rings of depth at least two above the complement of `V'`. Then `G ×_Y V` is identified
with `W` itself. -/
public theorem exists_isPullback_of_isPullback_restrict {Y G : Scheme.{u}} [IsLocallyNoetherian Y]
    (V V' : Y.Opens) (hVV : V' ≤ V)
    (hdepth : ∀ y : Y, y ∉ V' →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y))
    (W : FiniteEtaleOver V.toScheme) (f : G ⟶ Y) [IsFinite f]
    (c' : ((finiteEtaleBaseChange (Y.homOfLE hVV)).obj W).left ⟶ G)
    (hc' : IsPullback ((finiteEtaleBaseChange (Y.homOfLE hVV)).obj W).hom c' V'.ι f)
    (hdepthG : ∀ y : G, f y ∉ V' →
      (2 : ℕ∞) ≤ Module.depth (G.presheaf.stalk y) (maximalIdeal (G.presheaf.stalk y))
        (G.presheaf.stalk y)) :
    ∃ c : W.left ⟶ G, IsPullback W.hom c V.ι f := by
  classical
  let W' := (finiteEtaleBaseChange (Y.homOfLE hVV)).obj W
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  have : IsFinite W'.hom := W'.prop.1
  have : Etale W'.hom := W'.prop.2
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have : IsLocallyNoetherian W.left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ W.hom _ (inferInstanceAs
      (IsLocallyNoetherian V.toScheme))
  have : IsLocallyNoetherian ((𝟭 Scheme.{u}).obj W.left) := this
  have : IsLocallyNoetherian ((Functor.fromPUnit V.toScheme).obj W.right) :=
    inferInstanceAs (IsLocallyNoetherian V.toScheme)
  have hdV : ∀ x : Y, x ∉ (V.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk x) (maximalIdeal (Y.presheaf.stalk x))
        (Y.presheaf.stalk x) := fun x hx =>
    hdepth x fun hx' => hx (by rw [Scheme.Opens.opensRange_ι]; exact hVV hx')
  have hdV' : ∀ x : Y, x ∉ (V'.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk x) (maximalIdeal (Y.presheaf.stalk x))
        (Y.presheaf.stalk x) := fun x hx =>
    hdepth x fun hx' => hx (by rw [Scheme.Opens.opensRange_ι]; exact hx')
  let E := gluedSpectrum (extendedEtaleSituation V.ι W.hom hdV)
  have hfinE : IsFinite E.toBase :=
    isFinite_relativeSpectrum_extendedEtaleSituation V.ι W.hom hdV
  have : IsLocallyNoetherian (extendedEtaleSituation V.ι W.hom hdV).base := by
    change IsLocallyNoetherian Y
    infer_instance
  have : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian E.toBase
  let cW := extendedEtaleCoverMap V.ι W.hom hdV
  have hE : IsPullback W.hom cW V.ι E.toBase := extendedEtaleCoverMap_isPullback V.ι W.hom hdV
  have : IsOpenImmersion cW := MorphismProperty.of_isPullback hE inferInstance
  have hA : IsPullback (finiteEtaleBaseChangeProj (Y.homOfLE hVV) W) W'.hom W.hom
      (Y.homOfLE hVV) := IsPullback.of_hasPullback W.hom (Y.homOfLE hVV)
  have hE' : IsPullback W'.hom (finiteEtaleBaseChangeProj (Y.homOfLE hVV) W ≫ cW) V'.ι
      E.toBase := by
    have := (hA.paste_horiz hE.flip).flip
    rwa [Scheme.homOfLE_ι] at this
  have hdepthE : ∀ e : E.scheme, E.toBase e ∉ (V'.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (E.scheme.presheaf.stalk e)
        (maximalIdeal (E.scheme.presheaf.stalk e)) (E.scheme.presheaf.stalk e) := by
    intro e he
    rw [Scheme.Opens.opensRange_ι] at he
    by_cases hV : E.toBase e ∈ V
    · obtain ⟨w, hw, hwe⟩ := Scheme.exists_preimage_of_isPullback hE
        (⟨E.toBase e, hV⟩ : V.toScheme) e rfl
      subst hwe
      have h1 := RingHom.depth_eq_of_isEtaleLocalHom (cW.stalkMap w).hom
        ((AlgebraicGeometry.etale_iff_forall_isEtaleAt cW).mp inferInstance w)
      have h2 := RingHom.depth_eq_of_isEtaleLocalHom (W.hom.stalkMap w).hom
        ((AlgebraicGeometry.etale_iff_forall_isEtaleAt W.hom).mp inferInstance w)
      have h3 := RingHom.depth_eq_of_isEtaleLocalHom (V.ι.stalkMap (W.hom w)).hom
        ((AlgebraicGeometry.etale_iff_forall_isEtaleAt V.ι).mp inferInstance (W.hom w))
      have hkey : V.ι (W.hom w) = E.toBase (cW w) :=
        (Scheme.Hom.comp_apply W.hom V.ι w).symm.trans
          ((congrArg (fun g : W.left ⟶ Y => g w) hE.w).trans (Scheme.Hom.comp_apply cW _ w))
      have h0 := hdepth (V.ι (W.hom w)) fun h => he (hkey ▸ h)
      exact h0.trans_eq (h3.trans (h2.trans h1.symm))
    · exact extendedEtale_depth_ge_two V.ι W.hom hdV e (by rwa [Scheme.Opens.opensRange_ι])
  have hdepthG' : ∀ y : G, f y ∉ (V'.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (G.presheaf.stalk y) (maximalIdeal (G.presheaf.stalk y))
        (G.presheaf.stalk y) := fun y hy =>
    hdepthG y (by rwa [Scheme.Opens.opensRange_ι] at hy)
  obtain ⟨eG, ⟨hG, -⟩, -⟩ := extendedEtale_unique V'.ι W'.hom hdV' f c' hc' hdepthG'
  obtain ⟨eE, ⟨hEE, -⟩, -⟩ :=
    @extendedEtale_unique _ _ _ _ _ V'.ι _ W'.hom _ _ hdV' E.toBase hfinE _ hE' hdepthE
  let φ : E.scheme ≅ G := eE ≪≫ eG.symm
  have hGi : eG.inv ≫ f = (gluedSpectrum (extendedEtaleSituation V'.ι W'.hom hdV')).toBase :=
    (Iso.inv_comp_eq eG).mpr hG.symm
  have hφ : φ.hom ≫ f = E.toBase :=
    (Category.assoc _ _ _).trans ((congrArg (eE.hom ≫ ·) hGi).trans hEE)
  refine ⟨cW ≫ φ.hom, ?_⟩
  refine hE.of_iso (Iso.refl _) (Iso.refl _) φ (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans hφ.symm

/-! ### Essential surjectivity -/

/-- Transporting a pullback square along an isomorphism of its top-left corner. -/
private theorem isPullback_of_iso_left {C : Type*} [Category C] {P P' X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : P ≅ P')
    (fst' : P' ⟶ X) (hfst : e.hom ≫ fst' = fst) : IsPullback fst' (e.inv ≫ snd) f g :=
  h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simpa using hfst.symm) (by simp) (by simp)
    (by simp)

/-- If `W ⟶ U` is étale and `W ⟶ E` is an open immersion in a pullback square over the open `U`,
then `g : E ⟶ Y` is étale at every point above `U`. -/
private theorem etaleAt_of_mem_of_isPullback {Y E W : Scheme.{u}} (U : Y.Opens) (a : W ⟶ U.toScheme)
    (c : W ⟶ E) (g : E ⟶ Y) [Etale a] [IsOpenImmersion c] (h : IsPullback a c U.ι g) (y : E)
    (hy : g y ∈ U) : EtaleAt g y := by
  obtain ⟨w, -, rfl⟩ := Scheme.exists_preimage_of_isPullback h (⟨g y, hy⟩ : U.toScheme) y rfl
  refine ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp c g w ?_
  rw [← h.w]
  exact (etale_iff_forall_etaleAt _).1 inferInstance w

open ExtendedEtaleFold Stacks.RelativeSpec Stacks.Algebraization in
/-- **Essential surjectivity in [Stacks, Tag 0EYA].** Let `(A, 𝔪)` be a Noetherian local ring of
depth at least two, `B = A[[x_1, …, x_d]]` with `d ≥ 1`, and `V ⊆ Y = Spec B` an open containing
every prime `𝔮` with `𝔮 ∩ A ≠ 𝔪` and the prime `𝔪B`. Then every finite étale cover of `V` is the
restriction of a finite étale cover of `Y`. -/
public theorem essSurj_finiteEtaleBaseChange_mvPowerSeries (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ) (hd : 0 < d)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
        q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
        (maximalIdeal A) → q ∈ V) :
    (finiteEtaleBaseChange V.ι).EssSurj := by
  classical
  refine ⟨fun W => ?_⟩
  let B := MvPowerSeries (Fin d) A
  let Y : Scheme.{u} := Spec (.of B)
  let X : Scheme.{u} := Spec (.of A)
  let p : Y ⟶ X := Spec.map (CommRingCat.ofHom (MvPowerSeries.C : A →+* B))
  let s : X ⟶ Y := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff : B →+* A))
  have hsp : s ≫ p = 𝟙 X := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have hsp_apply (x : X) : p (s x) = x := by
    rw [← Scheme.Hom.comp_apply, hsp]
    rfl
  let V' : Y.Opens := p ⁻¹ᵁ Stacks.puncturedSpectrum A
  have hmemV' (q : Y) : q ∈ V' ↔
      q.asIdeal.comap (MvPowerSeries.C : A →+* B) ≠ maximalIdeal A := by
    change p q ≠ IsLocalRing.closedPoint A ↔ _
    exact not_congr ⟨fun h => congrArg PrimeSpectrum.asIdeal h, fun h => PrimeSpectrum.ext h⟩
  have hVV : V' ≤ V := fun q hq => hV₁ q ((hmemV' q).1 hq)
  have hdepthY : ∀ y : Y, y ∉ V' →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y) :=
    two_le_depth_stalk_of_notMem_mvPowerSeries A d hdepth V' fun q hq => (hmemV' q).2 hq
  let U₀ : X.Opens := s ⁻¹ᵁ V'
  have hmemU₀ (x : X) : x ∈ U₀ ↔ x ≠ IsLocalRing.closedPoint A := by
    change p (s x) ≠ _ ↔ _
    rw [hsp_apply]
  have hU₀ : (U₀ : Set X) = {IsLocalRing.closedPoint A}ᶜ := by
    ext x
    exact hmemU₀ x
  obtain ⟨hFF⟩ := fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries A d hd hdepth V' hU₀
  let W' := (finiteEtaleBaseChange (Y.homOfLE hVV)).obj W
  let W₀ := (finiteEtaleBaseChange (s ∣_ V')).obj W'
  have : IsFinite W₀.hom := W₀.prop.1
  have : Etale W₀.hom := W₀.prop.2
  have hle : V' ≤ p ⁻¹ᵁ U₀ := fun y hy => by
    change p y ∈ U₀
    rw [hmemU₀]
    exact hy
  let q : V'.toScheme ⟶ U₀.toScheme := p.resLE U₀ V' hle
  have hq : q ≫ U₀.ι = V'.ι ≫ p := Scheme.Hom.resLE_comp_ι p hle
  have hsq : (s ∣_ V') ≫ q = 𝟙 U₀.toScheme := by
    rw [← cancel_mono U₀.ι, Category.assoc, hq, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hsp, Category.comp_id, Category.id_comp]
  let W'' := (finiteEtaleBaseChange q).obj W₀
  let eI : (finiteEtaleBaseChange (s ∣_ V')).obj W'' ≅ W₀ :=
    ((finiteEtaleBaseChangeComp (s ∣_ V') q (𝟙 _) hsq.symm).app W₀).symm ≪≫
      finiteEtaleBaseChangeId.app W₀
  let e : W'' ≅ W' := hFF.preimageIso eI
  have hdX : ∀ x : X, x ∉ (U₀.ι.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) := by
    intro x hx
    rw [Scheme.Opens.opensRange_ι] at hx
    have hx' : x = IsLocalRing.closedPoint A := not_not.1 fun h => hx ((hmemU₀ x).2 h)
    have hloc : IsLocalRing (X.presheaf.stalk x) := inferInstance
    subst hx'
    rw [@Module.depth_self_eq_of_ringEquiv _ _ _ _ hloc _
      (AlgebraicGeometry.stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv]
    exact hdepth
  let E₀ := gluedSpectrum (extendedEtaleSituation U₀.ι W₀.hom hdX)
  let f₀ : E₀.scheme ⟶ X := E₀.toBase
  have : IsFinite f₀ := isFinite_relativeSpectrum_extendedEtaleSituation U₀.ι W₀.hom hdX
  let c₀ := extendedEtaleCoverMap U₀.ι W₀.hom hdX
  have hE₀ : IsPullback W₀.hom c₀ U₀.ι f₀ := extendedEtaleCoverMap_isPullback U₀.ι W₀.hom hdX
  have : IsOpenImmersion c₀ := MorphismProperty.of_isPullback hE₀ inferInstance
  have hpflat : Flat p := by
    refine Flat.SpecMap_iff.mpr ?_
    have hCA : (algebraMap A (MvPowerSeries (Fin d) A)) =
        (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) := by
      ext a; simp [MvPowerSeries.algebraMap_apply]
    have : Module.Flat A (MvPowerSeries (Fin d) A) :=
      (Module.flat_and_mittagLeffler_mvPowerSeries A d).1
    rw [CommRingCat.hom_ofHom, ← hCA]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  let G := Limits.pullback f₀ p
  let g : G ⟶ Y := Limits.pullback.snd f₀ p
  let gfst : G ⟶ E₀.scheme := Limits.pullback.fst f₀ p
  have hG : IsPullback gfst g f₀ p := IsPullback.of_hasPullback f₀ p
  have : IsFinite g := MorphismProperty.of_isPullback hG inferInstance
  have : Flat gfst := MorphismProperty.of_isPullback hG.flip inferInstance
  have : IsLocallyNoetherian Y := inferInstance
  have : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian g
  have hW'' : IsPullback (finiteEtaleBaseChangeProj q W₀) W''.hom W₀.hom q :=
    IsPullback.of_hasPullback W₀.hom q
  have hrect := hW''.paste_horiz hE₀.flip
  rw [hq] at hrect
  have hS := (IsPullback.of_right' hrect hG).flip
  let k : W''.left ⟶ G := hG.lift (finiteEtaleBaseChangeProj q W₀ ≫ c₀) (W''.hom ≫ V'.ι)
    (by rw [hrect.w, Category.assoc])
  change IsPullback W''.hom k V'.ι g at hS
  let eL : W''.left ≅ W'.left := (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso e
  have hc' : IsPullback W'.hom (eL.inv ≫ k) V'.ι g :=
    isPullback_of_iso_left hS eL _ (MorphismProperty.Over.w e.hom)
  have hdepthG : ∀ y : G, g y ∉ V' →
      (2 : ℕ∞) ≤ Module.depth (G.presheaf.stalk y) (maximalIdeal (G.presheaf.stalk y))
        (G.presheaf.stalk y) := by
    intro y hy
    have hpy : p (g y) = IsLocalRing.closedPoint A := not_not.1 hy
    have hfy : f₀ (gfst y) = p (g y) := by
      rw [← Scheme.Hom.comp_apply, hG.w, Scheme.Hom.comp_apply]
    refine le_trans ?_ (depth_stalk_le_depth_stalk_of_flat gfst y)
    refine extendedEtale_depth_ge_two U₀.ι W₀.hom hdX (gfst y) ?_
    rw [Scheme.Opens.opensRange_ι]
    change f₀ (gfst y) ∉ U₀
    rw [hfy, hmemU₀, hpy]
    exact fun h => h rfl
  obtain ⟨c, hc⟩ := exists_isPullback_of_isPullback_restrict V V' hVV hdepthY W g
    (eL.inv ≫ k) hc' hdepthG
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  have : IsOpenImmersion c := MorphismProperty.of_isPullback hc inferInstance
  have hetG : ∀ y : G, g y ∈ V → EtaleAt g y := etaleAt_of_mem_of_isPullback V W.hom c g hc
  have hker := MvPowerSeries.ker_map_of_fg (σ := Fin d) (residue A)
    (by rw [IsLocalRing.ker_residue]; exact (maximalIdeal A).fg_of_isNoetherianRing)
  rw [IsLocalRing.ker_residue] at hker
  have hmB : (Ideal.map (MvPowerSeries.C : A →+* B) (maximalIdeal A)).IsPrime := by
    have hdom : IsDomain (MvPowerSeries (Fin d) (ResidueField A)) :=
      NoZeroDivisors.to_isDomain _
    rw [← hker]
    exact RingHom.ker_isPrime _
  let P : Y := ⟨Ideal.map (MvPowerSeries.C : A →+* B) (maximalIdeal A), hmB⟩
  have hPV : P ∈ V := hV₂ P rfl
  have hpP : p P = IsLocalRing.closedPoint A := by
    refine PrimeSpectrum.ext ?_
    change (Ideal.map (MvPowerSeries.C : A →+* B) (maximalIdeal A)).comap
      (MvPowerSeries.C : A →+* B) = maximalIdeal A
    exact ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top
      Ideal.le_comap_map).symm
  have hetZ : ∀ z : E₀.scheme, EtaleAt f₀ z := by
    intro z
    by_cases hz : f₀ z ∈ U₀
    · exact etaleAt_of_mem_of_isPullback U₀ W₀.hom c₀ f₀ hE₀ z hz
    · have hz' : f₀ z = p P := by
        rw [hpP]
        exact not_not.1 fun h => hz ((hmemU₀ _).2 h)
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z P hz'
      have hy := (etaleAt_iff_of_isPullback hG (Or.inr hpflat) y).2
        (hetG y (by rw [show g y = P from hy2]; exact hPV))
      rwa [show gfst y = z from hy1] at hy
  have : Etale f₀ := (etale_iff_forall_etaleAt f₀).2 hetZ
  let F : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ f₀ ⟨inferInstance, inferInstance⟩
  refine ⟨(finiteEtaleBaseChange p).obj F, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk hc.flip.isoPullback.symm hc.flip.isoPullback_inv_snd

/-! ### Étaleness of a finite extension over a power series ring -/

open ExtendedEtaleFold Stacks.RelativeSpec Stacks.Algebraization in
/-- **A finite morphism to `Spec A[[x_1, …, x_d]]` that is étale over an open as in
[Stacks, Tag 0EYA] and has depth at least two off it is étale.** Let `(A, 𝔪)` be a Noetherian
local ring of depth at least two, `V` an open of `Y = Spec A[[x_1, …, x_d]]` containing every
prime `𝔮` with `𝔮 ∩ A ≠ 𝔪` and the prime `𝔪B`, and `f : E ⟶ Y` finite. Suppose `f` is étale
at every point above `V`, and the local rings of `E` above the complement of `V` have depth at
least two. Then `f` is étale. -/
public theorem etale_of_etaleAt_of_two_le_depth_mvPowerSeries (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
        q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
        (maximalIdeal A) → q ∈ V)
    {E : Scheme.{u}} (f : E ⟶ Spec (.of (MvPowerSeries (Fin d) A))) [IsFinite f]
    (het : ∀ e : E, f e ∈ V → EtaleAt f e)
    (hdE : ∀ e : E, f e ∉ V →
      (2 : ℕ∞) ≤ Module.depth (E.presheaf.stalk e) (maximalIdeal (E.presheaf.stalk e))
        (E.presheaf.stalk e)) :
    Etale f := by
  classical
  let Y : Scheme.{u} := Spec (.of (MvPowerSeries (Fin d) A))
  have : IsLocallyNoetherian Y := inferInstance
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- for `d = 0` the open `V` contains the closed point, hence everything
    subst hd0
    refine (etale_iff_forall_etaleAt f).2 fun e => het e ?_
    have hmax : Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin 0) A) (maximalIdeal A) =
        maximalIdeal (MvPowerSeries (Fin 0) A) := by
      refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_) fun x hx => ?_
      · exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          (IsLocalRing.mem_maximalIdeal _).1 ha (by
            simpa using MvPowerSeries.isUnit_iff_constantCoeff.1 hu)
      · have hx' : x = MvPowerSeries.C (MvPowerSeries.constantCoeff x) := by
          ext n
          have hn : n = 0 := Subsingleton.elim _ _
          subst hn
          simp
        rw [hx']
        refine Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
        exact (IsLocalRing.mem_maximalIdeal _).1 hx
          (MvPowerSeries.isUnit_iff_constantCoeff.2 hu)
    have hclosed : IsLocalRing.closedPoint (MvPowerSeries (Fin 0) A) ∈ V :=
      hV₂ _ hmax.symm
    have hle : f e ⤳ IsLocalRing.closedPoint (MvPowerSeries (Fin 0) A) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (f e).isPrime.ne_top)
    exact hle.mem_open V.isOpen hclosed
  have hEsq : IsPullback (Limits.pullback.fst f V.ι) (Limits.pullback.snd f V.ι) f V.ι :=
    IsPullback.of_hasPullback f V.ι
  have : IsFinite (Limits.pullback.snd f V.ι) := MorphismProperty.of_isPullback hEsq inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  have : Etale (Limits.pullback.snd f V.ι) := by
    refine (etale_iff_forall_etaleAt _).2 fun w => ?_
    refine (etaleAt_iff_of_isPullback hEsq (Or.inr inferInstance) w).1 (het _ ?_)
    rw [← Scheme.Hom.comp_apply, hEsq.w, Scheme.Hom.comp_apply]
    exact (Limits.pullback.snd f V.ι w).2
  let WV : FiniteEtaleOver V.toScheme :=
    MorphismProperty.Over.mk ⊤ (Limits.pullback.snd f V.ι) ⟨inferInstance, inferInstance⟩
  have hes := essSurj_finiteEtaleBaseChange_mvPowerSeries A d hd hdepth V hV₁ hV₂
  let F := (finiteEtaleBaseChange V.ι).objPreimage WV
  let eF : (finiteEtaleBaseChange V.ι).obj F ≅ WV :=
    (finiteEtaleBaseChange V.ι).objObjPreimageIso WV
  have : IsFinite F.hom := F.prop.1
  have : Etale F.hom := F.prop.2
  have hFsq : IsPullback (Limits.pullback.snd F.hom V.ι) (Limits.pullback.fst F.hom V.ι) V.ι
      F.hom := (IsPullback.of_hasPullback F.hom V.ι).flip
  let eL : (Limits.pullback F.hom V.ι) ≅ Limits.pullback f V.ι :=
    ((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso eF :)
  have hFsq' : IsPullback (Limits.pullback.snd f V.ι) (eL.inv ≫ Limits.pullback.fst F.hom V.ι)
      V.ι F.hom := isPullback_of_iso_left hFsq eL _ (MorphismProperty.Over.w eF.hom)
  have hdY : ∀ y : Y, y ∉ (V.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y) := fun y hy =>
    two_le_depth_stalk_of_notMem_mvPowerSeries A d hdepth V hV₁ y
      (by rwa [Scheme.Opens.opensRange_ι] at hy)
  have : IsLocallyNoetherian ((Functor.fromPUnit Y).obj F.right) :=
    inferInstanceAs (IsLocallyNoetherian Y)
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  have : IsLocallyNoetherian ((𝟭 Scheme.{u}).obj F.left) := this
  have hdF : ∀ y : F.left, F.hom y ∉ (V.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (F.left.presheaf.stalk y) (maximalIdeal (F.left.presheaf.stalk y))
        (F.left.presheaf.stalk y) := fun y hy =>
    (hdY _ hy).trans (depth_stalk_le_depth_stalk_of_flat F.hom y)
  have hdE' : ∀ e : E, f e ∉ (V.ι.opensRange : Set Y) →
      (2 : ℕ∞) ≤ Module.depth (E.presheaf.stalk e) (maximalIdeal (E.presheaf.stalk e))
        (E.presheaf.stalk e) := fun e he => hdE e (by rwa [Scheme.Opens.opensRange_ι] at he)
  obtain ⟨eE, ⟨hEE, -⟩, -⟩ := extendedEtale_unique V.ι (Limits.pullback.snd f V.ι) hdY f
    (Limits.pullback.fst f V.ι) hEsq.flip hdE'
  obtain ⟨eFF, ⟨hFF, -⟩, -⟩ := extendedEtale_unique V.ι (Limits.pullback.snd f V.ι) hdY F.hom
    _ hFsq' hdF
  have hφ : (eE.hom ≫ eFF.inv) ≫ F.hom = f :=
    (Category.assoc _ _ _).trans ((congrArg (eE.hom ≫ ·) ((Iso.inv_comp_eq eFF).mpr
      hFF.symm)).trans hEE)
  rw [← hφ]
  infer_instance

end Stacks.FundamentalGroup

end
