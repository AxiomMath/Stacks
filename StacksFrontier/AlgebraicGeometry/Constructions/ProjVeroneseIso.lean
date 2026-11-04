module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjBasicOpen
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjLocalizedRingMap
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading

/-!
# `Proj` of a graded ring is `Proj` of any positive Veronese subring

Let `S = ⨁_{n ≥ 0} Sₙ` be a graded ring and `d ≥ 1`. The `d`-th Veronese subring
`S⁽ᵈ⁾ = ⨁_n S_{nd}`, graded by `Stacks.Veronese.veroneseGrading`, has the same projective
spectrum as `S`: there is a canonical isomorphism of schemes

`Proj S ≅ Proj S⁽ᵈ⁾`,

which contracts homogeneous primes of `S` to `S⁽ᵈ⁾`, carries the standard open `D₊(f)` to
`D₊(f ᵈ)`, and on their rings of sections is the comparison of degree-zero localizations.

## Main definitions

* `Stacks.Veronese.veroneseChart` and `Stacks.Veronese.veroneseChartInv`: the two families of
  affine charts `Spec S₍f₎ ⟶ Proj S⁽ᵈ⁾` and `Spec (S⁽ᵈ⁾)₍f ᵈ₎ ⟶ Proj S`.
* `Stacks.Veronese.veroneseTargetOpenCover`: the cover of `Proj S⁽ᵈ⁾` by the standard opens
  `D₊(f ᵈ)`, indexed by the positive-degree homogeneous elements of `S`, with
  `veroneseTargetOpenCover_X` and `veroneseTargetOpenCover_f` naming its pieces and maps.
* `Stacks.Veronese.veroneseProjHom`, `Stacks.Veronese.veroneseProjInv` and
  `Stacks.Veronese.veroneseProjIso`: the canonical morphisms and the isomorphism.

## Main results

* `Stacks.Veronese.veroneseProjIso_mem_iff`: on points, the isomorphism contracts a homogeneous
  prime of `S` to `S⁽ᵈ⁾`.
* `Stacks.Veronese.veroneseProjIso_basicOpen`: it carries `D₊(f)` to `D₊(f ᵈ)`.
* `Stacks.Veronese.veroneseProjIso_awayToSection`: on the sections of a standard open, its
  structure-sheaf map is the comparison `Stacks.Veronese.veroneseAwayEquiv` of degree-zero
  localizations.
* `Stacks.Veronese.veroneseChart_compatible` and `Stacks.Veronese.veroneseChartInv_compatible`:
  the charts, and the inverse charts, agree on overlaps.
* `Stacks.Veronese.veroneseChart_comp_veroneseProjInv` and
  `Stacks.Veronese.veroneseChartInv_comp_veroneseProjHom`: each chart followed by the morphism in
  the other direction is the inclusion of a standard open.
* `Stacks.Veronese.iSup_basicOpen_veronesePower_eq_top`: the standard opens `D₊(f ᵈ)` cover
  `Proj S⁽ᵈ⁾`.
* `Stacks.Veronese.degreeZeroRingMap_eq_awayMap_of_mul`: for `x = fg` the restriction map
  `S₍f₎ → S₍x₎` is `HomogeneousLocalization.awayMap`.
* `Stacks.Veronese.mem_veroneseChart_base_iff`: the effect of a chart on homogeneous primes.
* `Stacks.Veronese.coe_decompose_veroneseGrading`: the degree-`n` component of an element of
  `S⁽ᵈ⁾` for the Veronese grading is its degree-`nd` component for the grading of `S`.
* `Stacks.Veronese.toSpec_basicOpenIsoSpec_inv_base`: the affine chart of a standard open is a
  section of `ProjectiveSpectrum.Proj.toSpec`.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 0EGH](https://stacks.math.columbia.edu/tag/0EGH)
-/

@[expose] public section

namespace Stacks.Veronese

open AlgebraicGeometry CategoryTheory

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The affine chart `Spec S₍f₎ ⟶ Proj S⁽ᵈ⁾` at a homogeneous element `f` of positive degree:
`Spec` of the comparison `veroneseAwayEquiv` of `(S⁽ᵈ⁾)₍f ᵈ₎` with `S₍f₎`, followed by the
inclusion of the standard open `D₊(f ᵈ)` of `Proj S⁽ᵈ⁾`. -/
public noncomputable def veroneseChart (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    Spec (.of (HomogeneousLocalization.Away 𝒮 f)) ⟶
      Proj (veroneseGrading 𝒮 d) := by
  let vf := veronesePower 𝒮 d f hf
  have hvf : vf ∈ veroneseGrading 𝒮 d e := by
    change f ^ d ∈ 𝒮 (e * d)
    simpa [mul_comm] using SetLike.pow_mem_graded d hf
  exact Spec.map
      (veroneseAwayEquiv 𝒮 d f hf hd).toCommRingCatIso.hom ≫
    Proj.awayι (veroneseGrading 𝒮 d) vf hvf he

/-- The chart `veroneseChart 𝒮 d hd f he hf` is an open immersion. -/
instance veroneseChart_isOpenImmersion (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    IsOpenImmersion (veroneseChart 𝒮 d hd f he hf) := by
  dsimp [veroneseChart]
  infer_instance

/-- The range of the chart `veroneseChart 𝒮 d hd f he hf` is the standard open `D₊(f ᵈ)` of
`Proj S⁽ᵈ⁾`. -/
theorem veroneseChart_opensRange (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    (veroneseChart 𝒮 d hd f he hf).opensRange =
      Proj.basicOpen (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d f hf) := by
  dsimp [veroneseChart]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Proj.opensRange_awayι _ _ _ _

/-- The affine chart `Spec (S⁽ᵈ⁾)₍f ᵈ₎ ⟶ Proj S` at a homogeneous element `f` of positive degree:
`Spec` of the inverse of `veroneseAwayEquiv`, followed by the inclusion of the standard open
`D₊(f)` of `Proj S`. -/
public noncomputable def veroneseChartInv (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    Spec (.of (HomogeneousLocalization.Away
      (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d f hf))) ⟶ Proj 𝒮 := by
  let vf := veronesePower 𝒮 d f hf
  have hvf : vf ∈ veroneseGrading 𝒮 d e := by
    change f ^ d ∈ 𝒮 (e * d)
    simpa [mul_comm] using SetLike.pow_mem_graded d hf
  exact Spec.map
      (veroneseAwayEquiv 𝒮 d f hf hd).symm.toCommRingCatIso.hom ≫
    Proj.awayι 𝒮 f hf he

/-- The chart `veroneseChartInv 𝒮 d hd f he hf` is an open immersion. -/
instance veroneseChartInv_isOpenImmersion (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    IsOpenImmersion (veroneseChartInv 𝒮 d hd f he hf) := by
  dsimp [veroneseChartInv]
  infer_instance

/-- The range of the chart `veroneseChartInv 𝒮 d hd f he hf` is the standard open `D₊(f)` of
`Proj S`. -/
theorem veroneseChartInv_opensRange (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    (veroneseChartInv 𝒮 d hd f he hf).opensRange = Proj.basicOpen 𝒮 f := by
  dsimp [veroneseChartInv]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Proj.opensRange_awayι _ _ _ _

/-- For homogeneous `f`, `g` and `x = f * g` of positive degree, the restriction map
`ProjectiveSpectrum.degreeZeroRingMap` from `S₍f₎` to `S₍x₎` is
`HomogeneousLocalization.awayMap`. -/
theorem degreeZeroRingMap_eq_awayMap_of_mul (f g x : S) {e k m : ℕ}
    (he : 0 < e) (_hk : 0 < k) (hm : 0 < m) (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k)
    (hxm : x ∈ 𝒮 m)
    (hx : x = f * g)
    (hfg : ProjectiveSpectrum.basicOpen 𝒮 x ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (ProjectiveSpectrum.degreeZeroRingMap 𝒮 f x
      ⟨e, he, hf⟩ ⟨m, hm, hxm⟩ hfg).toRingHom =
      HomogeneousLocalization.awayMap 𝒮 hg hx := by
  have hu : IsUnit (algebraMap S (Localization.Away x) f) := by
    simpa using ProjectiveSpectrum.isUnit_algebraMap_away_of_basicOpen_le
      𝒮 hf he hxm hm hfg
  let L : Localization.Away f →ₐ[S] Localization.Away x :=
    IsLocalization.Away.liftAlgHom (A := S) (P := Localization.Away x)
      (f := Algebra.ofId S (Localization.Away x)) f hu
  have hloc : ProjectiveSpectrum.localizedRingMap 𝒮 f x
      ⟨e, he, hf⟩ ⟨m, hm, hxm⟩ hfg =
      L := by
    apply AlgHom.ext
    intro z
    have heq : (ProjectiveSpectrum.localizedRingMap 𝒮 f x
        ⟨e, he, hf⟩ ⟨m, hm, hxm⟩ hfg).toRingHom =
        L.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext a
      simp
    exact congrArg (fun q => q z) heq
  ext z
  show HomogeneousLocalization.val
      (ProjectiveSpectrum.degreeZeroRingMap 𝒮 f x
        ⟨e, he, hf⟩ ⟨m, hm, hxm⟩ hfg z) =
    HomogeneousLocalization.val (HomogeneousLocalization.awayMap 𝒮 hg hx z)
  rw [ProjectiveSpectrum.val_degreeZeroRingMap,
    HomogeneousLocalization.val_awayMap, hloc]
  rfl

/-- The Veronese power of `x = f * g` is the product of those of `f` and `g`. -/
private theorem veronesePower_mul (d : ℕ) {f g x : S} {e k m : ℕ} (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k)
    (hxm : x ∈ 𝒮 m) (hx : x = f * g) :
    veronesePower 𝒮 d x hxm = veronesePower 𝒮 d f hf * veronesePower 𝒮 d g hg := by
  apply Subtype.ext
  change x ^ d = f ^ d * g ^ d
  rw [hx, mul_pow]

/-- For `x = f * g`, the comparison `veroneseAwayEquiv` commutes with the localization maps
`S₍f₎ → S₍x₎` and `(S⁽ᵈ⁾)₍f ᵈ₎ → (S⁽ᵈ⁾)₍x ᵈ₎`. -/
private theorem veroneseAwayEquiv_comp_awayMap (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) (f g x : S) {e k : ℕ} (he : 0 < e) (hk : 0 < k)
    (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k) (hx : x = f * g) :
    (veroneseAwayEquiv 𝒮 d x (hx ▸ SetLike.mul_mem_graded hf hg) hd).toRingHom.comp
        (HomogeneousLocalization.awayMap (veroneseGrading 𝒮 d) (veronesePower_mem 𝒮 d g hg)
          (veronesePower_mul 𝒮 d hf hg (hx ▸ SetLike.mul_mem_graded hf hg) hx)) =
      (HomogeneousLocalization.awayMap 𝒮 hg hx).comp
        (veroneseAwayEquiv 𝒮 d f hf hd).toRingHom := by
  have hxm : x ∈ 𝒮 (e + k) := hx ▸ SetLike.mul_mem_graded hf hg
  have hek : 0 < e + k := he.trans_le (Nat.le_add_right e k)
  have hfg : ProjectiveSpectrum.basicOpen 𝒮 x ≤ ProjectiveSpectrum.basicOpen 𝒮 f := by
    change Proj.basicOpen 𝒮 x ≤ Proj.basicOpen 𝒮 f
    rw [hx, Proj.basicOpen_mul]
    exact inf_le_left
  rw [← degreeZeroRingMap_eq_awayMap_of_mul (veroneseGrading 𝒮 d) _ _
      (veronesePower 𝒮 d x hxm) he hk hek
      (veronesePower_mem 𝒮 d f hf) (veronesePower_mem 𝒮 d g hg) (veronesePower_mem 𝒮 d x hxm)
      (veronesePower_mul 𝒮 d hf hg hxm hx) (basicOpen_veronesePower_le 𝒮 d f x hf hxm hfg he hek),
    ← degreeZeroRingMap_eq_awayMap_of_mul 𝒮 f g x he hk hek hf hg hxm hx hfg]
  ext z
  exact congrArg HomogeneousLocalization.val (veroneseAwayEquiv_naturality 𝒮 d hd f x he hek hf
    hxm hfg z)

/-- For `x = f * g`, the chart of `f` precomposed with `Spec` of the localization map
`S₍f₎ → S₍x₎` is the chart of `x`. -/
theorem veroneseChart_comp_awayMap (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f g x : S) {e k : ℕ} (he : 0 < e) (hk : 0 < k)
    (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k) (hx : x = f * g) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒮 hg hx)) ≫
        veroneseChart 𝒮 d hd f he hf =
      veroneseChart 𝒮 d hd x (he.trans_le (Nat.le_add_right e k))
        (hx ▸ SetLike.mul_mem_graded hf hg) := by
  have hSpec := congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ))
    (veroneseAwayEquiv_comp_awayMap 𝒮 d hd f g x he hk hf hg hx)
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, RingEquiv.toRingHom_eq_coe] at hSpec
  dsimp [veroneseChart]
  simp only [RingEquiv.toCommRingCatIso_hom]
  rw [← Category.assoc, ← hSpec, Category.assoc, Proj.SpecMap_awayMap_awayι]

/-- For `x = f * g`, the inverse chart of `f` precomposed with `Spec` of the localization map
`(S⁽ᵈ⁾)₍f ᵈ₎ → (S⁽ᵈ⁾)₍x ᵈ₎` is the inverse chart of `x`. -/
theorem veroneseChartInv_comp_awayMap (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f g x : S) {e k : ℕ} (he : 0 < e) (hk : 0 < k)
    (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k) (hx : x = f * g) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
        (𝒜 := veroneseGrading 𝒮 d)
        (hg := show veronesePower 𝒮 d g hg ∈
          veroneseGrading 𝒮 d k from by
          change g ^ d ∈ 𝒮 (k * d)
          simpa [mul_comm] using SetLike.pow_mem_graded d hg)
        (hx := show veronesePower 𝒮 d x
          (hx ▸ SetLike.mul_mem_graded hf hg) =
          veronesePower 𝒮 d f hf * veronesePower 𝒮 d g hg from by
          apply Subtype.ext
          change x ^ d = f ^ d * g ^ d
          rw [hx, mul_pow]))) ≫
      veroneseChartInv 𝒮 d hd f he hf =
    veroneseChartInv 𝒮 d hd x (he.trans_le (Nat.le_add_right e k))
      (hx ▸ SetLike.mul_mem_graded hf hg) := by
  have hring := veroneseAwayEquiv_comp_awayMap 𝒮 d hd f g x he hk hf hg hx
  have hring' : (HomogeneousLocalization.awayMap (veroneseGrading 𝒮 d)
        (veronesePower_mem 𝒮 d g hg)
        (veronesePower_mul 𝒮 d hf hg (hx ▸ SetLike.mul_mem_graded hf hg) hx)).comp
      (veroneseAwayEquiv 𝒮 d f hf hd).symm.toRingHom =
      (veroneseAwayEquiv 𝒮 d x (hx ▸ SetLike.mul_mem_graded hf hg) hd).symm.toRingHom.comp
        (HomogeneousLocalization.awayMap 𝒮 hg hx) := by
    ext z
    refine congrArg HomogeneousLocalization.val ?_
    apply (veroneseAwayEquiv 𝒮 d x (hx ▸ SetLike.mul_mem_graded hf hg) hd).injective
    simpa using RingHom.congr_fun hring ((veroneseAwayEquiv 𝒮 d f hf hd).symm z)
  have hSpec := congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) hring'
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, RingEquiv.toRingHom_eq_coe] at hSpec
  dsimp [veroneseChartInv]
  simp only [RingEquiv.toCommRingCatIso_hom]
  rw [← Category.assoc, hSpec, Category.assoc, Proj.SpecMap_awayMap_awayι]

/-- The standard opens `D₊(f ᵈ)`, for `f` homogeneous of positive degree in `S`, cover
`Proj S⁽ᵈ⁾`. -/
theorem iSup_basicOpen_veronesePower_eq_top (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) :
    (⨆ i : (Proj.affineOpenCover 𝒮).I₀,
      Proj.basicOpen (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d i.2.1 i.2.2)) = ⊤ := by
  apply le_antisymm le_top
  have hcover :
      (⨆ j : (Proj.affineOpenCover (veroneseGrading 𝒮 d)).I₀,
        Proj.basicOpen (veroneseGrading 𝒮 d) j.2.1) = ⊤ := by
    classical
    apply Proj.iSup_basicOpen_eq_top
    intro z hz
    rw [← DirectSum.sum_support_decompose (veroneseGrading 𝒮 d) z]
    refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
      Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
    · convert! Ideal.zero_mem _
      subst hc0
      exact hz
  rw [← hcover]
  apply iSup_le
  intro j
  let e : ℕ := j.1.1 * d
  have he : 0 < e := Nat.mul_pos j.1.2 hd
  have hf : (j.2.1 : S) ∈ 𝒮 e := by
    have hj : j.2.1 ∈ veroneseGrading 𝒮 d j.1.1 := j.2.2
    change ((j.2.1 : veroneseSubring 𝒮 d) : S) ∈
      𝒮 (j.1.1 * d) at hj
    simpa [e] using hj
  let i : (Proj.affineOpenCover 𝒮).I₀ :=
    ⟨⟨e, he⟩, ⟨(j.2.1 : S), hf⟩⟩
  have hi : veronesePower 𝒮 d i.2.1 i.2.2 = j.2.1 ^ d := by
    apply Subtype.ext
    rfl
  calc
    Proj.basicOpen (veroneseGrading 𝒮 d) j.2.1 =
        Proj.basicOpen (veroneseGrading 𝒮 d) (j.2.1 ^ d) :=
      (Proj.basicOpen_pow (veroneseGrading 𝒮 d) j.2.1 d hd).symm
    _ = Proj.basicOpen (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d i.2.1 i.2.2) := by rw [hi]
    _ ≤ ⨆ i : (Proj.affineOpenCover 𝒮).I₀,
        Proj.basicOpen (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d i.2.1 i.2.2) :=
      le_iSup (fun i : (Proj.affineOpenCover 𝒮).I₀ ↦
        Proj.basicOpen (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d i.2.1 i.2.2)) i

/-- The charts of `Proj S ⟶ Proj S⁽ᵈ⁾` agree on overlaps: on `D₊(f) ∩ D₊(g) = D₊(fg)` both
restrict to the chart of `fg`. -/
theorem veroneseChart_compatible (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    {f g : S} {e k : ℕ} (he : 0 < e) (hk : 0 < k) (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k) :
    Limits.pullback.fst (Proj.awayι 𝒮 f hf he) (Proj.awayι 𝒮 g hg hk) ≫
        veroneseChart 𝒮 d hd f he hf =
      Limits.pullback.snd (Proj.awayι 𝒮 f hf he) (Proj.awayι 𝒮 g hg hk) ≫
        veroneseChart 𝒮 d hd g hk hg := by
  let q := Proj.pullbackAwayιIso 𝒮 hf he hg hk (rfl : f * g = f * g)
  rw [← cancel_epi q.inv]
  have hleft : q.inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒮 hg rfl)) := by
    dsimp [q]
    exact Proj.pullbackAwayιIso_inv_fst 𝒮 hf he hg hk rfl
  have hright : q.inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒮 hf (mul_comm f g))) := by
    dsimp [q]
    exact Proj.pullbackAwayιIso_inv_snd 𝒮 hf he hg hk rfl
  rw [← Category.assoc, ← Category.assoc, hleft, hright,
    veroneseChart_comp_awayMap 𝒮 d hd f g (f * g) he hk hf hg rfl]
  symm
  convert veroneseChart_comp_awayMap 𝒮 d hd g f (f * g) hk he hg hf
    (mul_comm f g) using 1
  all_goals simp [Nat.add_comm]

/-- The canonical morphism `Proj S ⟶ Proj S⁽ᵈ⁾`, glued from the charts. -/
public noncomputable def veroneseProjHom (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) :
    AlgebraicGeometry.Proj 𝒮 ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒮 d) :=
  (Proj.affineOpenCover 𝒮).openCover.glueMorphisms
    (fun i ↦ veroneseChart 𝒮 d hd i.2.1 i.1.2 i.2.2)
    (fun i j ↦ veroneseChart_compatible 𝒮 d hd i.1.2 j.1.2 i.2.2 j.2.2)

/-- The chart of `f` is the restriction of `veroneseProjHom` to the standard open `D₊(f)`. -/
private theorem awayι_comp_veroneseProjHom_eq_chart (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    Proj.awayι 𝒮 f hf he ≫ veroneseProjHom 𝒮 d hd = veroneseChart 𝒮 d hd f he hf :=
  (Proj.affineOpenCover 𝒮).openCover.ι_glueMorphisms _ _ ⟨⟨e, he⟩, ⟨f, hf⟩⟩

/-- The open cover of `Proj S⁽ᵈ⁾` by the standard opens `D₊(f ᵈ)`, indexed by the homogeneous
elements `f` of positive degree of `S`. -/
@[instance_reducible]
public noncomputable def veroneseTargetOpenCover (d : ℕ)
    [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d) :
    Scheme.OpenCover (Proj (veroneseGrading 𝒮 d)) := by
  classical
  refine Scheme.Cover.mkOfCovers
    ((Proj.affineOpenCover 𝒮).I₀)
    (fun i ↦ Spec (.of (HomogeneousLocalization.Away
      (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d i.2.1 i.2.2))))
    (fun i ↦ Proj.awayι (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d i.2.1 i.2.2)
      (veronesePower_mem 𝒮 d i.2.1 i.2.2) i.1.2)
    (by
      intro x
      have hx : x ∈ (⨆ i : (Proj.affineOpenCover 𝒮).I₀,
          Proj.basicOpen (veroneseGrading 𝒮 d)
            (veronesePower 𝒮 d i.2.1 i.2.2)) := by
        rw [iSup_basicOpen_veronesePower_eq_top 𝒮 d hd]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      let vf := veronesePower 𝒮 d i.2.1 i.2.2
      have hdeg : vf ∈ veroneseGrading 𝒮 d i.1.1 :=
        veronesePower_mem 𝒮 d i.2.1 i.2.2
      have hrange : x ∈ (Proj.awayι (veroneseGrading 𝒮 d)
          vf hdeg i.1.2).opensRange := by
        rwa [Proj.opensRange_awayι]
      obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hrange
      exact ⟨i, y, hy⟩)
    (by
      intro i
      dsimp [Proj.awayι]
      infer_instance)

/-- The member of `veroneseTargetOpenCover` at `f` is `Spec (S⁽ᵈ⁾)₍f ᵈ₎`. -/
@[simp] theorem veroneseTargetOpenCover_X (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) (i : (veroneseTargetOpenCover 𝒮 d hd).I₀) :
    (veroneseTargetOpenCover 𝒮 d hd).X i =
      Spec (.of (HomogeneousLocalization.Away
        (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d i.2.1 i.2.2))) := rfl

/-- The map of `veroneseTargetOpenCover` at `f` is the inclusion of `D₊(f ᵈ)`. -/
@[simp] theorem veroneseTargetOpenCover_f (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) (i : (veroneseTargetOpenCover 𝒮 d hd).I₀) :
    (veroneseTargetOpenCover 𝒮 d hd).f i =
      Proj.awayι (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d i.2.1 i.2.2)
        (veronesePower_mem 𝒮 d i.2.1 i.2.2) i.1.2 := rfl

/-- The inverse charts agree on overlaps: on `D₊(f ᵈ) ∩ D₊(g ᵈ) = D₊((fg) ᵈ)` both restrict to
the chart of `fg`. -/
theorem veroneseChartInv_compatible (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    {f g : S} {e k : ℕ} (he : 0 < e) (hk : 0 < k) (hf : f ∈ 𝒮 e) (hg : g ∈ 𝒮 k) :
    Limits.pullback.fst
        (Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)
          (veronesePower_mem 𝒮 d f hf) he)
        (Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d g hg)
          (veronesePower_mem 𝒮 d g hg) hk) ≫
      veroneseChartInv 𝒮 d hd f he hf =
    Limits.pullback.snd
        (Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)
          (veronesePower_mem 𝒮 d f hf) he)
        (Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d g hg)
          (veronesePower_mem 𝒮 d g hg) hk) ≫
      veroneseChartInv 𝒮 d hd g hk hg := by
  have hxv := veronesePower_mul 𝒮 d hf hg (SetLike.mul_mem_graded hf hg) (rfl : f * g = f * g)
  let q := Proj.pullbackAwayιIso (veroneseGrading 𝒮 d)
    (veronesePower_mem 𝒮 d f hf) he (veronesePower_mem 𝒮 d g hg) hk hxv
  rw [← cancel_epi q.inv]
  have hleft : q.inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
        (veroneseGrading 𝒮 d) (veronesePower_mem 𝒮 d g hg) hxv)) := by
    dsimp [q]
    exact Proj.pullbackAwayιIso_inv_fst (veroneseGrading 𝒮 d)
      (veronesePower_mem 𝒮 d f hf) he (veronesePower_mem 𝒮 d g hg) hk hxv
  have hright : q.inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
        (veroneseGrading 𝒮 d) (veronesePower_mem 𝒮 d f hf)
          (hxv.trans (mul_comm _ _)))) := by
    dsimp [q]
    exact Proj.pullbackAwayιIso_inv_snd (veroneseGrading 𝒮 d)
      (veronesePower_mem 𝒮 d f hf) he (veronesePower_mem 𝒮 d g hg) hk hxv
  rw [← Category.assoc, ← Category.assoc, hleft, hright,
    veroneseChartInv_comp_awayMap 𝒮 d hd f g (f * g) he hk hf hg rfl]
  symm
  convert veroneseChartInv_comp_awayMap 𝒮 d hd g f (f * g) hk he hg hf
    (mul_comm f g) using 1
  all_goals rfl

/-- The canonical morphism `Proj S⁽ᵈ⁾ ⟶ Proj S`, glued from the inverse charts. -/
public noncomputable def veroneseProjInv (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d) :
    AlgebraicGeometry.Proj (veroneseGrading 𝒮 d) ⟶ AlgebraicGeometry.Proj 𝒮 := by
  let U := veroneseTargetOpenCover 𝒮 d hd
  exact U.glueMorphisms
    (fun i ↦ veroneseChartInv 𝒮 d hd i.2.1 i.1.2 i.2.2)
    (by intro i j; exact veroneseChartInv_compatible 𝒮 d hd i.1.2 j.1.2 i.2.2 j.2.2)

/-- The chart of `f` followed by `veroneseProjInv` is the inclusion of `D₊(f)` into `Proj S`. -/
theorem veroneseChart_comp_veroneseProjInv (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    veroneseChart 𝒮 d hd f he hf ≫ veroneseProjInv 𝒮 d hd =
      Proj.awayι 𝒮 f hf he := by
  let U := veroneseTargetOpenCover 𝒮 d hd
  let i : U.I₀ := ⟨⟨e, he⟩, ⟨f, hf⟩⟩
  have hvf : veronesePower 𝒮 d f hf ∈
      veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  have hchart₀ : U.f i ≫ veroneseProjInv 𝒮 d hd =
      veroneseChartInv 𝒮 d hd f he hf :=
    U.ι_glueMorphisms (fun j ↦ veroneseChartInv 𝒮 d hd j.2.1 j.1.2 j.2.2)
      (fun j k ↦ veroneseChartInv_compatible 𝒮 d hd j.1.2 k.1.2 j.2.2 k.2.2) i
  have hX : U.X i = Spec (.of (HomogeneousLocalization.Away
      (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d f hf))) :=
    veroneseTargetOpenCover_X 𝒮 d hd i
  have hF : U.f i = Proj.awayι (veroneseGrading 𝒮 d)
      (veronesePower 𝒮 d f hf) hvf he :=
    veroneseTargetOpenCover_f 𝒮 d hd i
  rw [hF] at hchart₀
  cases hX
  have hchart := hchart₀
  let E := veroneseAwayEquiv 𝒮 d f hf hd
  have hring : E.toRingHom.comp E.symm.toRingHom = RingHom.id _ :=
    RingEquiv.comp_symm E
  have hspec : Spec.map (CommRingCat.ofHom E.toRingHom) ≫
      Spec.map (CommRingCat.ofHom E.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
    simp
  dsimp [veroneseChart]
  calc
    Spec.map (CommRingCat.ofHom E.toRingHom) ≫
        (Proj.awayι (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d f hf) hvf he ≫
          veroneseProjInv 𝒮 d hd) =
      Spec.map (CommRingCat.ofHom E.toRingHom) ≫ veroneseChartInv 𝒮 d hd f he hf :=
        congrArg (fun g ↦ Spec.map (CommRingCat.ofHom E.toRingHom) ≫ g) hchart
    _ = Proj.awayι 𝒮 f hf he := by
      dsimp [veroneseChartInv]
      simp only [RingEquiv.toCommRingCatIso_hom]
      show (Spec.map (CommRingCat.ofHom E.toRingHom) ≫
          Spec.map (CommRingCat.ofHom E.symm.toRingHom)) ≫
          Proj.awayι 𝒮 f hf he = _
      rw [hspec]
      simp

/-- **The Veronese morphism on a chart.** On the standard open `D₊(f) = Spec S₍f₎` of `Proj S`,
the morphism `Proj S ⟶ Proj S⁽ᵈ⁾` is `Spec` of the canonical identification
`S'₍f ᵈ₎ ≅ S₍f₎` followed by the inclusion of the standard open `D₊(f ᵈ)` of `Proj S⁽ᵈ⁾`. -/
public theorem awayι_comp_veroneseProjHom (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    Proj.awayι 𝒮 f hf he ≫ veroneseProjHom 𝒮 d hd =
      Spec.map (veroneseAwayEquiv 𝒮 d f hf hd).toCommRingCatIso.hom ≫
        Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)
          (veronesePower_mem 𝒮 d f hf) he :=
  (Proj.affineOpenCover 𝒮).openCover.ι_glueMorphisms _ _ ⟨⟨e, he⟩, ⟨f, hf⟩⟩

/-- The inverse chart of `f` followed by `veroneseProjHom` is the inclusion of `D₊(f ᵈ)` into
`Proj S⁽ᵈ⁾`. -/
theorem veroneseChartInv_comp_veroneseProjHom (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    veroneseChartInv 𝒮 d hd f he hf ≫ veroneseProjHom 𝒮 d hd =
      Proj.awayι (veroneseGrading 𝒮 d)
        (veronesePower 𝒮 d f hf)
        (veronesePower_mem 𝒮 d f hf) he := by
  have hvf : veronesePower 𝒮 d f hf ∈
      veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  let E := veroneseAwayEquiv 𝒮 d f hf hd
  dsimp [veroneseChartInv]
  rw [Category.assoc, awayι_comp_veroneseProjHom_eq_chart]
  dsimp [veroneseChart]
  have hring : E.symm.toRingHom.comp E.toRingHom = RingHom.id _ :=
    RingEquiv.symm_comp E
  have hspec : Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom E.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
    simp
  simp only [RingEquiv.toCommRingCatIso_hom]
  show (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom E.toRingHom)) ≫
        Proj.awayι (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d f hf) hvf he = _
  rw [hspec]
  simp


/-- The canonical isomorphism from the projective spectrum of a graded ring to that of
its positive Veronese subring. -/
@[ega "II 3.1.8" "(i), graded ring case",
  ega "II 2.4.7" "(i)",
  ega "II 2.5.16",
  ega "II 8.14.13" "(d), special case"]
public noncomputable def veroneseProjIso (d : ℕ) (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    AlgebraicGeometry.Proj 𝒮 ≅
      AlgebraicGeometry.Proj (veroneseGrading 𝒮 d) :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  { hom := veroneseProjHom 𝒮 d hd
    inv := veroneseProjInv 𝒮 d hd
    hom_inv_id := by
      apply (Proj.affineOpenCover 𝒮).openCover.hom_ext
      intro i
      have hchart : (Proj.affineOpenCover 𝒮).openCover.f i ≫ veroneseProjHom 𝒮 d hd =
          veroneseChart 𝒮 d hd i.2.1 i.1.2 i.2.2 :=
        (Proj.affineOpenCover 𝒮).openCover.ι_glueMorphisms _ _ i
      have hinv : veroneseChart 𝒮 d hd i.2.1 i.1.2 i.2.2 ≫ veroneseProjInv 𝒮 d hd =
          Proj.awayι 𝒮 i.2.1 i.2.2 i.1.2 :=
        veroneseChart_comp_veroneseProjInv 𝒮 d hd i.2.1 i.1.2 i.2.2
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun φ ↦ φ ≫ veroneseProjInv 𝒮 d hd) hchart).trans
          (hinv.trans
            (Category.comp_id ((Proj.affineOpenCover 𝒮).openCover.f i)).symm))
    inv_hom_id := by
      apply (veroneseTargetOpenCover 𝒮 d hd).hom_ext
      intro i
      have hchart : (veroneseTargetOpenCover 𝒮 d hd).f i ≫ veroneseProjInv 𝒮 d hd =
          veroneseChartInv 𝒮 d hd i.2.1 i.1.2 i.2.2 :=
        (veroneseTargetOpenCover 𝒮 d hd).ι_glueMorphisms
          (fun j ↦ veroneseChartInv 𝒮 d hd j.2.1 j.1.2 j.2.2)
          (fun j k ↦ veroneseChartInv_compatible 𝒮 d hd j.1.2 k.1.2 j.2.2 k.2.2) i
      have hhom : veroneseChartInv 𝒮 d hd i.2.1 i.1.2 i.2.2 ≫ veroneseProjHom 𝒮 d hd =
          Proj.awayι (veroneseGrading 𝒮 d) (veronesePower 𝒮 d i.2.1 i.2.2)
            (veronesePower_mem 𝒮 d i.2.1 i.2.2) i.1.2 :=
        veroneseChartInv_comp_veroneseProjHom 𝒮 d hd i.2.1 i.1.2 i.2.2
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun φ ↦ φ ≫ veroneseProjHom 𝒮 d hd) hchart).trans
          (hhom.trans ((veroneseTargetOpenCover_f 𝒮 d hd i).symm.trans
            (Category.comp_id ((veroneseTargetOpenCover 𝒮 d hd).f i)).symm))) }

/-- On points, the identification `Proj.basicOpenIsoSpec` of the standard open `D₊(f)` with
`Spec A₍f₎` is a section of `ProjectiveSpectrum.Proj.toSpec`. -/
theorem toSpec_basicOpenIsoSpec_inv_base (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : S) {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m)
    (q : PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f)) :
    (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base
      ((Proj.basicOpenIsoSpec 𝒜 f hf hm).inv.base q) = q := by
  have h := congrArg (fun g ↦ g q) (CategoryTheory.Iso.inv_hom_id
    (Proj.basicOpenIsoSpec 𝒜 f hf hm))
  convert h using 1
  all_goals rfl

/-- A homogeneous element `a` of `S⁽ᵈ⁾` lies in the image under `veroneseChart` of a point `q` of
`Spec S₍f₎` exactly when `a`, as an element of `S`, lies in the image of `q` in `Proj S`. -/
theorem mem_veroneseChart_base_iff (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e)
    (q : Spec (.of (HomogeneousLocalization.Away 𝒮 f)))
    (a : veroneseSubring 𝒮 d) {n : ℕ}
    (ha : a ∈ veroneseGrading 𝒮 d n) :
    a ∈ ((veroneseChart 𝒮 d hd f he hf).base q).asHomogeneousIdeal ↔
      (a : S) ∈ ((Proj.awayι 𝒮 f hf he).base q).asHomogeneousIdeal := by
  let vf := veronesePower 𝒮 d f hf
  have hvf : vf ∈ veroneseGrading 𝒮 d e :=
    veronesePower_mem 𝒮 d f hf
  let E := veroneseAwayEquiv 𝒮 d f hf hd
  let q' := (Spec.map (CommRingCat.ofHom E.toRingHom)).base q
  let y := (Proj.basicOpenIsoSpec (veroneseGrading 𝒮 d)
    vf hvf he).inv.base q'
  have hpoint : (veroneseChart 𝒮 d hd f he hf).base q =
      (Proj.basicOpen (veroneseGrading 𝒮 d) vf).ι.base y := by
    rfl
  have hcoord : (ProjectiveSpectrum.Proj.toSpec
      (veroneseGrading 𝒮 d) vf).base y = q' :=
    toSpec_basicOpenIsoSpec_inv_base (veroneseGrading 𝒮 d)
      vf hvf he q'
  let zV : HomogeneousLocalization.NumDenSameDeg
      (veroneseGrading 𝒮 d) (.powers vf) :=
    ⟨e * n, ⟨a ^ e, by
        have hp := SetLike.pow_mem_graded e ha
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using hp⟩,
      ⟨vf ^ n, by
        have hp := SetLike.pow_mem_graded n hvf
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using hp⟩,
      ⟨n, rfl⟩⟩
  let zS : HomogeneousLocalization.NumDenSameDeg 𝒮 (.powers f) :=
    ⟨e * (n * d), ⟨(a : S) ^ e, by
        have hp := SetLike.pow_mem_graded e (show (a : S) ∈ 𝒮 (n * d) from ha)
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using hp⟩,
      ⟨f ^ (n * d), by
        have hp := SetLike.pow_mem_graded (n * d) hf
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using hp⟩,
      ⟨n * d, rfl⟩⟩
  have hzV : zV = ⟨n • e, ⟨a ^ e, by
      simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded e ha⟩,
      ⟨vf ^ n, by
        have hp := SetLike.pow_mem_graded n hvf
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using hp⟩, ⟨n, rfl⟩⟩ := by
    refine HomogeneousLocalization.NumDenSameDeg.ext (Submonoid.powers vf) ?_ rfl rfl
    simp [zV, Nat.mul_comm]
  have hzS : zS = ⟨(n * d) • e, ⟨(a : S) ^ e, by
      have hp := SetLike.pow_mem_graded e (show (a : S) ∈ 𝒮 (n * d) from ha)
      simpa [Nat.nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hp⟩,
      ⟨f ^ (n * d), by
        have hp := SetLike.pow_mem_graded (n * d) hf
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using hp⟩, ⟨n * d, rfl⟩⟩ := by
    refine HomogeneousLocalization.NumDenSameDeg.ext (Submonoid.powers f) ?_ rfl rfl
    simp [zS, Nat.mul_comm, Nat.mul_left_comm]
  have hmk : E (HomogeneousLocalization.mk zV) = HomogeneousLocalization.mk zS := by
    have hmk0 := veroneseAwayEquiv_mk 𝒮 d f hf hd n
      (a ^ e)
      (by simpa [Nat.nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded e ha)
      (by
        have hp := SetLike.pow_mem_graded e (show (a : S) ∈ 𝒮 (n * d) from ha)
        simpa [Nat.nsmul_eq_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hp)
    rwa [hzV, hzS]
  have hqmap : HomogeneousLocalization.mk zV ∈ q'.asIdeal ↔
      HomogeneousLocalization.mk zS ∈ q.asIdeal := by
    show E (HomogeneousLocalization.mk zV) ∈ q.asIdeal ↔ _
    rw [hmk]
  have htarget : HomogeneousLocalization.mk zV ∈
      ((ProjectiveSpectrum.Proj.toSpec
        (veroneseGrading 𝒮 d) vf).base y).asIdeal ↔
        a ^ e ∈ y.1.asHomogeneousIdeal :=
    ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
      (veroneseGrading 𝒮 d) y zV
  have hsource : HomogeneousLocalization.mk zS ∈ q.asIdeal ↔
      (a : S) ^ e ∈ ((Proj.awayι 𝒮 f hf he).base q).asHomogeneousIdeal := by
    have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒮
      ((Proj.basicOpenIsoSpec 𝒮 f hf he).inv.base q) zS
    rwa [toSpec_basicOpenIsoSpec_inv_base 𝒮 f hf he q] at h
  have hpTarget : a ^ e ∈ y.1.asHomogeneousIdeal ↔
      a ∈ y.1.asHomogeneousIdeal :=
    y.1.isPrime.pow_mem_iff_mem e he
  have hpSource : (a : S) ^ e ∈ ((Proj.awayι 𝒮 f hf he).base q).asHomogeneousIdeal ↔
      (a : S) ∈ ((Proj.awayι 𝒮 f hf he).base q).asHomogeneousIdeal :=
    ((Proj.awayι 𝒮 f hf he).base q).isPrime.pow_mem_iff_mem e he
  have htarget' : HomogeneousLocalization.mk zV ∈ q'.asIdeal ↔
      a ^ e ∈ y.1.asHomogeneousIdeal := by
    simpa [hcoord] using htarget
  rw [hpoint]
  show a ∈ y.1.asHomogeneousIdeal ↔
    (a : S) ∈ ((Proj.awayι 𝒮 f hf he).base q).asHomogeneousIdeal
  exact hpTarget.symm.trans (htarget'.symm.trans (hqmap.trans (hsource.trans hpSource)))

/-- The degree-`m` component in `S` of an element of `S⁽ᵈ⁾` is the sum of the degree-`m`
components of its Veronese homogeneous components. -/
private theorem decompose_coe_veroneseSubring (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)]
    [∀ (i : ℕ) (x : veroneseGrading 𝒮 d i), Decidable (x ≠ 0)] (f : veroneseSubring 𝒮 d) (m : ℕ) :
    (DirectSum.decompose 𝒮 (f : S) m : S) =
      ((∑ k ∈ (DirectSum.decompose (veroneseGrading 𝒮 d) f).support,
        DirectSum.decompose 𝒮 ((DirectSum.decompose (veroneseGrading 𝒮 d) f k :
          veroneseSubring 𝒮 d) : S) m : 𝒮 m) : S) := by
  have hfexp : (f : S) =
      ∑ k ∈ (DirectSum.decompose (veroneseGrading 𝒮 d) f).support,
        ((DirectSum.decompose (veroneseGrading 𝒮 d) f k :
          veroneseSubring 𝒮 d) : S) := by
    simpa using congrArg Subtype.val
      (DirectSum.sum_support_decompose (veroneseGrading 𝒮 d) f).symm
  rw [hfexp, DirectSum.decompose_sum, DirectSum.sum_apply]

/-- The degree-`n` component of an element of `S⁽ᵈ⁾` for the Veronese grading is its
degree-`nd` component for the grading of `S`. -/
theorem coe_decompose_veroneseGrading (d : ℕ) [GradedRing (veroneseGrading 𝒮 d)] (hd : 0 < d)
    (f : veroneseSubring 𝒮 d) (n : ℕ) :
    (DirectSum.decompose 𝒮 (f : S) (n * d) : S) =
      (DirectSum.decompose (veroneseGrading 𝒮 d) f n :
        veroneseSubring 𝒮 d) := by
  classical
  rw [decompose_coe_veroneseSubring, Finset.sum_eq_single n]
  · have hmem : ((DirectSum.decompose (veroneseGrading 𝒮 d) f n :
        veroneseSubring 𝒮 d) : S) ∈ 𝒮 (n * d) :=
      (DirectSum.decompose (veroneseGrading 𝒮 d) f n).property
    exact DirectSum.decompose_of_mem_same 𝒮 hmem
  · intro k hk hkn
    apply Subtype.ext
    apply DirectSum.decompose_of_mem_ne
    · exact (DirectSum.decompose (veroneseGrading 𝒮 d) f k).property
    · exact fun hmul ↦ hkn (Nat.eq_of_mul_eq_mul_right hd hmul)
  · intro hn
    have hzero : DirectSum.decompose (veroneseGrading 𝒮 d) f n = 0 := by
      by_contra hne
      exact hn (DFinsupp.mem_support_iff.mpr hne)
    simp [hzero]

/-- On homogeneous prime ideals, the canonical isomorphism contracts to the Veronese
subring. -/
@[ega "II 8.14.13" "(f)"]
public theorem veroneseProjIso_mem_iff (d : ℕ) (hd : 0 < d)
    (x : ProjectiveSpectrum 𝒮)
    (f : veroneseSubring 𝒮 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    f ∈ ((veroneseProjIso 𝒮 d hd).hom.base x).asHomogeneousIdeal ↔
      (f : S) ∈ x.asHomogeneousIdeal :=
  by
    let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
    let y := (veroneseProjIso 𝒮 d hd).hom.base x
    let I := y.asHomogeneousIdeal.toIdeal
    let J := x.asHomogeneousIdeal.toIdeal
    show (f : veroneseSubring 𝒮 d) ∈ I ↔ (f : S) ∈ J
    have hI := Ideal.IsHomogeneous.mem_iff (veroneseGrading 𝒮 d)
      y.asHomogeneousIdeal.isHomogeneous (x := (f : veroneseSubring 𝒮 d))
    have hJ := Ideal.IsHomogeneous.mem_iff 𝒮 x.asHomogeneousIdeal.isHomogeneous
      (x := (f : S))
    let C := (Proj.affineOpenCover 𝒮).openCover
    let i : C.I₀ := C.idx x
    obtain ⟨q, hq⟩ := C.covers x
    let g : S := i.2.1
    let e : ℕ := i.1.1
    let hg : g ∈ 𝒮 e := i.2.2
    let he : 0 < e := i.1.2
    have hfi : C.f i = Proj.awayι 𝒮 g hg he := rfl
    have hchart := awayι_comp_veroneseProjHom_eq_chart 𝒮 d hd g he hg
    have hpoint : y = (veroneseChart 𝒮 d hd g he hg).base q := by
      have h := congrArg (fun φ ↦ φ.base q) hchart
      change (veroneseProjHom 𝒮 d hd).base ((Proj.awayι 𝒮 g hg he).base q) = _ at h
      show (veroneseProjHom 𝒮 d hd).base x = _
      rwa [← hq]
    have hsourcePoint : (Proj.awayι 𝒮 g hg he).base q = x := by
      rwa [← hfi]
    have hchartComp : ∀ n,
        (DirectSum.decompose (veroneseGrading 𝒮 d) f n :
          veroneseSubring 𝒮 d) ∈ I ↔
        ((DirectSum.decompose (veroneseGrading 𝒮 d) f n :
          veroneseSubring 𝒮 d) : S) ∈ J := by
      intro n
      have ha : (DirectSum.decompose (veroneseGrading 𝒮 d) f n :
          veroneseSubring 𝒮 d) ∈ veroneseGrading 𝒮 d n :=
        (DirectSum.decompose (veroneseGrading 𝒮 d) f n).property
      have hmem := mem_veroneseChart_base_iff
        𝒮 d hd g he hg q (DirectSum.decompose (veroneseGrading 𝒮 d) f n) ha
      rw [← hpoint, hsourcePoint] at hmem
      simpa [I, J] using hmem
    have hcomponents :
        (∀ n, (DirectSum.decompose (veroneseGrading 𝒮 d) f n :
          veroneseSubring 𝒮 d) ∈ I) ↔
        (∀ m, (DirectSum.decompose 𝒮 (f : S) m : S) ∈ J) := by
      constructor
      · intro ht m
        by_cases hm : d ∣ m
        · obtain ⟨n, rfl⟩ := hm
          have hsrc : ((DirectSum.decompose (veroneseGrading 𝒮 d) f n :
              veroneseSubring 𝒮 d) : S) ∈ J := (hchartComp n).mp (ht n)
          have hc := coe_decompose_veroneseGrading 𝒮 d hd f n
          rw [show d * n = n * d by rw [Nat.mul_comm], hc]
          exact hsrc
        · have hzero : (DirectSum.decompose 𝒮 (f : S) m : S) = 0 := by
            classical
            rw [decompose_coe_veroneseSubring]
            exact congrArg Subtype.val (Finset.sum_eq_zero fun k hk ↦ by
              apply Subtype.ext
              apply DirectSum.decompose_of_mem_ne
              · exact (DirectSum.decompose (veroneseGrading 𝒮 d) f k).property
              · exact fun hmk ↦ hm ⟨k, by simpa [Nat.mul_comm] using hmk.symm⟩)
          simp [hzero]
      · intro hs n
        apply (hchartComp n).mpr
        have hc := coe_decompose_veroneseGrading 𝒮 d hd f n
        exact hc ▸ hs (n * d)
    exact hI.trans (hcomponents.trans hJ.symm)

/-- The inverse image of the standard open defined by `f ^ d` in the Veronese ring is
the standard open defined by `f` in the original ring. -/
public theorem veroneseProjIso_basicOpen (d : ℕ) (hd : 0 < d)
    (f : S) {e : ℕ} (_he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (veroneseProjIso 𝒮 d hd).hom ⁻¹ᵁ
        Proj.basicOpen (veroneseGrading 𝒮 d)
          (veronesePower 𝒮 d f hf) =
      Proj.basicOpen 𝒮 f :=
  by
    let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
    ext x
    show veronesePower 𝒮 d f hf ∉
        ((veroneseProjIso 𝒮 d hd).hom.base x).asHomogeneousIdeal ↔
      f ∉ x.asHomogeneousIdeal
    rw [veroneseProjIso_mem_iff 𝒮 d hd x
      (veronesePower 𝒮 d f hf)]
    show f ^ d ∉ x.asHomogeneousIdeal ↔ f ∉ x.asHomogeneousIdeal
    exact not_congr (x.isPrime.pow_mem_iff_mem d hd)

/-- On a standard open, the sheaf map of the canonical scheme isomorphism is the
degree-zero Veronese localization comparison. -/
public theorem veroneseProjIso_awayToSection (d : ℕ) (hd : 0 < d)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    let vf := veronesePower 𝒮 d f hf
    Proj.awayToSection (veroneseGrading 𝒮 d) vf ≫
        (veroneseProjIso 𝒮 d hd).hom.appLE
          (Proj.basicOpen (veroneseGrading 𝒮 d) vf)
          (Proj.basicOpen 𝒮 f)
          (by rw [veroneseProjIso_basicOpen 𝒮 d hd f he hf]) =
      CommRingCat.ofHom
          (veroneseAwayEquiv 𝒮 d f hf hd).toRingHom ≫
        Proj.awayToSection 𝒮 f :=
  by
    let : GradedRing (veroneseGrading 𝒮 d) := veroneseGradingGradedRing 𝒮 d hd
    let vf := veronesePower 𝒮 d f hf
    let Us := Proj.basicOpen 𝒮 f
    let Ut := Proj.basicOpen (veroneseGrading 𝒮 d) vf
    let E := veroneseAwayEquiv 𝒮 d f hf hd
    let isoS := Proj.basicOpenIsoSpec 𝒮 f hf he
    let isoT := Proj.basicOpenIsoSpec (veroneseGrading 𝒮 d) vf
      (veronesePower_mem 𝒮 d f hf) he
    have hpre : Us ≤ (veroneseProjIso 𝒮 d hd).hom ⁻¹ᵁ Ut := by
      rw [veroneseProjIso_basicOpen 𝒮 d hd f he hf]
    let hres := (veroneseProjIso 𝒮 d hd).hom.resLE Ut Us hpre
    have hAwaySquare : Proj.awayι 𝒮 f hf he ≫ (veroneseProjIso 𝒮 d hd).hom =
        Spec.map (CommRingCat.ofHom E.toRingHom) ≫ isoT.inv ≫ Ut.ι := by
      show Proj.awayι 𝒮 f hf he ≫ veroneseProjHom 𝒮 d hd = _
      rw [awayι_comp_veroneseProjHom_eq_chart]
      rfl
    have hresSquare : isoS.inv ≫ hres =
        Spec.map (CommRingCat.ofHom E.toRingHom) ≫ isoT.inv := by
      apply (cancel_mono Ut.ι).mp
      calc
        isoS.inv ≫ hres ≫ Ut.ι = (isoS.inv ≫ Us.ι) ≫ (veroneseProjIso 𝒮 d hd).hom := by
          rw [Scheme.Hom.resLE_comp_ι, Category.assoc]
        _ = Proj.awayι 𝒮 f hf he ≫ (veroneseProjIso 𝒮 d hd).hom := by rfl
        _ = Spec.map (CommRingCat.ofHom E.toRingHom) ≫ isoT.inv ≫ Ut.ι := hAwaySquare
        _ = (Spec.map (CommRingCat.ofHom E.toRingHom) ≫ isoT.inv) ≫ Ut.ι := by
          rw [Category.assoc]
    have hcomm : hres ≫ isoT.hom = isoS.hom ≫ Spec.map (CommRingCat.ofHom E.toRingHom) := by
      calc
        hres ≫ isoT.hom = (isoS.hom ≫ isoS.inv) ≫ hres ≫ isoT.hom := by simp
        _ = isoS.hom ≫ (isoS.inv ≫ hres) ≫ isoT.hom := by
          rw [Category.assoc, Category.assoc]
        _ = isoS.hom ≫ (Spec.map (CommRingCat.ofHom E.toRingHom) ≫ isoT.inv) ≫ isoT.hom := by
          rw [hresSquare]
        _ = isoS.hom ≫ Spec.map (CommRingCat.ofHom E.toRingHom) := by
          simp [Category.assoc]
    have happ := congrArg (fun k ↦ k.appTop) hcomm
    have hresTop : hres.appTop = Ut.topIso.hom ≫
        (veroneseProjIso 𝒮 d hd).hom.appLE Ut Us hpre ≫ Us.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top, hres] using
        (Scheme.Hom.resLE_app_top (f := (veroneseProjIso 𝒮 d hd).hom)
          (U := Ut) (V := Us) hpre)
    have happ' : isoT.hom.appTop ≫ Ut.topIso.hom ≫
        (veroneseProjIso 𝒮 d hd).hom.appLE Ut Us hpre ≫ Us.topIso.inv =
        (Spec.map (CommRingCat.ofHom E.toRingHom)).appTop ≫ isoS.hom.appTop := by
      simpa only [Scheme.Hom.comp_appTop, hresTop] using happ
    rw [show isoT.hom = Proj.basicOpenToSpec
        (veroneseGrading 𝒮 d) vf by rfl,
      show isoS.hom = Proj.basicOpenToSpec 𝒮 f by rfl] at happ'
    have ht : (Proj.basicOpenToSpec
        (veroneseGrading 𝒮 d) vf).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (veroneseGrading 𝒮 d) vf))).hom ≫
          Proj.awayToSection (veroneseGrading 𝒮 d) vf ≫ Ut.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top] using
        (Proj.basicOpenToSpec_app_top (veroneseGrading 𝒮 d) vf)
    have hs : (Proj.basicOpenToSpec 𝒮 f).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒮 f))).hom ≫
          Proj.awayToSection 𝒮 f ≫ Us.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top] using
        (Proj.basicOpenToSpec_app_top 𝒮 f)
    have hnat : (Spec.map (CommRingCat.ofHom E.toRingHom)).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒮 f))).hom =
      (Scheme.ΓSpecIso (CommRingCat.of
        (HomogeneousLocalization.Away (veroneseGrading 𝒮 d) vf))).hom ≫
        CommRingCat.ofHom E.toRingHom :=
      Scheme.ΓSpecIso_naturality (CommRingCat.ofHom E.toRingHom)
    rw [ht, hs] at happ'
    have hnatPost := congrArg (fun k ↦ k ≫ Proj.awayToSection 𝒮 f ≫ Us.topIso.inv) hnat
    have happ1 := happ'.trans hnatPost
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at happ1
    have happ'' : Proj.awayToSection (veroneseGrading 𝒮 d) vf ≫
          (veroneseProjIso 𝒮 d hd).hom.appLE Ut Us hpre ≫ Us.topIso.inv =
        CommRingCat.ofHom E.toRingHom ≫ Proj.awayToSection 𝒮 f ≫ Us.topIso.inv :=
      (cancel_epi (Scheme.ΓSpecIso
        (CommRingCat.of (HomogeneousLocalization.Away
          (veroneseGrading 𝒮 d) vf))).hom).mp happ1
    exact (cancel_mono Us.topIso.inv).mp happ''

end Stacks.Veronese

end
