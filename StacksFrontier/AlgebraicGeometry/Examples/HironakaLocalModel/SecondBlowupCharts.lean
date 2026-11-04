module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpIso
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.SecondBlowupRing

/-!
# The blow-up of a coordinate plane in affine space, by its two charts

Let `k` be a field and `R = k[X_l : l ∈ σ]`. For two distinct variables `X i`, `X j` the blow-up of
`Spec R` in the coordinate subspace `X i = X j = 0` has the two charts
`Spec k[X]` with `X j ↦ X i · X j` and `Spec k[X]` with `X i ↦ X j · X i`, and they cover it. This
is the shape of the second blow-up of Hironaka's local model (the source of [Stacks, Tag 08J1])
on the chart `U₂ = Spec k[v, y, z]` of the first blow-up, where the centre is `(v, z)`: the charts
are `Spec k[v, y, z₂]` (`z = v·z₂`) and `Spec k[v₂, y, z]` (`v = z·v₂`).

The ideal sheaf on `Spec R` of an ideal `I ⊆ R` is
`Stacks.Examples.HironakaLocalModel.idealSheafSpec I`, the ideal sheaf
`Scheme.IdealSheafData.ofIdealTop` of the transport of `I` along `Γ(Spec R, ⊤) ≅ R`; it is the
spelling of `Stacks.Blowup.affineBlowUpIso`, which identifies its blow-up with `Proj` of the Rees
algebra of `I`.

## Main definitions

* `Stacks.Examples.HironakaLocalModel.affineBlowupCoordEquiv`: the affine blowup algebra
  `R[I/X i]`, `I = (X i, X j)`, is the polynomial ring, with `X j / X i` as its new `X j`.
* `Stacks.Examples.HironakaLocalModel.coordChart`: the chart `Spec R ⟶ Bl_I Spec R`.

## Main results

* `Stacks.Examples.HironakaLocalModel.coordChart_blowUpToBase`: the chart lies over `Spec R` by
  `Spec` of `Stacks.Examples.HironakaLocalModel.blowupChartMap k i j`.
* `Stacks.Examples.HironakaLocalModel.coordChart_cover`: the two charts cover the blow-up.
* `Stacks.Examples.HironakaLocalModel.exists_isPullback_blowUp_of_comap_eq`: the blow-up of a
  scheme `B` in `K`, restricted over an open immersion `ι` with `K.comap ι = L`, is the blow-up
  in `L` ([Stacks, Tag 0805]).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Examples.HironakaLocalModel

attribute [local implicit_reducible] Stacks.Blowup.blowUpSpec

variable {k : Type u} [Field k] {σ : Type} [DecidableEq σ] {i j : σ}

/-! ### The affine blowup algebra of a coordinate plane -/

/-- The fraction `X j / X i` in `R_{X i}`. -/
def chartFrac (i j : σ) : Localization.Away (X i : MvPolynomial σ k) :=
  Localization.mk (X j) ⟨X i, Submonoid.mem_powers _⟩

omit [DecidableEq σ] in
/-- In `R_{X i}`, `X i · (x / X i) = x`. -/
theorem algebraMap_mul_mk (i : σ) (x : MvPolynomial σ k) :
    algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) (X i) *
        Localization.mk x ⟨X i, Submonoid.mem_powers _⟩ =
      algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) x := by
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec' _ x ⟨X i, Submonoid.mem_powers _⟩

variable (k) in
/-- The chart ring `k[X]` inside `R_{X i}`: `X j ↦ X j / X i`, every other variable to itself. -/
def chartFracMap (i j : σ) :
    MvPolynomial σ k →+* Localization.Away (X i : MvPolynomial σ k) :=
  eval₂Hom ((algebraMap (MvPolynomial σ k) _).comp C)
    fun l => if l = j then chartFrac i j else
      algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) (X l)

/-- The chart map sends `X j` to `X j / X i`. -/
theorem chartFracMap_X_self : chartFracMap k i j (X j) = chartFrac i j := by
  simp [chartFracMap]

/-- The chart map sends a variable `X l` with `l ≠ j` to its image in `R_{X i}`. -/
theorem chartFracMap_X_of_ne {l : σ} (hl : l ≠ j) :
    chartFracMap k i j (X l) =
      algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) (X l) := by
  simp [chartFracMap, hl]

/-- The chart map sends a constant `C c` to its image in `R_{X i}`. -/
theorem chartFracMap_C (c : k) : chartFracMap k i j (C c) =
    algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) (C c) := by
  simp [chartFracMap]

/-- The chart ring over `R`: composing the chart map `R ⟶ k[X]` with `k[X] ⟶ R_{X i}` is the
localization map. -/
theorem chartFracMap_comp (hij : i ≠ j) :
    (chartFracMap k i j).comp (blowupChartMap k i j : MvPolynomial σ k →+* MvPolynomial σ k) =
      algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_)
  · simp [chartFracMap_C]
  · simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    by_cases hl : l = j
    · subst hl
      rw [blowupChartMap_X_self, map_mul, chartFracMap_X_self, chartFracMap_X_of_ne hij]
      exact algebraMap_mul_mk i _
    · rw [blowupChartMap_X_of_ne k i j hl, chartFracMap_X_of_ne hl]

/-- The chart map sends `blowupChartMap k i j r` to the image of `r` in `R_{X i}`. -/
private theorem chartFracMap_blowupChartMap (hij : i ≠ j) (r : MvPolynomial σ k) :
    chartFracMap k i j (blowupChartMap k i j r) =
      algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) r :=
  congrArg (fun φ : MvPolynomial σ k →+* _ => φ r) (chartFracMap_comp hij)

/-- For `i ≠ j` the chart map `k[X] ⟶ R_{X i}` is injective. -/
theorem chartFracMap_injective (hij : i ≠ j) : Function.Injective (chartFracMap k i j) := by
  have hunit : IsUnit (((algebraMap (MvPolynomial σ k)
      (Localization.Away (X i : MvPolynomial σ k))).comp
      (blowupChartMap k i j : MvPolynomial σ k →+* MvPolynomial σ k)) (X i)) := by
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      blowupChartMap_X_of_ne k i j hij]
    exact IsLocalization.Away.algebraMap_isUnit _
  let lam : (Localization.Away (X i : MvPolynomial σ k)) →+*
      (Localization.Away (X i : MvPolynomial σ k)) :=
    IsLocalization.Away.lift (X i) hunit
  have hlam : ∀ r, lam (algebraMap _ (Localization.Away (X i : MvPolynomial σ k)) r) =
      algebraMap _ (Localization.Away (X i : MvPolynomial σ k)) (blowupChartMap k i j r) := fun r =>
    IsLocalization.lift_eq _ r
  have hcomp : lam.comp (chartFracMap k i j) =
      algebraMap _ (Localization.Away (X i : MvPolynomial σ k)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, chartFracMap_C, hlam,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      by_cases hl : l = j
      · subst hl
        rw [chartFracMap_X_self]
        refine (IsLocalization.Away.algebraMap_isUnit (R := MvPolynomial σ k)
          (S := Localization.Away (X i : MvPolynomial σ k)) (X i)).mul_left_cancel ?_
        have h1 := congrArg lam (algebraMap_mul_mk (k := k) i (X l))
        rw [map_mul, hlam, hlam, blowupChartMap_X_of_ne k i l hij, blowupChartMap_X_self,
          map_mul] at h1
        exact h1
      · rw [chartFracMap_X_of_ne hl, hlam, blowupChartMap_X_of_ne k i j hl]
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k))) :=
    IsLocalization.injective (Localization.Away (X i : MvPolynomial σ k))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero i))
  intro p q hpq
  apply hinj
  rw [← hcomp]
  exact congrArg lam hpq

/-- If `X j ∈ I`, the chart map takes values in the affine blowup algebra `R[I/X i]`. -/
theorem chartFracMap_mem_affineBlowup {I : Ideal (MvPolynomial σ k)} (hj : X j ∈ I)
    (p : MvPolynomial σ k) : chartFracMap k i j p ∈ affineBlowup I (X i) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [chartFracMap_C]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p l hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp ?_
    by_cases hl : l = j
    · subst hl
      rw [chartFracMap_X_self]
      exact Algebra.subset_adjoin ⟨X l, hj, rfl⟩
    · rw [chartFracMap_X_of_ne hl]
      exact Subalgebra.algebraMap_mem _ _

/-- For `i ≠ j` and `I = (X i, X j)`, every element of `R[I/X i]` is in the image of the chart
map. -/
theorem exists_chartFracMap_eq (hij : i ≠ j) {I : Ideal (MvPolynomial σ k)}
    (hI : I = Ideal.span {X i, X j}) (z : Localization.Away (X i : MvPolynomial σ k))
    (hz : z ∈ affineBlowup I (X i)) : ∃ p, chartFracMap k i j p = z := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨x, hxI, rfl⟩ := hx
    rw [hI] at hxI
    obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.1 hxI
    refine ⟨blowupChartMap k i j r + blowupChartMap k i j s * X j, ?_⟩
    rw [map_add, map_mul, chartFracMap_blowupChartMap hij, chartFracMap_blowupChartMap hij,
      chartFracMap_X_self]
    refine (IsLocalization.Away.algebraMap_isUnit (R := MvPolynomial σ k)
          (S := Localization.Away (X i : MvPolynomial σ k)) (X i)).mul_left_cancel ?_
    rw [algebraMap_mul_mk, mul_add, chartFrac, ← mul_assoc, mul_comm (algebraMap _ _ (X i))
      (algebraMap (MvPolynomial σ k) (Localization.Away (X i : MvPolynomial σ k)) s), mul_assoc,
      algebraMap_mul_mk]
    simp only [map_add, map_mul]
    ring
  | algebraMap r => exact ⟨blowupChartMap k i j r, chartFracMap_blowupChartMap hij r⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p * q, map_mul _ _ _⟩

variable (k) in
/-- **The affine blowup algebra of a coordinate plane is a polynomial ring.** For `i ≠ j` and
`I = (X i, X j)` in `R = k[X]`, the affine blowup algebra `R[I/X i] ⊆ R_{X i}` is `k[X]`, the new
`X j` being `X j / X i`. -/
def affineBlowupCoordEquiv (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) :
    affineBlowup I (X i) ≃+* MvPolynomial σ k :=
  (RingEquiv.ofBijective ((chartFracMap k i j).codRestrict (affineBlowup I (X i))
      (chartFracMap_mem_affineBlowup (hI ▸ Ideal.subset_span (Or.inr rfl))))
    ⟨RingHom.injective_codRestrict.mpr (chartFracMap_injective hij), fun z => by
      obtain ⟨p, hp⟩ := exists_chartFracMap_eq hij hI z.1 z.2
      exact ⟨p, Subtype.ext hp⟩⟩).symm

/-- `affineBlowupCoordEquiv` sends the image of `r ∈ R` to `blowupChartMap k i j r`. -/
theorem affineBlowupCoordEquiv_algebraMap (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) (r : MvPolynomial σ k) :
    affineBlowupCoordEquiv k hij I hI (algebraMap (MvPolynomial σ k) _ r) =
      blowupChartMap k i j r := by
  rw [affineBlowupCoordEquiv, RingEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  exact (chartFracMap_blowupChartMap hij r).symm

/-! ### The chart of `Proj` of the Rees algebra -/

omit [DecidableEq σ] in
/-- If `I = (X i, X j)`, then `X i ∈ I`. -/
theorem X_mem_of_eq_span {I : Ideal (MvPolynomial σ k)} (hI : I = Ideal.span {X i, X j}) :
    (X i : MvPolynomial σ k) ∈ I :=
  hI ▸ Ideal.subset_span (Or.inl rfl)

variable (k) in
/-- The chart ring `(R[It])_{((X i)⁽¹⁾)}` of `Proj` of the Rees algebra of `I = (X i, X j)` is the
polynomial ring `k[X]`. -/
def chartAwayCoordEquiv (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) :
    HomogeneousLocalization.Away (Stacks.Blowup.reesGrading I)
        (Stacks.Blowup.reesDegOne I (X_mem_of_eq_span hI)) ≃+* MvPolynomial σ k :=
  (Stacks.Blowup.reesAwayEquivAffineBlowup I (X i) (X_mem_of_eq_span hI)).trans
    (affineBlowupCoordEquiv k hij I hI)

/-- `chartAwayCoordEquiv` sends the image of `r ∈ R` in the chart ring to
`blowupChartMap k i j r`. -/
theorem chartAwayCoordEquiv_chartAwayMap (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) (r : MvPolynomial σ k) :
    chartAwayCoordEquiv k hij I hI (Stacks.Blowup.chartAwayMap I (X_mem_of_eq_span hI) r) =
      blowupChartMap k i j r := by
  rw [chartAwayCoordEquiv, RingEquiv.trans_apply, Stacks.Blowup.chartAwayMap,
    RingHom.comp_apply, Stacks.Blowup.reesAwayEquivAffineBlowup_fromZeroRingHom]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  exact affineBlowupCoordEquiv_algebraMap hij I hI r

/-! ### The two charts of the blow-up -/

/-- The ideal sheaf on `Spec R` of an ideal `I ⊆ R`: the ideal sheaf whose ideal of global
sections is the transport of `I` along `Γ(Spec R, ⊤) ≅ R`. -/
abbrev idealSheafSpec {R : Type u} [CommRing R] (I : Ideal R) :
    (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)

variable (k) in
/-- **The chart of the blow-up of `Spec k[X]` in `(X i, X j)` on which `X i` generates the
centre**, as a morphism `Spec k[X] ⟶ Bl_I Spec k[X]`. It lies over `Spec k[X]` by `Spec` of
`blowupChartMap k i j` (`X j ↦ X i · X j`): see
`Stacks.Examples.HironakaLocalModel.coordChart_blowUpToBase`. -/
def coordChart (hij : i ≠ j) (I : Ideal (MvPolynomial σ k)) (hI : I = Ideal.span {X i, X j}) :
    Spec (CommRingCat.of (MvPolynomial σ k)) ⟶ blowUp (idealSheafSpec I) :=
  Spec.map (CommRingCat.ofHom (chartAwayCoordEquiv k hij I hI).toRingHom) ≫
    Stacks.Blowup.awayChartι I (X_mem_of_eq_span hI) ≫
      (Stacks.Blowup.affineBlowUpIso (MvPolynomial σ k) I).hom

/-- The chart `coordChart` is an open immersion. -/
instance (hij : i ≠ j) (I : Ideal (MvPolynomial σ k)) (hI : I = Ideal.span {X i, X j}) :
    IsOpenImmersion (coordChart k hij I hI) := by
  have : IsIso (CommRingCat.ofHom (chartAwayCoordEquiv k hij I hI).toRingHom) :=
    inferInstanceAs (IsIso (chartAwayCoordEquiv k hij I hI).toCommRingCatIso.hom)
  dsimp only [coordChart]
  infer_instance

/-- **The chart lies over the base**: `Spec k[X] ⟶ Bl_I Spec k[X] ⟶ Spec k[X]` is `Spec` of the
chart map `X j ↦ X i · X j`. -/
theorem coordChart_blowUpToBase (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) :
    coordChart k hij I hI ≫ blowUpToBase (idealSheafSpec I) =
      Spec.map (CommRingCat.ofHom
        (blowupChartMap k i j : MvPolynomial σ k →+* MvPolynomial σ k)) := by
  rw [coordChart, Category.assoc, Category.assoc, Stacks.Blowup.affineBlowUpIso_hom_comp,
    Stacks.Blowup.awayι_comp_toSpec, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  exact chartAwayCoordEquiv_chartAwayMap hij I hI r

omit [DecidableEq σ] in
/-- A point of `Proj` of the Rees algebra of `(X i, X j)` lies in `D₊((X i)⁽¹⁾)` or in
`D₊((X j)⁽¹⁾)`: the degree-one elements of the Rees algebra are combinations of these two. -/
theorem mem_basicOpen_or_mem_basicOpen (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) (hi : X i ∈ I) (hj : X j ∈ I)
    (y : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)) :
    y ∈ Proj.basicOpen (Stacks.Blowup.reesGrading I) (Stacks.Blowup.reesDegOne I hi) ∨
      y ∈ Proj.basicOpen (Stacks.Blowup.reesGrading I) (Stacks.Blowup.reesDegOne I hj) := by
  by_contra h
  rw [not_or, Proj.mem_basicOpen, Proj.mem_basicOpen, not_not, not_not] at h
  have hy : y ∈ (⊤ : (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)).Opens) := trivial
  rw [← Stacks.Blowup.iSup_basicOpen_reesDegOne_eq_top I] at hy
  obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [Proj.mem_basicOpen] at hr
  apply hr
  have hrI : (r : MvPolynomial σ k) ∈ Ideal.span {X i, X j} := hI ▸ r.2
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 hrI
  have hdec : Stacks.Blowup.reesDegOne I r.2 =
      algebraMap _ (reesAlgebra I) α * Stacks.Blowup.reesDegOne I hi +
        algebraMap _ (reesAlgebra I) β * Stacks.Blowup.reesDegOne I hj := by
    apply Subtype.ext
    simp only [Stacks.Blowup.coe_reesDegOne, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.C_mul_monomial, ← hαβ]
    exact map_add _ _ _
  rw [hdec]
  exact Ideal.add_mem y.asHomogeneousIdeal.toIdeal
    (Ideal.mul_mem_left y.asHomogeneousIdeal.toIdeal _ h.1)
    (Ideal.mul_mem_left y.asHomogeneousIdeal.toIdeal _ h.2)

/-- The points of `Spec` of the chart ring of `Proj` of the Rees algebra, read on `Spec k[X]`. -/
theorem exists_coordChart_eq (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j})
    (y : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I))
    (hy : y ∈ Proj.basicOpen (Stacks.Blowup.reesGrading I)
      (Stacks.Blowup.reesDegOne I (X_mem_of_eq_span hI))) :
    ∃ w, coordChart k hij I hI w = (Stacks.Blowup.affineBlowUpIso (MvPolynomial σ k) I).hom y := by
  rw [← Proj.opensRange_awayι _ _ (Stacks.Blowup.reesDegOne_mem_reesGrading I
    (X_mem_of_eq_span hI)) Nat.one_pos] at hy
  obtain ⟨w, rfl⟩ := hy
  set e := chartAwayCoordEquiv k hij I hI
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) w, ?_⟩
  have hid : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
      ext t
      simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ coordChart k hij I hI) w = _
  rw [coordChart, ← Category.assoc, hid, Category.id_comp]
  rfl

/-- **The two charts cover the blow-up**: every point of `Bl_{(X i, X j)} Spec k[X]` lies on the
chart where `X i` generates the centre or on the one where `X j` does. -/
theorem coordChart_cover (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) (hI' : I = Ideal.span {X j, X i})
    (x : blowUp (idealSheafSpec I)) :
    x ∈ Set.range (coordChart k hij I hI) ∨ x ∈ Set.range (coordChart k hij.symm I hI') := by
  set e := Stacks.Blowup.affineBlowUpIso (MvPolynomial σ k) I
  have hx : x = e.hom (e.inv x) := by
    change x = (e.inv ≫ e.hom) x
    rw [e.inv_hom_id]
    rfl
  rcases mem_basicOpen_or_mem_basicOpen I hI (X_mem_of_eq_span hI) (X_mem_of_eq_span hI')
      (e.inv x) with h | h
  · obtain ⟨w, hw⟩ := exists_coordChart_eq hij I hI (e.inv x) h
    exact Or.inl ⟨w, hw.trans hx.symm⟩
  · obtain ⟨w, hw⟩ := exists_coordChart_eq hij.symm I hI' (e.inv x) h
    exact Or.inr ⟨w, hw.trans hx.symm⟩

/-- The two charts cover the blow-up, as an equality of opens. -/
theorem coordChart_opensRange_sup (hij : i ≠ j) (I : Ideal (MvPolynomial σ k))
    (hI : I = Ideal.span {X i, X j}) (hI' : I = Ideal.span {X j, X i}) :
    (coordChart k hij I hI).opensRange ⊔ (coordChart k hij.symm I hI').opensRange = ⊤ :=
  eq_top_iff.mpr fun x _ => coordChart_cover hij I hI hI' x

/-! ### Restriction to an open of the base -/

/-- **The blow-up restricts to opens** ([Stacks, Tag 0805]): for an open immersion `ι : U ⟶ B`
and an ideal sheaf `K` on `B` whose inverse image on `U` is `L`, the blow-up of `U` in `L` is the
base change along `ι` of the blow-up of `B` in `K`. -/
theorem exists_isPullback_blowUp_of_comap_eq {B U : Scheme.{u}} (K : B.IdealSheafData)
    (ι : U ⟶ B) [IsOpenImmersion ι] (L : U.IdealSheafData) (hL : K.comap ι = L) :
    ∃ h : blowUp L ⟶ blowUp K, IsPullback (blowUpToBase L) h ι (blowUpToBase K) := by
  subst hL
  exact exists_isPullback_blowUpToBase_comap ι K

/-! ### The second blow-up of the local model -/

variable (k) in
/-- The second centre of Hironaka's local model on the chart `U₂ = Spec k[v, y, z]` of the first
blow-up: the coordinate line `(v, z)`, `v = X 0`, `z = X 2`. -/
abbrev secondCentre : Ideal (MvPolynomial (Fin 3) k) := Ideal.span {X 0, X 2}

/-- The second centre is also `(z, v)`. -/
theorem secondCentre_eq_span_swap : secondCentre k = Ideal.span {X 2, X 0} := by
  rw [secondCentre, Set.pair_comm]

variable (k) in
/-- **The first chart of `Bl_{(v,z)} Spec k[v, y, z]`**: `Spec k[v, y, z₂]`, with `z = v·z₂`. -/
def secondChartOne :
    Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) ⟶ blowUp (idealSheafSpec (secondCentre k)) :=
  coordChart k (show (0 : Fin 3) ≠ 2 by decide) (secondCentre k) rfl

variable (k) in
/-- **The second chart of `Bl_{(v,z)} Spec k[v, y, z]`**: `Spec k[v₂, y, z]`, with `v = z·v₂`. -/
def secondChartTwo :
    Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) ⟶ blowUp (idealSheafSpec (secondCentre k)) :=
  coordChart k (show (2 : Fin 3) ≠ 0 by decide) (secondCentre k) secondCentre_eq_span_swap

/-- The first chart `secondChartOne` is an open immersion. -/
instance : IsOpenImmersion (secondChartOne k) := by
  dsimp only [secondChartOne]
  infer_instance

/-- The second chart `secondChartTwo` is an open immersion. -/
instance : IsOpenImmersion (secondChartTwo k) := by
  dsimp only [secondChartTwo]
  infer_instance

/-- The first chart lies over `Spec k[v, y, z]` by `Spec` of `chartOneMap k`. -/
theorem secondChartOne_blowUpToBase :
    secondChartOne k ≫ blowUpToBase (idealSheafSpec (secondCentre k)) =
      Spec.map (CommRingCat.ofHom
        (chartOneMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)) :=
  coordChart_blowUpToBase _ _ _

/-- The second chart lies over `Spec k[v, y, z]` by `Spec` of `chartTwoMap k`. -/
theorem secondChartTwo_blowUpToBase :
    secondChartTwo k ≫ blowUpToBase (idealSheafSpec (secondCentre k)) =
      Spec.map (CommRingCat.ofHom
        (chartTwoMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)) :=
  coordChart_blowUpToBase _ _ _

/-- **The two charts cover `Bl_{(v,z)} Spec k[v, y, z]`.** -/
theorem secondChart_opensRange_sup :
    (secondChartOne k).opensRange ⊔ (secondChartTwo k).opensRange = ⊤ :=
  coordChart_opensRange_sup _ _ _ _

/-- Every point of `Bl_{(v,z)} Spec k[v, y, z]` lies in the range of `secondChartOne` or of
`secondChartTwo`. -/
theorem secondChart_cover (x : blowUp (idealSheafSpec (secondCentre k))) :
    x ∈ Set.range (secondChartOne k) ∨ x ∈ Set.range (secondChartTwo k) :=
  coordChart_cover _ _ _ _ x

end Stacks.Examples.HironakaLocalModel

end
