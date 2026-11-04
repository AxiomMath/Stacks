module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine

/-!
# Points of `Proj` with values in a ring, from ring homomorphisms

Let `A` be a graded ring and `φ : A →+* B` a ring homomorphism sending a homogeneous element `t`
of positive degree to a unit. Then `φ` determines a `B`-valued point `Spec B ⟶ Proj A`, through
the standard chart `D₊(t) = Spec A_{(t)}`: the induced map `A_{(t)} → B` sends `a / tⁿ` to
`φ(a) φ(t)⁻ⁿ`.

## Main definitions

* `Stacks.ProjPoint.awayEval`: the map `A_{(t)} → B` induced by `φ`.
* `Stacks.ProjPoint.point`: the resulting morphism `Spec B ⟶ Proj A`.
* `Stacks.ProjPoint.glue`: the morphism out of `Proj A` glued from compatible morphisms out of
  the standard charts of a cover.

## Main results

* `Stacks.ProjPoint.point_indep`: the point does not depend on the chart `t`.
* `Stacks.ProjPoint.SpecMap_comp_point`: points are natural in `B`.
* `Stacks.ProjPoint.point_comp_map`: composing with the morphism `Proj.map f` induced by a
  graded ring homomorphism `f` corresponds to composing `φ` with `f`.
* `Stacks.ProjPoint.point_comp_toSpecZero`: the composite with `Proj A ⟶ Spec A₀` is `φ`
  restricted to `A₀`.
* `Stacks.ProjPoint.awayEval_eq_of_point_eq`: two points on the same chart agree only if the
  induced maps on `A_{(t)}` agree.
* `Stacks.ProjPoint.point_eq_of_scale`: rescaling `φ` in degree `n` by the `n`-th power of a unit
  does not change the point.
* `Stacks.ProjPoint.hom_ext_of_point`: two morphisms out of `Proj A` agree if they agree on a
  point whose maps on the degree-zero localizations of a cover are injective into a domain, for
  instance the generic point `A → Frac A` of a graded domain.
* `Stacks.ProjPoint.point_comp_glue`: a point on a chart, followed by a glued morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

namespace Stacks.ProjPoint

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {B : Type u} [CommRing B]

/-- The inverse of the `n`-th power of a unit is characterized by its product with that power. -/
theorem eq_val_inv_pow_of_mul_eq_one {C : Type u} [CommRing C] (v : Cˣ) (n : ℕ) {y : C}
    (h : y * (v : C) ^ n = 1) : y = ↑(v⁻¹ ^ n) := by
  rw [← Units.val_pow_eq_pow_val, mul_comm] at h
  rw [inv_pow]
  exact Units.eq_inv_of_mul_eq_one_left h

/-- The inverse of the `n`-th power of a unit, times that power, is one. -/
theorem val_inv_pow_mul_pow {C : Type u} [CommRing C] {x : C} (hx : IsUnit x) (n : ℕ) :
    (↑(hx.unit⁻¹ ^ n) : C) * x ^ n = 1 := by
  rw [show x ^ n = ↑(hx.unit ^ n) by simp, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]

/-- The ring homomorphism `A_{(t)} → B` induced by a ring homomorphism `φ : A →+* B` sending `t`
to a unit. -/
def awayEval (φ : A →+* B) (t : A) (hu : IsUnit (φ t)) : Away 𝒜 t →+* B :=
  (IsLocalization.Away.lift t hu).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- The value of `awayEval` on a fraction `a / tⁿ`. -/
theorem awayEval_mk (φ : A →+* B) {t : A} (hu : IsUnit (φ t)) {d : ℕ} (htd : t ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayEval 𝒜 φ t hu (Away.mk 𝒜 htd n a ha) = φ a * ↑(hu.unit⁻¹ ^ n) := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  show φ a = φ (t ^ n) * (φ a * ↑(hu.unit⁻¹ ^ n))
  rw [map_pow, mul_left_comm, mul_comm (φ t ^ n), val_inv_pow_mul_pow, mul_one]

/-- The `B`-valued point of `Proj A` determined by `φ : A →+* B`, read on the chart `D₊(t)`. -/
def point (φ : A →+* B) (t : A) {d : ℕ} (htd : t ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ t)) :
    Spec (.of B) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (awayEval 𝒜 φ t hu)) ≫ Proj.awayι 𝒜 t htd hd

/-- The point does not depend on how the chart element is written. -/
theorem point_congr (φ : A →+* B) {t t' : A} (h : t = t') {d : ℕ} (htd : t ∈ 𝒜 d)
    (htd' : t' ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ t)) (hu' : IsUnit (φ t')) :
    point 𝒜 φ t htd hd hu = point 𝒜 φ t' htd' hd hu' := by
  subst h
  rfl

/-- Equal ring homomorphisms give equal points. -/
theorem point_congr_ringHom {φ φ' : A →+* B} (h : φ = φ') (t : A) {d : ℕ} (htd : t ∈ 𝒜 d)
    (hd : 0 < d) (hu : IsUnit (φ t)) (hu' : IsUnit (φ' t)) :
    point 𝒜 φ t htd hd hu = point 𝒜 φ' t htd hd hu' := by
  subst h
  rfl

/-- The point does not depend on the degree in which the chart element is recorded. -/
theorem point_congr_deg (φ : A →+* B) {t : A} {d d' : ℕ} (h : d = d') (htd : t ∈ 𝒜 d)
    (htd' : t ∈ 𝒜 d') (hd : 0 < d) (hd' : 0 < d') (hu : IsUnit (φ t)) :
    point 𝒜 φ t htd hd hu = point 𝒜 φ t htd' hd' hu := by
  subst h
  rfl

/-- Passing from the chart `D₊(t)` to the smaller chart `D₊(t t')` is compatible with the maps
induced by `φ`. -/
theorem awayEval_comp_awayMap (φ : A →+* B) {t t' : A} {d d' : ℕ} (htd : t ∈ 𝒜 d)
    (htd' : t' ∈ 𝒜 d') (hu : IsUnit (φ t)) (hux : IsUnit (φ (t * t'))) :
    (awayEval 𝒜 φ (t * t') hux).comp (awayMap 𝒜 htd' (x := t * t') rfl) =
      awayEval 𝒜 φ t hu := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 htd x
  rw [RingHom.comp_apply, awayMap_mk, awayEval_mk, awayEval_mk, map_mul, map_pow, mul_assoc]
  congr 1
  refine eq_val_inv_pow_of_mul_eq_one hu.unit n ?_
  have h1 : (↑(hux.unit⁻¹ ^ n) : B) * (φ t ^ n * φ t' ^ n) = 1 := by
    rw [← mul_pow, ← map_mul]
    exact val_inv_pow_mul_pow hux n
  rw [IsUnit.unit_spec]
  linear_combination h1

/-- The point read on `D₊(t)` is the point read on `D₊(t t')`. -/
theorem point_eq_point_mul (φ : A →+* B) {t t' : A} {d d' : ℕ} (htd : t ∈ 𝒜 d)
    (htd' : t' ∈ 𝒜 d') (hd : 0 < d) (hu : IsUnit (φ t)) (hu' : IsUnit (φ t')) :
    point 𝒜 φ t htd hd hu =
      point 𝒜 φ (t * t') (SetLike.mul_mem_graded htd htd') (hd.trans_le (d.le_add_right d'))
        (by rw [map_mul]; exact hu.mul hu') := by
  have hux : IsUnit (φ (t * t')) := by simpa only [map_mul] using hu.mul hu'
  unfold point
  rw [← awayEval_comp_awayMap 𝒜 φ htd htd' hu hux, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]

/-- **The point does not depend on the chart.** -/
theorem point_indep (φ : A →+* B) {t t' : A} {d d' : ℕ} (htd : t ∈ 𝒜 d) (htd' : t' ∈ 𝒜 d')
    (hd : 0 < d) (hd' : 0 < d') (hu : IsUnit (φ t)) (hu' : IsUnit (φ t')) :
    point 𝒜 φ t htd hd hu = point 𝒜 φ t' htd' hd' hu' := by
  rw [point_eq_point_mul 𝒜 φ htd htd' hd hu hu', point_eq_point_mul 𝒜 φ htd' htd hd' hu' hu]
  have hux : IsUnit (φ (t * t')) := by simpa only [map_mul] using hu.mul hu'
  rw [point_congr 𝒜 φ (mul_comm t t') _
    (by rw [mul_comm]; exact SetLike.mul_mem_graded htd htd') _ hux
    (by rw [mul_comm]; exact hux)]
  exact point_congr_deg 𝒜 φ (add_comm d d') _ _ _ _ _

/-- **Points are natural in the ring of values.** -/
theorem SpecMap_comp_point {C : Type u} [CommRing C] (g : B →+* C) (φ : A →+* B) (t : A)
    {d : ℕ} (htd : t ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ t)) :
    Spec.map (CommRingCat.ofHom g) ≫ point 𝒜 φ t htd hd hu =
      point 𝒜 (g.comp φ) t htd hd (hu.map g) := by
  have key : g.comp (awayEval 𝒜 φ t hu) = awayEval 𝒜 (g.comp φ) t (hu.map g) := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 htd x
    rw [RingHom.comp_apply, awayEval_mk, awayEval_mk, map_mul, RingHom.comp_apply]
    congr 1
    refine eq_val_inv_pow_of_mul_eq_one _ n ?_
    rw [IsUnit.unit_spec, RingHom.comp_apply, ← map_pow, ← map_mul, val_inv_pow_mul_pow,
      map_one]
  unfold point
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-- The map on degree-zero localizations induced by a graded ring homomorphism `f` is
compatible with the maps induced by `φ` and by `φ ∘ f`. -/
theorem awayEval_comp_awayMapOfGraded {A' τ : Type u} [CommRing A'] [SetLike τ A']
    [AddSubgroupClass τ A'] {ℬ : ℕ → τ} [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (φ : A' →+* B) {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (φ (f s))) :
    (awayEval ℬ φ (f s) hu).comp (Away.map f s) =
      awayEval 𝒜 (φ.comp (f : A →+* A')) s hu := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  rw [RingHom.comp_apply, Away.map_mk, awayEval_mk,
    awayEval_mk 𝒜 (φ.comp (f : A →+* A')) (t := s) hu hs]
  rfl

/-- **Composing with the morphism induced by a graded ring homomorphism.** The point of `Proj ℬ`
determined by `φ`, read on `D₊(f s)`, followed by `Proj.map f`, is the point of `Proj 𝒜`
determined by `φ ∘ f`. -/
theorem point_comp_map {A' τ : Type u} [CommRing A'] [SetLike τ A'] [AddSubgroupClass τ A']
    {ℬ : ℕ → τ} [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (φ : A' →+* B) (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ (f s))) :
    point ℬ φ (f s) (f.2 hs) hd hu ≫ Proj.map f hf =
      point 𝒜 (φ.comp (f : A →+* A')) s hs hd hu := by
  unfold point
  rw [Category.assoc, Proj.awayι_comp_map f hf hd s hs, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, awayEval_comp_awayMapOfGraded 𝒜 f φ hs hu]

/-- `awayEval` on the degree-zero elements is `φ`. -/
theorem awayEval_fromZeroRingHom (φ : A →+* B) (t : A) {d : ℕ} (htd : t ∈ 𝒜 d)
    (hu : IsUnit (φ t)) (a : 𝒜 0) :
    awayEval 𝒜 φ t hu (fromZeroRingHom 𝒜 (Submonoid.powers t) a) = φ (a : A) := by
  have : fromZeroRingHom 𝒜 (Submonoid.powers t) a =
      Away.mk 𝒜 htd 0 (a : A) (by simp) := by
    ext
    show (HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩).val = _
    rw [HomogeneousLocalization.val_mk, Away.val_mk]
    congr 1
    ext
    simp
  rw [this, awayEval_mk, pow_zero, Units.val_one, mul_one]

/-- The composite of a point with the morphism `Proj A ⟶ Spec A₀` is `φ` restricted to `A₀`. -/
theorem point_comp_toSpecZero (φ : A →+* B) (t : A) {d : ℕ} (htd : t ∈ 𝒜 d) (hd : 0 < d)
    (hu : IsUnit (φ t)) :
    point 𝒜 φ t htd hd hu ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (𝒜 0) A))) := by
  have key : (awayEval 𝒜 φ t hu).comp (fromZeroRingHom 𝒜 (Submonoid.powers t)) =
      φ.comp (algebraMap (𝒜 0) A) := by
    ext a
    rw [RingHom.comp_apply, awayEval_fromZeroRingHom 𝒜 φ t htd hu]
    rfl
  unfold point
  rw [Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-- Two points read on the same chart agree only if the induced maps on the degree-zero
localization agree. -/
theorem awayEval_eq_of_point_eq {φ φ' : A →+* B} {t : A} {d : ℕ} (htd : t ∈ 𝒜 d)
    (hd : 0 < d) (hu : IsUnit (φ t)) (hu' : IsUnit (φ' t))
    (h : point 𝒜 φ t htd hd hu = point 𝒜 φ' t htd hd hu') :
    awayEval 𝒜 φ t hu = awayEval 𝒜 φ' t hu' := by
  unfold point at h
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The value in the localization of a fraction transported to a smaller chart. -/
theorem val_awayMap_mk {f g x : A} {d m' : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 m') (hx : x = f * g)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) (w : Localization.Away x)
    (hw : algebraMap A (Localization.Away x) f * w = 1) :
    (awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha)).val = algebraMap A _ a * w ^ n := by
  rw [val_awayMap]
  exact Localization.awayLift_mk _ _ _ _ hw n

/-- **Rescaling.** If `φ' = λⁿ φ` on the degree-`n` part of `A` for a unit `λ`, then `φ` and `φ'`
determine the same point. -/
theorem point_eq_of_scale {φ φ' : A →+* B} (μ : Bˣ)
    (hφ : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ' a = (μ : B) ^ n * φ a) (t : A) {d : ℕ}
    (htd : t ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (φ t)) (hu' : IsUnit (φ' t)) :
    point 𝒜 φ t htd hd hu = point 𝒜 φ' t htd hd hu' := by
  have key : awayEval 𝒜 φ t hu = awayEval 𝒜 φ' t hu' := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 htd x
    rw [awayEval_mk, awayEval_mk, hφ _ a ha]
    have h1 := val_inv_pow_mul_pow hu' n
    rw [show φ' t ^ n = (μ : B) ^ (n * d) * φ t ^ n by
      rw [hφ d t htd, mul_pow, ← pow_mul, mul_comm d n]] at h1
    have h2 : (μ : B) ^ (n * d) * ↑(hu'.unit⁻¹ ^ n) = ↑(hu.unit⁻¹ ^ n) :=
      eq_val_inv_pow_of_mul_eq_one hu.unit n (by rw [IsUnit.unit_spec]; linear_combination h1)
    rw [← h2]
    ring
  unfold point
  rw [key]

/-- `awayEval` of the map to the fraction field of a graded domain is injective. -/
theorem injective_awayEval_algebraMap [IsDomain A] (t : A)
    (hu : IsUnit (algebraMap A (FractionRing A) t)) :
    Function.Injective (awayEval 𝒜 (algebraMap A (FractionRing A)) t hu) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero]
  have hx' : IsLocalization.Away.lift t hu x.val = 0 := hx
  generalize x.val = y at hx' ⊢
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) y
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec, mul_zero] at hx'
  rw [(IsFractionRing.injective A (FractionRing A)) (hx'.trans (map_zero _).symm)]
  exact IsLocalization.mk'_zero s

/-- **Morphisms out of `Proj A` are determined on a suitable point.** Let `φ : A →+* L` be a ring
homomorphism to a domain sending each element `t i` of a family spanning the irrelevant ideal to a
unit, with injective maps `A_{(t i)} → L`. Two morphisms `Proj A ⟶ Z` over a separated `Z ⟶ S`
that agree on the points determined by `φ` on all the charts `D₊(t i)` are equal. -/
theorem hom_ext_of_point {Z S : Scheme.{u}} (s : Z ⟶ S) [IsSeparated s]
    {f g : Proj 𝒜 ⟶ Z} (hfg : f ≫ s = g ≫ s) {ι : Type*} (t : ι → A) {m : ι → ℕ}
    (ht : ∀ i, t i ∈ 𝒜 (m i)) (hm : ∀ i, 0 < m i)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range t))
    {L : Type u} [CommRing L] [IsDomain L] (φ : A →+* L) (hu : ∀ i, IsUnit (φ (t i)))
    (hinj : ∀ i, Function.Injective (awayEval 𝒜 φ (t i) (hu i)))
    (h : ∀ i, point 𝒜 φ (t i) (ht i) (hm i) (hu i) ≫ f = point 𝒜 φ (t i) (ht i) (hm i) (hu i) ≫ g) :
    f = g := by
  refine (Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 t ht hm hspan).openCover.hom_ext _ _
    (fun (i : ι) => ?_)
  show Proj.awayι 𝒜 (t i) (ht i) (hm i) ≫ f = Proj.awayι 𝒜 (t i) (ht i) (hm i) ≫ g
  have : IsDomain (Away 𝒜 (t i)) := (hinj i).isDomain _
  have : IsDominant (Spec.map (CommRingCat.ofHom (awayEval 𝒜 φ (t i) (hu i)))) :=
    isDominant_Spec_map_of_injective (CommRingCat.ofHom (awayEval 𝒜 φ (t i) (hu i))) (hinj i)
  refine ext_of_isDominant_of_isSeparated s ?_ (Spec.map (CommRingCat.ofHom
    (awayEval 𝒜 φ (t i) (hu i)))) ?_
  · simp only [Category.assoc, hfg]
  · simpa only [point, Category.assoc] using h i

section Glue

variable {Z : Scheme.{u}} {ι : Type*} (t : ι → A) {m : ι → ℕ} (ht : ∀ i, t i ∈ 𝒜 (m i))
  (hm : ∀ i, 0 < m i) (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range t))
  (c : ∀ i, Spec (.of (Away 𝒜 (t i))) ⟶ Z)
  (hc : ∀ i j, Spec.map (CommRingCat.ofHom (awayMap 𝒜 (ht j) (rfl : t i * t j = t i * t j))) ≫
      c i = Spec.map (CommRingCat.ofHom (awayMap 𝒜 (ht i) (mul_comm (t i) (t j)))) ≫ c j)

/-- **Gluing morphisms out of the standard charts.** Morphisms `Spec A_{(t i)} ⟶ Z` out of the
charts of a family spanning the irrelevant ideal, which agree on the charts `Spec A_{(t i t j)}`
of the overlaps, glue to a morphism `Proj A ⟶ Z`. -/
def glue : Proj 𝒜 ⟶ Z :=
  (Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 t ht hm hspan).openCover.glueMorphisms c
    (fun (i j : ι) => by
      change Limits.pullback.fst (Proj.awayι 𝒜 (t i) (ht i) (hm i))
          (Proj.awayι 𝒜 (t j) (ht j) (hm j)) ≫ c i =
        Limits.pullback.snd (Proj.awayι 𝒜 (t i) (ht i) (hm i))
          (Proj.awayι 𝒜 (t j) (ht j) (hm j)) ≫ c j
      rw [← cancel_epi (Proj.pullbackAwayιIso 𝒜 (ht i) (hm i) (ht j) (hm j) rfl).inv]
      change (Proj.pullbackAwayιIso 𝒜 (ht i) (hm i) (ht j) (hm j) rfl).inv ≫
          Limits.pullback.fst _ _ ≫ c i =
        (Proj.pullbackAwayιIso 𝒜 (ht i) (hm i) (ht j) (hm j) rfl).inv ≫
          Limits.pullback.snd _ _ ≫ c j
      rw [Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc]
      exact hc i j)

/-- The glued morphism restricts to the given morphism on each chart. -/
theorem awayι_glue (i : ι) :
    Proj.awayι 𝒜 (t i) (ht i) (hm i) ≫ glue 𝒜 t ht hm hspan c hc = c i :=
  (Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 t ht hm hspan).openCover.ι_glueMorphisms _ _ i

/-- **A point on a chart, followed by a glued morphism.** -/
theorem point_comp_glue (φ : A →+* B) (i : ι) (hu : IsUnit (φ (t i))) :
    point 𝒜 φ (t i) (ht i) (hm i) hu ≫ glue 𝒜 t ht hm hspan c hc =
      Spec.map (CommRingCat.ofHom (awayEval 𝒜 φ (t i) hu)) ≫ c i := by
  unfold point
  rw [Category.assoc, awayι_glue]

end Glue

end Stacks.ProjPoint

end
