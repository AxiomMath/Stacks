module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalCone

/-!
# Functoriality of the affine blowup algebra and of the chart `D₊(S)`

An affine blowup algebra `R[J/a] ⊆ R_a` is functorial in the triple `(R, J, a)`: a ring map
`φ : R ⟶ R'` with `φ(J) ⊆ J'` and `φ(a) = a'` induces `R[J/a] ⟶ R'[J'/a']`, the restriction of
the induced map of localizations `R_a ⟶ R'_{a'}`. This file records that map and specializes it to
the chart `D₊(S)` of the blowup at infinity, the affine blowup algebra `A[s][J/s]` with
`J = (I, s)`: a ring map `A ⟶ A'` carrying `I` into `I'` induces a map of charts
`A[s][J/s] ⟶ A'[s][J'/s]` which carries the ideal `(s)` into `(s)`.

## Main definitions

* `Stacks.Blowup.affineBlowupMap`: the map `R[J/a] ⟶ R'[J'/a']` induced by `φ`.
* `Stacks.Chow.infinityChartAlgebraMap`: the induced map of charts `A[s][J/s] ⟶ A'[s][J'/s]`.

## Main results

* `Stacks.Blowup.affineBlowupMap_algebraMap` and `Stacks.Chow.infinityChartAlgebraMap_algebraMap`:
  the maps extend `φ` and `Polynomial.map f`.
* `Stacks.Chow.map_infinityChartFibreIdeal_le`: the map of charts carries `(s)` into `(s)`.
-/

@[expose] public noncomputable section

namespace Stacks.Blowup

section AffineBlowupMap

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {J : Ideal R} {J' : Ideal R'}
  (hJ : J.map φ ≤ J') {a : R} {a' : R'} (ha : φ a = a')

include ha in
/-- If `φ a = a'`, then `φ` maps the powers of `a` into the powers of `a'`. -/
theorem powers_le_comap_powers :
    Submonoid.powers a ≤ (Submonoid.powers a').comap φ := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp [← ha]⟩

/-- The map of localizations `R_a ⟶ R'_{a'}` induced by `φ` with `φ a = a'`. -/
def awayMapOfEq : Localization.Away a →+* Localization.Away a' :=
  IsLocalization.map (Localization.Away a') φ (powers_le_comap_powers φ ha)

/-- The map `R_a ⟶ R'_{a'}` extends `φ`. -/
theorem awayMapOfEq_algebraMap (x : R) :
    awayMapOfEq φ ha (algebraMap R _ x) = algebraMap R' _ (φ x) :=
  IsLocalization.map_eq _ x

/-- The map `R_a ⟶ R'_{a'}` sends `x/aⁿ` to `φ(x)/a'ⁿ`. -/
theorem awayMapOfEq_mk (x : R) (n : ℕ) :
    awayMapOfEq φ ha (Localization.mk x (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)) =
      Localization.mk (φ x) (⟨a' ^ n, n, rfl⟩ : Submonoid.powers a') := by
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', awayMapOfEq,
    IsLocalization.map_mk']
  congr
  simp [← ha]

include hJ in
/-- If `φ(J) ⊆ J'`, the map `R_a ⟶ R'_{a'}` carries `R[J/a]` into `R'[J'/a']`. -/
theorem awayMapOfEq_mem_affineBlowup {z : Localization.Away a} (hz : z ∈ affineBlowup J a) :
    awayMapOfEq φ ha z ∈ affineBlowup J' a' := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have h := awayMapOfEq_mk φ ha x 1
    simp only [pow_one] at h
    rw [h]
    exact Algebra.subset_adjoin ⟨φ x, hJ (Ideal.mem_map_of_mem φ hx), rfl⟩
  | algebraMap r =>
    rw [awayMapOfEq_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- **Functoriality of the affine blowup algebra**: `φ : R ⟶ R'` with `φ(J) ⊆ J'` and
`φ(a) = a'` induces `R[J/a] ⟶ R'[J'/a']`. -/
def affineBlowupMap : affineBlowup J a →+* affineBlowup J' a' :=
  ((awayMapOfEq φ ha).comp (affineBlowup J a).val.toRingHom).codRestrict _
    fun z => awayMapOfEq_mem_affineBlowup φ hJ ha z.2

/-- The map `R[J/a] ⟶ R'[J'/a']` is the restriction of the map `R_a ⟶ R'_{a'}`. -/
theorem coe_affineBlowupMap (z : affineBlowup J a) :
    (affineBlowupMap φ hJ ha z : Localization.Away a') = awayMapOfEq φ ha z := rfl

/-- The map `R[J/a] ⟶ R'[J'/a']` extends `φ`. -/
theorem affineBlowupMap_algebraMap (x : R) :
    affineBlowupMap φ hJ ha (algebraMap R _ x) = algebraMap R' _ (φ x) :=
  Subtype.ext (awayMapOfEq_algebraMap φ ha x)

end AffineBlowupMap

end Stacks.Blowup

namespace Stacks.Chow

open Polynomial Stacks.Blowup

variable {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') {I : Ideal A} {I' : Ideal A'}
  (hI : I.map f ≤ I')

include hI in
/-- If `f(I) ⊆ I'`, then `Polynomial.map f` carries `J = (I, s)` into `J' = (I', s)`. -/
theorem map_infinityChartIdeal_le :
    (infinityChartIdeal I).map (mapRingHom f) ≤ infinityChartIdeal I' := by
  rw [infinityChartIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton,
    coe_mapRingHom, map_X, infinityChartIdeal]
  refine sup_le_sup ?_ le_rfl
  rw [show (mapRingHom f).comp C = C.comp f from RingHom.ext fun a => by simp, ← Ideal.map_map]
  exact Ideal.map_mono hI

/-- **The map of charts `D₊(S)` induced by `f : A ⟶ A'` with `f(I) ⊆ I'`**:
`A[s][J/s] ⟶ A'[s][J'/s]`. -/
def infinityChartAlgebraMap : infinityChartAlgebra I →+* infinityChartAlgebra I' :=
  affineBlowupMap (mapRingHom f) (map_infinityChartIdeal_le f hI)
    (show mapRingHom f Polynomial.X = Polynomial.X from map_X f)

/-- The map of charts `A[s][J/s] ⟶ A'[s][J'/s]` extends `Polynomial.map f`. -/
theorem infinityChartAlgebraMap_algebraMap (p : A[X]) :
    infinityChartAlgebraMap f hI (algebraMap _ _ p) = algebraMap _ _ (p.map f) :=
  affineBlowupMap_algebraMap _ _ _ p

/-- The map of charts sends `p/sⁿ` to `f(p)/sⁿ`, for `p ∈ Jⁿ`. -/
theorem infinityChartAlgebraMap_infinityChartMk (n : ℕ) (p : A[X])
    (hp : p ∈ infinityChartIdeal I ^ n) :
    infinityChartAlgebraMap f hI (infinityChartMk I n p hp) =
      infinityChartMk I' n (p.map f) (by
        have := Ideal.mem_map_of_mem (mapRingHom f) hp
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono (map_infinityChartIdeal_le f hI) n this) := by
  apply Subtype.ext
  rw [infinityChartAlgebraMap, coe_affineBlowupMap, infinityChartMk_val, infinityChartMk_val]
  exact awayMapOfEq_mk (mapRingHom f) (map_X f) p n

/-- The map of charts carries the ideal `(s)` into `(s)`. -/
theorem map_infinityChartFibreIdeal_le :
    (infinityChartFibreIdeal I).map (infinityChartAlgebraMap f hI) ≤
      infinityChartFibreIdeal I' := by
  rw [infinityChartFibreIdeal, Ideal.map_span, Set.image_singleton,
    infinityChartAlgebraMap_algebraMap, map_X, infinityChartFibreIdeal]

end Stacks.Chow

end
