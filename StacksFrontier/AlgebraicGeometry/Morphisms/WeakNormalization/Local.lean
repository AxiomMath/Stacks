module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring
public import StacksFrontier.AlgebraicGeometry.Properties.LocalRingProperty

/-!
# Seminormality and absolute weak normality are local properties

Seminormality and absolute weak normality of commutative rings are preserved by localization
away from an element and can be checked on a finite standard open covering.

## Main results

* `isSeminormalRing_propertyIsLocal` states that seminormality is a local property of rings.
* `isAbsolutelyWeaklyNormalRing_propertyIsLocal` states that absolute weak normality is a
  local property of rings.

## Implementation notes

Both results are expressed with `CommRing.PropertyIsLocal`. Uniqueness of the square and
cube root in a reduced ring is what makes the locally chosen roots agree on overlaps, so the
descent arguments go through a reducedness step; the absolute weak normality descent reuses
the seminormality one for its first component.

## References

* [Stacks Project, Tag 0EUM](https://stacks.math.columbia.edu/tag/0EUM)
-/

@[expose] public section

universe u

/-- In a reduced ring an element is determined by its square and its cube. -/
private theorem eq_of_sq_eq_sq_of_cube_eq_cube_of_isReduced
    {R : Type u} [CommRing R] [IsReduced R] {x y : R}
    (h₂ : x ^ 2 = y ^ 2) (h₃ : x ^ 3 = y ^ 3) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_pow_eq_zero (n := 3)
  linear_combination 4 * h₃ - 3 * (x + y) * h₂

/-- Seminormality passes to any ring realizing a localization away from an element. -/
private theorem localizationAway_preserves_seminormality
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) [IsLocalization.Away f S]
    (hR : IsSeminormalRing R) : IsSeminormalRing S := by
  intro x y hxy
  obtain ⟨nx, X₀, hx⟩ := IsLocalization.Away.surj f x
  obtain ⟨ny, Y₀, hy⟩ := IsLocalization.Away.surj f y
  let n := nx + ny
  let X := X₀ * f ^ (2 * n - nx)
  let Y := Y₀ * f ^ (3 * n - ny)
  have hx' : x * algebraMap R S (f ^ (2 * n)) = algebraMap R S X := by
    rw [show 2 * n = nx + (2 * n - nx) by omega, pow_add, map_mul]
    simp only [map_pow]
    rw [← mul_assoc, hx]
    simp [X]
  have hy' : y * algebraMap R S (f ^ (3 * n)) = algebraMap R S Y := by
    rw [show 3 * n = ny + (3 * n - ny) by omega, pow_add, map_mul]
    simp only [map_pow]
    rw [← mul_assoc, hy]
    simp [Y]
  have hmap : algebraMap R S (X ^ 3) = algebraMap R S (Y ^ 2) := by
    calc
      algebraMap R S (X ^ 3) = (x * algebraMap R S (f ^ (2 * n))) ^ 3 := by
        simpa only [map_pow] using congrArg (fun q : S => q ^ 3) hx'.symm
      _ = x ^ 3 * algebraMap R S (f ^ (6 * n)) := by
        simp only [mul_pow, map_pow, ← pow_mul]
        rw [show (2 * n) * 3 = 6 * n by omega]
      _ = y ^ 2 * algebraMap R S (f ^ (6 * n)) := by rw [hxy]
      _ = (y * algebraMap R S (f ^ (3 * n))) ^ 2 := by
        simp only [mul_pow, map_pow, ← pow_mul]
        rw [show (3 * n) * 2 = 6 * n by omega]
      _ = algebraMap R S (Y ^ 2) := by
        simpa only [map_pow] using congrArg (fun q : S => q ^ 2) hy'
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq f hmap
  have hbase : (f ^ (2 * k) * X) ^ 3 = (f ^ (3 * k) * Y) ^ 2 := by
    calc
      (f ^ (2 * k) * X) ^ 3 = f ^ (6 * k) * X ^ 3 := by
        rw [mul_pow, ← pow_mul, show (2 * k) * 3 = 6 * k by omega]
      _ = f ^ (5 * k) * (f ^ k * X ^ 3) := by rw [← mul_assoc, ← pow_add]; congr 2; omega
      _ = f ^ (5 * k) * (f ^ k * Y ^ 2) := congrArg _ hk
      _ = f ^ (6 * k) * Y ^ 2 := by rw [← mul_assoc, ← pow_add]; congr 2; omega
      _ = (f ^ (3 * k) * Y) ^ 2 := by
        simp only [mul_pow, ← pow_mul]
        rw [show (3 * k) * 2 = 6 * k by omega]
  obtain ⟨a, ha, _⟩ := hR _ _ hbase
  let uf : Sˣ := (IsLocalization.Away.algebraMap_isUnit f).unit
  let z : S := algebraMap R S a * ↑(uf⁻¹ ^ (n + k))
  have hzden : z * algebraMap R S (f ^ (n + k)) = algebraMap R S a := by
    change (algebraMap R S a * ↑(uf⁻¹ ^ (n + k))) * _ = _
    rw [map_pow]
    change (algebraMap R S a * ↑(uf⁻¹ ^ (n + k))) * ↑(uf ^ (n + k)) = _
    rw [mul_assoc]
    norm_cast
    simp
  have hzpow (m : ℕ) (q : S) (Q : R)
      (hq : q * algebraMap R S (f ^ (m * n)) = algebraMap R S Q)
      (hQ : f ^ (m * k) * Q = a ^ m) : q = z ^ m := by
    apply (IsUnit.mul_right_cancel ((IsLocalization.Away.algebraMap_isUnit f).pow (m * (n + k))))
    rw [← map_pow]
    calc
      q * algebraMap R S (f ^ (m * (n + k))) =
          algebraMap R S (f ^ (m * k)) * algebraMap R S Q := by
        rw [mul_add, pow_add, map_mul]
        calc
          q * (algebraMap R S (f ^ (m * n)) * algebraMap R S (f ^ (m * k))) =
              algebraMap R S (f ^ (m * k)) *
                (q * algebraMap R S (f ^ (m * n))) := by ring
          _ = _ := by rw [hq]
      _ = algebraMap R S (a ^ m) := by rw [← map_mul, hQ]
      _ = z ^ m * algebraMap R S (f ^ (m * (n + k))) := by
        calc
          algebraMap R S (a ^ m) = (z * algebraMap R S (f ^ (n + k))) ^ m := by
            simpa only [map_pow] using congrArg (fun q : S => q ^ m) hzden.symm
          _ = _ := by simp only [mul_pow, map_pow, ← pow_mul]; congr 2; ac_rfl
  have hz₂ : x = z ^ 2 := hzpow 2 x X hx' ha.1
  have hz₃ : y = z ^ 3 := hzpow 3 y Y hy' ha.2
  refine ⟨z, ⟨hz₂, hz₃⟩, ?_⟩
  intro z' hz'
  have : IsReduced R := seminormalRing_isReduced hR
  have : IsReduced S := isReduced_localizationPreserves (Submonoid.powers f) S inferInstance
  exact eq_of_sq_eq_sq_of_cube_eq_cube_of_isReduced (hz'.1.symm.trans hz₂)
    (hz'.2.symm.trans hz₃)

/-- Seminormality is a local property of commutative rings. -/
@[stacks 0EUM "seminormal_local_property"]
theorem isSeminormalRing_propertyIsLocal :
    CommRing.PropertyIsLocal
      (fun (R : Type u) [CommRing R] => IsSeminormalRing R) :=
  ⟨(fun f S _ _ _ h => localizationAway_preserves_seminormality (S := S) f h), by
    intro R _ ι _ f hspan hlocal x y hxy
    let s : Set R := Set.range f
    classical
    have hlocal_s (r : s) : IsSeminormalRing (Localization.Away r.1) := by
      rcases r with ⟨_, i, rfl⟩
      exact hlocal i
    have : ∀ r : s, IsReduced (Localization.Away r.1) := fun r =>
      seminormalRing_isReduced (hlocal_s r)
    have : IsReduced R := isReduced_of_injective
      (algebraMap R (∀ r : s, Localization.Away r.1))
      (Localization.algebraMap_injective_of_span_eq_top s (by simpa [s] using hspan))
    have hex (r : s) := (hlocal_s r).existsUnique_of_cube_eq_square
      (by simpa using congrArg (algebraMap R (Localization.Away r.1)) hxy)
    choose a ha _ using hex
    have hcompat (r t : s) :
        IsLocalization.Away.awayToAwayRight (P := Localization.Away (r * t : R))
            r.1 t (a r) =
          IsLocalization.Away.awayToAwayLeft t.1 r (a t) := by
      let T := Localization.Away (r * t : R)
      have : IsReduced T :=
        isReduced_localizationPreserves (Submonoid.powers (r * t : R)) T inferInstance
      apply eq_of_sq_eq_sq_of_cube_eq_cube_of_isReduced
      · rw [← map_pow, ← map_pow, ← (ha r).1, ← (ha t).1,
          IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
      · rw [← map_pow, ← map_pow, ← (ha r).2, ← (ha t).2,
          IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
    obtain ⟨z, hz, _⟩ :=
      Localization.existsUnique_algebraMap_eq_of_span_eq_top s (by simpa [s] using hspan) a hcompat
    have hz₂ : x = z ^ 2 := by
      apply Localization.algebraMap_injective_of_span_eq_top s (by simpa [s] using hspan)
      funext r
      simp [hz r, ha r]
    have hz₃ : y = z ^ 3 := by
      apply Localization.algebraMap_injective_of_span_eq_top s (by simpa [s] using hspan)
      funext r
      simp [hz r, ha r]
    refine ⟨z, ⟨hz₂, hz₃⟩, ?_⟩
    intro z' hz'
    exact eq_of_sq_eq_sq_of_cube_eq_cube_of_isReduced (hz'.1.symm.trans hz₂)
      (hz'.2.symm.trans hz₃)
  ⟩

/-- Equality of powers of two fractions yields a common witness clearing denominators. -/
private theorem exists_mul_eq_of_mk'_pow_eq_mk'_pow
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {M : Submonoid R} [IsLocalization M S]
    {a b : R} {sa sb : M} {m n : ℕ}
    (h : IsLocalization.mk' S a sa ^ m = IsLocalization.mk' S b sb ^ n) :
    ∃ q : M, (q : R) * ((sb : R) ^ n * a ^ m) = (q : R) * ((sa : R) ^ m * b ^ n) := by
  obtain ⟨q, hq⟩ := IsLocalization.exists_of_eq (M := M) (S := S) <| by
    simpa only [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_iff_eq] using h
  exact ⟨q, hq⟩

/-- Fractions agree once their cross-multiplied numerators agree after multiplying by `q`. -/
private theorem mk'_eq_mk'_of_mul_eq_mul
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {M : Submonoid R} [IsLocalization M S]
    {c c' : R} {s s' : M} (q : M) (h : c * (s' : R) * q = c' * (s : R) * q) :
    IsLocalization.mk' S c s = IsLocalization.mk' S c' s' := by
  apply IsLocalization.mk'_eq_iff_eq.mpr
  apply (IsLocalization.map_units S q).mul_left_cancel
  simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using (congr_arg (algebraMap R S) h)

/-- Absolute weak normality passes to any ring realizing a localization away from an
element. -/
private theorem localizationAway_preserves_absoluteWeakNormality
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) [IsLocalization.Away f S]
    (hR : IsAbsolutelyWeaklyNormalRing R) :
    IsAbsolutelyWeaklyNormalRing S := by
  constructor
  · intro x y hxy
    obtain ⟨a, sa, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
    obtain ⟨b, sb, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) y
    obtain ⟨q, hq⟩ := exists_mul_eq_of_mk'_pow_eq_mk'_pow hxy
    let w : Submonoid.powers f := q * sa * sb
    let A : R := a * q * sb
    let B : R := b * q * sa
    have hab : (A * (w : R)) ^ 3 = (B * (w : R) ^ 2) ^ 2 := by
      dsimp [A, B, w] at ⊢
      change (a * (q : R) * (sb : R) * ((q : R) * (sa : R) * (sb : R))) ^ 3 =
        (b * (q : R) * (sa : R) * ((q : R) * (sa : R) * (sb : R)) ^ 2) ^ 2
      linear_combination (q : R) ^ 5 * (sb : R) ^ 4 * (sa : R) ^ 3 * hq
    obtain ⟨c, hc, hc_unique⟩ := hR.1 _ _ hab
    let z := IsLocalization.mk' S c w
    have hz : IsLocalization.mk' S a sa = z ^ 2 ∧
        IsLocalization.mk' S b sb = z ^ 3 := by
      constructor
      · rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_iff_eq]
        dsimp [A, w]
        rw [← hc.1]
        dsimp [A, w]
        apply congr_arg (algebraMap R S)
        change ((q : R) * (sa : R) * (sb : R)) ^ 2 * a =
          (sa : R) * ((a * (q : R) * (sb : R)) * ((q : R) * (sa : R) * (sb : R)))
        ring
      · rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_iff_eq]
        dsimp [B, w]
        rw [← hc.2]
        dsimp [B, w]
        apply congr_arg (algebraMap R S)
        change ((q : R) * (sa : R) * (sb : R)) ^ 3 * b =
          (sb : R) * ((b * (q : R) * (sa : R)) * ((q : R) * (sa : R) * (sb : R)) ^ 2)
        ring
    refine ⟨z, hz, ?_⟩
    · intro z' hz'
      obtain ⟨c', sc, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) z'
      have hsquare : IsLocalization.mk' S c w ^ 2 = IsLocalization.mk' S c' sc ^ 2 :=
        hz.1.symm.trans hz'.1
      have hcube : IsLocalization.mk' S c w ^ 3 = IsLocalization.mk' S c' sc ^ 3 :=
        hz.2.symm.trans hz'.2
      obtain ⟨q₂, hq₂⟩ := exists_mul_eq_of_mk'_pow_eq_mk'_pow hsquare
      obtain ⟨q₃, hq₃⟩ := exists_mul_eq_of_mk'_pow_eq_mk'_pow hcube
      let C : R := c * (sc : R)
      let D : R := c' * (w : R)
      let q : Submonoid.powers f := q₂ * q₃
      have hCD₂ : (C * (q : R)) ^ 2 = (D * (q : R)) ^ 2 := by
        dsimp [C, D, q]
        change (c * (sc : R) * ((q₂ : R) * (q₃ : R))) ^ 2 =
          (c' * (w : R) * ((q₂ : R) * (q₃ : R))) ^ 2
        linear_combination (q₂ : R) * (q₃ : R) ^ 2 * hq₂
      have hCD₃ : (C * (q : R)) ^ 3 = (D * (q : R)) ^ 3 := by
        dsimp [C, D, q]
        change (c * (sc : R) * ((q₂ : R) * (q₃ : R))) ^ 3 =
          (c' * (w : R) * ((q₂ : R) * (q₃ : R))) ^ 3
        linear_combination (q₂ : R) ^ 3 * (q₃ : R) ^ 2 * hq₃
      have hpow : ((C * (q : R)) ^ 2) ^ 3 = ((C * (q : R)) ^ 3) ^ 2 := by ring
      have hCD : C * (q : R) = D * (q : R) :=
        (hR.1 _ _ hpow).unique ⟨rfl, rfl⟩ ⟨hCD₂, hCD₃⟩
      exact mk'_eq_mk'_of_mul_eq_mul q hCD.symm
  · intro p hp x y hxy
    have pow_pred (t : R) : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + 1) := by congr 1; have := hp.pos; omega
        _ = t ^ (p - 1) * t := by rw [pow_succ']; ring
    obtain ⟨a, sa, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
    obtain ⟨b, sb, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) y
    have hfrac : IsLocalization.mk' S ((p : R) ^ p * a) sa =
        IsLocalization.mk' S (b ^ p) (sb ^ p) := by
      calc
        IsLocalization.mk' S ((p : R) ^ p * a) sa =
            algebraMap R S ((p : R) ^ p) * IsLocalization.mk' S a sa := by
          rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]
        _ = (p : S) ^ p * IsLocalization.mk' S a sa := by simp
        _ = IsLocalization.mk' S b sb ^ p := hxy
        _ = IsLocalization.mk' S (b ^ p) (sb ^ p) := by
          rw [← IsLocalization.mk'_pow]
    obtain ⟨q₀, hq₀⟩ := IsLocalization.exists_of_eq (M := .powers f) (S := S) <| by
      simpa only [IsLocalization.mk'_eq_iff_eq] using hfrac
    let w : Submonoid.powers f := q₀ * sa * sb
    let A : R := a * q₀ * sb
    let B : R := b * q₀ * sa
    have hab : (p : R) ^ p * (A * (w : R) ^ (p - 1)) = B ^ p := by
      dsimp [A, B, w] at ⊢
      change (q₀ : R) * ((sb : R) ^ p * ((p : R) ^ p * a)) =
        (q₀ : R) * ((sa : R) * b ^ p) at hq₀
      simp only [mul_pow]
      rw [pow_pred (q₀ : R), pow_pred (sa : R)]
      rw [pow_pred (sb : R)] at hq₀
      linear_combination (q₀ : R) ^ (p - 1) * (sa : R) ^ (p - 1) * hq₀
    obtain ⟨c, hc, hc_unique⟩ := hR.2 p hp _ _ hab
    let z := IsLocalization.mk' S c w
    have hz : IsLocalization.mk' S a sa = z ^ p ∧
        IsLocalization.mk' S b sb = (p : S) * z := by
      constructor
      · rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_iff_eq]
        rw [← hc.1]
        dsimp [A, w]
        apply congr_arg (algebraMap R S)
        change ((q₀ : R) * (sa : R) * (sb : R)) ^ p * a =
          (sa : R) * ((a * (q₀ : R) * (sb : R)) *
            ((q₀ : R) * (sa : R) * (sb : R)) ^ (p - 1))
        simp only [mul_pow]
        rw [pow_pred (q₀ : R), pow_pred (sa : R), pow_pred (sb : R)]
        ring
      · apply IsLocalization.mk'_eq_iff_eq_mul.mpr
        dsimp [z]
        apply (IsLocalization.map_units S w).mul_right_cancel
        have hbden : b * (w : R) = (p : R) * c * (sb : R) := by
          dsimp [B, w]
          rw [← hc.2]
          ring
        have hmk : algebraMap R S c = IsLocalization.mk' S c w * algebraMap R S (w : R) :=
          IsLocalization.mk'_eq_iff_eq_mul.mp rfl
        calc
          algebraMap R S b * algebraMap R S (w : R) = algebraMap R S (b * (w : R)) := by
            rw [map_mul]
          _ = algebraMap R S ((p : R) * c * (sb : R)) := congrArg _ hbden
          _ = (p : S) * algebraMap R S c * algebraMap R S (sb : R) := by simp [map_mul]
          _ = ((p : S) * IsLocalization.mk' S c w * algebraMap R S (sb : R)) *
              algebraMap R S (w : R) := by rw [hmk]; ring
    refine ⟨z, hz, ?_⟩
    intro z' hz'
    obtain ⟨c', sc, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) z'
    have hpowers : IsLocalization.mk' S c w ^ p = IsLocalization.mk' S c' sc ^ p :=
      hz.1.symm.trans hz'.1
    have hmultiple : (p : S) * IsLocalization.mk' S c w =
        (p : S) * IsLocalization.mk' S c' sc := hz.2.symm.trans hz'.2
    obtain ⟨q₁, hq₁⟩ := exists_mul_eq_of_mk'_pow_eq_mk'_pow hpowers
    have hfracMul : IsLocalization.mk' S ((p : R) * c) w =
        IsLocalization.mk' S ((p : R) * c') sc := by
      calc
        IsLocalization.mk' S ((p : R) * c) w =
            (p : S) * IsLocalization.mk' S c w := by
          rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]
          simp
        _ = (p : S) * IsLocalization.mk' S c' sc := hmultiple
        _ = IsLocalization.mk' S ((p : R) * c') sc := by
          rw [← IsLocalization.mul_mk'_eq_mk'_of_mul]
          simp
    obtain ⟨q₂, hq₂⟩ := IsLocalization.exists_of_eq (M := .powers f) (S := S) <| by
      simpa only [IsLocalization.mk'_eq_iff_eq] using hfracMul
    let C : R := c * (sc : R)
    let D : R := c' * (w : R)
    let q : Submonoid.powers f := q₁ * q₂
    have hCDp : (C * (q : R)) ^ p = (D * (q : R)) ^ p := by
      dsimp [C, D, q]
      rw [pow_pred (sc : R), pow_pred (w : R)] at hq₁
      simp only [mul_pow]
      rw [pow_pred (q₁ : R), pow_pred (sc : R), pow_pred (w : R)]
      linear_combination (q₁ : R) ^ (p - 1) * (q₂ : R) ^ p * hq₁
    have hCDmul : (p : R) * (C * (q : R)) = (p : R) * (D * (q : R)) := by
      dsimp [C, D, q]
      change (q₂ : R) * ((sc : R) * ((p : R) * c)) =
        (q₂ : R) * ((w : R) * ((p : R) * c')) at hq₂
      linear_combination (q₁ : R) * hq₂
    have hroot : (p : R) ^ p * (C * (q : R)) ^ p =
        ((p : R) * (C * (q : R))) ^ p := by ring
    have hCD : C * (q : R) = D * (q : R) :=
      (hR.2 p hp _ _ hroot).unique ⟨rfl, rfl⟩ ⟨hCDp, hCDmul⟩
    exact mk'_eq_mk'_of_mul_eq_mul q hCD.symm

/-- Absolute weak normality descends from a finite standard open covering. -/
private theorem of_localization_span_absoluteWeakNormality
    {R : Type u} [CommRing R] {ι : Type u} [Finite ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, IsAbsolutelyWeaklyNormalRing (Localization.Away (f i))) :
    IsAbsolutelyWeaklyNormalRing R := by
  constructor
  · exact isSeminormalRing_propertyIsLocal.ofLocalizationSpan
      f hf (fun i => (h i).isSeminormalRing)
  · intro p hp x y hxy
    let s : Set R := Set.range f
    classical
    have hlocal_s (r : s) :
        IsAbsolutelyWeaklyNormalRing (Localization.Away r.1) := by
      rcases r with ⟨_, i, rfl⟩
      exact h i
    have hex (r : s) := (hlocal_s r).2 p hp _ _
      (by simpa using congrArg (algebraMap R (Localization.Away r.1)) hxy)
    choose a ha hunique using hex
    have hcompat (r t : s) :
        IsLocalization.Away.awayToAwayRight (P := Localization.Away (r * t : R))
            r.1 t (a r) =
          IsLocalization.Away.awayToAwayLeft t.1 r (a t) := by
      let P := Localization.Away (r * t : R)
      let Rr := Localization.Away r.1
      let Rt := Localization.Away t.1
      let T := Localization.Away (algebraMap R Rr t.1)
      have : IsLocalization.Away (r.1 * t.1) T :=
        IsLocalization.Away.mul' Rr T r.1 t.1
      let e : P ≃ₐ[R] T := IsLocalization.algEquiv (Submonoid.powers (r.1 * t.1)) P T
      have hT : IsAbsolutelyWeaklyNormalRing T :=
        localizationAway_preserves_absoluteWeakNormality (algebraMap R Rr t.1) (hlocal_s r)
      have hxyT : (p : T) ^ p * algebraMap R T x = (algebraMap R T y) ^ p := by
        simpa only [map_natCast, map_pow, map_mul] using congrArg (algebraMap R T) hxy
      have hmap {S' : Type u} [CommRing S'] [Algebra R S'] (g : S' →+* T)
          (hg : ∀ q, g (algebraMap R S' q) = algebraMap R T q) (b : S')
          (hb : algebraMap R S' x = b ^ p ∧ algebraMap R S' y = (p : S') * b) :
          algebraMap R T x = g b ^ p ∧ algebraMap R T y = (p : T) * g b := by
        rw [← hg, ← hg, hb.1, hb.2]
        simp
      have hroot := (hT.2 p hp _ _ hxyT).unique
        (hmap _ (IsLocalization.Away.awayToAwayRight_eq (S := Rr) (P := T) r.1 t) _ (ha r))
        (hmap _ (IsLocalization.Away.awayToAwayLeft_eq (S := Rt) (P := T) t.1 r) _ (ha t))
      have hrightMap :
          (e.toRingEquiv.toRingHom).comp
              (IsLocalization.Away.awayToAwayRight (S := Rr) (P := P) r.1 t) =
            (IsLocalization.Away.awayToAwayRight (S := Rr) (P := T) r.1 t) := by
        apply IsLocalization.ringHom_ext (Submonoid.powers r.1)
        ext q
        simp [e, IsLocalization.Away.awayToAwayRight_eq]
      have hleftMap :
          (e.toRingEquiv.toRingHom).comp
              (IsLocalization.Away.awayToAwayLeft (S := Rt) (P := P) t.1 r) =
            (IsLocalization.Away.awayToAwayLeft (S := Rt) (P := T) t.1 r) := by
        apply IsLocalization.ringHom_ext (Submonoid.powers t.1)
        ext q
        simp [e, IsLocalization.Away.awayToAwayLeft_eq]
      apply e.injective
      exact (congrArg (fun g : Localization.Away r.1 →+* T => g (a r)) hrightMap).trans
        (hroot.trans (congrArg (fun g : Localization.Away t.1 →+* T => g (a t)) hleftMap).symm)
    obtain ⟨z, hz, _hzuniq⟩ :=
      Localization.existsUnique_algebraMap_eq_of_span_eq_top s (by simpa [s] using hf) a hcompat
    have hzx : x = z ^ p := by
      apply Localization.algebraMap_injective_of_span_eq_top s (by simpa [s] using hf)
      funext r
      simpa [hz r] using (ha r).1
    have hzy : y = (p : R) * z := by
      apply Localization.algebraMap_injective_of_span_eq_top s (by simpa [s] using hf)
      funext r
      simpa [hz r] using (ha r).2
    refine ⟨z, ⟨hzx, hzy⟩, ?_⟩
    intro z' hz'
    apply Localization.algebraMap_injective_of_span_eq_top s (by simpa [s] using hf)
    funext r
    have hmap {u v : R} (h : u = v) := congrArg (algebraMap R (Localization.Away r.1)) h
    exact (hunique r (algebraMap R (Localization.Away r.1) z')
      ⟨by simpa only [map_pow] using hmap hz'.1,
        by simpa only [map_mul, map_natCast] using hmap hz'.2⟩).trans (hz r).symm

/-- Being an absolutely weakly normal commutative ring is a local property of rings. -/
@[stacks 0EUM "absolutely_weakly_normal_local_property"]
theorem isAbsolutelyWeaklyNormalRing_propertyIsLocal :
    CommRing.PropertyIsLocal
      (fun (R : Type u) [CommRing R] => IsAbsolutelyWeaklyNormalRing R) :=
  ⟨fun f _S _ _ _ h ↦ localizationAway_preserves_absoluteWeakNormality f h,
    of_localization_span_absoluteWeakNormality⟩

end
