module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Algebra
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.SpreadingOut
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Spreading out a relative quasi-regular sequence

Let `A → B` be flat and of finite presentation, let `f₁, …, f_r ∈ B` be a quasi-regular sequence
whose quotient `B/(f₁, …, f_r)` is flat over `A`, and let `q` be a prime of `B` containing every
`fᵢ`.  Then there is a `g ∉ q` such that `f₁, …, f_r` is a weakly regular sequence in `B_g`.

## Main results

* `Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime`: a
  sequence regular in `B_q` whose partial quotients `B_q/(f₁, …, f_k)` are flat over `A` is weakly
  regular in `B_g` for some `g ∉ q`.
* `Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_away`: the same for a
  quasi-regular sequence with flat quotient.

## References

* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
-/

@[expose] public section

namespace Stacks.RingTheory.SpreadingOut

open RingTheory.Sequence

section Elementwise

variable {B : Type*} [CommRing B]

/-- For a localization `L` of `B` at a submonoid `U` and an ideal `I` of `B`, the image of `x ∈ B`
in `L/IL` vanishes exactly when some `u ∈ U` carries `x` into `I`. -/
theorem algebraMap_quotientMap_eq_zero_iff (I : Ideal B) (U : Submonoid B)
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization U L] (x : B) :
    algebraMap B (L ⧸ I.map (algebraMap B L)) x = 0 ↔ ∃ u ∈ U, u * x ∈ I := by
  have htower : IsScalarTower B (B ⧸ I) (L ⧸ I.map (algebraMap B L)) :=
    .of_algebraMap_eq fun _ => rfl
  have hquot : ∀ y : B, algebraMap B (B ⧸ I) y = 0 ↔ y ∈ I := fun y =>
    Ideal.Quotient.eq_zero_iff_mem
  rw [IsScalarTower.algebraMap_apply B (B ⧸ I) (L ⧸ I.map (algebraMap B L)),
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid (B ⧸ I) U)]
  constructor
  · rintro ⟨⟨m, u, hu, rfl⟩, hm⟩
    exact ⟨u, hu, (hquot (u * x)).mp (by rwa [map_mul])⟩
  · rintro ⟨u, hu, hux⟩
    refine ⟨⟨algebraMap B (B ⧸ I) u, u, hu, rfl⟩, ?_⟩
    show algebraMap B (B ⧸ I) u * algebraMap B (B ⧸ I) x = 0
    rwa [← map_mul, hquot]

/-- Every element of `L/IL` becomes the image of an element of `B` after multiplication by the
image of an element of `U`. -/
theorem exists_mul_algebraMap_eq_algebraMap (I : Ideal B) (U : Submonoid B)
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization U L]
    (z : L ⧸ I.map (algebraMap B L)) :
    ∃ (x : B) (u : B), u ∈ U ∧
      z * algebraMap B (L ⧸ I.map (algebraMap B L)) u =
        algebraMap B (L ⧸ I.map (algebraMap B L)) x := by
  have htower : IsScalarTower B (B ⧸ I) (L ⧸ I.map (algebraMap B L)) :=
    .of_algebraMap_eq fun _ => rfl
  obtain ⟨⟨y, ⟨m, u, hu, rfl⟩⟩, hy⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid (B ⧸ I) U) z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨x, u, hu, ?_⟩
  rwa [IsScalarTower.algebraMap_apply B (B ⧸ I) (L ⧸ I.map (algebraMap B L)) u,
    IsScalarTower.algebraMap_apply B (B ⧸ I) (L ⧸ I.map (algebraMap B L)) x]

/-- The image in `L/IL` of an element of `U` is a unit. -/
theorem isUnit_algebraMap_quotientMap (I : Ideal B) (U : Submonoid B)
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization U L] {u : B} (hu : u ∈ U) :
    IsUnit (algebraMap B (L ⧸ I.map (algebraMap B L)) u) := by
  have htower : IsScalarTower B L (L ⧸ I.map (algebraMap B L)) :=
    .of_algebraMap_eq fun _ => rfl
  rw [IsScalarTower.algebraMap_apply B L (L ⧸ I.map (algebraMap B L))]
  exact (IsLocalization.map_units L (⟨u, hu⟩ : U)).map _

/-- The image of `h` is a nonzerodivisor on `L/IL` exactly when, for every `x ∈ B`, an element
of `U` carrying `hx` into `I` forces an element of `U` carrying `x` into `I`. -/
theorem isSMulRegular_quotientMap_iff (I : Ideal B) (U : Submonoid B)
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization U L] (h : B) :
    IsSMulRegular (L ⧸ I.map (algebraMap B L))
        (algebraMap B (L ⧸ I.map (algebraMap B L)) h) ↔
      ∀ x : B, (∃ u ∈ U, u * (h * x) ∈ I) → ∃ u ∈ U, u * x ∈ I := by
  constructor
  · intro hreg x hx
    rw [← algebraMap_quotientMap_eq_zero_iff I U L x]
    refine hreg (a₂ := 0) ?_
    show algebraMap B (L ⧸ I.map (algebraMap B L)) h •
        algebraMap B (L ⧸ I.map (algebraMap B L)) x =
      algebraMap B (L ⧸ I.map (algebraMap B L)) h • (0 : L ⧸ I.map (algebraMap B L))
    rw [smul_zero, smul_eq_mul, ← map_mul]
    exact (algebraMap_quotientMap_eq_zero_iff I U L (h * x)).mpr hx
  · intro hcond
    have key : ∀ z : L ⧸ I.map (algebraMap B L),
        algebraMap B (L ⧸ I.map (algebraMap B L)) h * z = 0 → z = 0 := by
      intro z hz
      obtain ⟨x, u, hu, hxu⟩ := exists_mul_algebraMap_eq_algebraMap I U L z
      have hzero : algebraMap B (L ⧸ I.map (algebraMap B L)) (h * x) = 0 := by
        rw [map_mul, ← hxu, ← mul_assoc, hz, zero_mul]
      have hx := hcond x ((algebraMap_quotientMap_eq_zero_iff I U L (h * x)).mp hzero)
      have hxz : z * algebraMap B (L ⧸ I.map (algebraMap B L)) u = 0 := by
        rw [hxu]
        exact (algebraMap_quotientMap_eq_zero_iff I U L x).mpr hx
      exact (isUnit_algebraMap_quotientMap I U L hu).mul_left_cancel
        (by rw [mul_comm, hxz, mul_zero])
    exact fun z₁ z₂ hz => sub_eq_zero.mp (key _ (by rw [mul_sub]; exact sub_eq_zero.mpr hz))

end Elementwise

section Spreading

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The ideal generated by the first `k` members of a finite family. -/
abbrev partialIdeal {r : ℕ} (f : Fin r → B) (k : ℕ) : Ideal B :=
  Ideal.ofList ((List.ofFn f).take k)

/-- Taking the whole family back gives the ideal it generates. -/
lemma partialIdeal_length {r : ℕ} (f : Fin r → B) :
    partialIdeal f r = Ideal.span (Set.range f) := by
  show Ideal.ofList ((List.ofFn f).take r) = _
  rw [List.take_of_length_le (by simp)]
  exact congrArg Ideal.span (Set.ext fun _ => List.mem_ofFn.trans Set.mem_range.symm)

private lemma partialIdeal_fg {r : ℕ} (f : Fin r → B) (k : ℕ) : (partialIdeal f k).FG :=
  Submodule.fg_span (List.finite_toSet _)

private lemma partialIdeal_le {r : ℕ} (f : Fin r → B) (k : ℕ) {q : Ideal B}
    (hq : ∀ i, f i ∈ q) : partialIdeal f k ≤ q := by
  refine Ideal.span_le.mpr fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
  exact hq i

private lemma partialIdeal_succ {r : ℕ} (f : Fin r → B) (k : ℕ) (hk : k < r) :
    partialIdeal f (k + 1) = partialIdeal f k ⊔ Ideal.span {f ⟨k, hk⟩} := by
  have hlen : k < (List.ofFn f).length := by simpa using hk
  have hlist : (List.ofFn f).take (k + 1) =
      (List.ofFn f).take k ++ [f ⟨k, hk⟩] := by
    rw [List.take_succ_eq_append_getElem hlen]
    simp
  show Ideal.ofList ((List.ofFn f).take (k + 1)) = _
  rw [hlist, Ideal.ofList_append, Ideal.ofList_singleton]

/-- The ideal generated by the first `k` members of a family maps to the ideal generated by the
first `k` members of the image family. -/
lemma map_partialIdeal {r : ℕ} (f : Fin r → B) (k : ℕ)
    (L : Type*) [CommRing L] [Algebra B L] :
    (partialIdeal f k).map (algebraMap B L) =
      Ideal.ofList ((List.ofFn fun i => algebraMap B L (f i)).take k) := by
  show Ideal.map (algebraMap B L) (Ideal.ofList ((List.ofFn f).take k)) = _
  rw [Ideal.map_ofList]
  congr 1
  rw [List.map_take, List.map_ofFn]
  rfl

/-- Regularity of the `k`-th image of a family modulo the previous ones, in the form used for
`partialIdeal`. -/
private lemma isSMulRegular_ofList_take_iff {r : ℕ} (f : Fin r → B) (k : Fin r)
    (L : Type*) [CommRing L] [Algebra B L]
    (hk : k.val < (List.ofFn fun j => algebraMap B L (f j)).length) :
    IsSMulRegular (L ⧸ (Ideal.ofList ((List.ofFn fun j => algebraMap B L (f j)).take k.val) •
        (⊤ : Submodule L L))) (List.ofFn fun j => algebraMap B L (f j))[k.val] ↔
      IsSMulRegular (L ⧸ (partialIdeal f k.val).map (algebraMap B L)) (algebraMap B L (f k)) := by
  have hsm : (Ideal.ofList ((List.ofFn fun j => algebraMap B L (f j)).take k.val) •
      (⊤ : Submodule L L)) = (partialIdeal f k.val).map (algebraMap B L) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, map_partialIdeal]
  have hidx : (List.ofFn fun j => algebraMap B L (f j))[k.val]'hk = algebraMap B L (f k) := by
    simp
  rw [hsm, hidx]

/-- Let `A → B` be of finite presentation, let `I` be a finitely generated ideal of `B` and let
`h ∈ B`. If `B_{g₁}/IB_{g₁}` and `B_{g₁}/(I + hB)B_{g₁}` are flat over `A`, and if `h` is a
nonzerodivisor modulo `I` after localizing at `q`, then a single `b ∉ q` carries into `I` — up to a
power of `g₁` — every multiple of `h` that a power of `g₁` already carries there. -/
private lemma exists_notMem_forall_mul_mem_of_flat
    [Algebra.FinitePresentation A B] (q : Ideal B) [q.IsPrime]
    (I : Ideal B) (hIfg : I.FG) (h g₁ : B) (hg₁ : g₁ ∉ q)
    (hflat' : Module.Flat A (Localization.Away g₁ ⧸
      (I ⊔ Ideal.span {h}).map (algebraMap B (Localization.Away g₁))))
    (hstalk : ∀ x : B, (∃ t ∈ q.primeCompl, t * (h * x) ∈ I) → ∃ t ∈ q.primeCompl, t * x ∈ I) :
    ∃ b ∈ q.primeCompl, ∀ x : B,
      (∃ u ∈ Submonoid.powers g₁, u * (h * x) ∈ I) →
        ∃ u ∈ Submonoid.powers g₁, u * (b * x) ∈ I := by
  classical
  have hB'fp : Algebra.FinitePresentation A (Localization.Away g₁) :=
    Algebra.FinitePresentation.trans A B (Localization.Away g₁)
  have hCfp : Algebra.FinitePresentation A
      (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) :=
    Algebra.FinitePresentation.quotient (hIfg.map _)
  have hsup : (I ⊔ Ideal.span {h}).map (algebraMap B (Localization.Away g₁)) =
      I.map (algebraMap B (Localization.Away g₁)) ⊔
        Ideal.span {algebraMap B (Localization.Away g₁) h} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmap : Ideal.span {algebraMap B
        (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) h} =
      (Ideal.span {algebraMap B (Localization.Away g₁) h}).map
        (Ideal.Quotient.mkₐ A (I.map (algebraMap B (Localization.Away g₁)))) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hCquot : Module.Flat A
      ((Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) ⧸
        Ideal.span {algebraMap B
          (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) h}) := by
    refine Module.Flat.of_linearEquiv
      (M := Localization.Away g₁ ⧸
        (I ⊔ Ideal.span {h}).map (algebraMap B (Localization.Away g₁)))
      (AlgEquiv.toLinearEquiv ?_)
    exact ((Ideal.quotientEquivAlgOfEq A hmap).trans
      (DoubleQuot.quotQuotEquivQuotSupₐ A _ _)).trans
      (Ideal.quotientEquivAlgOfEq A hsup.symm)
  have hker : ∀ y, y ∈ LinearMap.ker (LinearMap.lsmul
      (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁)))
      (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁)))
      (algebraMap B (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) h)) ↔
      algebraMap B (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁)))
        h * y = 0 := fun y => by
    simp [LinearMap.mem_ker, smul_eq_mul]
  obtain ⟨s, hs⟩ := fg_ker_lsmul_of_flat_quotient (A := A)
    (algebraMap B (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) h) hCquot
  have hgen : ∀ y ∈ s, ∃ t ∈ q.primeCompl,
      algebraMap B (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) t * y
        = 0 := by
    intro y hy
    have hyker : algebraMap B
        (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) h * y = 0 := by
      exact (hker y).mp (hs ▸ Submodule.subset_span hy)
    obtain ⟨x, u, hu, hxu⟩ := exists_mul_algebraMap_eq_algebraMap I (Submonoid.powers g₁)
      (Localization.Away g₁) y
    have hzero : algebraMap B
        (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) (h * x) = 0 := by
      rw [map_mul, ← hxu, ← mul_assoc, hyker, zero_mul]
    obtain ⟨u', hu', hmem'⟩ := (algebraMap_quotientMap_eq_zero_iff I (Submonoid.powers g₁)
      (Localization.Away g₁) (h * x)).mp hzero
    have hu'q : u' ∉ q := by
      obtain ⟨n, rfl⟩ := hu'
      exact fun hmem'' => hg₁ (‹q.IsPrime›.mem_of_pow_mem n hmem'')
    obtain ⟨t, htq, htmem⟩ := hstalk (u' * x)
      ⟨1, one_mem _, by rw [one_mul, show h * (u' * x) = u' * (h * x) by ring]; exact hmem'⟩
    refine ⟨t * u', q.primeCompl.mul_mem htq hu'q, ?_⟩
    have h0 : algebraMap B
        (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁)))
        (t * u' * x) = 0 :=
      (algebraMap_quotientMap_eq_zero_iff I (Submonoid.powers g₁) (Localization.Away g₁)
        (t * u' * x)).mpr
        ⟨1, one_mem _, by rw [one_mul, show t * u' * x = t * (u' * x) by ring]; exact htmem⟩
    refine (isUnit_algebraMap_quotientMap I (Submonoid.powers g₁)
      (Localization.Away g₁) hu).mul_left_cancel ?_
    rwa [mul_zero, mul_comm (algebraMap B _ u), mul_assoc, hxu, ← map_mul]
  choose! t ht ht0 using hgen
  refine ⟨∏ y ∈ s, t y, q.primeCompl.prod_mem fun y hy => ht y hy, fun x hx => ?_⟩
  have hxker := (hker _).mpr (by
    rw [← map_mul]
    exact (algebraMap_quotientMap_eq_zero_iff I (Submonoid.powers g₁) (Localization.Away g₁)
      (h * x)).mpr hx)
  rw [← hs] at hxker
  have hkill : algebraMap B
      (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) (∏ y ∈ s, t y) *
      algebraMap B
        (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁))) x = 0 := by
    refine Submodule.span_induction (p := fun w _ => algebraMap B
      (Localization.Away g₁ ⧸ I.map (algebraMap B (Localization.Away g₁)))
        (∏ y ∈ s, t y) * w = 0) ?_ (by simp) ?_ ?_ hxker
    · intro y hy
      have hys : y ∈ s := Finset.mem_coe.mp hy
      rw [show (∏ z ∈ s, t z) = (∏ z ∈ s.erase y, t z) * t y from
        (Finset.prod_erase_mul _ _ hys).symm, map_mul, mul_assoc, ht0 y hys, mul_zero]
    · intro w₁ w₂ _ _ h₁ h₂; rw [mul_add, h₁, h₂, add_zero]
    · intro c w _ hcw; rw [smul_eq_mul, mul_comm c w, ← mul_assoc, hcw, zero_mul]
  rw [← map_mul] at hkill
  exact (algebraMap_quotientMap_eq_zero_iff I (Submonoid.powers g₁)
    (Localization.Away g₁) _).mp hkill

/-- Let `A → B` be flat and of finite presentation, let `q` be a prime of `B` and let
`f₁, …, f_r ∈ q`.  If `f₁, …, f_r` is a regular sequence in the localization `B_q` and every
partial quotient `B_q/(f₁, …, f_k)` is flat over `A`, then `f₁, …, f_r` is a weakly regular
sequence in `B_g` for some `g ∉ q`. -/
@[ega "IV 11.3.8" "(a), special case"]
theorem exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] {r : ℕ} (f : Fin r → B) (hq : ∀ i, f i ∈ q)
    (hregT : IsRegular (Localization.AtPrime q)
      (List.ofFn fun i => algebraMap B (Localization.AtPrime q) (f i)))
    (hflatT : ∀ k : ℕ, Module.Flat A (Localization.AtPrime q ⧸
      Ideal.ofList ((List.ofFn fun j => algebraMap B (Localization.AtPrime q) (f j)).take k))) :
    ∃ g ∉ q, IsWeaklyRegular (Localization.Away g)
      (List.ofFn fun i => algebraMap B (Localization.Away g) (f i)) := by
  classical
  have hstalk : ∀ k : Fin r, ∀ x : B,
      (∃ t ∈ q.primeCompl, t * (f k * x) ∈ partialIdeal f k.val) →
        ∃ t ∈ q.primeCompl, t * x ∈ partialIdeal f k.val := by
    intro k
    refine (isSMulRegular_quotientMap_iff (partialIdeal f k.val) q.primeCompl
      (Localization.AtPrime q) (f k)).mp ?_
    have hklt : k.val < (List.ofFn fun j => algebraMap B (Localization.AtPrime q) (f j)).length :=
      by simp
    exact (isSMulRegular_ofList_take_iff f k _ hklt).mp (hregT.regular_mod_prev k.val hklt)
  have hflats : ∀ k ∈ Finset.range (r + 1), Module.Flat A
      (Localization.AtPrime q ⧸
        (partialIdeal f k).map (algebraMap B (Localization.AtPrime q))) := by
    intro k _
    rw [map_partialIdeal]
    exact hflatT k
  obtain ⟨g₁, hg₁, hg₁flat⟩ := exists_notMem_forall_flat_quotient_away_of_fg q
    (Finset.range (r + 1)) (partialIdeal f) (fun k _ => partialIdeal_fg f k)
    (fun k _ => partialIdeal_le f k hq) hflats
  have hkill : ∀ k : Fin r, ∃ b ∈ q.primeCompl, ∀ x : B,
      (∃ u ∈ Submonoid.powers g₁, u * (f k * x) ∈ partialIdeal f k.val) →
        ∃ u ∈ Submonoid.powers g₁, u * (b * x) ∈ partialIdeal f k.val := by
    intro k
    refine exists_notMem_forall_mul_mem_of_flat (A := A) q (partialIdeal f k.val)
      (partialIdeal_fg f k.val) (f k) g₁ hg₁
      ?_ (hstalk k)
    rw [← partialIdeal_succ f k.val k.isLt]
    exact hg₁flat (k.val + 1) (Finset.mem_range.mpr (by omega))
  choose! b hb hb0 using hkill
  refine ⟨g₁ * ∏ l : Fin r, b l, q.primeCompl.mul_mem hg₁
    (q.primeCompl.prod_mem fun l _ => hb l), ?_⟩
  refine (isWeaklyRegular_iff_Fin _ _).mpr fun i => ?_
  have hilt : i.val < r := by simpa using i.isLt
  set k : Fin r := ⟨i.val, hilt⟩ with hk
  refine (isSMulRegular_ofList_take_iff f k _ i.isLt).mpr ?_
  refine (isSMulRegular_quotientMap_iff (partialIdeal f k.val)
    (Submonoid.powers (g₁ * ∏ l : Fin r, b l))
    (Localization.Away (g₁ * ∏ l : Fin r, b l)) (f k)).mpr fun x hx => ?_
  obtain ⟨u, ⟨m, rfl⟩, hmem⟩ := hx
  obtain ⟨c, hc⟩ : ∃ c : B, (∏ l : Fin r, b l) = b k * c :=
    ⟨∏ l ∈ Finset.univ.erase k, b l, by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_comm]⟩
  obtain ⟨u₂, ⟨n, rfl⟩, hmem₂⟩ := hb0 k ((∏ l : Fin r, b l) ^ m * x)
    ⟨g₁ ^ m, ⟨m, rfl⟩, by
      rw [show g₁ ^ m * (f k * ((∏ l : Fin r, b l) ^ m * x)) =
        (g₁ * ∏ l : Fin r, b l) ^ m * (f k * x) by rw [mul_pow]; ring]
      exact hmem⟩
  refine ⟨(g₁ * ∏ l : Fin r, b l) ^ max n (m + 1), ⟨max n (m + 1), rfl⟩, ?_⟩
  have hrw : (g₁ * ∏ l : Fin r, b l) ^ max n (m + 1) * x =
      (g₁ ^ (max n (m + 1) - n) * (b k * c) ^ (max n (m + 1) - (m + 1)) * c) *
        (g₁ ^ n * (b k * ((b k * c) ^ m * x))) := by
    rw [mul_pow, hc,
      show g₁ ^ max n (m + 1) = g₁ ^ (max n (m + 1) - n) * g₁ ^ n by
        rw [← pow_add]; congr 1; omega,
      show (b k * c) ^ max n (m + 1)
          = (b k * c) ^ (max n (m + 1) - (m + 1)) * (b k * c) ^ (m + 1) by
        rw [← pow_add]; congr 1; omega]
    rw [pow_succ]
    ring
  rw [hrw, ← hc]
  exact Ideal.mul_mem_left _ _ hmem₂

/-- Let `A → B` be flat and of finite presentation, let `f₁, …, f_r ∈ B` be a quasi-regular
sequence contained in a prime `q` and such that `B/(f₁, …, f_r)` is flat over `A`.  Then
`f₁, …, f_r` is a weakly regular sequence in `B_g` for some `g ∉ q`. -/
theorem exists_notMem_isWeaklyRegular_away
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] {r : ℕ} (f : Fin r → B) (hq : ∀ i, f i ∈ q)
    (hqr : IsQuasiRegular B (List.ofFn f))
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f))) :
    ∃ g ∉ q, IsWeaklyRegular (Localization.Away g)
      (List.ofFn fun i => algebraMap B (Localization.Away g) (f i)) :=
  have h := RelativeQuasiRegular.isRegular_localization_and_flat_quotients f hqr hflat q hq
  exists_notMem_isWeaklyRegular_away_of_isRegular_atPrime q f hq h.1 h.2

end Spreading

end Stacks.RingTheory.SpreadingOut

end
