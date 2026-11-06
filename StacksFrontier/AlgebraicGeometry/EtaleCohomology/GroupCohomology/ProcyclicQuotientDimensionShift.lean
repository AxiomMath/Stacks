module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.CoinductionRetraction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionDimensionShifting

/-!
# Cohomological dimension of an extension by a `ℤ_ℓ`-like quotient

Let `G` be a profinite group, `N` a closed normal subgroup and `σ ∈ G` an element whose image
topologically generates `G / N`, in the following quantitative form:

* for every open normal subgroup `W ⊇ N`, every `x ∈ G` lies in `σ ^ (-j) W` for some `j ≥ 0`;
* for every such `W` and every `b`, there is a smaller open normal subgroup `W' ⊇ N` such that
  the order of `σ` in `G / W'` is a multiple of `ℓ ^ b` times its order in `G / W`.

This is the situation of `G / N ≅ ℤ_ℓ`, and the second condition says that `G / N` has no
largest finite `ℓ`-power quotient. If `Hᵠ(N, M') = 0` for every `q > d` and every `ℓ`-power
torsion discrete `N`-module `M'`, then `Hᵠ(G, M) = 0` for every `q > d + 1` and every
`ℓ`-power torsion discrete `G`-module `M`: `cd_ℓ(G) ≤ cd_ℓ(N) + 1`.

The proof avoids the Hochschild–Serre spectral sequence. For an `ℓ`-power torsion `M` there is a
short exact sequence of discrete `G`-modules

`0 → M → Coind_N^G M → Coind_N^G M → 0`,

the second map being `f ↦ σ • f(σ⁻¹ · -) - f`. Shapiro's lemma identifies the cohomology of
`Coind_N^G M` with that of `N`, and the long exact sequence gives the bound. In terms of the
function `φ(x) = x⁻¹ • f(x)` on `G / N`, the second map is the difference operator
`φ ↦ φ(σ⁻¹ ·) - φ`; its kernel is the constant functions because `σ` generates `G / N`, and it
is onto because a function on a finite cyclic quotient `G / W'` of order `ℓ ^ b` times a period
of `φ` has a telescoping primitive once `ℓ ^ b` kills the values of `φ`.

## Main definitions

* `Stacks.GroupCohomology.shiftIndex`: the least `j` with `σ ^ j * x ∈ W`.
* `Stacks.GroupCohomology.shiftSum`: the telescoping primitive `∑_{i < j(x)} φ(σ⁻ⁱ)`.
* `Stacks.GroupCohomology.coindShiftSub`: the morphism `f ↦ σ • f(σ⁻¹ · -) - f` of
  `Coind_N^G M`.
* `Stacks.GroupCohomology.coindShiftShortComplex`: the sequence `M → Coind_N^G M → Coind_N^G M`.

## Main results

* `Stacks.GroupCohomology.shiftSum_inv_mul_sub`: the telescoping identity.
* `Stacks.GroupCohomology.coindShiftShortComplex_shortExact`: the sequence is short exact.
* `Stacks.GroupCohomology.subsingleton_ext_of_procyclic_quotient`: `cd_ℓ(G) ≤ cd_ℓ(N) + 1`.
* `Stacks.GroupCohomology.subsingleton_ext_of_procyclic_filtration`: the same, for `N` the
  intersection of open normal subgroups `U k` with `G / U k` cyclic of order `ℓ ^ k`.

## References

* J.-P. Serre, *Cohomologie galoisienne*, I §3.3, Proposition 15 (the inequality
  `cd_ℓ(G) ≤ cd_ℓ(N) + cd_ℓ(G / N)`, here for `G / N` procyclic pro-`ℓ` of infinite order).
* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8) (Shapiro's lemma).
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v w

namespace Stacks.GroupCohomology

section Telescoping

variable {G : Type*} [Group G]

/-- The least `j ≥ 0` with `σ ^ j * x ∈ W`, and `0` when there is none. -/
def shiftIndex (W : Subgroup G) (σ x : G) : ℕ := sInf {j : ℕ | σ ^ j * x ∈ W}

variable {W : Subgroup G} {σ : G}

/-- If some `σ ^ j * x` lies in `W`, then so does `σ ^ shiftIndex W σ x * x`. -/
lemma pow_shiftIndex_mul_mem {x : G} (h : ∃ j : ℕ, σ ^ j * x ∈ W) :
    σ ^ shiftIndex W σ x * x ∈ W :=
  Nat.sInf_mem h

/-- `shiftIndex W σ x ≤ j` whenever `σ ^ j * x ∈ W`. -/
lemma shiftIndex_le {x : G} {j : ℕ} (hj : σ ^ j * x ∈ W) : shiftIndex W σ x ≤ j :=
  Nat.sInf_le hj

/-- `shiftIndex W σ` is invariant under right translation by `W`. -/
lemma shiftIndex_mul_right {x w : G} (hw : w ∈ W) :
    shiftIndex W σ (x * w) = shiftIndex W σ x := by
  unfold shiftIndex
  congr 1
  ext j
  simp only [Set.mem_setOf_eq, ← mul_assoc]
  exact Subgroup.mul_mem_cancel_right W hw

/-- For `W` normal, `shiftIndex W σ` is invariant under left translation by `W`. -/
lemma shiftIndex_mul_left [hW : W.Normal] {x w : G} (hw : w ∈ W) :
    shiftIndex W σ (w * x) = shiftIndex W σ x := by
  unfold shiftIndex
  congr 1
  ext j
  simp only [Set.mem_setOf_eq]
  rw [show σ ^ j * (w * x) = (σ ^ j * w * (σ ^ j)⁻¹) * (σ ^ j * x) by group]
  exact Subgroup.mul_mem_cancel_left W (hW.conj_mem w hw _)

/-- If `σ ^ P ∈ W` with `0 < P` and some `σ ^ j * x` lies in `W`, then
`shiftIndex W σ x < P`. -/
lemma shiftIndex_lt {x : G} {P : ℕ} (hP : σ ^ P ∈ W) (hpos : 0 < P)
    (h : ∃ j : ℕ, σ ^ j * x ∈ W) : shiftIndex W σ x < P := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ : ∃ k, shiftIndex W σ x = P + k := ⟨shiftIndex W σ x - P, by omega⟩
  have hk' : σ ^ k * x ∈ W := by
    have e : σ ^ k * x = (σ ^ P)⁻¹ * (σ ^ shiftIndex W σ x * x) := by
      rw [hk, pow_add]
      group
    rw [e]
    exact W.mul_mem (W.inv_mem hP) (pow_shiftIndex_mul_mem h)
  have := shiftIndex_le hk'
  omega

variable {A : Type*} [AddCommGroup A]

/-- The telescoping primitive `x ↦ ∑_{i < j(x)} φ(σ⁻ⁱ)`, `j(x)` being `shiftIndex W σ x`. -/
def shiftSum (W : Subgroup G) (σ : G) (φ : G → A) (x : G) : A :=
  ∑ i ∈ Finset.range (shiftIndex W σ x), φ (σ⁻¹ ^ i)

/-- `shiftSum W σ φ` is invariant under right translation by `W`. -/
lemma shiftSum_mul_right {φ : G → A} {x w : G} (hw : w ∈ W) :
    shiftSum W σ φ (x * w) = shiftSum W σ φ x := by
  rw [shiftSum, shiftSum, shiftIndex_mul_right hw]

/-- For `W` normal, `shiftSum W σ φ` is invariant under left translation by `W`. -/
lemma shiftSum_mul_left [W.Normal] {φ : G → A} {x w : G} (hw : w ∈ W) :
    shiftSum W σ φ (w * x) = shiftSum W σ φ x := by
  rw [shiftSum, shiftSum, shiftIndex_mul_left hw]

/-- A sum over `c` periods of a periodic sequence is `c` times the sum over one period. -/
lemma sum_range_mul_eq_nsmul {φ' : ℕ → A} {P : ℕ} (hper : ∀ i, φ' (i + P) = φ' i) (c : ℕ) :
    ∑ i ∈ Finset.range (c * P), φ' i = c • ∑ i ∈ Finset.range P, φ' i := by
  have hper' : ∀ c i, φ' (c * P + i) = φ' i := by
    intro c
    induction c with
    | zero => simp
    | succ c ih =>
      intro i
      rw [Nat.succ_mul, show c * P + P + i = (c * P + i) + P by ring, hper, ih]
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ hper' c i

/-- A sum of a `P`-periodic sequence killed by `m` vanishes over any multiple of `m * P`. -/
lemma sum_range_eq_zero_of_periodic {φ' : ℕ → A} {P m n : ℕ}
    (hper : ∀ i, φ' (i + P) = φ' i) (hm : ∀ i, m • φ' i = 0) (hdvd : m * P ∣ n) :
    ∑ i ∈ Finset.range n, φ' i = 0 := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [show m * P * c = c * m * P by ring, sum_range_mul_eq_nsmul hper, mul_smul,
    Finset.smul_sum]
  simp [hm]

/-- **The telescoping identity.** Let `W' ≤ W` be subgroups, `W'` normal, `σ` an element whose
powers meet every coset of `W'`, of order exactly `P'` modulo `W'`, and let `φ` be invariant
under right translation by `W`, with values killed by `ℓ ^ b`. If `σ ^ P ∈ W` and
`ℓ ^ b * P ∣ P'`, then `shiftSum W' σ φ` is a primitive of `φ` for the difference operator
`ψ ↦ ψ(σ⁻¹ ·) - ψ`. -/
theorem shiftSum_inv_mul_sub {W W' : Subgroup G} (hW' : W' ≤ W) {σ : G}
    {φ : G → A} (hφ : ∀ x w, w ∈ W → φ (x * w) = φ x) {ℓ b P P' : ℕ}
    (hb : ∀ x, ℓ ^ b • φ x = 0) (hP : σ ^ P ∈ W) (hP' : σ ^ P' ∈ W')
    (hmin : ∀ i : ℕ, σ ^ i ∈ W' → P' ∣ i) (hpos : 0 < P') (hdvd : ℓ ^ b * P ∣ P')
    (hgen : ∀ x : G, ∃ j : ℕ, σ ^ j * x ∈ W') (x : G) :
    shiftSum W' σ φ (σ⁻¹ * x) - shiftSum W' σ φ x = φ x := by
  have hjmem : σ ^ shiftIndex W' σ x * x ∈ W' := pow_shiftIndex_mul_mem (hgen x)
  have himem : σ ^ shiftIndex W' σ (σ⁻¹ * x) * (σ⁻¹ * x) ∈ W' := pow_shiftIndex_mul_mem (hgen _)
  have hjlt : shiftIndex W' σ x < P' := shiftIndex_lt hP' hpos (hgen x)
  have hφx : φ x = φ (σ⁻¹ ^ shiftIndex W' σ x) := by
    have e : x = σ⁻¹ ^ shiftIndex W' σ x * (σ ^ shiftIndex W' σ x * x) := by
      rw [inv_pow, inv_mul_cancel_left]
    conv_lhs => rw [e]
    exact hφ _ _ (hW' hjmem)
  have hile : shiftIndex W' σ (σ⁻¹ * x) ≤ shiftIndex W' σ x + 1 := shiftIndex_le (by
    rw [pow_succ, mul_assoc, mul_inv_cancel_left]
    exact hjmem)
  set j := shiftIndex W' σ x with hj
  set i := shiftIndex W' σ (σ⁻¹ * x) with hi
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · have h1 : σ⁻¹ * x ∈ W' := by simpa [hi0] using himem
    have hj1 : j + 1 = P' := by
      have := Nat.le_of_dvd (Nat.succ_pos j) (hmin _ (by
        have e : σ ^ (j + 1) = (σ ^ j * x) * (σ⁻¹ * x)⁻¹ := by
          rw [pow_succ]
          group
        rw [e]
        exact W'.mul_mem hjmem (W'.inv_mem h1)))
      omega
    have hper : ∀ k, φ (σ⁻¹ ^ (k + P)) = φ (σ⁻¹ ^ k) := fun k ↦ by
      rw [pow_add, inv_pow σ P]
      exact hφ _ _ (W.inv_mem hP)
    have htot : ∑ k ∈ Finset.range (j + 1), φ (σ⁻¹ ^ k) = 0 := by
      rw [hj1]
      exact sum_range_eq_zero_of_periodic (φ' := fun k ↦ φ (σ⁻¹ ^ k)) hper (fun _ ↦ hb _) hdvd
    rw [Finset.sum_range_succ, add_eq_zero_iff_eq_neg] at htot
    rw [shiftSum, ← hi, hi0, Finset.sum_range_zero, zero_sub, shiftSum, ← hj, hφx, htot,
      neg_neg]
  · have hge : j + 1 ≤ i := by
      obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hkmem : σ ^ k * x ∈ W' := by
        rwa [hk, pow_succ, mul_assoc, mul_inv_cancel_left] at himem
      have := shiftIndex_le hkmem
      omega
    have hieq : i = j + 1 := le_antisymm hile hge
    rw [shiftSum, ← hi, hieq, Finset.sum_range_succ, shiftSum, ← hj, hφx]
    abel

end Telescoping

section Module

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (N : Subgroup G) [hN : N.Normal]
  {M : ContinuousGModule.{v, max v w} G}

/-- Left translation by `σ` on the module coinduced from the normal subgroup `N`:
`f ↦ σ • f(σ⁻¹ · -)`. -/
def coindLeftTranslate (σ : G) (f : CoindRes N M) : CoindRes N M :=
  ⟨fun x ↦ (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)), fun h x ↦ by
      have hc : σ⁻¹ * (h : G) * σ ∈ N := by
        simpa using hN.conj_mem h h.2 σ⁻¹
      change (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * ((h : G) * x))) =
        (M.obj.obj.ρ h).asHom.hom ((M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)))
      rw [show σ⁻¹ * ((h : G) * x) = (σ⁻¹ * h * σ) * (σ⁻¹ * x) by group,
        coindVal_mul f _ hc, ← ρ_mul_apply, ← ρ_mul_apply,
        show σ * (σ⁻¹ * (h : G) * σ) = h * σ by group],
    Subgroup.isOpen_mono (H₁ := rightStabilizer (coindVal f))
      (fun g hg x ↦ by
        change (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * (x * g))) =
          (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x))
        rw [← mul_assoc, show coindVal f (σ⁻¹ * x * g) = coindVal f (σ⁻¹ * x) from hg _])
      (isOpen_rightStabilizer f)⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The value of `coindLeftTranslate N σ f` at `x` is `σ • f(σ⁻¹ * x)`. -/
@[simp]
lemma coindLeftTranslate_apply (σ : G) (f : CoindRes N M) (x : G) :
    coindVal (coindLeftTranslate N σ f) x = (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)) := rfl

/-- The map `f ↦ σ • f(σ⁻¹ · -) - f` on the underlying group of `Coind_N^G M`. -/
def coindShiftSubHom (σ : G) : CoindRes N M →+ CoindRes N M where
  toFun f := coindLeftTranslate N σ f - f
  map_zero' := Subtype.ext (funext fun x ↦ by
    change (M.obj.obj.ρ σ).asHom.hom 0 - 0 = 0
    simp)
  map_add' f f' := Subtype.ext (funext fun x ↦ by
    change (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x) + coindVal f' (σ⁻¹ * x)) -
        (coindVal f x + coindVal f' x) =
      ((M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)) - coindVal f x) +
        ((M.obj.obj.ρ σ).asHom.hom (coindVal f' (σ⁻¹ * x)) - coindVal f' x)
    rw [map_add]
    abel)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The value of `coindShiftSubHom N σ f` at `x` is `σ • f(σ⁻¹ * x) - f(x)`. -/
lemma coindShiftSubHom_apply (σ : G) (f : CoindRes N M) (x : G) :
    coindVal (coindShiftSubHom N σ f) x =
      (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)) - coindVal f x := rfl

/-- **The morphism `f ↦ σ • f(σ⁻¹ · -) - f` of `Coind_N^G M`.** It commutes with the action of
`G` by right translation because left and right translations commute. -/
def coindShiftSub (σ : G) :
    (coinduction.{v, w} N).obj ((restriction N.subtype continuous_subtype_val).obj M) ⟶
      (coinduction.{v, w} N).obj ((restriction N.subtype continuous_subtype_val).obj M) :=
  (gModuleHomEquiv G _ _).symm ⟨coindShiftSubHom N σ, fun g f ↦ Subtype.ext (funext fun x ↦ by
    change (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x * g)) - coindVal f (x * g) =
      (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * (x * g))) - coindVal f (x * g)
    rw [mul_assoc])⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The value of `coindShiftSub N σ` applied to `f` at `x` is `σ • f(σ⁻¹ * x) - f(x)`. -/
lemma coindShiftSub_apply (σ : G) (f : CoindRes N M) (x : G) :
    coindVal (((coindShiftSub N σ).hom.hom.hom.hom f : CoindRes N M)) x =
      (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)) - coindVal f x := rfl

/-- The constant functions `x ↦ x • m`, the image of `M` in `Coind_N^G M`. -/
def coindConstFun (m : M.obj.obj.V) : CoindRes N M :=
  ⟨fun x ↦ (M.obj.obj.ρ x).asHom.hom m, fun h x ↦ by
      change (M.obj.obj.ρ ((h : G) * x)).asHom.hom m = (M.obj.obj.ρ h).asHom.hom ((M.obj.obj.ρ x).asHom.hom m)
      rw [ρ_mul_apply],
    Subgroup.isOpen_mono (H₁ := elementStabilizer G M m)
      (fun g hg x ↦ by
        change (M.obj.obj.ρ (x * g)).asHom.hom m = (M.obj.obj.ρ x).asHom.hom m
        rw [ρ_mul_apply, show (M.obj.obj.ρ g).asHom.hom m = m from hg])
      (isOpen_stabilizer ℤ G M m)⟩

omit hN [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The value of `coindConstFun N m` at `x` is `x • m`. -/
lemma coindConstFun_apply (m : M.obj.obj.V) (x : G) :
    coindVal (coindConstFun N m) x = (M.obj.obj.ρ x).asHom.hom m := rfl

/-- **The inclusion `M → Coind_N^G M`**, `m ↦ (x ↦ x • m)`: the unit of restriction and
coinduction, written out. -/
def coindConst :
    M ⟶ (coinduction.{v, w} N).obj ((restriction N.subtype continuous_subtype_val).obj M) :=
  (gModuleHomEquiv G _ _).symm
    ⟨{ toFun := coindConstFun N
       map_zero' := Subtype.ext (funext fun x ↦ by
         change (M.obj.obj.ρ x).asHom.hom 0 = 0
         exact map_zero _)
       map_add' := fun a b ↦ Subtype.ext (funext fun x ↦ by
         change (M.obj.obj.ρ x).asHom.hom (a + b) = (M.obj.obj.ρ x).asHom.hom a + (M.obj.obj.ρ x).asHom.hom b
         exact map_add _ _ _) },
      fun g m ↦ Subtype.ext (funext fun x ↦ by
        change (M.obj.obj.ρ x).asHom.hom ((M.obj.obj.ρ g).asHom.hom m) = (M.obj.obj.ρ (x * g)).asHom.hom m
        rw [ρ_mul_apply])⟩

omit hN [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The value of `coindConst N` applied to `m` at `x` is `x • m`. -/
lemma coindConst_apply (m : M.obj.obj.V) (x : G) :
    coindVal ((coindConst N).hom.hom.hom.hom m : CoindRes N M) x = (M.obj.obj.ρ x).asHom.hom m := rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- `f ↦ σ • f(σ⁻¹ · -) - f` vanishes on the image of `coindConst N`. -/
lemma coindShiftSub_coindConst (σ : G) (m : M.obj.obj.V) :
    (coindShiftSub N σ).hom.hom.hom.hom ((coindConst N).hom.hom.hom.hom m) = 0 :=
  Subtype.ext (funext fun x ↦ by
    change (M.obj.obj.ρ σ).asHom.hom ((M.obj.obj.ρ (σ⁻¹ * x)).asHom.hom m) - (M.obj.obj.ρ x).asHom.hom m = 0
    rw [← ρ_mul_apply, mul_inv_cancel_left, sub_self])

/-- The short complex `M → Coind_N^G M → Coind_N^G M`, the first map being `m ↦ (x ↦ x • m)`
and the second `f ↦ σ • f(σ⁻¹ · -) - f`. -/
def coindShiftShortComplex (M : ContinuousGModule.{v, max v w} G) (σ : G) :
    ShortComplex (ContinuousGModule.{v, max v w} G) :=
  ShortComplex.mk (coindConst (M := M) N) (coindShiftSub (M := M) N σ)
    (hom_ext fun m ↦ coindShiftSub_coindConst (M := M) N σ m)

/-- The function `x ↦ x⁻¹ • f(x)` attached to an element of `Coind_N^G M`; it is invariant under
left translation by `N`. -/
def coindUntwist (f : CoindRes N M) (x : G) : M.obj.obj.V :=
  (M.obj.obj.ρ x⁻¹).asHom.hom (coindVal f x)

/-- The open normal subgroup `N ⊔ V`. -/
def supOpenNormal (V : OpenNormalSubgroup G) : OpenNormalSubgroup G where
  toSubgroup := N ⊔ V.toSubgroup
  isOpen' := Subgroup.isOpen_mono le_sup_right V.isOpen'
  isNormal' := Subgroup.sup_normal _ _

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- `N ≤ N ⊔ V`. -/
lemma le_supOpenNormal (V : OpenNormalSubgroup G) : N ≤ (supOpenNormal N V).toSubgroup :=
  le_sup_left

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- `x ↦ x⁻¹ • f(x)` is invariant under right translation by `N ⊔ V` for an open normal
subgroup `V` adapted to `f`. -/
lemma coindUntwist_mul_right {f : CoindRes N M} {V : OpenNormalSubgroup G} (hV : IsAdapted f V)
    (x w : G) (hw : w ∈ (supOpenNormal N V).toSubgroup) :
    coindUntwist N f (x * w) = coindUntwist N f x := by
  obtain ⟨n, hn, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
  have hc : x * n * x⁻¹ ∈ N := hN.conj_mem n hn x
  have e1 : coindVal f (x * (n * u)) = coindVal f (x * n) := by
    rw [← mul_assoc]
    exact hV.1 hu (x * n)
  have e2 : coindVal f (x * n) = (M.obj.obj.ρ (x * n * x⁻¹)).asHom.hom (coindVal f x) := by
    have := coindVal_mul f (x * n * x⁻¹) hc x
    rwa [show x * n * x⁻¹ * x = x * n by group] at this
  have hcu : x * u⁻¹ * x⁻¹ ∈ V.toSubgroup := V.isNormal'.conj_mem _ (V.inv_mem hu) x
  have e3 : (M.obj.obj.ρ (x * u⁻¹ * x⁻¹)).asHom.hom (coindVal f x) = coindVal f x :=
    hV.2 x _ hcu
  unfold coindUntwist
  rw [e1, e2, ← ρ_mul_apply, show (x * (n * u))⁻¹ * (x * n * x⁻¹) = x⁻¹ * (x * u⁻¹ * x⁻¹) by
    group, ρ_mul_apply, e3]

omit hN [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- An open normal subgroup adapted to `f` fixes the values of `x ↦ x⁻¹ • f(x)`. -/
lemma ρ_coindUntwist {f : CoindRes N M} {V : OpenNormalSubgroup G} (hV : IsAdapted f V)
    (x u : G) (hu : u ∈ V.toSubgroup) :
    (M.obj.obj.ρ u).asHom.hom (coindUntwist N f x) = coindUntwist N f x := by
  have hcu : x * u * x⁻¹ ∈ V.toSubgroup := V.isNormal'.conj_mem _ hu x
  unfold coindUntwist
  rw [← ρ_mul_apply, show u * x⁻¹ = x⁻¹ * (x * u * x⁻¹) by group, ρ_mul_apply, hV.2 x _ hcu]

omit hN [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- `x • (x⁻¹ • f(x)) = f(x)`. -/
lemma ρ_coindUntwist_self (f : CoindRes N M) (x : G) :
    (M.obj.obj.ρ x).asHom.hom (coindUntwist N f x) = coindVal f x :=
  ρ_apply_ρ_inv_apply M x _

variable {N}

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- `σ` raised to its order in `G ⧸ W` lies in `W`. -/
lemma pow_mem_of_orderOf (W : OpenNormalSubgroup G) (σ : G) :
    σ ^ orderOf (σ : G ⧸ W.toSubgroup) ∈ W.toSubgroup := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- If `σ ^ i ∈ W`, then the order of `σ` in `G ⧸ W` divides `i`. -/
lemma orderOf_dvd_of_pow_mem (W : OpenNormalSubgroup G) (σ : G) {i : ℕ}
    (hi : σ ^ i ∈ W.toSubgroup) : orderOf (σ : G ⧸ W.toSubgroup) ∣ i :=
  orderOf_dvd_of_pow_eq_one (by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff])

omit [TotallyDisconnectedSpace G] in
/-- In a compact group, the order of `σ` in the quotient by an open normal subgroup is
positive. -/
lemma orderOf_pos_of_openNormal (W : OpenNormalSubgroup G) (σ : G) :
    0 < orderOf (σ : G ⧸ W.toSubgroup) := by
  have := Subgroup.quotient_finite_of_isOpen W.toSubgroup W.isOpen'
  exact orderOf_pos _

variable {ℓ : ℕ} {σ : G}
  (hgen : ∀ W : OpenNormalSubgroup G, N ≤ W.toSubgroup → ∀ x : G, ∃ j : ℕ,
    σ ^ j * x ∈ W.toSubgroup)

include hgen in
omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- An element of `Coind_N^G M` killed by `f ↦ σ • f(σ⁻¹ · -) - f` comes from `M`. -/
theorem mem_range_coindConst_of_coindShiftSub_eq_zero (f : CoindRes N M)
    (V : OpenNormalSubgroup G) (hV : IsAdapted f V)
    (hf : (coindShiftSub N σ).hom.hom.hom.hom f = 0) :
    f = (coindConst N).hom.hom.hom.hom (coindVal f 1) := by
  have hT : ∀ x, (M.obj.obj.ρ σ).asHom.hom (coindVal f (σ⁻¹ * x)) = coindVal f x := fun x ↦
    sub_eq_zero.mp (congrFun (congrArg Subtype.val hf) x)
  have hinv : ∀ x, coindUntwist N f (σ⁻¹ * x) = coindUntwist N f x := fun x ↦ by
    unfold coindUntwist
    rw [← hT x, ← ρ_mul_apply, show (σ⁻¹ * x)⁻¹ = x⁻¹ * σ by group]
  have hpow : ∀ (j : ℕ) x, coindUntwist N f (σ ^ j * x) = coindUntwist N f x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro x
      rw [← hinv, show σ⁻¹ * (σ ^ (j + 1) * x) = σ ^ j * x by
        rw [pow_succ', mul_assoc, inv_mul_cancel_left], ih]
  have hconst : ∀ x, coindUntwist N f x = coindUntwist N f 1 := fun x ↦ by
    obtain ⟨j, hj⟩ := hgen (supOpenNormal N V) (le_supOpenNormal N V) x
    rw [← hpow j x, ← one_mul (σ ^ j * x), coindUntwist_mul_right N hV 1 _ hj]
  apply Subtype.ext
  funext x
  change coindVal f x = (M.obj.obj.ρ x).asHom.hom (coindVal f 1)
  rw [← ρ_coindUntwist_self N f x, hconst x]
  simp [coindUntwist]

variable (hdeep : ∀ W : OpenNormalSubgroup G, N ≤ W.toSubgroup → ∀ b : ℕ,
    ∃ W' : OpenNormalSubgroup G, N ≤ W'.toSubgroup ∧ W'.toSubgroup ≤ W.toSubgroup ∧
      ℓ ^ b * orderOf (σ : G ⧸ W.toSubgroup) ∣ orderOf (σ : G ⧸ W'.toSubgroup))

include hgen hdeep in
/-- **`f ↦ σ • f(σ⁻¹ · -) - f` is onto** on `Coind_N^G M` for an `ℓ`-power torsion `M`. -/
theorem coindShiftSub_surjective (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    Function.Surjective (coindShiftSub (M := M) N σ).hom.hom.hom.hom := by
  intro f
  obtain ⟨b, hb⟩ := exists_pow_smul_coinduction_eq_zero
    (N := (restriction N.subtype continuous_subtype_val).obj M) hM f
  have hbx : ∀ x, ℓ ^ b • coindVal f x = 0 := fun x ↦
    congrFun (congrArg Subtype.val hb) x
  obtain ⟨V, hV⟩ := exists_isAdapted f
  set W := supOpenNormal N V
  have hφb : ∀ x, ℓ ^ b • coindUntwist N f x = 0 := fun x ↦ by
    unfold coindUntwist
    rw [← map_nsmul, hbx, map_zero]
  obtain ⟨W', hNW', hW'W, hdvd⟩ := hdeep W (le_supOpenNormal N V) b
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = shiftSum W'.toSubgroup σ (coindUntwist N f) := ⟨_, rfl⟩
  have hψl : ∀ h ∈ N, ∀ x, ψ (h * x) = ψ x := fun h hh x ↦ by
    rw [hψ]
    exact shiftSum_mul_left (hNW' hh)
  have hψr : ∀ u ∈ W'.toSubgroup, ∀ x, ψ (x * u) = ψ x := fun u hu x ↦ by
    rw [hψ]
    exact shiftSum_mul_right hu
  have hψtel : ∀ x, ψ (σ⁻¹ * x) - ψ x = coindUntwist N f x := fun x ↦ by
    rw [hψ]
    exact shiftSum_inv_mul_sub hW'W (coindUntwist_mul_right N hV) hφb (pow_mem_of_orderOf W σ)
      (pow_mem_of_orderOf W' σ) (fun i hi ↦ orderOf_dvd_of_pow_mem W' σ hi)
      (orderOf_pos_of_openNormal W' σ) hdvd (hgen W' hNW') x
  have hψfix : ∀ x, ∀ u ∈ V.toSubgroup, (M.obj.obj.ρ u).asHom.hom (ψ x) = ψ x := fun x u hu ↦ by
    rw [hψ]
    change (M.obj.obj.ρ u).asHom.hom (∑ i ∈ Finset.range _, coindUntwist N f (σ⁻¹ ^ i)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ ρ_coindUntwist N hV _ u hu
  let g : CoindRes N M := ⟨fun x ↦ (M.obj.obj.ρ x).asHom.hom (ψ x), fun h x ↦ by
      change (M.obj.obj.ρ ((h : G) * x)).asHom.hom (ψ ((h : G) * x)) =
        (M.obj.obj.ρ h).asHom.hom ((M.obj.obj.ρ x).asHom.hom (ψ x))
      rw [ρ_mul_apply, hψl _ h.2],
    Subgroup.isOpen_mono (H₁ := V.toSubgroup ⊓ W'.toSubgroup)
      (fun u hu x ↦ by
        change (M.obj.obj.ρ (x * u)).asHom.hom (ψ (x * u)) = (M.obj.obj.ρ x).asHom.hom (ψ x)
        rw [hψr u hu.2, ρ_mul_apply, hψfix x u hu.1])
      (by
        rw [Subgroup.coe_inf]
        exact V.isOpen'.inter W'.isOpen')⟩
  refine ⟨g, Subtype.ext (funext fun x ↦ ?_)⟩
  change (M.obj.obj.ρ σ).asHom.hom ((M.obj.obj.ρ (σ⁻¹ * x)).asHom.hom (ψ (σ⁻¹ * x))) -
    (M.obj.obj.ρ x).asHom.hom (ψ x) = coindVal f x
  rw [← ρ_mul_apply, mul_inv_cancel_left, ← map_sub, hψtel]
  exact ρ_coindUntwist_self N f x

include hgen hdeep in
/-- **The sequence `0 → M → Coind_N^G M → Coind_N^G M → 0` is short exact** for an `ℓ`-power
torsion discrete `G`-module `M`. -/
theorem coindShiftShortComplex_shortExact
    (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    (coindShiftShortComplex N M σ).ShortExact := by
  refine shortExact_of_function_exact _ ?_ (coindShiftSub_surjective hgen hdeep hM) ?_
  · intro m m' hmm'
    exact (ρ_one_apply M m).symm.trans
      ((congrFun (congrArg Subtype.val hmm') 1).trans (ρ_one_apply M m'))
  · intro f
    constructor
    · intro hf
      obtain ⟨V, hV⟩ := exists_isAdapted (H := N) (M := M) f
      exact ⟨coindVal f 1, (mem_range_coindConst_of_coindShiftSub_eq_zero hgen f V hV hf).symm⟩
    · rintro ⟨m, rfl⟩
      exact coindShiftSub_coindConst N σ m

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]
  [HasExt.{max v w} (ContinuousGModule.{v, max v w} N)]

include hgen hdeep in
/-- **`cd_ℓ(G) ≤ cd_ℓ(N) + 1` when `G / N` is `ℤ_ℓ`-like** (Serre, *Cohomologie galoisienne*,
I §3.3, Proposition 15). Let `N` be a normal subgroup of a profinite group `G` and `σ ∈ G` an
element generating `G / N` in the sense of `hgen` and `hdeep`. If `Hᵠ(N, M') = 0` for every
`q > d` and every `ℓ`-power torsion discrete `N`-module `M'`, then `Hᵠ(G, M) = 0` for every
`q > d + 1` and every `ℓ`-power torsion discrete `G`-module `M`. -/
theorem subsingleton_ext_of_procyclic_quotient {d : ℕ}
    (hNd : ∀ M' : ContinuousGModule.{v, max v w} N,
      (∀ x : M'.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) → ∀ q : ℕ, d < q →
        Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} N (ULift.{max v w} ℤ)) M' q))
    (M : ContinuousGModule.{v, max v w} G) (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0)
    (q : ℕ) (hq : d + 1 < q) :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M q) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hS := coindShiftShortComplex_shortExact (M := M) hgen hdeep hM
  have hR : ∀ x : ((restriction N.subtype continuous_subtype_val).obj M).obj.obj.V,
      ∃ k : ℕ, ℓ ^ k • x = 0 := hM
  have hcoind : ∀ n, d < n → Subsingleton (Abelian.Ext
      (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ))
      ((coinduction.{v, w} N).obj ((restriction N.subtype continuous_subtype_val).obj M)) n) :=
    fun n hn ↦ by
      have := hNd _ hR n hn
      exact (shapiroAddEquiv.{v, w} N _ n).symm.injective.subsingleton
  have h₂ := hcoind (q + 1) (by omega)
  have h₃ := hcoind q (by omega)
  have hzero : ∀ c : Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M (q + 1),
      c = 0 := fun c ↦ by
    obtain ⟨e, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS c (h₂.elim _ _) rfl
    rw [show e = 0 from h₃.elim e 0, Abelian.Ext.zero_comp]
    rfl
  exact subsingleton_of_forall_eq 0 hzero

end Module

section Filtration

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {N : Subgroup G} [N.Normal]

omit [TotallyDisconnectedSpace G] [N.Normal] in
/-- In a compact group, an open subgroup containing the intersection of a decreasing sequence of
open subgroups contains one of them. -/
theorem exists_le_of_iInf_le (U : ℕ → OpenNormalSubgroup G)
    (hanti : ∀ k, (U (k + 1)).toSubgroup ≤ (U k).toSubgroup)
    (hNU : ∀ g, g ∈ N ↔ ∀ k, g ∈ (U k).toSubgroup) (W : OpenNormalSubgroup G)
    (hNW : N ≤ W.toSubgroup) : ∃ k, (U k).toSubgroup ≤ W.toSubgroup := by
  have hmono : Antitone fun k ↦ ((U k).toSubgroup : Set G) :=
    antitone_nat_of_succ_le fun k ↦ hanti k
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact' (V := fun k ↦ ((U k).toSubgroup : Set G))
    hmono.directed_ge (fun k ↦ (U k).toOpenSubgroup.isClosed.isCompact)
    (fun k ↦ (U k).toOpenSubgroup.isClosed)
    (W.isOpen'.mem_nhdsSet.mpr fun g hg ↦ hNW ((hNU g).mpr (Set.mem_iInter.mp hg)))
  exact ⟨k, hk⟩

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]
  [HasExt.{max v w} (ContinuousGModule.{v, max v w} N)]

/-- **`cd_ℓ(G) ≤ cd_ℓ(N) + 1` when `G / N ≅ ℤ_ℓ`**, in terms of a filtration: `N` is the
intersection of a decreasing sequence of open normal subgroups `U k` with `G / U k` cyclic of
order `ℓ ^ k`, generated by the image of `σ`. If `Hᵠ(N, M') = 0` for every `q > d` and every
`ℓ`-power torsion discrete `N`-module `M'`, then `Hᵠ(G, M) = 0` for every `q > d + 1` and every
`ℓ`-power torsion discrete `G`-module `M`. -/
theorem subsingleton_ext_of_procyclic_filtration {ℓ d : ℕ} (σ : G) (U : ℕ → OpenNormalSubgroup G)
    (hanti : ∀ k, (U (k + 1)).toSubgroup ≤ (U k).toSubgroup)
    (hNU : ∀ g, g ∈ N ↔ ∀ k, g ∈ (U k).toSubgroup)
    (hord : ∀ k, orderOf (σ : G ⧸ (U k).toSubgroup) = ℓ ^ k)
    (hcyc : ∀ k (x : G), ∃ j : ℕ, σ ^ j * x ∈ (U k).toSubgroup)
    (hNd : ∀ M' : ContinuousGModule.{v, max v w} N,
      (∀ x : M'.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) → ∀ q : ℕ, d < q →
        Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} N (ULift.{max v w} ℤ)) M' q))
    (M : ContinuousGModule.{v, max v w} G) (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0)
    (q : ℕ) (hq : d + 1 < q) :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M q) := by
  have hanti' : Antitone fun k ↦ (U k).toSubgroup := antitone_nat_of_succ_le fun k ↦ hanti k
  have hgen : ∀ W : OpenNormalSubgroup G, N ≤ W.toSubgroup → ∀ x : G, ∃ j : ℕ,
      σ ^ j * x ∈ W.toSubgroup := fun W hNW x ↦ by
    obtain ⟨k, hk⟩ := exists_le_of_iInf_le U hanti hNU W hNW
    obtain ⟨j, hj⟩ := hcyc k x
    exact ⟨j, hk hj⟩
  have hdeep : ∀ W : OpenNormalSubgroup G, N ≤ W.toSubgroup → ∀ b : ℕ,
      ∃ W' : OpenNormalSubgroup G, N ≤ W'.toSubgroup ∧ W'.toSubgroup ≤ W.toSubgroup ∧
        ℓ ^ b * orderOf (σ : G ⧸ W.toSubgroup) ∣ orderOf (σ : G ⧸ W'.toSubgroup) := by
    intro W hNW b
    obtain ⟨k, hk⟩ := exists_le_of_iInf_le U hanti hNU W hNW
    refine ⟨U (k + b), fun g hg ↦ (hNU g).mp hg (k + b), (hanti' (by omega)).trans hk, ?_⟩
    have hW : orderOf (σ : G ⧸ W.toSubgroup) ∣ ℓ ^ k := by
      apply orderOf_dvd_of_pow_mem W σ
      apply hk
      have := pow_mem_of_orderOf (U k) σ
      rwa [hord k] at this
    rw [hord (k + b), pow_add, mul_comm (ℓ ^ k)]
    exact mul_dvd_mul_left _ hW
  exact subsingleton_ext_of_procyclic_quotient.{v, w} (N := N) (ℓ := ℓ) (σ := σ) hgen hdeep hNd
    M hM q hq

end Filtration

end Stacks.GroupCohomology

end
