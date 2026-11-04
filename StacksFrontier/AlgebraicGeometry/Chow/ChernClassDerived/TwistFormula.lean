module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleShift
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BoundedComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTensor

/-!
# The twist of a total Chow cohomology class

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project. For a total
Chow cohomology class `x` of `Y` homogeneous of degree `1` (such as the first Chern class
`c₁(ℒ)` of an invertible module) and an integer `r`, the *twist* of a total class `c` is the
total class `T_{r,x}(c)` whose degree-`i` component is

  `T_{r,x}(c)_i = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j} x^j`,

with the generalized binomial coefficient `Ring.choose`. [Stacks, Tag 02UD] says that the total
Chern class of `ℰ ⊗ ℒ`, for `ℰ` finite locally free of rank `r`, is `T_{r,c₁(ℒ)}(c(ℰ))`, and
[Stacks, Tag 0FAF] says the same for a perfect object of constant rank `r`.

On every test scheme the operation of `T_{r,x}(c)` is the twist
`Stacks.Chow.gradedTwist` of the graded cap family of `c`
(`Stacks.Chow.TotalChowClass.op_twist`), so the algebra of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing` transfers to total classes:
`T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)` when `x` commutes with `d`, `T_{0,x}(1) = 1`, and the
twist of an inverse at the opposite rank is the inverse of the twist.

The first Chern class `c₁(ℒ) ∈ A^1(Y)` of [Stacks, Tag 0B77] is a total class homogeneous of
degree `1` (`Stacks.Chow.TotalChowClass.firstChernTotal`), and it commutes with the total Chern
class of every finite locally free module: on the test schemes this is the commutation of the
cap products `c₁(ℒ) ∩ -` and `c_j(ℰ) ∩ -`
(`Stacks.Chow.GenuineChern.chernCap_invCap_comm`).

## Main definitions

* `Stacks.Chow.TotalChowClass.IsHomogeneous`, `Stacks.Chow.TotalChowClass.homComponent`,
  `Stacks.Chow.TotalChowClass.series` — homogeneous total classes, components and series.
* `Stacks.Chow.TotalChowClass.twist` — the twist `T_{r,x}`.
* `Stacks.Chow.TotalChowClass.twistUnit` — the twist of a unit commuting with `x`, as a unit.
* `Stacks.Chow.TotalChowClass.firstChernTotal` — `c₁(ℒ)` as a total class.

## Main results

* `Stacks.Chow.TotalChowClass.op_twist` — the operation of a twist is the twist of the operation.
* `Stacks.Chow.TotalChowClass.twist_mul`, `Stacks.Chow.TotalChowClass.twist_zero_one`,
  `Stacks.Chow.TotalChowClass.twist_inv_mul`, `Stacks.Chow.TotalChowClass.twist_mul_inv`.
* `Stacks.Chow.TotalChowClass.commute_firstChernTotal_totalChern` — `c₁(ℒ)` commutes with
  `c(ℰ)`.
* `Stacks.Chow.TotalChowClass.totalChern_sheafTensor` — Stacks 02UD for total classes:
  `c(ℰ ⊗ ℒ) = T_{r,c₁(ℒ)}(c(ℰ))`.
* `Stacks.Chow.TotalChowClass.totalChern_sheafTensor_degree` — the same identity in degree `i`,
  which is Equation (02UE) as the source displays it.
* `Stacks.Chow.TotalChowClass.complexChernBounded_twistComplex` — for a bounded complex `P` of
  finite locally free modules of constant ranks `ρ`, `c(P ⊗ ℳ) = T_{r,c₁(ℳ)}(c(P))` with
  `r = ∑_n (-1)^n ρ n`.

## References

* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe v u

namespace Stacks.Chow

/-! ### Commuting with a graded cap family of index one -/

section Graded

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)] {x : GradedCapFamily G}

/-- The index-`m` component of a product is a single convolution summand when all the others
vanish. -/
private theorem gradedCap_mul_apply_of_eq_single (u v : GradedCapFamily G) (k : ℤ) {m q : ℕ}
    (hqm : q ≤ m) (a : G k) (h : ∀ j ≤ m, j ≠ q → convolveTerm u v k m j a = 0) :
    (u * v) k m a = convolveTerm u v k m q a := by
  rw [gradedCap_mul_apply]
  exact Finset.sum_eq_single_of_mem q (mem_range.mpr (by omega)) fun j hj hjq ↦
    h j (Nat.lt_succ_iff.mp (mem_range.mp hj)) hjq

/-- Multiplying on the left by an element of index `1`: the index-`m + 1` component of `x c` is
`x` after the index-`m` component of `c`. -/
theorem gradedCap_mul_succ_of_isHomogeneous_one_left (hx : x.IsHomogeneous 1)
    (c : GradedCapFamily G) (k : ℤ) (m : ℕ) (a : G k) :
    (x * c) k (m + 1) a = capTo x 1 (by push_cast; ring) (c k m a) := by
  rw [gradedCap_mul_apply_of_eq_single x c k (Nat.le_succ m) a fun j hj hjm ↦ by
      rw [convolveTerm_of_le _ _ _ hj]
      exact capTo_of_eq_zero x _ (hx _ _ (by omega)) _,
    convolveTerm_of_le _ _ _ (Nat.le_succ m), capTo_congr_index x (by omega : m + 1 - m = 1)]

/-- Multiplying on the left by an element of index `1` kills the index-`0` component. -/
theorem gradedCap_mul_zero_of_isHomogeneous_one_left (hx : x.IsHomogeneous 1)
    (c : GradedCapFamily G) (k : ℤ) (a : G k) : (x * c) k 0 a = 0 := by
  rw [gradedCap_mul_apply, Finset.sum_range_one, convolveTerm_of_le _ _ _ le_rfl]
  exact capTo_of_eq_zero x _ (hx _ _ (by omega)) _

/-- Multiplying on the right by an element of index `1`: the index-`m + 1` component of `c x` is
the index-`m` component of `c` after `x`. -/
theorem gradedCap_mul_succ_of_isHomogeneous_one_right (hx : x.IsHomogeneous 1)
    (c : GradedCapFamily G) (k : ℤ) (m : ℕ) (a : G k) :
    (c * x) k (m + 1) a = capTo c m (by push_cast; ring) (x k 1 a) := by
  rw [gradedCap_mul_apply_of_eq_single c x k (Nat.le_add_left 1 m) a fun j hj hj1 ↦ by
      rw [convolveTerm_of_le _ _ _ hj, hx k j hj1, AddMonoidHom.zero_apply]
      exact capTo_zero c _ _,
    convolveTerm_of_le _ _ _ (by omega), capTo_congr_index c (by omega : m + 1 - 1 = m)]

/-- Multiplying on the right by an element of index `1` kills the index-`0` component. -/
theorem gradedCap_mul_zero_of_isHomogeneous_one_right (hx : x.IsHomogeneous 1)
    (c : GradedCapFamily G) (k : ℤ) (a : G k) : (c * x) k 0 a = 0 := by
  rw [gradedCap_mul_apply, Finset.sum_range_one, convolveTerm_of_le _ _ _ le_rfl,
    hx k 0 (by omega), AddMonoidHom.zero_apply]
  exact capTo_zero c _ _

/-- Multiplying on the right by an element homogeneous of index `q ≤ m`: the index-`m` component
of `u v` is the index-`m - q` component of `u` after `v`. -/
theorem gradedCap_mul_apply_of_isHomogeneous_right {v : GradedCapFamily G} {q : ℕ}
    (hv : v.IsHomogeneous q) (u : GradedCapFamily G) (k : ℤ) {m : ℕ} (hqm : q ≤ m) (a : G k) :
    (u * v) k m a = capTo u (m - q) (by omega) (v k q a) := by
  rw [gradedCap_mul_apply_of_eq_single u v k hqm a fun j hj hjq ↦ by
      rw [convolveTerm_of_le _ _ _ hj, hv k j hjq, AddMonoidHom.zero_apply]
      exact capTo_zero u _ _,
    convolveTerm_of_le _ _ _ hqm]

/-- **An element of index `1` commutes with every element whose components it commutes with.** -/
theorem commute_of_isHomogeneous_one (hx : x.IsHomogeneous 1) {c : GradedCapFamily G}
    (h : ∀ (k : ℤ) (m : ℕ) (a : G k),
      capTo x 1 (by push_cast; ring : k - (m : ℤ) - ((1 : ℕ) : ℤ) = k - ((m + 1 : ℕ) : ℤ))
          (c k m a) =
        capTo c m (by push_cast; ring : k - ((1 : ℕ) : ℤ) - (m : ℤ) = k - ((m + 1 : ℕ) : ℤ))
          (x k 1 a)) :
    Commute x c := by
  show x * c = c * x
  funext k m
  refine AddMonoidHom.ext fun a ↦ ?_
  cases m with
  | zero =>
    rw [gradedCap_mul_zero_of_isHomogeneous_one_left hx,
      gradedCap_mul_zero_of_isHomogeneous_one_right hx]
  | succ m =>
    rw [gradedCap_mul_succ_of_isHomogeneous_one_left hx,
      gradedCap_mul_succ_of_isHomogeneous_one_right hx]
    exact h k m a

end Graded

namespace TotalChowClass

/-! ### Homogeneous total classes, components and series -/

section Homogeneous

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- A total class is *homogeneous of degree `i`* if its components of every degree other than `i`
vanish. The first Chern class of an invertible module is homogeneous of degree `1`. -/
def IsHomogeneous (i : ℕ) (c : TotalChowClass C sY) : Prop :=
  ∀ p : ℕ, p ≠ i → c p = 0

/-- The operation of a homogeneous total class is homogeneous of the same index. -/
theorem IsHomogeneous.op {i : ℕ} {c : TotalChowClass C sY} (hc : c.IsHomogeneous i)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] : (c.op g).IsHomogeneous i :=
  fun k p hp ↦ AddMonoidHom.ext fun α ↦ by
    rw [op_apply, hc p hp, BivariantClass.idRule_zero]
    rfl

/-- The homogeneous component of degree `i`: the component of degree `i` is kept, the others
replaced by zero. -/
def homComponent (i : ℕ) : TotalChowClass C sY →+ TotalChowClass C sY where
  toFun c p := if p = i then c p else 0
  map_zero' := by
    refine TotalChowClass.ext fun p ↦ ?_
    change (if p = i then (0 : TotalChowClass C sY) p else 0) = 0
    split_ifs <;> rfl
  map_add' c d := by
    refine TotalChowClass.ext fun p ↦ ?_
    change (if p = i then (c + d) p else 0) =
      (if p = i then c p else 0) + (if p = i then d p else 0)
    split_ifs <;> simp

/-- The components of a homogeneous component. -/
theorem homComponent_apply (i : ℕ) (c : TotalChowClass C sY) (p : ℕ) :
    homComponent i c p = if p = i then c p else 0 :=
  rfl

/-- The homogeneous component of degree `i` is homogeneous of degree `i`. -/
theorem isHomogeneous_homComponent (i : ℕ) (c : TotalChowClass C sY) :
    (homComponent i c).IsHomogeneous i :=
  fun _ hp ↦ if_neg hp

/-- **The operation of a homogeneous component is the homogeneous component of the
operation.** -/
theorem op_homComponent (i : ℕ) (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (homComponent i c).op g = Stacks.Chow.homComponent i (c.op g) := by
  funext k p
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [op_apply, homComponent_apply, Stacks.Chow.homComponent_apply]
  split_ifs
  · rfl
  · rw [BivariantClass.idRule_zero]
    rfl

/-- The *series* of a family `f` of total classes: the total class whose degree-`i` component is
the degree-`i` component of `f i`. For `f i` homogeneous of degree `i` it is `∑_i f i`. -/
def series (f : ℕ → TotalChowClass C sY) : TotalChowClass C sY :=
  fun p ↦ f p p

/-- The components of a series. -/
theorem series_apply (f : ℕ → TotalChowClass C sY) (p : ℕ) : series f p = f p p :=
  rfl

/-- The operation of a series is the series of the operations. -/
theorem op_series (f : ℕ → TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (series f).op g = gradedSeries fun i ↦ (f i).op g :=
  rfl

/-- The operation of an integer multiple is that multiple of the operation. -/
theorem op_zsmul (n : ℤ) (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (n • c).op g = n • c.op g :=
  map_zsmul (opHom g) n c

/-- The operation of a power is the power of the operation. -/
theorem op_pow (c : TotalChowClass C sY) (n : ℕ) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (c ^ n).op g = c.op g ^ n :=
  map_pow (opRingHom g) c n

/-- The operation of a finite sum is the sum of the operations. -/
theorem op_sum {ι : Type*} (s : Finset ι) (c : ι → TotalChowClass C sY) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] : (∑ i ∈ s, c i).op g = ∑ i ∈ s, (c i).op g :=
  map_sum (opHom g) c s

end Homogeneous

/-! ### The twist -/

section Twist

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **The twist `T_{r,x}`** of total classes: the degree-`m` component of `T_{r,x}(c)` is
`∑_{j=0}^{m} binom(r - m + j, j) c_{m-j} x^j`. For `ℰ` finite locally free of rank `r`, `ℒ`
invertible and `x = c₁(ℒ)`, Stacks 02UD says `c(ℰ ⊗ ℒ) = T_{r,x}(c(ℰ))`. -/
def twist (r : ℤ) (x : TotalChowClass C sY) : TotalChowClass C sY →+ TotalChowClass C sY :=
  AddMonoidHom.mk' (fun c ↦ series fun m ↦ ∑ j ∈ range (m + 1),
      Ring.choose (r - m + j) j • (homComponent (m - j) c * x ^ j))
    (fun c c' ↦ by
      refine TotalChowClass.ext fun p ↦ ?_
      rw [add_apply, series_apply, series_apply, series_apply]
      simp only [map_add, add_mul, smul_add, Finset.sum_add_distrib, add_apply])

/-- The defining formula of the twist. -/
theorem twist_apply (r : ℤ) (x c : TotalChowClass C sY) :
    twist r x c = series fun m ↦ ∑ j ∈ range (m + 1),
      Ring.choose (r - m + j) j • (homComponent (m - j) c * x ^ j) :=
  rfl

/-- **The operation of a twist is the twist of the operation.** -/
theorem op_twist (r : ℤ) (x c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (twist r x c).op g = gradedTwist r (x.op g) (c.op g) := by
  rw [twist_apply, op_series, gradedTwist_apply]
  congr 1
  funext m
  rw [op_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [op_zsmul, op_mul, op_homComponent, op_pow]

variable {x : TotalChowClass C sY}

/-- **The twist is multiplicative in the class and additive in the rank:**
`T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)`, for `x` of degree `1` commuting with `d`. -/
theorem twist_mul (hx : x.IsHomogeneous 1) (r s : ℤ) (c : TotalChowClass C sY)
    {d : TotalChowClass C sY} (hxd : Commute x d) :
    twist (r + s) x (c * d) = twist r x c * twist s x d :=
  ext_op fun g _ ↦ by
    rw [op_twist, op_mul, op_mul, op_twist, op_twist]
    exact gradedTwist_mul (hx.op g) r s _ (hxd.map (opRingHom g))

/-- `T_{0,x}(1) = 1`. -/
theorem twist_zero_one (hx : x.IsHomogeneous 1) : twist 0 x (1 : TotalChowClass C sY) = 1 :=
  ext_op fun g _ ↦ by
    rw [op_twist, op_one]
    exact gradedTwist_zero_one (hx.op g)

/-- **The twist of an inverse:** `T_{-r,x}(c⁻¹) T_{r,x}(c) = 1` for a unit `c` commuting with
`x`. -/
theorem twist_inv_mul (hx : x.IsHomogeneous 1) (r : ℤ) (c : (TotalChowClass C sY)ˣ)
    (hxc : Commute x c) : twist (-r) x ↑c⁻¹ * twist r x c = 1 := by
  rw [← twist_mul hx _ _ _ hxc, neg_add_cancel, Units.inv_mul, twist_zero_one hx]

/-- **The twist of an inverse:** `T_{r,x}(c) T_{-r,x}(c⁻¹) = 1` for a unit `c` commuting with
`x`. -/
theorem twist_mul_inv (hx : x.IsHomogeneous 1) (r : ℤ) (c : (TotalChowClass C sY)ˣ)
    (hxc : Commute x c) : twist r x c * twist (-r) x ↑c⁻¹ = 1 := by
  rw [← twist_mul hx _ _ _ hxc.units_inv_right, add_neg_cancel, Units.mul_inv, twist_zero_one hx]

/-- The twist of a unit commuting with `x`, as a unit, with inverse the twist of the inverse at
the opposite rank. -/
def twistUnit (hx : x.IsHomogeneous 1) (r : ℤ) (c : (TotalChowClass C sY)ˣ)
    (hxc : Commute x c) : (TotalChowClass C sY)ˣ where
  val := twist r x c
  inv := twist (-r) x ↑c⁻¹
  val_inv := twist_mul_inv hx r c hxc
  inv_val := twist_inv_mul hx r c hxc

/-- The underlying total class of `Stacks.Chow.TotalChowClass.twistUnit`. -/
theorem coe_twistUnit (hx : x.IsHomogeneous 1) (r : ℤ) (c : (TotalChowClass C sY)ˣ)
    (hxc : Commute x c) : (twistUnit hx r c hxc : TotalChowClass C sY) = twist r x c :=
  rfl

/-- **The twist of a power `c^{±1}`**: for a unit `c` commuting with `x` and a sign `u = ±1`,
`T_{u r,x}(c^u) = T_{r,x}(c)^u`. -/
theorem twist_zpow_units (hx : x.IsHomogeneous 1) (r : ℤ) (c : (TotalChowClass C sY)ˣ)
    (hxc : Commute x c) (u : ℤˣ) :
    twist ((u : ℤ) * r) x ↑(c ^ (u : ℤ)) = ↑(twistUnit hx r c hxc ^ (u : ℤ)) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [Units.val_one, one_mul, zpow_one, coe_twistUnit]
  · simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, zpow_neg, zpow_one]
    rfl

/-- **The twist of an ordered product**: for units `c_n` commuting with `x` and ranks `r_n`,
`T_{∑ r_n,x}(∏ c_n) = ∏ T_{r_n,x}(c_n)`, the products taken in the order of a list. -/
theorem twist_list_prod (hx : x.IsHomogeneous 1) {ι : Type*} (l : List ι) (r : ι → ℤ)
    (c : ι → TotalChowClass C sY) (hxc : ∀ n ∈ l, Commute x (c n)) :
    twist (l.map r).sum x (l.map c).prod = (l.map fun n ↦ twist (r n) x (c n)).prod := by
  induction l with
  | nil => exact twist_zero_one hx
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.prod_cons,
      List.prod_cons, twist_mul hx _ _ _ ((Commute.list_prod_right _ _) fun d hd ↦ ?_),
      ih fun n hn ↦ hxc n (List.mem_cons_of_mem a hn)]
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hd
    exact hxc n (List.mem_cons_of_mem a hn)

end Twist

/-! ### The first Chern class as a total class -/

section FirstChern

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- **The first Chern class `c₁(ℒ)` as a total class**: the class `c₁(ℒ) ∈ A^1(Y)` of
Stacks 0B77 in degree `1`, and zero in every other degree. -/
def firstChernTotal : TotalChowClass C sY := fun p ↦
  if h : p = 1 then
    bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
      (show (1 : ℤ) = (p : ℤ) by simp [h]) (GenuineChern.firstChernClass C sY L)
  else 0

/-- The degree-`1` component of `c₁(ℒ)` is the class `c₁(ℒ) ∈ A^1(Y)`. -/
theorem firstChernTotal_apply_one :
    firstChernTotal C sY L 1 =
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (by simp)
        (GenuineChern.firstChernClass C sY L) :=
  dif_pos rfl

/-- The components of `c₁(ℒ)` away from degree `1` vanish. -/
theorem firstChernTotal_apply_of_ne {p : ℕ} (hp : p ≠ 1) : firstChernTotal C sY L p = 0 :=
  dif_neg hp

/-- `c₁(ℒ)` is homogeneous of degree `1`. -/
theorem isHomogeneous_firstChernTotal : (firstChernTotal C sY L).IsHomogeneous 1 :=
  fun _ hp ↦ firstChernTotal_apply_of_ne C sY L hp

/-- **The operation of `c₁(ℒ)`** on a test scheme `g : T ⟶ Y` has index-`1` component
`c₁(g^*ℒ) ∩ -`. -/
theorem op_firstChernTotal_one_heq {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    (firstChernTotal C sY L).op g k 1 α ≍
      (invCap C (g ≫ sY) ((Scheme.Modules.pullback g).obj L)).capOnChow C (g ≫ sY) (k - 1)
        (chowGroupCast C (g ≫ sY) (by omega) α) := by
  rw [op_apply, firstChernTotal_apply_one]
  exact (BivariantClass.idRule_bivariantClassDegreeCongr C _ sY _ _ g k α).trans
    (heq_of_eq (GenuineChern.idRule_firstChernClass C sY L g k α))

/-- The Chern class cap products at heterogeneously equal arguments in equal degrees. -/
theorem chernCap_heq {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F : T.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) {d₁ d₂ : ℤ} (hd : d₁ = d₂) {a : chowGroup C q d₁} {b : chowGroup C q d₂}
    (hab : a ≍ b) : GenuineChern.chernCap C r q F d₁ j a ≍ GenuineChern.chernCap C r q F d₂ j b :=
  heq_apply_of_degree C q q (fun d ↦ d) (fun d ↦ d - (j : ℤ))
    (fun d ↦ GenuineChern.chernCap C r q F d j) hd hab

/-- **`c₁(ℒ)` commutes with the total Chern class** of a finite locally free module: on every test
scheme, `c₁(g^*ℒ) ∩ -` commutes with `c_j(g^*ℰ) ∩ -`. -/
theorem commute_firstChernTotal_totalChern (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    Commute (firstChernTotal C sY L) (totalChern C sY F r) := by
  show _ * _ = _ * _
  refine ext_op fun g _ ↦ ?_
  rw [op_mul, op_mul]
  refine commute_of_isHomogeneous_one ((isHomogeneous_firstChernTotal C sY L).op g)
    fun k m α ↦ ?_
  by_cases hm : m < r + 1
  · let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
    have := isInvertible_pullback g L
    have hcomm := GenuineChern.chernCap_invCap_comm C (g ≫ sY) ((Scheme.Modules.pullback g).obj L)
      ((Scheme.Modules.pullback g).obj F) r (k - 1) ⟨m, hm⟩
      (chowGroupCast C (g ≫ sY) (by omega) α)
    rw [capTo_def, capTo_def]
    refine eq_of_heq ((gradedDegreeCast_heq _ _).trans (HEq.trans ?_
      (gradedDegreeCast_heq _ _).symm))
    rw [op_totalChern_apply C sY F r g k ⟨m, hm⟩ α]
    refine (op_firstChernTotal_one_heq C sY L g _ _).trans ?_
    refine HEq.trans ?_ (heq_of_eq (op_totalChern_apply C sY F r g _ ⟨m, hm⟩ _).symm)
    refine HEq.trans ?_ (chernCap_heq C _ _ r ⟨m, hm⟩ (by push_cast; ring)
      (op_firstChernTotal_one_heq C sY L g k α).symm)
    refine HEq.trans ?_ (heq_of_eq hcomm.symm)
    refine capOnChow_heq C _ _ (by simp only; ring) ?_
    refine (chowGroupCast_heq C _ _ _).trans (HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm)
    exact chernCap_heq C _ _ r ⟨m, hm⟩ (by ring) (chowGroupCast_heq C _ _ _).symm
  · rw [op_totalChern_of_lt C sY F r g k (by omega), AddMonoidHom.zero_apply, capTo_zero,
      capTo_of_eq_zero _ _ (op_totalChern_of_lt C sY F r g _ (by omega))]

/-- **The powers of `c₁(ℒ)`**: on a test scheme `g : T ⟶ Y` the index-`j` component of the
operation of `c₁(ℒ)^j` is `c₁(g^*ℒ)^j ∩ -`. -/
theorem op_firstChernTotal_pow_heq {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (j : ℕ) (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    letI := isInvertible_pullback g L
    ((firstChernTotal C sY L).op g ^ j) k j α ≍
      capPow C (g ≫ sY) (invCap C (g ≫ sY) ((Scheme.Modules.pullback g).obj L)) j k
        (k - (j : ℤ)) (by ring) α := by
  let := isInvertible_pullback g L
  induction j generalizing k with
  | zero =>
    rw [pow_zero, gradedCap_one_apply_zero, capPow_zero_apply]
    exact (gradedDegreeCast_heq _ α).trans (chowGroupCast_heq C _ _ α).symm
  | succ j ih =>
    rw [pow_succ, gradedCap_mul_succ_of_isHomogeneous_one_right
      ((isHomogeneous_firstChernTotal C sY L).op g), capTo_def, capPow_succ_apply]
    refine (gradedDegreeCast_heq _ _).trans ((ih (k - 1) _).trans ?_)
    exact GenuineChern.capPow_heq C _ _ _ _ rfl rfl (by push_cast; ring)
      (op_firstChernTotal_one_heq C sY L g k α)

/-- **From the cap products to the total Chern classes.** If on every test scheme `g : T ⟶ Y`
the Chern class cap products of `g^*ℰ'` are given by the formula of Stacks 02UD in terms of
those of `g^*ℰ` and of `c₁(g^*ℒ)`, then `c(ℰ') = T_{r,c₁(ℒ)}(c(ℰ))`. -/
theorem totalChern_eq_twist_of_chernCap (E E' : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (hcap : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g],
      letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r g
      letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E' r g
      letI := isInvertible_pullback g L
      ∀ (k : ℤ) (i : Fin (r + 1)) (α : chowGroup C (g ≫ sY) k),
        GenuineChern.chernCap C r (g ≫ sY) ((Scheme.Modules.pullback g).obj E') k i α =
          ∑ j : Fin ((i : ℕ) + 1), ((r - i + j : ℕ).choose j : ℤ) •
            chowGroupCast C (g ≫ sY) (by simp only; omega)
              (GenuineChern.chernCap C r (g ≫ sY) ((Scheme.Modules.pullback g).obj E)
                (k - (j : ℤ)) ⟨(i : ℕ) - j, by omega⟩
                (capPow C (g ≫ sY) (invCap C (g ≫ sY) ((Scheme.Modules.pullback g).obj L)) j k
                  (k - (j : ℤ)) (by ring) α))) :
    totalChern C sY E' r = twist (r : ℤ) (firstChernTotal C sY L) (totalChern C sY E r) := by
  refine ext_op fun g _ ↦ ?_
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r g
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E' r g
  let := isInvertible_pullback g L
  rw [op_twist]
  funext k m
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [gradedTwist_apply, gradedSeries_apply, gradedCap_sum_apply, Finset.sum_range]
  have hjm : ∀ j : Fin (m + 1), (j : ℕ) ≤ m := fun j ↦ Nat.lt_succ_iff.mp j.isLt
  have hterm : ∀ j : Fin (m + 1),
      (Ring.choose ((r : ℤ) - m + (j : ℕ)) j • (Stacks.Chow.homComponent (m - j)
          ((totalChern C sY E r).op g) * (firstChernTotal C sY L).op g ^ (j : ℕ))) k m α =
        Ring.choose ((r : ℤ) - m + (j : ℕ)) j • capTo ((totalChern C sY E r).op g) (m - j)
          (by have := j.isLt; omega) (((firstChernTotal C sY L).op g ^ (j : ℕ)) k j α) := by
    intro j
    rw [Pi.smul_apply, Pi.smul_apply, AddMonoidHom.smul_apply,
      gradedCap_mul_apply_of_isHomogeneous_right
        (((isHomogeneous_firstChernTotal C sY L).op g).pow j) _ k (hjm j),
      capTo_def, capTo_def, Stacks.Chow.homComponent_apply_self]
  simp only [hterm]
  by_cases hm : m < r + 1
  · rw [op_totalChern_apply C sY E' r g k ⟨m, hm⟩ α, hcap g k ⟨m, hm⟩ α]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    · simp only [Fin.val_mk]
      rw [show (r : ℤ) - m + (j : ℕ) = ((r - m + j : ℕ) : ℤ) by omega, Ring.choose_natCast]
    · rw [capTo_def]
      refine eq_of_heq ((chowGroupCast_heq C _ _ _).trans (HEq.trans ?_
        (gradedDegreeCast_heq _ _).symm))
      rw [op_totalChern_apply C sY E r g _ ⟨m - j, by omega⟩]
      exact chernCap_heq C _ _ r _ (by ring) (op_firstChernTotal_pow_heq C sY L g j k α).symm
  · rw [op_totalChern_of_lt C sY E' r g k (by omega), AddMonoidHom.zero_apply]
    refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
    by_cases hj : r < m - j
    · rw [capTo_of_eq_zero _ _ (op_totalChern_of_lt C sY E r g _ hj), smul_zero]
    · rw [show (r : ℤ) - m + (j : ℕ) = ((r + j - m : ℕ) : ℤ) by omega, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

/-- **Stacks 02UD for total classes**: for `ℰ` finite locally free of rank `r` and `ℒ`
invertible, `c(ℰ ⊗ ℒ) = T_{r,c₁(ℒ)}(c(ℰ))`, that is,
`c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) c₁(ℒ)^j`.

This is the identity of Stacks 02UD in the Chow cohomology of `Y`. It holds in every degree `i`
separately, as `Stacks.Chow.TotalChowClass.totalChern_sheafTensor_degree` states. -/
@[stacks 02UD "Equation (02UE) in A^*(X), as the single identity c(E tensor L) = \
  T_{r,c_1(L)}(c(E)) of total Chow cohomology classes, under the source's hypotheses and no \
  others. It is Equation (02UE) in each degree i by \
  Stacks.Chow.TotalChowClass.totalChern_sheafTensor_degree"]
theorem totalChern_sheafTensor (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    -- `totalChern` reads the rank of a `Y.Modules`, so it asks for the twist's rank at
    -- `Y.ringCatSheaf`, while `GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor` states it at
    -- the native `Tensor.ringSheaf Y.sheaf`. The two are the same sheaf of rings, but only
    -- after unfolding the `Tensor.ringSheaf` def, which instance search does not do, so the
    -- twist's rank is handed over by name at the spelling the statement needs.
    letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (R := Y.ringCatSheaf)
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r :=
      GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor E r L
    totalChern C sY (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r =
      twist (r : ℤ) (firstChernTotal C sY L) (totalChern C sY E r) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Y.ringCatSheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r :=
    GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor E r L
  refine totalChern_eq_twist_of_chernCap C sY L E _ r fun {T} g _ ↦ ?_
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r g
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r g
  let := isInvertible_pullback g L
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := T.ringCatSheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor T.sheaf).obj
        ((Scheme.Modules.pullback g).obj E)).obj ((Scheme.Modules.pullback g).obj L)) r :=
    GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor ((Scheme.Modules.pullback g).obj E) r
      ((Scheme.Modules.pullback g).obj L)
  intro k i α
  rw [GenuineChern.chernCap_congr C (g ≫ sY) r (sheafTensorPullbackIso g E L) k i α]
  exact GenuineChern.chernCap_sheafTensor C (g ≫ sY) _ r _ k i α

/-- **Equation (02UE) of Stacks 02UD in degree `i`**: for `ℰ` finite locally free of rank `r`
and `ℒ` invertible,

  `c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) c₁(ℒ)^j`

in `A^i(Y)`, the `j`-th summand being the degree-`i` part of the product of `c_{i-j}(ℰ)` with
`c₁(ℒ)^j`, that is their product `A^{i-j}(Y) × A^j(Y) ⟶ A^i(Y)` of Stacks 0B75. -/
theorem totalChern_sheafTensor_degree (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (i : ℕ) :
    -- The twist's rank is handed over by name at the spelling `totalChern` needs, exactly as in
    -- `totalChern_sheafTensor`: `Y.ringCatSheaf` and `Tensor.ringSheaf Y.sheaf` are the same
    -- sheaf of rings only after the `Tensor.ringSheaf` def unfolds, which instance search for
    -- `IsFiniteLocallyFreeOfRank` does not do.
    letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (R := Y.ringCatSheaf)
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r :=
      GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor E r L
    totalChern C sY (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r i =
      ∑ j ∈ range (i + 1), Ring.choose ((r : ℤ) - i + j) j •
        (homComponent (i - j) (totalChern C sY E r) * firstChernTotal C sY L ^ j) i := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Y.ringCatSheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj E).obj L) r :=
    GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor E r L
  rw [totalChern_sheafTensor C sY L E r, twist_apply, series_apply, sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ rfl

end FirstChern

/-! ### The twist of a bounded complex -/

section Complex

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (P : CochainComplex Y.Modules ℤ) (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- **The twist of the total Chern class of a bounded complex**: for a complex `P` whose `n`-th
term is finite locally free of rank `ρ n`, with `ρ` finitely supported, and an invertible module
`ℳ`, the termwise twist `P ⊗ ℳ` has

  `c(P ⊗ ℳ) = T_{r,c₁(ℳ)}(c(P))`,  `r = ∑_n (-1)^n ρ n`,

the factor `c(P^n ⊗ ℳ)^{(-1)^n} = T_{(-1)^n ρ n, c₁(ℳ)}(c(P^n)^{(-1)^n})` of each term being
Stacks 02UD for total classes. -/
theorem complexChernBounded_twistComplex (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hPM : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((twistComplex P M).X n) (ρ n)) :
    complexChernBounded C sY (twistComplex P M) ρ hPM =
      twist (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ)) (firstChernTotal C sY M)
        (complexChernBounded C sY P ρ hP) := by
  have hx := isHomogeneous_firstChernTotal C sY M
  have hcomm : ∀ n, let := hP n
      Commute (firstChernTotal C sY M) (totalChernUnit C sY (P.X n) (ρ n) : TotalChowClass C sY) :=
    fun n ↦ by
      let := hP n
      exact commute_firstChernTotal_totalChern C sY M (P.X n) (ρ n)
  have hfac : ∀ n, (complexChernFactor C sY (twistComplex P M) ρ hPM n : TotalChowClass C sY) =
      twist ((n.negOnePow : ℤ) * (ρ n : ℤ)) (firstChernTotal C sY M)
        (complexChernFactor C sY P ρ hP n) := by
    intro n
    let := hP n
    let := hPM n
    have hunit : totalChernUnit C sY ((twistComplex P M).X n) (ρ n) =
        twistUnit hx (ρ n) (totalChernUnit C sY (P.X n) (ρ n)) (hcomm n) :=
      Units.ext (totalChern_sheafTensor C sY M (P.X n) (ρ n))
    rw [complexChernFactor, complexChernFactor, twist_zpow_units hx _ _ (hcomm n), hunit]
  have hsum : (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ)) =
      ((ρ.support.sort (· ≤ ·)).map fun n ↦ (n.negOnePow : ℤ) * (ρ n : ℤ)).sum := by
    rw [finsum_eq_sum_of_support_subset _ (s := ρ.support) fun n hn ↦ ?_,
      ← List.sum_toFinset _ (ρ.support.sort_nodup _), Finset.sort_toFinset]
    refine Finsupp.mem_support_iff.mpr fun h0 ↦ hn ?_
    simp [h0]
  have hcoe : ∀ l : List (TotalChowClass C sY)ˣ,
      ((l.prod : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) = (l.map Units.val).prod :=
    fun l ↦ map_list_prod (Units.coeHom (TotalChowClass C sY)) l
  rw [complexChernBounded, complexChernBounded, complexChernProd, complexChernProd, hsum,
    hcoe, hcoe, List.map_map, List.map_map,
    twist_list_prod hx _ _ _ fun n _ ↦ ?_]
  · congr 1
    exact List.map_congr_left fun n _ ↦ hfac n
  · let := hP n
    exact (hcomm n).units_zpow_right _

end Complex

end TotalChowClass

end Stacks.Chow

end
