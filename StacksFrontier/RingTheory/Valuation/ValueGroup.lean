module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

-- Stacks tag 00IG: https://stacks.math.columbia.edu/tag/00IG
-- Given a totally ordered abelian group `Γ`, a field `K` and a homomorphism
-- `v : Kˣ → Γ` with `v(a+b) ≥ min (v a) (v b)`, the set `A = {x | x = 0 ∨ v x ≥ 0}`
-- is a valuation ring with value group `Im(v) ⊆ Γ`, maximal ideal `{x | x = 0 ∨ v x > 0}`
-- and units `{x | v x = 0}`.

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {K : Type*} [Field K]

/-- A Stacks-00IG valuation on a field `K`: a homomorphism `v : Kˣ → Γ` of abelian
groups, where `Γ` is a totally ordered abelian group, satisfying the ultrametric
inequality `min (v a) (v b) ≤ v (a + b)` whenever `a, b, a + b` are all nonzero. -/
structure StacksValuation (K Γ : Type*) [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] where
  /-- The underlying map `Kˣ → Γ`. -/
  toFun : Kˣ → Γ
  /-- `v` is a group homomorphism. -/
  map_mul' : ∀ a b : Kˣ, toFun (a * b) = toFun a + toFun b
  /-- The ultrametric inequality, for `a, b, a + b` all nonzero. -/
  map_add' : ∀ (a b : Kˣ) (h : (a : K) + (b : K) ≠ 0),
      min (toFun a) (toFun b) ≤ toFun (Units.mk0 ((a : K) + (b : K)) h)

namespace StacksValuation

variable (sv : StacksValuation K Γ)

/-- A Stacks-00IG valuation sends the unit `1` to `0`. -/
lemma toFun_one : sv.toFun 1 = 0 := by
  have h := sv.map_mul' 1 1
  rw [mul_one] at h
  have h2 : sv.toFun 1 + sv.toFun 1 = sv.toFun 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- A Stacks-00IG valuation sends an inverse to the negative of its value. -/
lemma toFun_inv (u : Kˣ) : sv.toFun u⁻¹ = -sv.toFun u := by
  have h := sv.map_mul' u u⁻¹
  rw [mul_inv_cancel, sv.toFun_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

open Classical in
/-- The total `WithTop Γ`-valued additive valuation extending `v`, sending `0 ↦ ⊤`. -/
noncomputable def rawVal (x : K) : WithTop Γ :=
  if h : x = 0 then ⊤ else (sv.toFun (Units.mk0 x h) : WithTop Γ)

/-- `rawVal` sends `0` to `⊤`. -/
lemma rawVal_zero : sv.rawVal 0 = ⊤ := dite_eq_left rfl

/-- On a nonzero element, `rawVal` is the value of `v` on the corresponding unit. -/
lemma rawVal_of_ne_zero {x : K} (hx : x ≠ 0) :
    sv.rawVal x = (sv.toFun (Units.mk0 x hx) : WithTop Γ) := dite_eq_right hx

/-- `rawVal` sends `1` to `0`. -/
lemma rawVal_one : sv.rawVal (1 : K) = 0 := by
  rw [rawVal_of_ne_zero sv one_ne_zero, Units.mk0_one, sv.toFun_one, WithTop.coe_zero]

/-- `rawVal` is additive on products. -/
lemma rawVal_mul (x y : K) : sv.rawVal (x * y) = sv.rawVal x + sv.rawVal y := by
  by_cases hx : x = 0
  · subst hx; simp [rawVal_zero, zero_mul, top_add]
  · by_cases hy : y = 0
    · subst hy; simp [rawVal_zero, mul_zero, add_top]
    · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      rw [rawVal_of_ne_zero sv hxy, rawVal_of_ne_zero sv hx, rawVal_of_ne_zero sv hy,
        ← WithTop.coe_add]
      congr 1
      rw [← sv.map_mul']
      congr 1
      ext; simp

/-- The ultrametric inequality for `rawVal`, valid for all `x, y : K`. -/
lemma rawVal_add (x y : K) : min (sv.rawVal x) (sv.rawVal y) ≤ sv.rawVal (x + y) := by
  by_cases hx : x = 0
  · subst hx; rw [zero_add]; exact min_le_right _ _
  · by_cases hy : y = 0
    · subst hy; rw [add_zero]; exact min_le_left _ _
    · by_cases hxy : x + y = 0
      · rw [hxy, rawVal_zero]; exact le_top
      · rw [rawVal_of_ne_zero sv hx, rawVal_of_ne_zero sv hy, rawVal_of_ne_zero sv hxy,
          ← WithTop.coe_min, WithTop.coe_le_coe]
        have hne : ((Units.mk0 x hx : K) + (Units.mk0 y hy : K)) ≠ 0 := by simpa using hxy
        have key := sv.map_add' (Units.mk0 x hx) (Units.mk0 y hy) hne
        have hu : Units.mk0 ((Units.mk0 x hx : K) + (Units.mk0 y hy : K)) hne
            = Units.mk0 (x + y) hxy := by ext; simp
        rwa [hu] at key

/-- The additive valuation `K → WithTop Γ` associated to a Stacks-00IG valuation. -/
noncomputable def addVal : AddValuation K (WithTop Γ) :=
  AddValuation.of sv.rawVal sv.rawVal_zero sv.rawVal_one sv.rawVal_add sv.rawVal_mul

/-- `addVal` agrees with `rawVal` pointwise. -/
lemma addVal_apply (x : K) : sv.addVal x = sv.rawVal x := rfl

/-- The valuation ring `A = {x ∈ K | x = 0 ∨ v x ≥ 0}` of Stacks 00IG. -/
noncomputable def integerSubring : Subring K where
  carrier := {x | 0 ≤ sv.addVal x}
  zero_mem' := by
    change 0 ≤ sv.addVal 0
    rw [AddValuation.map_zero]; exact le_top
  one_mem' := by
    change 0 ≤ sv.addVal 1
    exact le_of_eq (AddValuation.map_one sv.addVal).symm
  mul_mem' := by
    intro a b ha hb
    change 0 ≤ sv.addVal (a * b)
    rw [AddValuation.map_mul]
    exact add_nonneg ha hb
  add_mem' := by
    intro a b ha hb
    change 0 ≤ sv.addVal (a + b)
    exact le_trans (le_min ha hb) (AddValuation.map_add sv.addVal a b)
  neg_mem' := by
    intro a ha
    change 0 ≤ sv.addVal (-a)
    rw [AddValuation.map_neg]; exact ha

/-- Membership in `A`: `x ∈ A` iff `0 ≤ v x` in `WithTop Γ`. -/
lemma mem_integerSubring {x : K} : x ∈ sv.integerSubring ↔ 0 ≤ sv.addVal x := Iff.rfl

/-- Faithful rendering of the carrier of `A`: `x ∈ A` iff `x = 0` or `v x ≥ 0`. -/
lemma mem_integerSubring_iff (x : K) :
    x ∈ sv.integerSubring ↔ x = 0 ∨ ∃ h : x ≠ 0, 0 ≤ sv.toFun (Units.mk0 x h) := by
  rw [mem_integerSubring]
  by_cases h : x = 0
  · subst h; rw [addVal_apply, rawVal_zero]; simp
  · rw [addVal_apply, rawVal_of_ne_zero sv h, ← WithTop.coe_zero, WithTop.coe_le_coe]
    constructor
    · exact fun hg => Or.inr ⟨h, hg⟩
    · rintro (rfl | ⟨h', hg⟩)
      · exact (h rfl).elim
      · exact hg

/-- If `v a ≤ v b` with `a ≠ 0`, then `b / a` lies in `A`. -/
lemma div_mem_integerSubring_of_le {a b : K} (ha : a ≠ 0) (hab : sv.addVal a ≤ sv.addVal b) :
    b / a ∈ sv.integerSubring := by
  have hav : sv.addVal a ≠ ⊤ := fun h => ha (sv.addVal.top_iff.mp h)
  rw [mem_integerSubring, ← WithTop.add_le_add_iff_left hav, add_zero,
    ← AddValuation.map_mul, mul_div_cancel₀ b ha]
  exact hab

/-- `A = {x ∈ K | 0 ≤ v x}` is a valuation ring. -/
instance instValuationRing : ValuationRing sv.integerSubring :=
  { cond' := by
      rintro a b
      by_cases ha : (a : K) = 0
      · exact ⟨0, Or.inr (by simp [Subtype.ext_iff, ha])⟩
      by_cases hb : (b : K) = 0
      · exact ⟨0, Or.inl (by simp [Subtype.ext_iff, hb])⟩
      rcases le_total (sv.addVal (a : K)) (sv.addVal (b : K)) with hab | hab
      · exact ⟨⟨_, sv.div_mem_integerSubring_of_le ha hab⟩,
          Or.inl (Subtype.ext (mul_div_cancel₀ _ ha))⟩
      · exact ⟨⟨_, sv.div_mem_integerSubring_of_le hb hab⟩,
          Or.inr (Subtype.ext (mul_div_cancel₀ _ hb))⟩ }

/-- The group of units of `A` is `{x ∈ Kˣ | v x = 0}`. -/
lemma isUnit_iff_addVal_eq_zero (x : sv.integerSubring) : IsUnit x ↔ sv.addVal (x : K) = 0 := by
  refine ⟨fun hu ↦ ?_, fun hx0 ↦ ?_⟩
  · obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    have hxy : (x : K) * (y : K) = 1 := by simpa using congrArg Subtype.val hy
    have hsum : sv.addVal (x : K) + sv.addVal (y : K) = 0 := by
      rw [← AddValuation.map_mul sv.addVal (x : K) (y : K), hxy, AddValuation.map_one]
    have hax : 0 ≤ sv.addVal (x : K) := sv.mem_integerSubring.mp x.property
    have hay : 0 ≤ sv.addVal (y : K) := sv.mem_integerSubring.mp y.property
    exact le_antisymm ((le_add_of_nonneg_right hay).trans_eq hsum) hax
  · have hxne : (x : K) ≠ 0 := fun h => by simp [h] at hx0
    have hyA : (x : K)⁻¹ ∈ sv.integerSubring := by
      rw [mem_integerSubring, AddValuation.map_inv, hx0, neg_zero]
    have hmul1 : x * (⟨(x : K)⁻¹, hyA⟩ : sv.integerSubring) = 1 :=
      Subtype.ext (mul_inv_cancel₀ hxne)
    exact IsUnit.of_mul_eq_one _ hmul1

/-- Valuation ring, unit group and maximal ideal of `A = {x ∈ K | x = 0 ∨ v x ≥ 0}`
(the first three clauses of Stacks 00IG), together with the fact that `Set.range v` is
an additive subgroup of `Γ`. The complete statement of Stacks 00IG, including the
identification of the value group `Kˣ/A*` of `A` with `Im(v)` as ordered groups, is
`StacksValuation.isValuationRing_valueGroup`. -/
theorem isValuationRing :
    -- `A` is a valuation ring.
    ValuationRing sv.integerSubring ∧
    -- The group of units of `A` is `{x | v x = 0}`.
    (∀ x : sv.integerSubring, IsUnit x ↔ sv.addVal (x : K) = 0) ∧
    -- The maximal ideal of `A` is `m = {x | v x > 0}`.
    (∀ x : sv.integerSubring,
      x ∈ IsLocalRing.maximalIdeal sv.integerSubring ↔ 0 < sv.addVal (x : K)) ∧
    -- The value group `Im(v) ⊆ Γ` is an additive subgroup of `Γ`.
    ((0 : Γ) ∈ Set.range sv.toFun ∧
      (∀ g ∈ Set.range sv.toFun, ∀ g' ∈ Set.range sv.toFun, g + g' ∈ Set.range sv.toFun) ∧
      (∀ g ∈ Set.range sv.toFun, -g ∈ Set.range sv.toFun)) := by
  refine ⟨inferInstance, sv.isUnit_iff_addVal_eq_zero, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, sv.isUnit_iff_addVal_eq_zero x]
    have hx : 0 ≤ sv.addVal (x : K) := sv.mem_integerSubring.mp x.property
    exact ⟨fun hne => lt_of_le_of_ne hx (Ne.symm hne), ne_of_gt⟩
  · exact ⟨1, sv.toFun_one⟩
  · rintro _ ⟨ua, rfl⟩ _ ⟨ub, rfl⟩
    exact ⟨ua * ub, sv.map_mul' ua ub⟩
  · rintro _ ⟨ua, rfl⟩
    exact ⟨ua⁻¹, sv.toFun_inv ua⟩

/-- The image `Im(v) ⊆ Γ` of a Stacks-00IG valuation, as an additive subgroup of `Γ`. -/
def valueSubgroup : AddSubgroup Γ where
  carrier := Set.range sv.toFun
  zero_mem' := ⟨1, sv.toFun_one⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, sv.map_mul' a b⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, sv.toFun_inv a⟩

/-- `v : Kˣ → Im(v)`, written multiplicatively. -/
def toValueSubgroup : Kˣ →* Multiplicative sv.valueSubgroup where
  toFun x := Multiplicative.ofAdd ⟨sv.toFun x, x, rfl⟩
  map_one' := Multiplicative.toAdd.injective (Subtype.ext sv.toFun_one)
  map_mul' x y := Multiplicative.toAdd.injective (Subtype.ext (sv.map_mul' x y))

/-- `v : Kˣ → Im(v)` is surjective. -/
lemma toValueSubgroup_surjective : Function.Surjective sv.toValueSubgroup := by
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

/-- The value of `toValueSubgroup x` in `Γ` is `v x`. -/
lemma toAdd_toValueSubgroup (x : Kˣ) :
    ((Multiplicative.toAdd (sv.toValueSubgroup x) : sv.valueSubgroup) : Γ) = sv.toFun x := rfl

/-- Every `x : K` satisfies `x ∈ A` or `x⁻¹ ∈ A`. -/
lemma mem_or_inv_mem_integerSubring (x : K) :
    x ∈ sv.integerSubring ∨ x⁻¹ ∈ sv.integerSubring := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx]; exact zero_mem sv.integerSubring)
  · rcases le_total 0 (sv.toFun (Units.mk0 x hx)) with h | h
    · exact Or.inl ((sv.mem_integerSubring_iff x).mpr (Or.inr ⟨hx, h⟩))
    · refine Or.inr ((sv.mem_integerSubring_iff _).mpr (Or.inr ⟨inv_ne_zero hx, ?_⟩))
      have hu : Units.mk0 x⁻¹ (inv_ne_zero hx) = (Units.mk0 x hx)⁻¹ := Units.ext (by simp)
      rw [hu, sv.toFun_inv]
      exact neg_nonneg.mpr h

/-- `A = {x ∈ K | x = 0 ∨ v x ≥ 0}`, as a valuation subring of `K`. -/
noncomputable def valuationSubring : ValuationSubring K :=
  ValuationSubring.ofSubring sv.integerSubring sv.mem_or_inv_mem_integerSubring

/-- The underlying subring of `sv.valuationSubring` is `sv.integerSubring`. -/
lemma valuationSubring_toSubring : sv.valuationSubring.toSubring = sv.integerSubring := rfl

/-- For `x, y ∈ Kˣ`, the class of `x` is `≤` the class of `y` in the value group `K / A*`
(i.e. `x / y ∈ A`) iff `v y ≤ v x`. -/
lemma valuation_le_valuation_iff (x y : Kˣ) :
    sv.valuationSubring.valuation (x : K) ≤ sv.valuationSubring.valuation (y : K) ↔
      sv.toFun y ≤ sv.toFun x := by
  rw [ValuationSubring.valuation_le_iff]
  have hval : sv.toFun (x / y) = sv.toFun x - sv.toFun y := by
    rw [div_eq_mul_inv, sv.map_mul', sv.toFun_inv, sub_eq_add_neg]
  have hmem : ((x / y : Kˣ) : K) ∈ sv.integerSubring ↔ sv.toFun y ≤ sv.toFun x := by
    rw [sv.mem_integerSubring_iff, ← sub_nonneg, ← hval]
    refine ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨(x / y).ne_zero, by rwa [Units.mk0_val]⟩⟩
    rcases h with h | ⟨_, hv⟩
    · exact absurd h (x / y).ne_zero
    · rwa [Units.mk0_val] at hv
  rw [← hmem]
  constructor
  · rintro ⟨a, ha⟩
    have : ((x / y : Kˣ) : K) = a := by
      rw [Units.val_div_eq_div_val, ← ha, mul_div_cancel_right₀ _ y.ne_zero]
    rw [this]
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, by simp⟩

/-- The map `Kˣ → (K / A*)ˣ = Kˣ / A*` sending `x` to its class. -/
noncomputable def toValueGroupUnits : Kˣ →* sv.valuationSubring.ValueGroupˣ :=
  Units.map (sv.valuationSubring.valuation : K →* sv.valuationSubring.ValueGroup)

lemma coe_toValueGroupUnits (x : Kˣ) :
    (sv.toValueGroupUnits x : sv.valuationSubring.ValueGroup) =
      sv.valuationSubring.valuation (x : K) := rfl

lemma toValueGroupUnits_surjective : Function.Surjective sv.toValueGroupUnits := by
  intro u
  obtain ⟨x, hx⟩ := sv.valuationSubring.valuation_surjective (u : sv.valuationSubring.ValueGroup)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hx
    exact u.ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, Units.ext hx⟩

lemma toValueGroupUnits_le_iff (x y : Kˣ) :
    sv.toValueGroupUnits x ≤ sv.toValueGroupUnits y ↔ sv.toFun y ≤ sv.toFun x := by
  rw [← Units.val_le_val, coe_toValueGroupUnits, coe_toValueGroupUnits,
    sv.valuation_le_valuation_iff]

lemma ker_toValueGroupUnits : sv.toValueGroupUnits.ker = sv.toValueSubgroup.ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  rw [← map_one sv.toValueGroupUnits, le_antisymm_iff, sv.toValueGroupUnits_le_iff,
    sv.toValueGroupUnits_le_iff, ← le_antisymm_iff, sv.toFun_one]
  constructor
  · intro h
    exact Multiplicative.toAdd.injective (Subtype.ext h.symm)
  · intro h
    exact (congrArg (fun z ↦ ((Multiplicative.toAdd z : sv.valueSubgroup) : Γ)) h).symm

/-- The isomorphism `Kˣ / A* ≅ Im(v)` induced by `v`, from the value group of `A`
(the nonzero part `(K / A*)ˣ` of `ValuationRing.ValueGroup`) to `Im(v)`, written
multiplicatively. -/
noncomputable def valueGroupEquiv :
    sv.valuationSubring.ValueGroupˣ ≃* Multiplicative sv.valueSubgroup :=
  ((QuotientGroup.quotientKerEquivOfSurjective _ sv.toValueGroupUnits_surjective).symm.trans
    (QuotientGroup.quotientMulEquivOfEq sv.ker_toValueGroupUnits)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ sv.toValueSubgroup_surjective)

/-- `valueGroupEquiv` sends the class of `x ∈ Kˣ` to `v x`. -/
lemma valueGroupEquiv_toValueGroupUnits (x : Kˣ) :
    sv.valueGroupEquiv (sv.toValueGroupUnits x) = sv.toValueSubgroup x := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _ sv.toValueGroupUnits_surjective).symm
      (sv.toValueGroupUnits x) = (x : Kˣ ⧸ sv.toValueGroupUnits.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [valueGroupEquiv, MulEquiv.trans_apply, h]
  rfl

/-- **Stacks 00IG** (`lemma-valuation-valuation-ring`).
Let `(Γ, ≥)` be a totally ordered abelian group, `K` a field, and `v : Kˣ → Γ` a
group homomorphism with `v(a + b) ≥ min (v a) (v b)` for `a, b, a + b` nonzero.
Then `A = {x ∈ K | x = 0 ∨ v x ≥ 0}` is a valuation ring with value group
`Im(v) ⊆ Γ`, with maximal ideal `m = {x ∈ K | x = 0 ∨ v x > 0}` and group of units
`A* = {x ∈ Kˣ | v x = 0}`.

The value group of `A` (Stacks 00ID/00IE) is `Kˣ/A*`; in the library it is the
nonzero part `(ValuationRing.ValueGroup A K)ˣ` of `K / A*`, written multiplicatively
and ordered by `[x] ≤ [y] ↔ x / y ∈ A` (the reverse of the additive order `≥` of
Stacks). The last clause gives a group isomorphism `e : Kˣ/A* ≅ Im(v)` induced by `v`
(it sends the class of `x` to `v x`), which is an isomorphism of ordered groups for
these conventions. Here `A` is `sv.valuationSubring`, whose underlying subring is
`sv.integerSubring`. -/
@[stacks 00IG "The value group Kˣ/A* is (ValuationRing.ValueGroup A K)ˣ, multiplicative \
and ordered by [x] ≤ [y] iff x/y ∈ A; the isomorphism with Im(v) sends the class of x to v x."]
theorem isValuationRing_valueGroup :
    -- `A` is a valuation ring.
    ValuationRing sv.integerSubring ∧
    -- The group of units of `A` is `{x | v x = 0}`.
    (∀ x : sv.integerSubring, IsUnit x ↔ sv.addVal (x : K) = 0) ∧
    -- The maximal ideal of `A` is `m = {x | v x > 0}`.
    (∀ x : sv.integerSubring,
      x ∈ IsLocalRing.maximalIdeal sv.integerSubring ↔ 0 < sv.addVal (x : K)) ∧
    -- `sv.valuationSubring` is `A`, as a valuation subring of `K`.
    sv.valuationSubring.toSubring = sv.integerSubring ∧
    -- The value group `Kˣ/A*` of `A` is isomorphic to `Im(v) ⊆ Γ` as an ordered group,
    -- by the isomorphism induced by `v`.
    ∃ e : sv.valuationSubring.ValueGroupˣ ≃* Multiplicative sv.valueSubgroup,
      (∀ x : Kˣ, ((Multiplicative.toAdd
          (e (Units.map (sv.valuationSubring.valuation : K →* sv.valuationSubring.ValueGroup)
            x)) : sv.valueSubgroup) : Γ) = sv.toFun x) ∧
      ∀ a b : sv.valuationSubring.ValueGroupˣ,
        a ≤ b ↔ Multiplicative.toAdd (e b) ≤ Multiplicative.toAdd (e a) := by
  obtain ⟨h1, h2, h3, -⟩ := sv.isValuationRing
  refine ⟨h1, h2, h3, rfl, sv.valueGroupEquiv, fun x ↦ ?_, fun a b ↦ ?_⟩
  · exact congrArg Subtype.val (congrArg Multiplicative.toAdd
      (sv.valueGroupEquiv_toValueGroupUnits x))
  · obtain ⟨x, rfl⟩ := sv.toValueGroupUnits_surjective a
    obtain ⟨y, rfl⟩ := sv.toValueGroupUnits_surjective b
    rw [sv.toValueGroupUnits_le_iff, sv.valueGroupEquiv_toValueGroupUnits,
      sv.valueGroupEquiv_toValueGroupUnits]
    exact Iff.rfl

end StacksValuation

-- ===== merged from StacksDraft.Ch10.Sec50.Tag00IH =====

/-!
# Ideals of a valuation ring correspond to ideals of the value group

This is Stacks project Lemma 10.50.17 (tag `00IH`), Commutative Algebra,
Section 10.50 (Valuation rings).

Let `A` be a valuation ring with fraction field `K`, value group `Γ` and
valuation `v : K^* → Γ`.  There are two maps

  `Φ : Id(A) → Id(Γ)`,   `Φ(𝔞) = v(𝔞 \ {0}) = { v(x) : x ∈ 𝔞, x ≠ 0 }`,
  `Ψ : Id(Γ) → Id(A)`,   `Ψ(I) = { x ∈ A : x = 0 ∨ v(x) ∈ I }`,

where `Id(A)` is the set of ideals of `A` and `Id(Γ)` is the set of ideals of
the totally ordered abelian group `Γ`.  The lemma asserts that `Φ` and `Ψ` are
mutually inverse, inclusion preserving, and restrict to a bijection between
prime ideals.

## Convention: multiplicative-with-zero value group

We use the canonical Mathlib object `ValuationRing.ValueGroup A K`, which is
`K / A^*` together with a `LinearOrderedCommGroupWithZero` structure and the
valuation `v = ValuationRing.valuation A K : Valuation K (ValueGroup A K)`.
This is `Γ` together with an extra zero element `0 = v(0)`, written
*multiplicatively*, and with the order *reversed* relative to the additive
picture.  The dictionary is:

  * additive `γ + γ'`            ↔ multiplicative `γ * γ'`;
  * additive identity `0`        ↔ multiplicative identity `1`;
  * additive `γ ≥ 0` (so `γ` is the value of some `a ∈ A \ {0}`)
                                 ↔ multiplicative `γ ≠ 0 ∧ γ ≤ 1`;
  * additive `γ' ≥ γ`            ↔ multiplicative `γ' ≤ γ`.

Under this dictionary the notions of ideal and prime ideal of `Γ` become
`IsIdealGamma` and `IsPrimeIdealGamma`, and the maps `Φ`, `Ψ` become `gammaPhi`,
`gammaPsi`.
-/

@[expose] public section

variable (A : Type*) [CommRing A] (K : Type*) [Field K] [Algebra A K]
  [IsDomain A] [ValuationRing A] [IsFractionRing A K]

/-- The value group `Γ_0 = K / A^*` as a `LinearOrderedCommGroupWithZero`. -/
abbrev Gamma := ValuationRing.ValueGroup A K

/-- The valuation `v : K → Γ_0`. -/
noncomputable abbrev gammaVal : Valuation K (Gamma A K) := ValuationRing.valuation A K

/-- **Ideal of `Γ`**, in the multiplicative-with-zero picture.
A subset `I ⊆ Γ_0` is an *ideal of `Γ`* iff:
* every element of `I` is in `Γ_{≥0}`, i.e. is nonzero and `≤ 1`
  (the additive `γ ≥ 0`); and
* `I` is "upward closed" in the additive order, i.e. *downward* closed here:
  if `γ ∈ I` and `γ'` is nonzero with `γ' ≤ γ`, then `γ' ∈ I`. -/
def IsIdealGamma (I : Set (Gamma A K)) : Prop :=
  (∀ γ ∈ I, γ ≠ 0 ∧ γ ≤ 1) ∧
  (∀ γ γ' : Gamma A K, γ ∈ I → γ' ≠ 0 → γ' ≤ γ → γ' ∈ I)

/-- **Prime ideal of `Γ`**, in the multiplicative-with-zero
picture.  An ideal `I` of `Γ` is *prime* iff `0 ∉ I` (additively), i.e.
`1 ∉ I` (multiplicatively), and for `γ, γ' ∈ Γ_{≥0}` (nonzero and `≤ 1`),
if `γ * γ' ∈ I` (additive `γ + γ'`) then `γ ∈ I` or `γ' ∈ I`. -/
def IsPrimeIdealGamma (I : Set (Gamma A K)) : Prop :=
  IsIdealGamma A K I ∧ (1 ∉ I) ∧
  (∀ γ γ' : Gamma A K, γ ≠ 0 → γ ≤ 1 → γ' ≠ 0 → γ' ≤ 1 →
    γ * γ' ∈ I → γ ∈ I ∨ γ' ∈ I)

/-- **The map `Φ`** on carrier sets:
`Φ(S) = v(S \ {0}) = { v(x) : x ∈ S, x ≠ 0 }`.
Applied to the carrier `↑𝔞` of an ideal `𝔞 ⊆ A`, this is `Φ(𝔞)`.
Here `v(x)` means `v(algebraMap A K x)`. -/
noncomputable def gammaPhi (S : Set A) : Set (Gamma A K) :=
  {γ | ∃ x : A, x ∈ S ∧ x ≠ 0 ∧ gammaVal A K (algebraMap A K x) = γ}

/-- **The map `Ψ`**:
`Ψ(I) = { x ∈ A : x = 0 ∨ v(x) ∈ I }`, as a subset of `A`.
Here `v(x)` means `v(algebraMap A K x)`. -/
noncomputable def gammaPsi (I : Set (Gamma A K)) : Set A :=
  {x : A | x = 0 ∨ gammaVal A K (algebraMap A K x) ∈ I}

/-- An element `γ` of `Γ` lies in `Φ(S)` iff `γ = v(x)` for some nonzero `x ∈ S`. -/
@[simp]
theorem mem_gammaPhi_iff {S : Set A} {γ : Gamma A K} :
    γ ∈ gammaPhi A K S ↔ ∃ x ∈ S, x ≠ 0 ∧ gammaVal A K (algebraMap A K x) = γ :=
  Iff.rfl

/-- An element `x ∈ A` lies in `Ψ(I)` iff `x = 0` or `v(x) ∈ I`. -/
@[simp]
theorem mem_gammaPsi_iff {I : Set (Gamma A K)} {x : A} :
    x ∈ gammaPsi A K I ↔ x = 0 ∨ gammaVal A K (algebraMap A K x) ∈ I :=
  Iff.rfl

/-- `v (algebraMap A K a) = 0 ↔ a = 0`. -/
private theorem val_eq_zero_iff' (a : A) : gammaVal A K (algebraMap A K a) = 0 ↔ a = 0 := by
  rw [Valuation.zero_iff, FaithfulSMul.algebraMap_eq_zero_iff]

private theorem val_ne_zero' {a : A} (ha : a ≠ 0) : gammaVal A K (algebraMap A K a) ≠ 0 :=
  (val_eq_zero_iff' A K a).not.mpr ha

/-- `v x ≤ 1` iff `x` lies in the image of `A`. -/
private theorem val_le_one_iff' (x : K) :
    gammaVal A K x ≤ 1 ↔ ∃ a : A, algebraMap A K a = x := by
  rw [← Valuation.mem_integer_iff, ValuationRing.mem_integer_iff]

/-- `v (algebraMap A K a) ≤ 1`. -/
private theorem val_le_one' (a : A) : gammaVal A K (algebraMap A K a) ≤ 1 :=
  (val_le_one_iff' A K _).2 ⟨a, rfl⟩

/-- For `γ ≤ 1` nonzero, there is a nonzero `c : A` with `v (algebraMap A K c) = γ`. -/
private theorem exists_ne_zero_val_eq {γ : Gamma A K} (hγ0 : γ ≠ 0) (hγ : γ ≤ 1) :
    ∃ c : A, c ≠ 0 ∧ gammaVal A K (algebraMap A K c) = γ := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep γ
  obtain ⟨c, rfl⟩ := (val_le_one_iff' A K x).1 hγ
  exact ⟨c, fun h => hγ0 ((val_eq_zero_iff' A K c).2 h), rfl⟩

/-- `v b ≤ v a → a ∣ b` (for `a ≠ 0`). -/
private theorem dvd_of_val_le (a b : A) (ha : a ≠ 0)
    (h : gammaVal A K (algebraMap A K b) ≤ gammaVal A K (algebraMap A K a)) :
    a ∣ b := by
  have ha' : algebraMap A K a ≠ 0 := (FaithfulSMul.algebraMap_eq_zero_iff A K).not.mpr ha
  obtain ⟨c, hc⟩ := (val_le_one_iff' A K _).1
    (show gammaVal A K (algebraMap A K b / algebraMap A K a) ≤ 1 by
      rwa [map_div₀, div_le_one₀ (zero_lt_iff.2 (val_ne_zero' A K ha))])
  exact ⟨c, FaithfulSMul.algebraMap_injective A K <| by rw [map_mul, hc, mul_div_cancel₀ _ ha']⟩

/-- An ideal containing a nonzero `a` contains every `b` with `v b ≤ v a`. -/
private theorem mem_of_val_le (𝔞 : Ideal A) {a b : A} (ha : a ∈ 𝔞) (ha0 : a ≠ 0)
    (h : gammaVal A K (algebraMap A K b) ≤ gammaVal A K (algebraMap A K a)) : b ∈ 𝔞 := by
  obtain ⟨d, rfl⟩ := dvd_of_val_le A K a b ha0 h
  exact 𝔞.mul_mem_right d ha

/-- `Φ` is well defined: for every ideal `𝔞 ⊆ A` the set
`Φ(𝔞) = v(𝔞 \ {0})` is an ideal of `Γ`. -/
theorem isIdealGamma_gammaPhi (𝔞 : Ideal A) :
    IsIdealGamma A K (gammaPhi A K (𝔞 : Set A)) := by
  refine ⟨fun γ ⟨x, _, hx0, hx⟩ => hx ▸ ⟨val_ne_zero' A K hx0, val_le_one' A K x⟩, ?_⟩
  rintro γ γ' ⟨x, hx𝔞, hx0, rfl⟩ hγ'0 hγ'le
  obtain ⟨c, hc0, rfl⟩ := exists_ne_zero_val_eq A K hγ'0 (hγ'le.trans (val_le_one' A K x))
  exact ⟨c, mem_of_val_le A K 𝔞 hx𝔞 hx0 hγ'le, hc0, rfl⟩

/-- `Ψ(I)` as an ideal of `A`, for an ideal `I` of `Γ`. -/
noncomputable def gammaPsiIdeal (I : Set (Gamma A K)) (hI : IsIdealGamma A K I) : Ideal A where
  carrier := gammaPsi A K I
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    simp only [mem_gammaPsi_iff] at hx hy ⊢
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    right
    rcases hx with rfl | hxI
    · simpa using hy.resolve_left (by simpa using hxy)
    rcases hy with rfl | hyI
    · simpa using hxI
    have hadd := (gammaVal A K).map_add (algebraMap A K x) (algebraMap A K y)
    rw [← map_add] at hadd
    rcases le_max_iff.mp hadd with h | h
    · exact hI.2 _ _ hxI (val_ne_zero' A K hxy) h
    · exact hI.2 _ _ hyI (val_ne_zero' A K hxy) h
  smul_mem' := by
    intro r x hx
    simp only [mem_gammaPsi_iff, smul_eq_mul] at hx ⊢
    by_cases hrx : r * x = 0
    · exact Or.inl hrx
    rcases hx with rfl | hxI
    · simp at hrx
    refine Or.inr (hI.2 _ _ hxI (val_ne_zero' A K hrx) ?_)
    rw [map_mul, map_mul]
    exact mul_le_of_le_one_left' (val_le_one' A K r)

/-- The carrier of the ideal `gammaPsiIdeal A K I hI` is `Ψ(I)`. -/
@[simp]
theorem coe_gammaPsiIdeal (I : Set (Gamma A K)) (hI : IsIdealGamma A K I) :
    (gammaPsiIdeal A K I hI : Set A) = gammaPsi A K I :=
  rfl

/-- `Ψ` is well defined: for every ideal `I ⊆ Γ` the set `Ψ(I)` is the carrier of
an ideal of `A`. -/
theorem exists_ideal_gammaPsi (I : Set (Gamma A K)) (hI : IsIdealGamma A K I) :
    ∃ J : Ideal A, (J : Set A) = gammaPsi A K I :=
  ⟨gammaPsiIdeal A K I hI, rfl⟩

/-- `Ψ` is a left inverse of `Φ`: `Ψ(Φ(𝔞)) = 𝔞` for every ideal `𝔞 ⊆ A`. -/
theorem gammaPsi_gammaPhi (𝔞 : Ideal A) :
    gammaPsi A K (gammaPhi A K (𝔞 : Set A)) = (𝔞 : Set A) := by
  ext x
  simp only [mem_gammaPsi_iff, mem_gammaPhi_iff, SetLike.mem_coe]
  refine ⟨?_, fun hx => or_iff_not_imp_left.2 fun hx0 => ⟨x, hx, hx0, rfl⟩⟩
  rintro (rfl | ⟨y, hy𝔞, hy0, hyx⟩)
  · exact 𝔞.zero_mem
  · exact mem_of_val_le A K 𝔞 hy𝔞 hy0 hyx.ge

/-- `Ψ` is a right inverse of `Φ`: `Φ(Ψ(I)) = I` for every ideal `I ⊆ Γ`. -/
theorem gammaPhi_gammaPsi (I : Set (Gamma A K)) (hI : IsIdealGamma A K I) :
    gammaPhi A K (gammaPsi A K I) = I := by
  ext γ
  simp only [mem_gammaPhi_iff, mem_gammaPsi_iff]
  constructor
  · rintro ⟨x, hx0' | hxI, hx0, rfl⟩
    exacts [absurd hx0' hx0, hxI]
  · intro hγI
    obtain ⟨c, hc0, rfl⟩ := exists_ne_zero_val_eq A K (hI.1 γ hγI).1 (hI.1 γ hγI).2
    exact ⟨c, Or.inr hγI, hc0, rfl⟩

/-- `Φ` preserves and reflects inclusion.  For ideals
`𝔞, 𝔟 ⊆ A`, `𝔞 ⊆ 𝔟 ↔ Φ(𝔞) ⊆ Φ(𝔟)`. -/
theorem subset_iff_gammaPhi_subset (𝔞 𝔟 : Ideal A) :
    (𝔞 : Set A) ⊆ (𝔟 : Set A) ↔ gammaPhi A K (𝔞 : Set A) ⊆ gammaPhi A K (𝔟 : Set A) := by
  refine ⟨fun hsub γ ⟨x, hx𝔞, hx0, hxγ⟩ => ⟨x, hsub hx𝔞, hx0, hxγ⟩, fun hsub x hx𝔞 => ?_⟩
  by_cases hx0 : x = 0
  · exact hx0 ▸ 𝔟.zero_mem
  obtain ⟨y, hy𝔟, hy0, hyx⟩ := hsub ⟨x, hx𝔞, hx0, rfl⟩
  exact mem_of_val_le A K 𝔟 hy𝔟 hy0 hyx.ge

/-- `Ψ` preserves and reflects inclusion: for ideals `I, J ⊆ Γ`,
`I ⊆ J ↔ Ψ(I) ⊆ Ψ(J)`. -/
theorem subset_iff_gammaPsi_subset (I J : Set (Gamma A K)) (hI : IsIdealGamma A K I) :
    I ⊆ J ↔ gammaPsi A K I ⊆ gammaPsi A K J := by
  refine ⟨fun hsub x hx => hx.imp_right (@hsub _), fun hsub γ hγI => ?_⟩
  obtain ⟨c, hc0, rfl⟩ := exists_ne_zero_val_eq A K (hI.1 γ hγI).1 (hI.1 γ hγI).2
  exact (hsub (Or.inr hγI : c ∈ gammaPsi A K I)).resolve_left hc0

/-- `Φ` carries primes to primes.  For every prime ideal
`𝔭 ⊆ A` (including `𝔭 = (0)`, prime since `A` is a domain),
`Φ(𝔭)` is a prime ideal of `Γ`. -/
theorem isPrimeIdealGamma_gammaPhi (𝔭 : Ideal A) (h : 𝔭.IsPrime) :
    IsPrimeIdealGamma A K (gammaPhi A K (𝔭 : Set A)) := by
  refine ⟨isIdealGamma_gammaPhi A K 𝔭, ?_, ?_⟩
  · rintro ⟨x, hx𝔭, hx0, hx1⟩
    refine h.ne_top (𝔭.eq_top_of_isUnit_mem hx𝔭 (isUnit_of_dvd_one ?_))
    exact dvd_of_val_le A K x 1 hx0 (by rw [map_one, map_one, hx1])
  · intro γ γ' hγ0 hγ1 hγ'0 hγ'1 hprod
    obtain ⟨a, ha0, rfl⟩ := exists_ne_zero_val_eq A K hγ0 hγ1
    obtain ⟨b, hb0, rfl⟩ := exists_ne_zero_val_eq A K hγ'0 hγ'1
    rw [← map_mul, ← map_mul] at hprod
    obtain ⟨z, hz𝔭, hz0, hzv⟩ := hprod
    exact (h.mem_or_mem (mem_of_val_le A K 𝔭 hz𝔭 hz0 hzv.ge)).imp
      (⟨a, ·, ha0, rfl⟩) (⟨b, ·, hb0, rfl⟩)

/-- `Ψ` carries primes to primes: for every prime ideal `I ⊆ Γ`, the ideal `J` of
`A` with carrier `Ψ(I)` is prime. -/
theorem isPrime_gammaPsi (I : Set (Gamma A K)) (hI : IsPrimeIdealGamma A K I)
    (J : Ideal A) (hJ : (J : Set A) = gammaPsi A K I) : J.IsPrime := by
  obtain ⟨-, h1, hprod⟩ := hI
  have memJ (a : A) : a ∈ J ↔ (a = 0 ∨ gammaVal A K (algebraMap A K a) ∈ I) := by
    rw [← SetLike.mem_coe, hJ, mem_gammaPsi_iff]
  refine ⟨?_, fun {x y} hxy => ?_⟩
  · rw [Ideal.ne_top_iff_one, memJ, map_one, map_one]
    exact fun h => h.elim one_ne_zero h1
  by_cases hx0 : x = 0
  · exact Or.inl ((memJ x).mpr (Or.inl hx0))
  by_cases hy0 : y = 0
  · exact Or.inr ((memJ y).mpr (Or.inl hy0))
  rw [memJ, map_mul, map_mul] at hxy
  have hxyI := hxy.resolve_left (mul_ne_zero hx0 hy0)
  exact (hprod _ _ (val_ne_zero' A K hx0) (val_le_one' A K x) (val_ne_zero' A K hy0)
    (val_le_one' A K y) hxyI).imp (fun h => (memJ x).mpr (Or.inr h))
    (fun h => (memJ y).mpr (Or.inr h))

/-- The inclusion-preserving bijection `Φ : Id(A) ≃ Id(Γ)` of Stacks tag 00IH,
with inverse `Ψ`. -/
noncomputable def idealEquivValueGroupIdeal :
    Ideal A ≃ {I : Set (Gamma A K) // IsIdealGamma A K I} where
  toFun 𝔞 := ⟨gammaPhi A K (𝔞 : Set A), isIdealGamma_gammaPhi A K 𝔞⟩
  invFun I := gammaPsiIdeal A K I.1 I.2
  left_inv 𝔞 := SetLike.coe_injective (gammaPsi_gammaPhi A K 𝔞)
  right_inv I := Subtype.ext (gammaPhi_gammaPsi A K I.1 I.2)

/-- **Stacks tag 00IH.**  Let `A` be a valuation ring with fraction field `K`
and value group `Γ = ValueGroup A K`.  The ideals of `A` are in
inclusion-preserving bijection with the ideals of `Γ` (`IsIdealGamma`), via
`Φ(𝔞) = v(𝔞 \ {0})`, and this bijection carries prime ideals to prime ideals
(and reflects them). -/
@[stacks 00IH]
theorem ideals_correspond_to_valueGroupIdeals :
    ∃ e : Ideal A ≃ {I : Set (Gamma A K) // IsIdealGamma A K I},
      (∀ 𝔞 𝔟 : Ideal A, 𝔞 ≤ 𝔟 ↔ (e 𝔞).1 ⊆ (e 𝔟).1) ∧
        (∀ 𝔞 : Ideal A, 𝔞.IsPrime ↔ IsPrimeIdealGamma A K (e 𝔞).1) :=
  ⟨idealEquivValueGroupIdeal A K, subset_iff_gammaPhi_subset A K, fun 𝔞 =>
    ⟨isPrimeIdealGamma_gammaPhi A K 𝔞, fun h =>
      isPrime_gammaPsi A K _ h 𝔞 (gammaPsi_gammaPhi A K 𝔞).symm⟩⟩
