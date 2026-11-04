module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Tactic.Linarith
public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksFrontier.Order.CoherentFiniteToOne

/-!
# An inverse system of surjections whose limit projections are not surjective

Over a directed index set of uncountable cofinality the projections out of the inverse limit of
a system with surjective transition maps need not be surjective. This file exhibits this for a
system which is a **twist, by the coherent sequence of `StacksFrontier.Order.CoherentFiniteToOne`,
of a system of quotients of one fixed vector space**.

Fix a well-ordered index `I` which is uncountable and whose initial segments are countable —
the countable ordinals. Let `Amb I = I →₀ ℚ` and let
`van b` be the functions vanishing below `b`, so that the stage `Stage b = Amb I ⧸ van b` is
"rational functions on the initial segment below `b`" and the transition maps `Stage a → Stage b`
for `b ≤ a` are truncation, surjective, with the whole system a quotient of the constant system
at `Amb I`. The twisted system puts a rational scalar alongside a stage, which is to say it
takes the trivial square-zero extension

`StageRing b = ℚ ⊕ Stage b`,

and its transition map translates the stage component by that scalar times the difference
`F a - F b` of the coherent sequence, which is finitely supported below `b` precisely because
the sequence is coherent. The transition maps stay surjective, and a compatible family with
scalar component `1` would uniformize the coherent sequence, which is impossible.

## Main definitions

* `Stacks.Coherent.van`, `Stacks.Coherent.Stage` and `Stacks.Coherent.stageMap`: the untwisted
  system of quotients of `I →₀ ℚ`.
* `Stacks.Coherent.cocy`: the cocycle, the finitely supported difference of two members of the
  coherent sequence below the smaller index.
* `Stacks.Coherent.StageRing` and `Stacks.Coherent.twMap`: the twisted system. The stage is a
  ring, the square-zero extension of `ℚ` by `Stage b`; the twisted map is not a ring
  homomorphism but a semilinear map over the untwisted one.
* `Stacks.Coherent.TwSection`: a compatible family for the twisted system.

## Main results

* `Stacks.Coherent.cocy_add_sub_mem_van`: the cocycle identity.
* `Stacks.Coherent.twMap_comp`: the twisted maps compose, so they form an inverse system.
* `Stacks.Coherent.twMap_surjective`: every twisted transition map is surjective.
* `Stacks.Coherent.not_surjective_twSection`: **no projection out of the limit of the twisted
  system is surjective.**

## Implementation notes

The scalar component is left untouched by the transition maps, so it is constant along a
compatible family; the index being linearly ordered, it is then globally constant. Taking the
value `1` is what makes the translation terms add up along the family into the cocycle relation,
and lifting the stage components to `Amb I` turns that relation into the statement that
`F b + w b` and `F a + w a` agree below `b`. Those germs therefore glue to a single function
`g : I → ℚ`, and `g` agrees with each `F a` below `a` off the support of the finitely supported
`w a` — that is, `g` uniformizes the coherent sequence, which
`Stacks.Coherent.not_uniformizable` forbids.

The index has no greatest element, which the gluing needs; that, like the boundedness of
countable subsets, is `Stacks.Coherent.exists_gt_of_countable` rather than a hypothesis — it
follows from uncountability together with the countability of initial segments.
-/

@[expose] public noncomputable section

attribute [local instance] Classical.propDecidable

namespace Stacks.Coherent

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-! ### The untwisted system of quotients -/

/-- Finitely supported rational functions on the index. This is the one fixed vector space all
the stages of the system are quotients of. -/
abbrev Amb (I : Type u) := I →₀ ℚ

/-- The finitely supported rational functions vanishing below `b`. -/
def van (b : I) : Submodule ℚ (Amb I) where
  carrier := {v | ∀ γ < b, v γ = 0}
  add_mem' hv hw γ hγ := by simp [hv γ hγ, hw γ hγ]
  zero_mem' γ _ := rfl
  smul_mem' c _ hv γ hγ := by simp [hv γ hγ]

omit [WellFoundedLT I] in
/-- A function lies in `van b` exactly when it vanishes below `b`. -/
@[simp]
theorem mem_van {b : I} {v : Amb I} : v ∈ van b ↔ ∀ γ < b, v γ = 0 := Iff.rfl

omit [WellFoundedLT I] in
/-- Vanishing below a larger index is a stronger condition. -/
theorem van_antitone {a b : I} (h : b ≤ a) : van a ≤ van b :=
  fun _ hv γ hγ ↦ hv γ (hγ.trans_le h)

/-- A stage of the system: rational functions on the initial segment below `b`, presented as a
quotient of the fixed space. -/
abbrev Stage (b : I) := Amb I ⧸ van b

/-- The transition map of the untwisted system: truncation to a shorter initial segment. -/
def stageMap {a b : I} (h : b ≤ a) : Stage a →ₗ[ℚ] Stage b :=
  Submodule.mapQ _ _ LinearMap.id (van_antitone h)

omit [WellFoundedLT I] in
/-- Truncation sends the class of a function to its class in the shorter stage. -/
@[simp]
theorem stageMap_mk {a b : I} (h : b ≤ a) (v : Amb I) :
    stageMap h ((van a).mkQ v) = (van b).mkQ v := rfl

omit [WellFoundedLT I] in
/-- The transition maps of the untwisted system compose. -/
theorem stageMap_comp {a b c : I} (hab : b ≤ a) (hbc : c ≤ b) (x : Stage a) :
    stageMap hbc (stageMap hab x) = stageMap (hbc.trans hab) x := by
  obtain ⟨v, rfl⟩ := (van a).mkQ_surjective x
  rfl

omit [WellFoundedLT I] in
/-- The transition map along the identity is the identity. -/
@[simp]
theorem stageMap_refl {a : I} (x : Stage a) : stageMap (le_refl a) x = x := by
  obtain ⟨v, rfl⟩ := (van a).mkQ_surjective x
  rfl

omit [WellFoundedLT I] in
/-- The transition maps of the untwisted system are surjective. -/
theorem stageMap_surjective {a b : I} (h : b ≤ a) : Function.Surjective (stageMap h) := by
  intro x
  obtain ⟨v, rfl⟩ := (van b).mkQ_surjective x
  exact ⟨(van a).mkQ v, rfl⟩

/-! ### The cocycle -/

/-- Two members of the coherent sequence differ on a finite set below the smaller index. -/
theorem finite_ne_F_le (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    {γ : I | γ < b ∧ F a γ ≠ F b γ}.Finite := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro γ ⟨-, hne⟩
    exact absurd rfl hne
  · exact finite_ne_F hcnt a b hlt

/-- The cocycle of the twisted system: the difference of two members of the coherent sequence,
cut off below the smaller index, which is finitely supported by coherence. -/
def cocy (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) : Amb I :=
  Finsupp.onFinset (finite_ne_F_le hcnt h).toFinset
    (fun γ ↦ if γ < b then (F a γ : ℚ) - (F b γ : ℚ) else 0) (by
      intro γ hγ
      by_cases hb : γ < b
      · simp only [hb, ite_eq_left] at hγ
        refine Set.Finite.mem_toFinset _ |>.mpr ⟨hb, fun h ↦ ?_⟩
        exact hγ (by rw [h, sub_self])
      · simp only [hb, ite_eq_right, not_false_eq_true] at hγ
        exact absurd rfl hγ)

/-- The cocycle at `γ` is the difference of the two members of the coherent sequence at `γ` when
`γ` lies below the smaller index, and zero otherwise. -/
theorem cocy_apply (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) (γ : I) :
    cocy hcnt h γ = if γ < b then (F a γ : ℚ) - (F b γ : ℚ) else 0 := rfl

/-- **The cocycle identity.** Below the smallest of three indices the cocycle of the outer pair
is the sum of the cocycles of the two inner pairs. -/
theorem cocy_add_sub_mem_van (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b c : I} (hab : b ≤ a)
    (hbc : c ≤ b) :
    cocy hcnt hab + cocy hcnt hbc - cocy hcnt (hbc.trans hab) ∈ van c := by
  intro γ hγ
  have hb : γ < b := hγ.trans_le hbc
  simp only [Finsupp.sub_apply, Finsupp.add_apply, cocy_apply, ite_eq_left hγ, ite_eq_left hb]
  rw [sub_add_sub_cancel, sub_self]

/-- The cocycle of a pair of equal indices vanishes: the two members of the coherent sequence
are the same one. -/
@[simp]
theorem cocy_refl (hcnt : ∀ a : I, (Set.Iio a).Countable) (a : I) :
    cocy hcnt (le_refl a) = 0 := by
  refine Finsupp.ext fun γ ↦ ?_
  rw [cocy_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases h : γ < a
  · rw [ite_eq_left h, sub_self]
  · rw [ite_eq_right h]

/-! ### The twisted system -/

/-- A stage of the twisted system: the trivial square-zero extension of `ℚ` by a stage of the
untwisted system, that is a rational scalar alongside a stage. -/
abbrev StageRing (b : I) := TrivSqZeroExt ℚ (Stage b)

/-- The transition map of the twisted system: the untwisted truncation on the stage component,
translated by the scalar component times the cocycle. It is not a ring homomorphism — the twist
moves `1` — but it is semilinear over the untwisted ring map. -/
def twMap (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    StageRing a → StageRing b :=
  fun x ↦ (x.fst, stageMap h x.snd + x.fst • (van b).mkQ (cocy hcnt h))

/-- The twisted transition map preserves the scalar component. -/
@[simp]
theorem twMap_fst (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : StageRing a) : (twMap hcnt h x).fst = x.fst := rfl

/-- The stage component of the twisted transition map is the truncation of the stage component,
translated by the scalar component times the class of the cocycle. -/
@[simp]
theorem twMap_snd (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : StageRing a) :
    (twMap hcnt h x).snd = stageMap h x.snd + x.fst • (van b).mkQ (cocy hcnt h) := rfl

/-- **The twisted maps form an inverse system.** This is the cocycle identity. -/
theorem twMap_comp (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b c : I} (hab : b ≤ a)
    (hbc : c ≤ b) (x : StageRing a) :
    twMap hcnt hbc (twMap hcnt hab x) = twMap hcnt (hbc.trans hab) x := by
  refine TrivSqZeroExt.ext rfl ?_
  change stageMap hbc (stageMap hab x.snd + x.fst • (van b).mkQ (cocy hcnt hab))
      + x.fst • (van c).mkQ (cocy hcnt hbc)
    = stageMap (hbc.trans hab) x.snd + x.fst • (van c).mkQ (cocy hcnt (hbc.trans hab))
  have hmk : (van c).mkQ (cocy hcnt hab) + (van c).mkQ (cocy hcnt hbc)
      = (van c).mkQ (cocy hcnt (hbc.trans hab)) := by
    rw [← map_add]
    exact (Submodule.Quotient.eq _).2 (cocy_add_sub_mem_van hcnt hab hbc)
  rw [map_add, map_smul, stageMap_comp hab hbc, stageMap_mk, add_assoc, ← smul_add, hmk]

/-- **The twisted transition maps are surjective.** -/
theorem twMap_surjective (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    Function.Surjective (twMap hcnt h) := by
  intro y
  obtain ⟨v, hv⟩ := stageMap_surjective h (y.snd - y.fst • (van b).mkQ (cocy hcnt h))
  refine ⟨(y.fst, v), TrivSqZeroExt.ext rfl ?_⟩
  change stageMap h v + y.fst • (van b).mkQ (cocy hcnt h) = y.snd
  rw [hv, sub_add_cancel]

/-- The twisted transition map along the identity is the identity: its cocycle vanishes. -/
@[simp]
theorem twMap_refl (hcnt : ∀ a : I, (Set.Iio a).Countable) {a : I} (x : StageRing a) :
    twMap hcnt (le_refl a) x = x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [twMap_fst]
  · rw [twMap_snd, stageMap_refl, cocy_refl, map_zero, smul_zero, add_zero]

/-- A compatible family for the twisted system: an element of its inverse limit. -/
abbrev TwSection (hcnt : ∀ a : I, (Set.Iio a).Countable) : Type u :=
  {s : ∀ b : I, StageRing b // ∀ (a b : I) (h : b ≤ a), twMap hcnt h (s a) = s b}

/-- **No projection out of the limit of the twisted system is surjective.** A compatible family
hitting `1` at any index would, after lifting its stage components to the fixed space,
uniformize the coherent sequence. -/
theorem not_surjective_twSection [Uncountable I] (hcnt : ∀ a : I, (Set.Iio a).Countable)
    (b₀ : I) :
    ¬ Function.Surjective (fun s : TwSection hcnt ↦ s.1 b₀) := by
  intro hsurj
  obtain ⟨s, hs⟩ := hsurj 1
  have hs' : s.val b₀ = 1 := hs
  have hone : ∀ b : I, (s.val b).fst = 1 := by
    intro b
    obtain ⟨c, hb₀c, hbc⟩ := exists_ge_ge b₀ b
    have h1 : (s.val c).fst = (s.val b₀).fst := by rw [← s.property c b₀ hb₀c, twMap_fst]
    have h2 : (s.val c).fst = (s.val b).fst := by rw [← s.property c b hbc, twMap_fst]
    rw [← h2, h1, hs', TrivSqZeroExt.fst_one]
  choose w hw using fun b : I ↦ (van b).mkQ_surjective (s.val b).snd
  have hglue : ∀ (a b : I) (h : b ≤ a), ∀ γ < b,
      (F b γ : ℚ) + w b γ = (F a γ : ℚ) + w a γ := by
    intro a b h γ hγ
    have hrel : stageMap h (s.val a).snd + (s.val a).fst • (van b).mkQ (cocy hcnt h)
        = (s.val b).snd := congrArg TrivSqZeroExt.snd (s.property a b h)
    rw [hone a, one_smul, ← hw a, stageMap_mk, ← hw b, ← map_add] at hrel
    have hz := (Submodule.Quotient.eq _).1 hrel γ hγ
    simp only [Finsupp.sub_apply, Finsupp.add_apply, cocy_apply, ite_eq_left hγ] at hz
    linarith [hz]
  have hgt : ∀ γ : I, ∃ a : I, γ < a := fun γ ↦ by
    obtain ⟨a, ha⟩ := exists_gt_of_countable hcnt {γ} (Set.countable_singleton γ)
    exact ⟨a, ha γ rfl⟩
  choose σ hσ using hgt
  have hgval : ∀ (a : I) (γ : I), γ < a →
      (F (σ γ) γ : ℚ) + w (σ γ) γ = (F a γ : ℚ) + w a γ := by
    intro a γ hγa
    obtain ⟨c, hσc, hac⟩ := exists_ge_ge (σ γ) a
    rw [hglue c (σ γ) hσc γ (hσ γ), hglue c a hac γ hγa]
  refine not_uniformizable hcnt (fun n : ℕ ↦ (n : ℚ)) Nat.cast_injective
    (fun γ ↦ (F (σ γ) γ : ℚ) + w (σ γ) γ) ?_
  intro a
  refine Set.Finite.subset (w a).support.finite_toSet ?_
  rintro γ ⟨hγa, hne⟩
  refine Finsupp.mem_support_iff.mpr fun hzero ↦ hne ?_
  show (F a γ : ℚ) = (F (σ γ) γ : ℚ) + w (σ γ) γ
  rw [hgval a γ hγa, hzero, add_zero]

end Stacks.Coherent

end
