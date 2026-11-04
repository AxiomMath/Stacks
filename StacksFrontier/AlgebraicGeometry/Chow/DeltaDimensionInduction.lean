module

public import StacksFrontier.AlgebraicGeometry.Chow.MaximalDeltaComponent

/-!
# Strict decrease of delta-dimension, and induction on it

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. On an integral scheme
`Y` locally of finite type over `S` of finite delta-dimension, a closed subscheme missing the
generic point of `Y` has *strictly* smaller delta-dimension; equivalently, so does the reduced
complement of a nonempty open subscheme.

Delta-dimension is valued in `EInt`, so it is a well-founded measure only above a floor. Fixing
a floor `k : ℤ`, a property of schemes locally of finite type over `S` holds for every such
scheme of finite delta-dimension as soon as it holds at delta-dimension below `k` and is
inherited at delta-dimension `d ≥ k` from all smaller delta-dimensions. Below the floor the
property is vacuous in the intended applications: `Z_k(X) = 0` when no point of `X` has
relative dimension `k`, which is `Stacks.Chow.cyclesOfDimension_eq_bot`.

## Main results

* `Stacks.Chow.schemeDeltaDimension_lt_of_notMem_range` — a closed subscheme of an integral
  scheme of finite delta-dimension missing the generic point has strictly smaller
  delta-dimension.
* `Stacks.Chow.schemeDeltaDimension_lt_of_range_eq_compl` — the same for the reduced complement
  of a nonempty open subscheme.
* `Stacks.Chow.schemeDeltaDimension_induction` — strong induction on the delta-dimension of a
  scheme locally of finite type over the base, above a floor.
* `Stacks.Chow.schemeDeltaDimension_induction_of_eq` — the same, for a scheme whose
  delta-dimension is a given integer.

## References

* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- An element of `EInt` caught between `m` and `m + 1` is `m`. -/
private theorem eq_coe_of_coe_le_of_lt_coe_add_one {x : EInt} {m : ℤ}
    (hle : (m : EInt) ≤ x) (hlt : x < ((m + 1 : ℤ) : EInt)) : x = (m : EInt) := by
  induction x using WithBotTop.rec with
  | bot => exact absurd hle (by simp)
  | coe d =>
    rw [WithBotTop.coe_le_coe] at hle
    rw [WithBotTop.coe_lt_coe] at hlt
    exact congrArg (fun z : ℤ => (z : EInt)) (by omega)
  | top => exact absurd hlt (not_lt.mpr le_top)

/-- An element of `EInt` that is neither `⊥` nor `⊤` is an integer. -/
private theorem exists_eq_coe {x : EInt} (hbot : x ≠ ⊥) (htop : x < ⊤) :
    ∃ d : ℤ, x = (d : EInt) := by
  induction x using WithBotTop.rec with
  | bot => exact absurd rfl hbot
  | coe d => exact ⟨d, rfl⟩
  | top => exact absurd htop (lt_irrefl _)

/-- A closed subscheme of an integral scheme of finite delta-dimension that misses the generic
point has strictly smaller delta-dimension. -/
theorem schemeDeltaDimension_lt_of_notMem_range (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt))
    (hi : genericPoint Y ∉ Set.range i.base) :
    schemeDeltaDimension C (i ≫ p) < schemeDeltaDimension C p := by
  refine lt_of_le_of_lt (schemeDeltaDimension_le_sub_one_of_notMem_range C p i hn hi) ?_
  rw [hn, WithBotTop.coe_lt_coe]
  omega

/-- A closed subscheme of an integral scheme of finite delta-dimension whose range is the
complement of a nonempty open subscheme has strictly smaller delta-dimension. -/
theorem schemeDeltaDimension_lt_of_range_eq_compl (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] (V : Y.Opens)
    (hcomplement : Set.range i.base = (Set.range V.ι.base)ᶜ)
    (hV : (V : Set Y).Nonempty) {n : ℤ} (hn : schemeDeltaDimension C p = (n : EInt)) :
    schemeDeltaDimension C (i ≫ p) < schemeDeltaDimension C p := by
  refine schemeDeltaDimension_lt_of_notMem_range C p i hn ?_
  obtain ⟨v, hv⟩ := hV
  have hmem : genericPoint Y ∈ (V : Set Y) :=
    (specializes_iff_forall_open.mp (genericPoint_specializes v)) _ V.2 hv
  rw [hcomplement, Scheme.Opens.range_ι]
  exact fun h => h hmem

/-- **Strong induction on the delta-dimension, above a floor `k`.** A property of schemes
locally of finite type over the base of a Chow situation that holds at delta-dimension below
`k`, and that holds at delta-dimension `d ≥ k` whenever it holds at every smaller
delta-dimension, holds for every scheme of finite delta-dimension. -/
theorem schemeDeltaDimension_induction (C : ChowSituation.{u}) (k : ℤ)
    {P : (X : Scheme.{u}) → (f : X ⟶ C.S) → [LocallyOfFiniteType f] → Prop}
    (base : ∀ (X : Scheme.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f],
      schemeDeltaDimension C f < (k : EInt) → P X f)
    (step : ∀ d : ℤ, k ≤ d →
      (∀ (Y : Scheme.{u}) (g : Y ⟶ C.S) [LocallyOfFiniteType g],
        schemeDeltaDimension C g < (d : EInt) → P Y g) →
      ∀ (X : Scheme.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f],
        schemeDeltaDimension C f = (d : EInt) → P X f)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (hfin : schemeDeltaDimension C f < ⊤) :
    P X f := by
  have key : ∀ m : ℕ, ∀ (Y : Scheme.{u}) (g : Y ⟶ C.S) [LocallyOfFiniteType g],
      schemeDeltaDimension C g < ((k + (m : ℤ) : ℤ) : EInt) → P Y g := by
    intro m
    induction m with
    | zero => intro Y g _ h; exact base Y g (by simpa using h)
    | succ m ih =>
      intro Y g _ h
      have hcast : (k + ((m + 1 : ℕ) : ℤ) : ℤ) = (k + (m : ℤ)) + 1 := by push_cast; ring
      rw [hcast] at h
      by_cases hlt : schemeDeltaDimension C g < ((k + (m : ℤ) : ℤ) : EInt)
      · exact ih Y g hlt
      · exact step (k + (m : ℤ)) (by omega) (fun Y' g' _ h' => ih Y' g' h') Y g
          (eq_coe_of_coe_le_of_lt_coe_add_one (not_lt.mp hlt) h)
  by_cases hk : schemeDeltaDimension C f < (k : EInt)
  · exact base X f hk
  -- below the floor the base case applies; above it the delta-dimension is an integer `d ≥ k`
  have hbot : schemeDeltaDimension C f ≠ ⊥ := by
    intro h
    rw [h] at hk
    exact hk (bot_lt_iff_ne_bot.mpr (WithBotTop.coe_ne_bot k))
  obtain ⟨d, hd⟩ := exists_eq_coe hbot hfin
  have hkd : k ≤ d := by
    rw [hd, not_lt, WithBotTop.coe_le_coe] at hk
    exact hk
  refine key ((d - k).toNat + 1) X f ?_
  rw [hd, WithBotTop.coe_lt_coe]
  omega

/-- Strong induction on the delta-dimension above a floor `k`, for a scheme whose
delta-dimension is a given integer. -/
theorem schemeDeltaDimension_induction_of_eq (C : ChowSituation.{u}) (k : ℤ)
    {P : (X : Scheme.{u}) → (f : X ⟶ C.S) → [LocallyOfFiniteType f] → Prop}
    (base : ∀ (X : Scheme.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f],
      schemeDeltaDimension C f < (k : EInt) → P X f)
    (step : ∀ d : ℤ, k ≤ d →
      (∀ (Y : Scheme.{u}) (g : Y ⟶ C.S) [LocallyOfFiniteType g],
        schemeDeltaDimension C g < (d : EInt) → P Y g) →
      ∀ (X : Scheme.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f],
        schemeDeltaDimension C f = (d : EInt) → P X f)
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {n : ℤ}
    (hn : schemeDeltaDimension C f = (n : EInt)) :
    P X f :=
  schemeDeltaDimension_induction C k base step f
    (hn ▸ lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top n))

end Stacks.Chow

end
