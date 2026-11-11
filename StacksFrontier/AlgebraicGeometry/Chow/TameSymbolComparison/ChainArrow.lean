module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Arrows

/-!
# Arrows between chain groups of a function decreasing along specializations

Let `X` be a scheme and `δ : X → ℤ`. Given, for every specialization `x ⇝ x'` with
`δ(x) = δ(x') + 1`, an additive map `Φ_{x, x'} : K^M_{i+1}(κ(x)) → K^M_i(κ(x'))` which is locally
finite in `x'` (for a class `α` and a quasi-compact open `U` only finitely many `x' ∈ U` have
`Φ_{x, x'}(α) ≠ 0`), this file builds the arrow

`⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) → ⨁_{δ(x) = j} K^M_i(κ(x))`,
`(α_x) ↦ (∑_{x ⇝ x'} Φ_{x, x'}(α_x))`,

(`Stacks.Chow.chainArrow`). It is the construction of `Stacks.Chow.dimMilnorChainBoundary` with
an arbitrary family of local components in place of the tame symbol, so that the arrows of
Stacks 0EAY can be built from a tame symbol — the symbol `d_A` of Stacks 02Q1, or the tame
symbol of Section 42.5 given by the recipe of Stacks 0EAQ — and from the order of vanishing.

## Main definitions

* `Stacks.Chow.ChainArrowLocallyFinite`: The local finiteness condition on the family `Φ`.
* `Stacks.Chow.chainArrow`: The arrow `(α_x) ↦ (∑_{x ⇝ x'} Φ_{x, x'}(α_x))` between chain groups.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (δ : X → ℤ) (i : ℕ)
  (Φ : ∀ x x' : X, x ⤳ x' → δ x = δ x' + 1 →
    MilnorKTheory ↥(X.residueField x) (i + 1) →+ MilnorKTheory ↥(X.residueField x') i)

/-- The local finiteness of a family of local components. -/
def ChainArrowLocallyFinite : Prop :=
  ∀ (x : X) (α : MilnorKTheory ↥(X.residueField x) (i + 1)) (U : X.Opens),
    IsCompact (U : Set X) → {x' : X | x' ∈ (U : Set X) ∧
      ∃ (h : x ⤳ x') (hd : δ x = δ x' + 1), Φ x x' h hd α ≠ 0}.Finite

open Classical in
/-- The contribution of `x` to the coefficient at `x'`. -/
def chainArrowTerm (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x : {x : X | δ x = j + 1}) (x' : {x : X | δ x = j}) : MilnorKTheory ↥(X.residueField x'.1) i :=
  if h : (x.1 : X) ⤳ (x'.1 : X) then
    Φ x.1 x'.1 h (by rw [x.2, x'.2]) (ξ.1 x)
  else 0

variable {δ i Φ}

open Classical in
/-- If `x ⤳ x'`, the contribution of `x` at `x'` is `Φ_{x, x'}(ξ_x)`. -/
theorem chainArrowTerm_of_specializes (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x : {x : X | δ x = j + 1}) (x' : {x : X | δ x = j}) (h : (x.1 : X) ⤳ (x'.1 : X)) :
    chainArrowTerm δ i Φ j ξ x x' = Φ x.1 x'.1 h (by rw [x.2, x'.2]) (ξ.1 x) := by
  rw [chainArrowTerm, dite_eq_left h]

open Classical in
/-- If `x` does not specialize to `x'`, the contribution of `x` at `x'` is zero. -/
theorem chainArrowTerm_of_not_specializes (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x : {x : X | δ x = j + 1}) (x' : {x : X | δ x = j}) (h : ¬(x.1 : X) ⤳ (x'.1 : X)) :
    chainArrowTerm δ i Φ j ξ x x' = 0 := by
  rw [chainArrowTerm, dite_eq_right h]

open Classical in
/-- If the component `ξ_x` vanishes, the contribution of `x` at every `x'` is zero. -/
theorem chainArrowTerm_of_eq_zero (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    {x : {x : X | δ x = j + 1}} (hx : ξ.1 x = 0) (x' : {x : X | δ x = j}) :
    chainArrowTerm δ i Φ j ξ x x' = 0 := by
  rw [chainArrowTerm]
  split
  · rw [hx, map_zero]
  · rfl

open Classical in
/-- The contribution of `x` at `x'` is additive in the chain. -/
theorem chainArrowTerm_add (j : ℤ) (ξ η : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x : {x : X | δ x = j + 1}) (x' : {x : X | δ x = j}) :
    chainArrowTerm δ i Φ j (ξ + η) x x' =
      chainArrowTerm δ i Φ j ξ x x' + chainArrowTerm δ i Φ j η x x' := by
  rw [chainArrowTerm, chainArrowTerm, chainArrowTerm]
  split
  · rw [show (ξ + η).1 x = ξ.1 x + η.1 x from rfl, map_add]
  · rw [add_zero]

/-- If `x` contributes nontrivially at `x'`, then `ξ_x ≠ 0` and `x ⤳ x'`. -/
private theorem ne_zero_and_specializes_of_chainArrowTerm_ne_zero (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) {x : {x : X | δ x = j + 1}}
    {x' : {x : X | δ x = j}} (hx : chainArrowTerm δ i Φ j ξ x x' ≠ 0) :
    ξ.1 x ≠ 0 ∧ (x.1 : X) ⤳ (x'.1 : X) :=
  ⟨fun h ↦ hx (chainArrowTerm_of_eq_zero j ξ h x'),
    by_contra fun hnot ↦ hx (chainArrowTerm_of_not_specializes j ξ x x' hnot)⟩

/-- Only finitely many `x` contribute to the coefficient at `x'`. -/
theorem finite_support_chainArrowTerm (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x' : {x : X | δ x = j}) :
    (Function.support fun x : {x : X | δ x = j + 1} ↦ chainArrowTerm δ i Φ j ξ x x').Finite := by
  obtain ⟨t, ht, hfin⟩ := locallyFinite_closure_support_of_mem_locallyFiniteDirectSum _ _ ξ x'.1
  refine (Set.Finite.image (fun q : {x : {x : X | δ x = j + 1} // ξ.1 x ≠ 0} ↦ q.1) hfin).subset ?_
  intro x hx
  obtain ⟨hax, hspec⟩ := ne_zero_and_specializes_of_chainArrowTerm_ne_zero j ξ hx
  exact ⟨⟨x, hax⟩, ⟨x'.1, specializes_iff_mem_closure.mp hspec, mem_of_mem_nhds ht⟩, rfl⟩

variable (δ i Φ) in
/-- The coefficient at `x'`: the sum over `x` of the contributions of `x` at `x'`. -/
def chainArrowCoeff (j : ℤ) (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x' : {x : X | δ x = j}) : MilnorKTheory ↥(X.residueField x'.1) i :=
  ∑ᶠ x : {x : X | δ x = j + 1}, chainArrowTerm δ i Φ j ξ x x'

/-- The coefficient at `x'` is additive in the chain. -/
theorem chainArrowCoeff_add (j : ℤ) (ξ η : DimMilnorChainGroup X δ (j + 1) (i + 1))
    (x' : {x : X | δ x = j}) :
    chainArrowCoeff δ i Φ j (ξ + η) x' =
      chainArrowCoeff δ i Φ j ξ x' + chainArrowCoeff δ i Φ j η x' := by
  rw [chainArrowCoeff, chainArrowCoeff, chainArrowCoeff,
    ← finsum_add_distrib (finite_support_chainArrowTerm j ξ x')
      (finite_support_chainArrowTerm j η x')]
  exact finsum_congr fun x ↦ chainArrowTerm_add j ξ η x x'

/-- The coefficient at `x'` of the zero chain is zero. -/
theorem chainArrowCoeff_zero (j : ℤ) (x' : {x : X | δ x = j}) :
    chainArrowCoeff δ i Φ j 0 x' = 0 := by
  rw [chainArrowCoeff, finsum_congr fun x ↦ chainArrowTerm_of_eq_zero j 0 rfl x']
  exact finsum_zero

/-- A single point contributes at only finitely many points of a quasi-compact open. -/
theorem finite_chainArrowTerm_ne_zero (hΦ : ChainArrowLocallyFinite δ i Φ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x : {x : X | δ x = j + 1}) (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    {x' : {x : X | δ x = j} |
      (x'.1 : X) ∈ (U : Set X) ∧ chainArrowTerm δ i Φ j ξ x x' ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image (f := fun x' : {x : X | δ x = j} ↦ (x'.1 : X))
    ((hΦ x.1 (ξ.1 x) U hU).subset ?_) (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨x', ⟨hx'U, hx'ne⟩, rfl⟩
  by_cases hspec : (x.1 : X) ⤳ (x'.1 : X)
  · refine ⟨hx'U, hspec, by rw [x.2, x'.2], ?_⟩
    rwa [chainArrowTerm_of_specializes j ξ x x' hspec] at hx'ne
  · exact absurd (chainArrowTerm_of_not_specializes j ξ x x' hspec) hx'ne

/-- The family of coefficients is locally finite. -/
theorem finite_chainArrowCoeff_ne_zero (hΦ : ChainArrowLocallyFinite δ i Φ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {x' : {x : X | δ x = j} |
      (x'.1 : X) ∈ (U : Set X) ∧ chainArrowCoeff δ i Φ j ξ x' ≠ 0}.Finite := by
  classical
  have hF : {x : {x : X | δ x = j + 1} | (x.1 : X) ∈ (U : Set X) ∧ ξ.1 x ≠ 0}.Finite := ξ.2 U hU
  refine (hF.biUnion (fun x _ ↦ finite_chainArrowTerm_ne_zero hΦ j ξ x U hU)).subset ?_
  rintro x' ⟨hx'U, hx'ne⟩
  have hsupp : ∃ x : {x : X | δ x = j + 1}, chainArrowTerm δ i Φ j ξ x x' ≠ 0 := by
    by_contra hall
    refine hx'ne ?_
    rw [chainArrowCoeff, finsum_congr fun x ↦ not_not.mp fun hne ↦ hall ⟨x, hne⟩]
    exact finsum_zero
  obtain ⟨x, hx⟩ := hsupp
  obtain ⟨hax, hspec⟩ := ne_zero_and_specializes_of_chainArrowTerm_ne_zero j ξ hx
  have hxU : (x.1 : X) ∈ (U : Set X) := by
    obtain ⟨v, hvU, hv⟩ := mem_closure_iff.mp (specializes_iff_mem_closure.mp hspec)
      (U : Set X) U.2 hx'U
    rw [← Set.mem_singleton_iff.mp hv]
    exact hvU
  exact Set.mem_biUnion (show x ∈ {y : {x : X | δ x = j + 1} | (y.1 : X) ∈ (U : Set X) ∧
    ξ.1 y ≠ 0} from ⟨hxU, hax⟩) (show x' ∈ {y' : {x : X | δ x = j} |
      (y'.1 : X) ∈ (U : Set X) ∧ chainArrowTerm δ i Φ j ξ x y' ≠ 0} from ⟨hx'U, hx⟩)

variable (δ i Φ) in
/-- **The arrow `⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) → ⨁_{δ(x) = j} K^M_i(κ(x))` built from a locally
finite family of local components.** -/
def chainArrow (hΦ : ChainArrowLocallyFinite δ i Φ) (j : ℤ) :
    DimMilnorChainGroup X δ (j + 1) (i + 1) →+ DimMilnorChainGroup X δ j i where
  toFun ξ := ⟨fun x' ↦ chainArrowCoeff δ i Φ j ξ x', fun U hU ↦
    finite_chainArrowCoeff_ne_zero hΦ j ξ U hU⟩
  map_zero' := Subtype.ext (funext fun x' ↦ chainArrowCoeff_zero j x')
  map_add' ξ η := Subtype.ext (funext fun x' ↦ chainArrowCoeff_add j ξ η x')

/-- The component at `x'` of the image of `ξ` under `chainArrow` is its coefficient at `x'`. -/
@[simp]
theorem chainArrow_apply (hΦ : ChainArrowLocallyFinite δ i Φ) (j : ℤ)
    (ξ : DimMilnorChainGroup X δ (j + 1) (i + 1)) (x' : {x : X | δ x = j}) :
    (chainArrow δ i Φ hΦ j ξ).1 x' = chainArrowCoeff δ i Φ j ξ x' := rfl

end Stacks.Chow

end
