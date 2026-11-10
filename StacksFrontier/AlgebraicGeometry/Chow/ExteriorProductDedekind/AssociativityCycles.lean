module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Associativity
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionLocal
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# Associativity of the exterior product over a Dedekind base

Stacks 0FC8 says that the exterior product of Stacks section 42.63 is associative: for `(S, δ)` as
in that section, `X`, `Y`, `Z` locally of finite type over `S`, and `α ∈ CH_*(X)`, `β ∈ CH_*(Y)`,
`γ ∈ CH_*(Z)`,

  `(α × β) × γ = α × (β × γ)`  in  `CH_*(X ×_S Y ×_S Z)`.

`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Associativity` supplies the
associativity of the fibre product of schemes — the associator of the triple fibre product and the
agreement of the two iterated delta-dimensions — and deduces the identity on Chow groups from its
cycle-level form `Stacks.Chow.IsExteriorProductDedekindAssociative`. This file proves the
cycle-level form, and states the identity on Chow groups with nothing assumed beyond the setting
of section 42.63.

## Main results

* `Stacks.Chow.exteriorProductDedekindCycles_pointClosureCycle_closedSubscheme_apply`:
  `[closure {x}] × [P]_k = [closure {x} ×_S P]_{n+k-1}` when `x` dominates a component of the
  base at a point which is not closed, or `x` dominates no component and `P` is flat over the base.
* `Stacks.Chow.exteriorProductDedekindCycles_pointClosureCycle_assoc`: associativity on three
  point closures.
* `Stacks.Chow.isExteriorProductDedekindAssociative`: associativity of the exterior product of
  cycles.
* `Stacks.Chow.exteriorProductDedekindChow_assoc_of_isDedekindChowBase`: **Stacks 0FC8**,
  associativity on Chow groups.

## References

* [Stacks Project, Tag 0FC8](https://stacks.math.columbia.edu/tag/0FC8)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The fundamental cycle of a point closure -/

section PointCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (n : ℤ)

/-- The fundamental cycle `[closure {x}]_n` of the reduced closure of a point, read in
delta-dimension `n`. -/
abbrev pointClosureCycle (x : X) : CycleGroup C f n :=
  cycleAssociatedToClosedSubscheme C f (integralComponentAt x).subschemeι n

/-- The fundamental cycle of the closure of a point of delta-dimension `n` has coefficient one at
that point. -/
theorem pointClosureCycle_apply_self {x : X}
    (hx : relativeDimension C.dimensionFunction f x = n) :
    (pointClosureCycle C f n x).1 x = 1 :=
  cycleAssociatedToClosedSubscheme_integralComponentAt_self C f x
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f x hx)

/-- The fundamental cycle of the closure of a point vanishes at every other point. -/
theorem pointClosureCycle_apply_of_ne {x y : X} (hy : y ≠ x) :
    (pointClosureCycle C f n x).1 y = 0 :=
  cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C f n x hy

end PointCycle

/-! ### Exterior products with a point closure -/

section Collapse

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-- The term of an exterior product vanishes at a pair whose first entry carries no coefficient. -/
theorem exteriorProductDedekindTerm_eq_zero_of_left (α : CycleGroup C f n)
    (β : CycleGroup C g m) (w : (pullback f g : Scheme.{u})) (p : X × Y) (hp : α.1 p.1 = 0) :
    exteriorProductDedekindTerm C f g n m α β w p = 0 := by
  classical
  unfold exteriorProductDedekindTerm
  split_ifs <;> simp [hp]

/-- The term of an exterior product vanishes at a pair whose second entry carries no
coefficient. -/
theorem exteriorProductDedekindTerm_eq_zero_of_right (α : CycleGroup C f n)
    (β : CycleGroup C g m) (w : (pullback f g : Scheme.{u})) (p : X × Y) (hp : β.1 p.2 = 0) :
    exteriorProductDedekindTerm C f g n m α β w p = 0 := by
  classical
  unfold exteriorProductDedekindTerm
  split_ifs <;> simp [hp]

/-- The exterior product with the fundamental cycle of the closure of `x` only involves the pairs
whose first entry is `x`. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_left_apply (x : X)
    (β : CycleGroup C g m) (w : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x) β).1 w =
      ∑ᶠ t : Y, exteriorProductDedekindTerm C f g n m (pointClosureCycle C f n x) β w (x, t) := by
  rw [exteriorProductDedekindCycles_apply,
    finsum_curry _ (exteriorProductDedekindTerm_support_finite C f g n m _ β w)]
  refine finsum_eq_single _ x fun x' hx' ↦ finsum_eq_zero_of_forall_eq_zero fun t ↦ ?_
  exact exteriorProductDedekindTerm_eq_zero_of_left C f g n m _ β w (x', t)
    (pointClosureCycle_apply_of_ne C f n hx')

/-- The exterior product with the fundamental cycle of the closure of `y` only involves the pairs
whose second entry is `y`. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_right_apply (α : CycleGroup C f n)
    (y : Y) (w : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n m α (pointClosureCycle C g m y)).1 w =
      ∑ᶠ s : X, exteriorProductDedekindTerm C f g n m α (pointClosureCycle C g m y) w (s, y) := by
  rw [exteriorProductDedekindCycles_apply,
    finsum_curry _ (exteriorProductDedekindTerm_support_finite C f g n m α _ w)]
  refine finsum_congr fun s ↦ finsum_eq_single _ y fun y' hy' ↦ ?_
  exact exteriorProductDedekindTerm_eq_zero_of_right C f g n m α _ w (s, y')
    (pointClosureCycle_apply_of_ne C g m hy')

/-! ### Locality of the exterior product -/

/-- A point whose closure contains `a` lies in every open neighbourhood of `a`. -/
theorem mem_of_mem_closure_singleton_of_isOpen {T : Type*} [TopologicalSpace T] {a x : T}
    (hx : a ∈ closure ({x} : Set T)) {U : Set T} (hU : IsOpen U) (haU : a ∈ U) : x ∈ U := by
  obtain ⟨t, htU, htx⟩ := mem_closure_iff.1 hx U hU haU
  exact Set.mem_of_eq_of_mem (Set.eq_of_mem_singleton htx).symm htU

/-- The closure of the image of a point contains the image of each point of its closure. -/
theorem mem_closure_singleton_map {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']
    {φ : T → T'} (hφ : Continuous φ) {a b : T} (h : a ∈ closure ({b} : Set T)) :
    φ a ∈ closure ({φ b} : Set T') :=
  map_mem_closure hφ h (Set.mapsTo_singleton.2 rfl)

/-- **Locality in the first variable.** If `α` vanishes at every point whose closure contains
`a`, then `α × β` vanishes at every point `w` whose first projection has `a` in its closure. -/
theorem exteriorProductDedekindCycles_apply_eq_zero_of_left (α : CycleGroup C f n)
    (β : CycleGroup C g m) (a : X) (hα : ∀ x : X, a ∈ closure ({x} : Set X) → α.1 x = 0)
    (w : (pullback f g : Scheme.{u}))
    (hw : a ∈ closure ({(pullback.fst f g).base w} : Set X)) :
    (exteriorProductDedekindCycles C f g n m α β).1 w = 0 := by
  rw [exteriorProductDedekindCycles_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun p ↦ ?_
  by_contra hp
  have h1 := (mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n m α β w p hp).1
  have hsub : closure ({(pullback.fst f g).base w} : Set X) ⊆ closure ({p.1} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.2 h1) isClosed_closure
  exact hp (exteriorProductDedekindTerm_eq_zero_of_left C f g n m α β w p (hα _ (hsub hw)))

/-- **Locality in the second variable.** If `β` vanishes at every point whose closure contains
`b`, then `α × β` vanishes at every point `w` whose second projection has `b` in its closure. -/
theorem exteriorProductDedekindCycles_apply_eq_zero_of_right (α : CycleGroup C f n)
    (β : CycleGroup C g m) (b : Y) (hβ : ∀ y : Y, b ∈ closure ({y} : Set Y) → β.1 y = 0)
    (w : (pullback f g : Scheme.{u}))
    (hw : b ∈ closure ({(pullback.snd f g).base w} : Set Y)) :
    (exteriorProductDedekindCycles C f g n m α β).1 w = 0 := by
  rw [exteriorProductDedekindCycles_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun p ↦ ?_
  by_contra hp
  have h2 := (mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n m α β w p hp).2
  have hsub : closure ({(pullback.snd f g).base w} : Set Y) ⊆ closure ({p.2} : Set Y) :=
    closure_minimal (Set.singleton_subset_iff.2 h2) isClosed_closure
  exact hp (exteriorProductDedekindTerm_eq_zero_of_right C f g n m α β w p (hβ _ (hsub hw)))

end Collapse

/-! ### Reduction to fundamental cycles of point closures -/

section Reduction

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (n : ℤ)

/-- Evaluation of a cycle at a point, as an additive map. -/
def cycleEval (x : X) : CycleGroup C f n →+ ℤ where
  toFun c := c.1 x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `cycleEval C f n x` sends a cycle to its coefficient at `x`. -/
@[simp]
theorem cycleEval_apply (x : X) (c : CycleGroup C f n) : cycleEval C f n x c = c.1 x := rfl

/-- Only finitely many points carrying a coefficient of a cycle specialize to a given point. -/
theorem finite_setOf_ne_zero_mem_closure (α : CycleGroup C f n) (a : X) :
    {x : X | α.1 x ≠ 0 ∧ a ∈ closure ({x} : Set X)}.Finite := by
  obtain ⟨t, ht, hfin⟩ := Function.locallyFinsupp.locallyFiniteSupport α.1 a
  obtain ⟨U, hUt, hU, haU⟩ := mem_nhds_iff.1 ht
  exact hfin.subset fun x ⟨hx, hax⟩ ↦ ⟨hUt (mem_of_mem_closure_singleton_of_isOpen hax hU haU), hx⟩

/-- **Reduction to fundamental cycles of point closures.** Two additive maps out of `Z_n(X)` which
only see the coefficients at points specializing to `a`, and which agree on the fundamental cycles
of the closures of the points of delta-dimension `n` specializing to `a`, are equal. -/
theorem addMonoidHom_ext_of_pointClosureCycle (Φ Ψ : CycleGroup C f n →+ ℤ) (a : X)
    (hΦ : ∀ α : CycleGroup C f n, (∀ x : X, a ∈ closure ({x} : Set X) → α.1 x = 0) → Φ α = 0)
    (hΨ : ∀ α : CycleGroup C f n, (∀ x : X, a ∈ closure ({x} : Set X) → α.1 x = 0) → Ψ α = 0)
    (h : ∀ x : X, a ∈ closure ({x} : Set X) →
      relativeDimension C.dimensionFunction f x = n →
        Φ (pointClosureCycle C f n x) = Ψ (pointClosureCycle C f n x)) :
    Φ = Ψ := by
  classical
  refine AddMonoidHom.ext fun α ↦ ?_
  set F := (finite_setOf_ne_zero_mem_closure C f n α a).toFinset with hF
  have hmem : ∀ x, x ∈ F ↔ α.1 x ≠ 0 ∧ a ∈ closure ({x} : Set X) := fun x ↦ by
    rw [hF, Set.Finite.mem_toFinset]; rfl
  set αF : CycleGroup C f n := ∑ x ∈ F, α.1 x • pointClosureCycle C f n x with hαF
  have hdim : ∀ x ∈ F, relativeDimension C.dimensionFunction f x = n := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point C f n α.1).1 α.2 x ((hmem x).1 hx).1
  have hval : ∀ x : X, a ∈ closure ({x} : Set X) → (α - αF).1 x = 0 := by
    intro x hax
    have heval : (αF).1 x = ∑ x' ∈ F, α.1 x' * (pointClosureCycle C f n x').1 x := by
      change cycleEval C f n x αF = _
      rw [hαF, map_sum]
      refine Finset.sum_congr rfl fun x' _ ↦ ?_
      rw [map_zsmul, cycleEval_apply, smul_eq_mul]
    change α.1 x - (αF).1 x = 0
    rw [heval]
    by_cases hx : x ∈ F
    · rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by
          rw [pointClosureCycle_apply_of_ne C f n (Ne.symm hx'), mul_zero])
        (fun h' ↦ absurd hx h'), pointClosureCycle_apply_self C f n (hdim x hx), mul_one, sub_self]
    · have hα0 : α.1 x = 0 := not_not.1 fun h0 ↦ hx ((hmem x).2 ⟨h0, hax⟩)
      rw [hα0, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun x' hx' ↦ ?_
      rw [pointClosureCycle_apply_of_ne C f n (fun h' ↦ hx (by rw [h']; exact hx')), mul_zero]
  have hsplit : α = αF + (α - αF) := by abel
  rw [hsplit, map_add, map_add, hΦ _ hval, hΨ _ hval, add_zero, add_zero, hαF, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [map_zsmul, map_zsmul, h x ((hmem x).1 hx).2 (hdim x hx)]

end Reduction

/-! ### Collapsing the sum over the second factor: a dominating point -/

section CollapseDominating

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n : ℤ)

/-- The closure of a point dominating a component at a point which is not closed is flat of
relative dimension one less than the delta-dimension of the point. -/
theorem exists_relativeDimension_vanishingIdeal_of_dominates (hC : IsDedekindChowBase C) (x : X)
    (hx : relativeDimension C.dimensionFunction f x = n) (hdom : DominatesBaseComponent C f x)
    (hnc : ¬ IsClosed ({f.base x} : Set C.S)) :
    ∃ (_ : Flat ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f)) (r : ℕ),
      AlgebraicGeometry.RelativeDimension ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) r ∧ n = 1 + (r : ℤ) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hint : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have hη : I.subschemeι.base (genericPoint I.subscheme) = x :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x
  have hqη : (I.subschemeι ≫ f).base (genericPoint I.subscheme) = f.base x := by
    rw [Scheme.Hom.comp_apply, hη]
  have hflat : Flat (I.subschemeι ≫ f) :=
    hC.flat_of_mem_irreducibleComponents (I.subschemeι ≫ f) (by rw [hqη]; exact hdom)
  have hrel := relativeDimension_of_irreducibleSpace (I.subschemeι ≫ f)
    (fun _ ↦ ⟨inferInstance, hC.ringKrullDim_stalk_le_one _⟩)
  refine ⟨hflat, _, hrel, ?_⟩
  have h1 : relativeDimension C.dimensionFunction (I.subschemeι ≫ f)
      (genericPoint I.subscheme) = relativeDimension C.dimensionFunction f x := by
    rw [relativeDimension_comp_closedImmersion, hη]
  have h2 : relativeDimension C.dimensionFunction (I.subschemeι ≫ f)
      (genericPoint I.subscheme) =
      C.dimensionFunction ((I.subschemeι ≫ f).base (genericPoint I.subscheme)) +
        (Cardinal.toNat (residueTrdeg (I.subschemeι ≫ f) (genericPoint I.subscheme)) : ℤ) := rfl
  rw [h2, hqη, hC.2.2 _ hnc, hx] at h1
  exact h1.symm

/-- A point at which the cycle coefficient of a closed subscheme is nonzero lies on its support. -/
theorem mem_support_of_closedSubschemeCycleCoeff_ne_zero {T : Scheme.{u}} (p : T ⟶ C.S)
    [LocallyOfFiniteType p] (I : T.IdealSheafData) (k : ℤ) (t : T)
    (ht : closedSubschemeCycleCoeff C p I.subschemeι k t ≠ 0) : t ∈ (I.support : Set T) := by
  classical
  rw [← I.range_subschemeι]
  unfold closedSubschemeCycleCoeff at ht
  split_ifs at ht with h
  · obtain ⟨ξ, hξ⟩ := h
    exact ⟨ξ.1, hξ.1⟩
  · exact absurd rfl ht

/-- A point at which the cycle coefficient of a sum of pulled back ideals is nonzero lies over the
support of the first ideal. -/
private theorem fst_mem_support_of_closedSubschemeCycleCoeff_ne_zero (I : X.IdealSheafData)
    (P : Y.IdealSheafData) (k : ℤ) (v : (pullback f g : Scheme.{u}))
    (h : closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      (I.comap (pullback.fst f g) ⊔ P.comap (pullback.snd f g)).subschemeι k v ≠ 0) :
    (pullback.fst f g).base v ∈ (I.support : Set X) := by
  have h1 := mem_support_of_closedSubschemeCycleCoeff_ne_zero C (pullback.fst f g ≫ f) _ _ v h
  rw [Scheme.IdealSheafData.support_sup, Scheme.IdealSheafData.support_comap] at h1
  exact h1.1

/-- The coefficient of the product of two point closures, with its ideal sheaf written out. -/
theorem closedSubschemeCycleCoeff_exteriorProductIdeal {S' P Q : Scheme.{u}} (a : P ⟶ S')
    (b : Q ⟶ S') (p : (pullback a b : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType p] (x : P) (y : Q)
    (k : ℤ) (v : (pullback a b : Scheme.{u})) :
    closedSubschemeCycleCoeff C p (exteriorProductIdeal a b x y).subschemeι k v =
      closedSubschemeCycleCoeff C p
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set P))).comap
            (pullback.fst a b) ⊔
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Q))).comap
            (pullback.snd a b)).subschemeι k v :=
  rfl

/-- The term of the exterior product with a fundamental cycle of a point closure, made explicit. -/
theorem exteriorProductDedekindTerm_pointClosureCycle (x : X)
    (hx : relativeDimension C.dimensionFunction f x = n) {k : ℤ} (β : CycleGroup C g k)
    (v : (pullback f g : Scheme.{u})) (t : Y) :
    exteriorProductDedekindTerm C f g n k (pointClosureCycle C f n x) β v (x, t) =
      open Classical in
      if DominatesBaseComponent C f x ∨ DominatesBaseComponent C g t then
        β.1 t * closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
          (exteriorProductIdeal f g x t).subschemeι (n + k - 1) v
      else 0 := by
  classical
  unfold exteriorProductDedekindTerm
  split_ifs
  · rw [pointClosureCycle_apply_self C f n hx, one_mul]
  · rfl

/-- **The sum over the second factor at a dominating point.** Let `x` be a point of
delta-dimension `n` whose closure dominates an irreducible component of the base at a point which
is not closed, and let `P ⊆ Y` be a closed subscheme of delta-dimension at most `k`. Then the terms
of `[closure {x}] × [P]_k` attached to `x` sum, at every point, to the coefficient of the product
`closure {x} ×_S P` in delta-dimension `n + k - 1`. -/
theorem finsum_exteriorProductDedekindTerm_cycleAssociatedToClosedSubscheme_of_dominates
    (hC : IsDedekindChowBase C) (x : X) (hx : relativeDimension C.dimensionFunction f x = n)
    (hdom : DominatesBaseComponent C f x) (hnc : ¬ IsClosed ({f.base x} : Set C.S))
    (P : Y.IdealSheafData) (k : ℤ)
    (hP : schemeDeltaDimension C (P.subschemeι ≫ g) ≤ (k : EInt))
    (v : (pullback f g : Scheme.{u})) :
    ∑ᶠ t : Y, exteriorProductDedekindTerm C f g n k (pointClosureCycle C f n x)
        (cycleAssociatedToClosedSubscheme C g P.subschemeι k) v (x, t) =
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap
            (pullback.fst f g) ⊔ P.comap (pullback.snd f g)).subschemeι (n + k - 1) v := by
  classical
  simp_rw [exteriorProductDedekindTerm_pointClosureCycle C f g n x hx, ite_eq_left (Or.inl hdom),
    closedSubschemeCycleCoeff_exteriorProductIdeal]
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  obtain ⟨hflat, r, hrel, hn⟩ :=
    exists_relativeDimension_vanishingIdeal_of_dominates C f n hC x hx hdom hnc
  have hdeg : n + k - 1 = (r : ℤ) + k := by rw [hn]; ring
  simp_rw [hdeg]
  by_cases hz : (pullback.fst f g).base v ∈ (I.support : Set X)
  · set y₀ := (pullback.snd f g).base v with hy₀
    rw [closedSubschemeCycleCoeff_product_left C f g I P r hrel k hP v hz]
    rw [finsum_eq_single _ y₀ fun t ht ↦ ?_]
    · rfl
    · by_cases hPt : (cycleAssociatedToClosedSubscheme C g P.subschemeι k).1 t = 0
      · rw [hPt, zero_mul]
      have htd := (mem_cyclesOfDimension_iff_forall_point C g k _).1
        (cycleAssociatedToClosedSubscheme C g P.subschemeι k).2 t hPt
      have hJ := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C g t htd
      rw [closedSubschemeCycleCoeff_product_left C f g I
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({t} : Set Y))) r hrel k
        (le_of_eq hJ) v hz]
      have h0 := cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C g k t
        (Ne.symm ht)
      change closedSubschemeCycleCoeff C g (integralComponentAt t).subschemeι k y₀ = 0 at h0
      change _ * (closedSubschemeCycleCoeff C g (integralComponentAt t).subschemeι k y₀ * _) = 0
      rw [h0, zero_mul, mul_zero]
  · have hR : closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (I.comap (pullback.fst f g) ⊔ P.comap (pullback.snd f g)).subschemeι ((r : ℤ) + k) v =
          0 := by
      by_contra h
      exact hz (fst_mem_support_of_closedSubschemeCycleCoeff_ne_zero C f g I P _ v h)
    rw [hR]
    refine finsum_eq_zero_of_forall_eq_zero fun t ↦ ?_
    by_contra ht
    exact hz (fst_mem_support_of_closedSubschemeCycleCoeff_ne_zero C f g I _ _ v
      (right_ne_zero_of_mul ht))

end CollapseDominating

/-! ### Collapsing the sum over the second factor: a point over a closed point -/

section CollapseClosedPoint

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n : ℤ)

/-- A closed subscheme `K` pulled back to itself is everything. -/
theorem comap_subschemeι_self {T : Scheme.{u}} (K : T.IdealSheafData) :
    K.comap K.subschemeι = ⊥ := by
  have h := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion K.subschemeι K.subschemeι
  rw [K.ker_subschemeι] at h
  rw [← h, Scheme.Hom.ker_eq_bot_of_isIso]

/-- For `K ≤ A`, the pullback of `A` to `K` is isomorphic to `A`, compatibly with the inclusions. -/
private theorem exists_iso_comap_subschemeι_of_le {T : Scheme.{u}} (K A : T.IdealSheafData)
    (hKA : K ≤ A) : ∃ ψ : (A.comap K.subschemeι).subscheme ≅ A.subscheme,
      ψ.hom ≫ A.subschemeι = (A.comap K.subschemeι).subschemeι ≫ K.subschemeι := by
  have hI : K.subschemeι.ker ≤ A.subschemeι.ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  have := isIso_pullback_snd_of_ker_le K.subschemeι A.subschemeι hI
  refine ⟨(A.comapIso K.subschemeι).trans (asIso (pullback.snd K.subschemeι A.subschemeι)), ?_⟩
  change ((A.comapIso K.subschemeι).hom ≫ pullback.snd _ _) ≫ _ = _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- The coefficient of a closed subscheme `A ⊇ K`, read inside `K`, is its coefficient in the
ambient scheme. -/
theorem closedSubschemeCycleCoeff_comap_subschemeι_of_le {T : Scheme.{u}} (p : T ⟶ C.S)
    [LocallyOfFiniteType p] (K A : T.IdealSheafData) (hKA : K ≤ A) (d : ℤ) (t : K.subscheme) :
    closedSubschemeCycleCoeff C (K.subschemeι ≫ p) (A.comap K.subschemeι).subschemeι d t =
      closedSubschemeCycleCoeff C p A.subschemeι d (K.subschemeι.base t) := by
  obtain ⟨_, hcomp⟩ := exists_iso_comap_subschemeι_of_le K A hKA
  rw [← closedSubschemeCycleCoeff_eq_of_iso C p _ _ _ hcomp,
    closedSubschemeCycleCoeff_comp_isClosedImmersion C _ p K.subschemeι rfl]

/-- **A divisor drops the delta-dimension of a closed subscheme meeting it properly.** If `Z` has
delta-dimension at most `k + 1` and `D ∩ Z` is an effective Cartier divisor on `Z`, then `D ∩ Z`
has delta-dimension at most `k`. -/
theorem schemeDeltaDimension_comap_le_of_isEffectiveCartierDivisor {T : Scheme.{u}}
    (p : T ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (Z D : T.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap Z.subschemeι)) :
    schemeDeltaDimension C ((Z.comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ p) ≤
      (k : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C (D.subschemeι ≫ p) _
    fun q ↦ ?_
  set t := D.subschemeι.base ((Z.comap D.subschemeι).subschemeι.base q) with ht
  have htZ : t ∈ (Z.support : Set T) := by
    have := Set.mem_range_self (f := (Z.comap D.subschemeι).subschemeι.base) q
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at this
    exact this
  have htD : t ∈ (D.support : Set T) := by
    rw [← D.range_subschemeι]
    exact Set.mem_range_self _
  rw [relativeDimension_comp_closedImmersion]
  obtain ⟨t', ht'⟩ : t ∈ Set.range Z.subschemeι.base := by rwa [Z.range_subschemeι]
  have hle := relativeDimension_le_of_schemeDeltaDimension_le C p Z.subschemeι hZ t'
  rw [ht'] at hle
  have hne : relativeDimension C.dimensionFunction p t ≠ k + 1 := fun h ↦
    not_mem_support_of_top_dimension_of_effectiveCartier C p k Z D hZ hDZ t htZ h htD
  change relativeDimension C.dimensionFunction p t ≤ k
  omega

/-- **The sum over the second factor at a point over a closed point.** Let `x` be a point of
delta-dimension `n` whose closure lies over a closed point of the base which is not the generic
point of a component, and let `P ⊆ Y` be a closed subscheme of delta-dimension at most `k`, flat
over the base. Then the terms of `[closure {x}] × [P]_k` attached to `x` sum, at every point, to
the coefficient of the product `closure {x} ×_S P` in delta-dimension `n + k - 1`. -/
theorem finsum_exteriorProductDedekindTerm_cycleAssociatedToClosedSubscheme_of_not_dominates
    (hC : IsDedekindChowBase C) (x : X) (hx : relativeDimension C.dimensionFunction f x = n)
    (hnd : ¬ DominatesBaseComponent C f x) (P : Y.IdealSheafData) [Flat (P.subschemeι ≫ g)]
    (k : ℤ) (hP : schemeDeltaDimension C (P.subschemeι ≫ g) ≤ (k : EInt))
    (v : (pullback f g : Scheme.{u})) :
    ∑ᶠ t : Y, exteriorProductDedekindTerm C f g n k (pointClosureCycle C f n x)
        (cycleAssociatedToClosedSubscheme C g P.subschemeι k) v (x, t) =
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap
            (pullback.fst f g) ⊔ P.comap (pullback.snd f g)).subschemeι (n + k - 1) v := by
  classical
  have hs : closure ({f.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  obtain ⟨L, hLinv, σ, hσ, htriv⟩ := hC.exists_section_zeroScheme_eq hs
  have htrivY := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections g L σ htriv
  have hDY := Stacks.Divisors.zeroScheme_pullback g L σ
  set D := Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback g).obj L)
    (AlgebraicGeometry.pullbackGlobalSections g L σ) with hD
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  set K := dedekindPointFibre f g x with hK
  set A := I.comap (pullback.fst f g) ⊔ P.comap (pullback.snd f g) with hA
  have hx1 : (pointClosureCycle C f n x).1 x ≠ 0 := by
    rw [pointClosureCycle_apply_self C f n hx]
    exact one_ne_zero
  obtain ⟨w, hwlft, hwflat, r, hw, hwrel, hrn⟩ :=
    exists_flat_dedekindPointFibre_fibre C f g n hC x hnd L σ hσ _ hx1 _ hDY
  have hdeg : k - 1 + (r : ℤ) = n + k - 1 := by rw [hrn]; ring
  have hk : k - 1 + 1 = k := by ring
  have hβ' : (cycleAssociatedToClosedSubscheme C g P.subschemeι (k - 1 + 1)).1 =
      (cycleAssociatedToClosedSubscheme C g P.subschemeι k).1 := by
    rw [hk]
  have hbase : w ≫ (D.subschemeι ≫ g) = K.subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [← Category.assoc, hw, Category.assoc, ← pullback.condition]
  have key := properPushforward_flatPullback_gysin_of_not_dominates C f g n k hC x hnd L σ hσ
    (pointClosureCycle C f n x) (cycleAssociatedToClosedSubscheme C g P.subschemeι k) _ _ htrivY
    hDY w hw r hwrel hdeg _ hβ' _ (val_cycleGroup_cast C _ hdeg _) v
  rw [← key]
  have hDS : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme C.S L σ) := by
    rw [hσ]
    exact hC.isEffectiveCartierDivisor_vanishingIdeal hs
  have hDZ : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap P.subschemeι) := by
    rw [hDY, ← Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isPullbackDefined_of_flat (P.subschemeι ≫ g) _ hDS
  have hZ : schemeDeltaDimension C (P.subschemeι ≫ g) ≤ ((k - 1 + 1 : ℤ) : EInt) := by
    rwa [hk]
  have hgys := gysinCycleMap_cycleAssociatedToClosedSubscheme_of_isEffectiveCartierDivisor C g
    (k - 1) _ _ htrivY P hZ hDZ
  have hJ := schemeDeltaDimension_comap_le_of_isEffectiveCartierDivisor C g (k - 1) P D hZ hDZ
  have hKA : K ≤ A := le_sup_left
  have hKI : K = I.comap (pullback.fst f g) := rfl
  have hAK : A.comap K.subschemeι = (P.comap D.subschemeι).comap w := by
    rw [hA, Scheme.IdealSheafData.comap_sup, ← hKI, comap_subschemeι_self, bot_sup_eq,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hw]
  by_cases hv : v ∈ Set.range K.subschemeι.base
  · obtain ⟨v', rfl⟩ := hv
    rw [properPushforward_apply_image_of_isClosedImmersion, val_cycleGroup_cast,
      flatPullback_apply, pointClosureCycle_apply_self C f n hx, one_smul, hgys]
    change closedSubschemeCycleCoeff C (D.subschemeι ≫ g) (P.comap D.subschemeι).subschemeι
      (k - 1) (w.base v') * _ = _
    rw [← closedSubschemeCycleCoeff_comap C (K.subschemeι ≫ (pullback.fst f g ≫ f))
      (D.subschemeι ≫ g) w hbase r hwrel (P.comap D.subschemeι) (k - 1) hJ v', hdeg,
      ← closedSubschemeCycleCoeff_congr_idealSheaf C _ hAK]
    exact closedSubschemeCycleCoeff_comap_subschemeι_of_le C (pullback.fst f g ≫ f) K A hKA _ v'
  · rw [properPushforward_apply_of_notMem_range C _ _ _ rfl _ _ hv, eq_comm]
    by_contra h
    refine hv ?_
    rw [K.range_subschemeι, hKI, Scheme.IdealSheafData.support_comap]
    exact fst_mem_support_of_closedSubschemeCycleCoeff_ne_zero C f g I P _ v h

end CollapseClosedPoint

/-! ### The product of two point closures -/

section PointClosureProduct

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The product of two point closures, as the inverse image along the symmetry of the fibre
product of the product in the other order. -/
theorem exteriorProductIdeal_eq_comap_pullbackSymmetry (x : X) (y : Y) :
    exteriorProductIdeal f g x y =
      (exteriorProductIdeal g f y x).comap (pullbackSymmetry f g).hom := by
  rw [exteriorProductIdeal, exteriorProductIdeal, Scheme.IdealSheafData.comap_sup,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
  exact sup_comm _ _

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- The symmetry of the fibre product lies over the base. -/
theorem pullbackSymmetry_hom_comp_structure :
    (pullbackSymmetry f g).hom ≫ (pullback.fst g f ≫ g) = pullback.fst f g ≫ f := by
  rw [← Category.assoc, pullbackSymmetry_hom_comp_fst, ← pullback.condition]

/-- **The delta-dimension of the product of two point closures.** If one of two points of
delta-dimensions `n` and `m` dominates an irreducible component of the base at a point which is not
closed, the product of their closures has delta-dimension at most `n + m - 1`. -/
theorem schemeDeltaDimension_exteriorProductIdeal_le (hC : IsDedekindChowBase C) (x : X) (y : Y)
    (hx : relativeDimension C.dimensionFunction f x = n)
    (hy : relativeDimension C.dimensionFunction g y = m)
    (h : (DominatesBaseComponent C f x ∧ ¬ IsClosed ({f.base x} : Set C.S)) ∨
      (DominatesBaseComponent C g y ∧ ¬ IsClosed ({g.base y} : Set C.S))) :
    schemeDeltaDimension C ((exteriorProductIdeal f g x y).subschemeι ≫ pullback.fst f g ≫ f) ≤
      ((n + m - 1 : ℤ) : EInt) := by
  have key : ∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ C.S) [LocallyOfFiniteType f'] (g' : Y' ⟶ C.S)
      [LocallyOfFiniteType g'] (n' m' : ℤ) (x' : X') (y' : Y'),
      relativeDimension C.dimensionFunction f' x' = n' →
      relativeDimension C.dimensionFunction g' y' = m' →
      DominatesBaseComponent C g' y' → ¬ IsClosed ({g'.base y'} : Set C.S) →
      schemeDeltaDimension C ((exteriorProductIdeal f' g' x' y').subschemeι ≫
        pullback.fst f' g' ≫ f') ≤ ((n' + m' - 1 : ℤ) : EInt) := by
    intro X' Y' f' _ g' _ n' m' x' y' hx' hy' hd hnc
    obtain ⟨hfl, r, hr, hm⟩ :=
      exists_relativeDimension_vanishingIdeal_of_dominates C g' m' hC y' hy' hd hnc
    have hI := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f' x' hx'
    have hdeg : n' + m' - 1 = n' + (r : ℤ) := by rw [hm]; ring
    rw [hdeg]
    exact schemeDeltaDimension_product_le C f' g' _ _ r hr n' (le_of_eq hI)
  rcases h with h | h
  · have h' := key g f m n y x hy hx h.1 h.2
    rw [exteriorProductIdeal_eq_comap_pullbackSymmetry]
    set E := exteriorProductIdeal g f y x
    set φ := comapSubschemeIsoOfIsIso (pullbackSymmetry f g).hom E
    have hmor : (E.comap (pullbackSymmetry f g).hom).subschemeι ≫ pullback.fst f g ≫ f =
        φ.hom ≫ E.subschemeι ≫ pullback.fst g f ≫ g := by
      rw [← Category.assoc φ.hom, comapSubschemeIsoOfIsIso_hom_subschemeι, Category.assoc,
        pullbackSymmetry_hom_comp_structure]
    rwa [schemeDeltaDimension_congr C hmor, schemeDeltaDimension_comp_iso,
      show n + m - 1 = m + n - 1 by ring]
  · exact key f g n m x y hx hy h.1 h.2

omit [LocallyOfFiniteType g] in
/-- **The product of two dominating point closures is flat over the base.** -/
theorem flat_exteriorProductIdeal (hC : IsDedekindChowBase C) (x : X) (y : Y)
    (hdx : DominatesBaseComponent C f x) (hdy : DominatesBaseComponent C g y) :
    Flat ((exteriorProductIdeal f g x y).subschemeι ≫ pullback.fst f g ≫ f) := by
  obtain ⟨hvflat, r, hr, -⟩ := exists_relativeDimension_dedekindPointFibre C f g hC x hdx
  set K := dedekindPointFibre f g x with hK
  set E := exteriorProductIdeal f g x y with hE
  set Iy := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y)) with hIy
  set v := K.subschemeι ≫ pullback.snd f g with hv
  have hinty : IsIntegral Iy.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  have hηy : Iy.subschemeι.base (genericPoint Iy.subscheme) = y :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure y
  have hflaty : Flat (Iy.subschemeι ≫ g) :=
    hC.flat_of_mem_irreducibleComponents (Iy.subschemeι ≫ g)
      (by rw [Scheme.Hom.comp_apply, hηy]; exact hdy)
  have hEK : E.comap K.subschemeι = Iy.comap v :=
    comap_exteriorProductIdeal_dedekindPointFibre f g x y
  obtain ⟨ψ, hcomp⟩ := exists_iso_comap_subschemeι_of_le K E le_sup_left
  have hflatJ : Flat ((E.comap K.subschemeι).subschemeι ≫ K.subschemeι ≫ pullback.fst f g ≫ f) := by
    rw [hEK]
    have hmor : (Iy.comap v).subschemeι ≫ K.subschemeι ≫ pullback.fst f g ≫ f =
        (Iy.comapIso v).hom ≫ pullback.snd v Iy.subschemeι ≫ Iy.subschemeι ≫ g := by
      rw [pullback.condition, hv, ← pullback.condition_assoc,
        ← Scheme.IdealSheafData.comapIso_hom_fst Iy v]
      simp only [Category.assoc]
      rfl
    rw [hmor]
    infer_instance
  have hmor : E.subschemeι ≫ pullback.fst f g ≫ f =
      ψ.inv ≫ (E.comap K.subschemeι).subschemeι ≫ K.subschemeι ≫ pullback.fst f g ≫ f := by
    rw [← Category.assoc (E.comap K.subschemeι).subschemeι, ← hcomp, Category.assoc,
      Iso.inv_hom_id_assoc]
  rw [hmor]
  infer_instance

/-- If the closure of the image of `a` is an irreducible component of the base and the image of
`a` lies in the closure of the image of `b`, then the closure of the image of `b` is that
component. -/
theorem DominatesBaseComponent.of_mem_closure {T T' : Scheme.{u}} {p : T ⟶ C.S} {q : T' ⟶ C.S}
    {a : T} {b : T'} (hab : p.base a ∈ closure ({q.base b} : Set C.S))
    (ha : DominatesBaseComponent C p a) : DominatesBaseComponent C q b := by
  unfold DominatesBaseComponent at ha ⊢
  have hsub : closure ({p.base a} : Set C.S) ⊆ closure ({q.base b} : Set C.S) :=
    closure_minimal (Set.singleton_subset_iff.2 hab) isClosed_closure
  have heq := le_antisymm hsub (ha.2 isIrreducible_singleton.closure hsub)
  rwa [← heq]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- A point of the product of two point closures which dominates a component of the base lies
over two dominating points. -/
theorem dominates_of_mem_support_exteriorProductIdeal (x : X) (y : Y)
    (w : (pullback f g : Scheme.{u}))
    (hw : w ∈ ((exteriorProductIdeal f g x y).support : Set (pullback f g : Scheme.{u})))
    (hd : DominatesBaseComponent C (pullback.fst f g ≫ f) w) :
    DominatesBaseComponent C f x ∧ DominatesBaseComponent C g y := by
  rw [exteriorProductIdeal, Scheme.IdealSheafData.support_sup] at hw
  obtain ⟨h1, h2⟩ := hw
  rw [Scheme.IdealSheafData.support_comap] at h1 h2
  replace h1 : (pullback.fst f g).base w ∈ closure ({x} : Set X) := by simpa using h1
  replace h2 : (pullback.snd f g).base w ∈ closure ({y} : Set Y) := by simpa using h2
  refine ⟨DominatesBaseComponent.of_mem_closure C (p := pullback.fst f g ≫ f)
      (mem_closure_singleton_map f.continuous h1) hd,
    DominatesBaseComponent.of_mem_closure C (p := pullback.fst f g ≫ f) ?_ hd⟩
  have hc : (pullback.fst f g ≫ f).base w = g.base ((pullback.snd f g).base w) := by
    rw [pullback.condition, Scheme.Hom.comp_apply]
  rw [hc]
  exact mem_closure_singleton_map g.continuous h2

end PointClosureProduct

/-! ### Exterior products of point closures with closed subschemes -/

section ProductFormulas

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType g] in
/-- Every point of the symmetric fibre product is the image of its partner. -/
theorem pullbackSymmetry_inv_hom_apply (w : (pullback f g : Scheme.{u})) :
    (pullbackSymmetry f g).inv.base ((pullbackSymmetry f g).hom.base w) = w := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- **A point dominating a component which is a closed point.** If the closure of `x` dominates an
irreducible component of the base which is a single closed point, the exterior product with
`[closure {x}]_n` vanishes. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_left_eq_zero (hC : IsDedekindChowBase C)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = n)
    (hdom : DominatesBaseComponent C f x) (hcl : IsClosed ({f.base x} : Set C.S)) {k : ℤ}
    (β : CycleGroup C g k) :
    exteriorProductDedekindCycles C f g n k (pointClosureCycle C f n x) β = 0 := by
  classical
  obtain ⟨hflat, r, hr, hrx⟩ := exists_relativeDimension_dedekindPointFibre C f g hC x hdom
  rw [hC.2.1 _ hcl, zero_add, hx] at hrx
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
  change (exteriorProductDedekindCycles C f g n k (pointClosureCycle C f n x) β).1 v = 0
  rw [exteriorProductDedekindCycles_pointClosureCycle_left_apply]
  by_cases hv : v ∈ Set.range (dedekindPointFibre f g x).subschemeι.base
  · obtain ⟨w, rfl⟩ := hv
    rw [finsum_exteriorProductDedekindTerm_of_flat C f g n k _ β x hdom r hr w,
      ite_eq_right (by omega)]
  · exact finsum_eq_zero_of_forall_eq_zero fun t ↦
      exteriorProductDedekindTerm_eq_zero_of_notMem_range C f g n k _ β x t hv

/-- If the closure of `y` dominates an irreducible component of the base which is a single closed
point, the exterior product with `[closure {y}]_m` vanishes. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_right_eq_zero (hC : IsDedekindChowBase C)
    (y : Y) (hy : relativeDimension C.dimensionFunction g y = m)
    (hdom : DominatesBaseComponent C g y) (hcl : IsClosed ({g.base y} : Set C.S)) {k : ℤ}
    (α : CycleGroup C f k) :
    exteriorProductDedekindCycles C f g k m α (pointClosureCycle C g m y) = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)
  change (exteriorProductDedekindCycles C f g k m α (pointClosureCycle C g m y)).1 u = 0
  rw [← pullbackSymmetry_inv_hom_apply C f g u, exteriorProductDedekindCycles_pullbackSymmetry,
    exteriorProductDedekindCycles_pointClosureCycle_left_eq_zero C g f m hC y hy hdom hcl α]
  rfl

/-- **The exterior product of two point closures.** -/
theorem exteriorProductDedekindCycles_pointClosureCycle_pointClosureCycle (x : X) (y : Y)
    (hx : relativeDimension C.dimensionFunction f x = n)
    (hy : relativeDimension C.dimensionFunction g y = m) :
    exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
        (pointClosureCycle C g m y) =
      open Classical in
      if DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y then
        cycleAssociatedToClosedSubscheme C (pullback.fst f g ≫ f)
          (exteriorProductIdeal f g x y).subschemeι (n + m - 1)
      else 0 := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  change (exteriorProductDedekindCycles C f g n m _ _).1 w = (if _ then _ else _ :
    CycleGroup C (pullback.fst f g ≫ f) (n + m - 1)).1 w
  rw [exteriorProductDedekindCycles_pointClosureCycle_left_apply,
    finsum_eq_single _ y fun t ht ↦ exteriorProductDedekindTerm_eq_zero_of_right C f g n m _ _ w
      (x, t) (pointClosureCycle_apply_of_ne C g m ht),
    exteriorProductDedekindTerm_pointClosureCycle C f g n x hx,
    pointClosureCycle_apply_self C g m hy, one_mul]
  split_ifs <;> rfl

/-- **The exterior product of a point closure with a closed subscheme.** Let `x` be a point of
delta-dimension `n` and `P ⊆ Y` a closed subscheme of delta-dimension at most `k`. If either `x`
dominates an irreducible component of the base at a point which is not closed, or `x` dominates no
component and `P` is flat over the base, then

  `[closure {x}]_n × [P]_k = [closure {x} ×_S P]_{n+k-1}`. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_closedSubscheme_apply
    (hC : IsDedekindChowBase C) (x : X) (hx : relativeDimension C.dimensionFunction f x = n)
    (P : Y.IdealSheafData) (k : ℤ) (hP : schemeDeltaDimension C (P.subschemeι ≫ g) ≤ (k : EInt))
    (hcond : (DominatesBaseComponent C f x ∧ ¬ IsClosed ({f.base x} : Set C.S)) ∨
      (¬ DominatesBaseComponent C f x ∧ Flat (P.subschemeι ≫ g)))
    (v : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n k (pointClosureCycle C f n x)
        (cycleAssociatedToClosedSubscheme C g P.subschemeι k)).1 v =
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap
            (pullback.fst f g) ⊔ P.comap (pullback.snd f g)).subschemeι (n + k - 1) v := by
  rw [exteriorProductDedekindCycles_pointClosureCycle_left_apply]
  rcases hcond with ⟨hdom, hnc⟩ | ⟨hnd, hflat⟩
  · exact finsum_exteriorProductDedekindTerm_cycleAssociatedToClosedSubscheme_of_dominates C f g n
      hC x hx hdom hnc P k hP v
  · exact finsum_exteriorProductDedekindTerm_cycleAssociatedToClosedSubscheme_of_not_dominates C f
      g n hC x hx hnd P k hP v

/-- The coefficient of a closed subscheme of the target of an isomorphism over the base, read
through the isomorphism. -/
theorem closedSubschemeCycleCoeff_comap_hom_of_isIso {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (ι : A ⟶ B) [IsIso ι]
    (hι : ι ≫ sB = sA) (I : B.IdealSheafData) (k : ℤ) (a : A) :
    closedSubschemeCycleCoeff C sA (I.comap ι).subschemeι k a =
      closedSubschemeCycleCoeff C sB I.subschemeι k (ι.base a) := by
  rw [closedSubschemeCycleCoeff_of_isIso_ambient C sA sB ι hι (I.comap ι).subschemeι k a]
  exact closedSubschemeCycleCoeff_eq_of_iso C sB ((I.comap ι).subschemeι ≫ ι) I.subschemeι
    (comapSubschemeIsoOfIsIso ι I) (comapSubschemeIsoOfIsIso_hom_subschemeι ι I) k (ι.base a)

/-- **The exterior product of a closed subscheme with a point closure.** The mirror image of the
exterior product of a point closure with a closed subscheme:

  `[P]_k × [closure {y}]_m = [P ×_S closure {y}]_{k+m-1}`. -/
theorem exteriorProductDedekindCycles_closedSubscheme_pointClosureCycle_apply
    (hC : IsDedekindChowBase C) (y : Y) (hy : relativeDimension C.dimensionFunction g y = m)
    (P : X.IdealSheafData) (k : ℤ) (hP : schemeDeltaDimension C (P.subschemeι ≫ f) ≤ (k : EInt))
    (hcond : (DominatesBaseComponent C g y ∧ ¬ IsClosed ({g.base y} : Set C.S)) ∨
      (¬ DominatesBaseComponent C g y ∧ Flat (P.subschemeι ≫ f)))
    (u : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g k m (cycleAssociatedToClosedSubscheme C f P.subschemeι k)
        (pointClosureCycle C g m y)).1 u =
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (P.comap (pullback.fst f g) ⊔ (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g)).subschemeι
        (k + m - 1) u := by
  rw [← pullbackSymmetry_inv_hom_apply C f g u, exteriorProductDedekindCycles_pullbackSymmetry,
    pullbackSymmetry_inv_hom_apply,
    exteriorProductDedekindCycles_pointClosureCycle_closedSubscheme_apply C g f m
      hC y hy P k hP hcond, show m + k - 1 = k + m - 1 by ring,
    ← closedSubschemeCycleCoeff_comap_hom_of_isIso C (pullback.fst f g ≫ f) (pullback.fst g f ≫ g)
      (pullbackSymmetry f g).hom (pullbackSymmetry_hom_comp_structure C f g)]
  refine closedSubschemeCycleCoeff_congr_idealSheaf C _ ?_ _ _
  rw [Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  exact sup_comm _ _

/-- An exterior product vanishes when every pair of components it involves has two
non-dominating entries. -/
theorem exteriorProductDedekindCycles_apply_eq_zero_of_not_dominates (α : CycleGroup C f n)
    (β : CycleGroup C g m)
    (h : ∀ (s : X) (t : Y), α.1 s ≠ 0 → β.1 t ≠ 0 →
      ¬ DominatesBaseComponent C f s ∧ ¬ DominatesBaseComponent C g t)
    (w : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n m α β).1 w = 0 := by
  classical
  rw [exteriorProductDedekindCycles_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun p ↦ ?_
  by_cases hs : α.1 p.1 = 0
  · exact exteriorProductDedekindTerm_eq_zero_of_left C f g n m α β w p hs
  by_cases ht : β.1 p.2 = 0
  · exact exteriorProductDedekindTerm_eq_zero_of_right C f g n m α β w p ht
  obtain ⟨h1, h2⟩ := h p.1 p.2 hs ht
  unfold exteriorProductDedekindTerm
  rw [ite_eq_right (by tauto)]

/-- The points carrying a coefficient of the cycle of a product of two point closures one of which
does not dominate a component of the base do not dominate a component either. -/
theorem not_dominates_of_cycleAssociatedToClosedSubscheme_exteriorProductIdeal_ne_zero (x : X)
    (y : Y) (h : ¬ DominatesBaseComponent C f x ∨ ¬ DominatesBaseComponent C g y) (d : ℤ)
    (w : (pullback f g : Scheme.{u}))
    (hw : (cycleAssociatedToClosedSubscheme C (pullback.fst f g ≫ f)
      (exteriorProductIdeal f g x y).subschemeι d).1 w ≠ 0) :
    ¬ DominatesBaseComponent C (pullback.fst f g ≫ f) w := by
  intro hd
  have hmem := mem_support_of_closedSubschemeCycleCoeff_ne_zero C (pullback.fst f g ≫ f) _ d w hw
  have := dominates_of_mem_support_exteriorProductIdeal C f g x y w hmem hd
  tauto

end ProductFormulas

/-! ### Associativity on fundamental cycles of point closures -/

section PrimeAssociativity

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S) [LocallyOfFiniteType h] (n m l : ℤ)

/-- The hypothesis of the product formula with a point closure, for a point `t` which does not lie
over a closed dominated component, when the other factor is a product of two point closures. -/
private theorem dominates_not_closed_or_flat_exteriorProductIdeal (hC : IsDedekindChowBase C)
    {Y' T : Scheme.{u}} (g' : Y' ⟶ C.S) (q : T ⟶ C.S) (t : T) (x : X) (y : Y')
    (hbt : ¬ (DominatesBaseComponent C q t ∧ IsClosed ({q.base t} : Set C.S)))
    (hxyt : DominatesBaseComponent C q t ∨
      (DominatesBaseComponent C f x ∧ DominatesBaseComponent C g' y)) :
    (DominatesBaseComponent C q t ∧ ¬ IsClosed ({q.base t} : Set C.S)) ∨
      (¬ DominatesBaseComponent C q t ∧
        Flat ((exteriorProductIdeal f g' x y).subschemeι ≫ pullback.fst f g' ≫ f)) := by
  by_cases hd : DominatesBaseComponent C q t
  · exact Or.inl ⟨hd, fun hcl ↦ hbt ⟨hd, hcl⟩⟩
  · have hd' := hxyt.resolve_left hd
    exact Or.inr ⟨hd, flat_exteriorProductIdeal C f g' hC x y hd'.1 hd'.2⟩

/-- The left-bracketed product of three point closures, where it does not vanish: the
multiplicity of the triple product `(closure {x} ×_S closure {y}) ×_S closure {z}`. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_assoc_left_apply
    (hC : IsDedekindChowBase C) (x : X) (y : Y) (z : Z)
    (hx : relativeDimension C.dimensionFunction f x = n)
    (hy : relativeDimension C.dimensionFunction g y = m)
    (hz : relativeDimension C.dimensionFunction h z = l)
    (hxy : DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y)
    (hxyz : DominatesBaseComponent C h z ∨
      (DominatesBaseComponent C f x ∧ DominatesBaseComponent C g y))
    (hbx : ¬ (DominatesBaseComponent C f x ∧ IsClosed ({f.base x} : Set C.S)))
    (hby : ¬ (DominatesBaseComponent C g y ∧ IsClosed ({g.base y} : Set C.S)))
    (hbz : ¬ (DominatesBaseComponent C h z ∧ IsClosed ({h.base z} : Set C.S)))
    (u : (pullback (pullback.fst f g ≫ f) h : Scheme.{u})) :
    (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
        (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
          (pointClosureCycle C g m y)) (pointClosureCycle C h l z)).1 u =
      tripleProductWeightLeft C f g h (n + m + l - 2) x y z u := by
  classical
  rw [exteriorProductDedekindCycles_pointClosureCycle_pointClosureCycle C f g n m x y hx hy,
    ite_eq_left hxy]
  have hP := schemeDeltaDimension_exteriorProductIdeal_le C f g n m hC x y hx hy (by tauto)
  have hcond := dominates_not_closed_or_flat_exteriorProductIdeal C f hC g h z x y hbz hxyz
  rw [exteriorProductDedekindCycles_closedSubscheme_pointClosureCycle_apply C
    (pullback.fst f g ≫ f) h l hC z hz (exteriorProductIdeal f g x y) (n + m - 1) hP hcond u,
    show n + m - 1 + l - 1 = n + m + l - 2 by ring]
  rfl

/-- The right-bracketed product of three point closures, where it does not vanish: the
multiplicity of the triple product `closure {x} ×_S (closure {y} ×_S closure {z})`. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_assoc_right_apply
    (hC : IsDedekindChowBase C) (x : X) (y : Y) (z : Z)
    (hx : relativeDimension C.dimensionFunction f x = n)
    (hy : relativeDimension C.dimensionFunction g y = m)
    (hz : relativeDimension C.dimensionFunction h z = l)
    (hyz : DominatesBaseComponent C g y ∨ DominatesBaseComponent C h z)
    (hxyz : DominatesBaseComponent C f x ∨
      (DominatesBaseComponent C g y ∧ DominatesBaseComponent C h z))
    (hbx : ¬ (DominatesBaseComponent C f x ∧ IsClosed ({f.base x} : Set C.S)))
    (hby : ¬ (DominatesBaseComponent C g y ∧ IsClosed ({g.base y} : Set C.S)))
    (hbz : ¬ (DominatesBaseComponent C h z ∧ IsClosed ({h.base z} : Set C.S)))
    (v : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1)
        (pointClosureCycle C f n x)
        (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
          (pointClosureCycle C h l z))).1 v =
      tripleProductWeightRight C f g h (n + m + l - 2) x y z v := by
  classical
  rw [exteriorProductDedekindCycles_pointClosureCycle_pointClosureCycle C g h m l y z hy hz,
    ite_eq_left hyz]
  have hP := schemeDeltaDimension_exteriorProductIdeal_le C g h m l hC y z hy hz (by tauto)
  have hcond := dominates_not_closed_or_flat_exteriorProductIdeal C g hC h f x y z hbx hxyz
  rw [exteriorProductDedekindCycles_pointClosureCycle_closedSubscheme_apply C f
    (pullback.fst g h ≫ g) n hC x hx (exteriorProductIdeal g h y z) (m + l - 1) hP hcond v,
    show n + (m + l - 1) - 1 = n + m + l - 2 by ring]
  rfl

/-- The left-bracketed product of three point closures vanishes when no pair of components it
involves has a dominating entry. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_assoc_left_eq_zero (x : X) (y : Y) (z : Z)
    (hx : relativeDimension C.dimensionFunction f x = n)
    (hy : relativeDimension C.dimensionFunction g y = m)
    (h0 : ¬ (DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y) ∨
      (¬ DominatesBaseComponent C h z ∧
        (¬ DominatesBaseComponent C f x ∨ ¬ DominatesBaseComponent C g y)))
    (u : (pullback (pullback.fst f g ≫ f) h : Scheme.{u})) :
    (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
        (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
          (pointClosureCycle C g m y)) (pointClosureCycle C h l z)).1 u = 0 := by
  classical
  rw [exteriorProductDedekindCycles_pointClosureCycle_pointClosureCycle C f g n m x y hx hy]
  split_ifs with hg
  · have h1 := h0.resolve_left (not_not.2 hg)
    refine exteriorProductDedekindCycles_apply_eq_zero_of_not_dominates C _ h _ _ _ _
      (fun s t hs ht ↦ ⟨?_, ?_⟩) u
    · exact not_dominates_of_cycleAssociatedToClosedSubscheme_exteriorProductIdeal_ne_zero C f g x
        y h1.2 _ s hs
    · obtain rfl : t = z := not_not.1 fun hne ↦ ht (pointClosureCycle_apply_of_ne C h l hne)
      exact h1.1
  · rw [map_zero, AddMonoidHom.zero_apply]
    rfl

/-- The right-bracketed product of three point closures vanishes when no pair of components it
involves has a dominating entry. -/
theorem exteriorProductDedekindCycles_pointClosureCycle_assoc_right_eq_zero (x : X) (y : Y)
    (z : Z) (hy : relativeDimension C.dimensionFunction g y = m)
    (hz : relativeDimension C.dimensionFunction h z = l)
    (h0 : ¬ (DominatesBaseComponent C g y ∨ DominatesBaseComponent C h z) ∨
      (¬ DominatesBaseComponent C f x ∧
        (¬ DominatesBaseComponent C g y ∨ ¬ DominatesBaseComponent C h z)))
    (v : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1)
        (pointClosureCycle C f n x)
        (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
          (pointClosureCycle C h l z))).1 v = 0 := by
  classical
  rw [exteriorProductDedekindCycles_pointClosureCycle_pointClosureCycle C g h m l y z hy hz]
  split_ifs with hg
  · have h1 := h0.resolve_left (not_not.2 hg)
    refine exteriorProductDedekindCycles_apply_eq_zero_of_not_dominates C f _ _ _ _ _
      (fun s t hs ht ↦ ⟨?_, ?_⟩) v
    · obtain rfl : s = x := not_not.1 fun hne ↦ hs (pointClosureCycle_apply_of_ne C f n hne)
      exact h1.1
    · exact not_dominates_of_cycleAssociatedToClosedSubscheme_exteriorProductIdeal_ne_zero C g h y
        z h1.2 _ t ht
  · rw [map_zero]
    rfl

/-- **Associativity of the exterior product on three point closures.** -/
theorem exteriorProductDedekindCycles_pointClosureCycle_assoc (hC : IsDedekindChowBase C)
    (x : X) (y : Y) (z : Z) (hx : relativeDimension C.dimensionFunction f x = n)
    (hy : relativeDimension C.dimensionFunction g y = m)
    (hz : relativeDimension C.dimensionFunction h z = l)
    (v : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
        (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
          (pointClosureCycle C g m y)) (pointClosureCycle C h l z)).1
        ((tripleFibreProductAssoc f g h).inv.base v) =
      (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1)
        (pointClosureCycle C f n x)
        (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
          (pointClosureCycle C h l z))).1 v := by
  classical
  by_cases hbx : DominatesBaseComponent C f x ∧ IsClosed ({f.base x} : Set C.S)
  · rw [exteriorProductDedekindCycles_pointClosureCycle_left_eq_zero C f g n hC x hx hbx.1 hbx.2,
      exteriorProductDedekindCycles_pointClosureCycle_left_eq_zero C f _ n hC x hx hbx.1 hbx.2,
      map_zero, AddMonoidHom.zero_apply]
    rfl
  by_cases hbz : DominatesBaseComponent C h z ∧ IsClosed ({h.base z} : Set C.S)
  · rw [exteriorProductDedekindCycles_pointClosureCycle_right_eq_zero C _ h l hC z hz hbz.1 hbz.2,
      exteriorProductDedekindCycles_pointClosureCycle_right_eq_zero C g h l hC z hz hbz.1 hbz.2,
      map_zero]
    rfl
  by_cases hby : DominatesBaseComponent C g y ∧ IsClosed ({g.base y} : Set C.S)
  · rw [exteriorProductDedekindCycles_pointClosureCycle_right_eq_zero C f g m hC y hy hby.1 hby.2,
      exteriorProductDedekindCycles_pointClosureCycle_left_eq_zero C g h m hC y hy hby.1 hby.2,
      map_zero, map_zero, AddMonoidHom.zero_apply]
    rfl
  have hval : ∀ (hxy : DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y)
      (hxyz : DominatesBaseComponent C h z ∨
        (DominatesBaseComponent C f x ∧ DominatesBaseComponent C g y))
      (hyz : DominatesBaseComponent C g y ∨ DominatesBaseComponent C h z)
      (hxyz' : DominatesBaseComponent C f x ∨
        (DominatesBaseComponent C g y ∧ DominatesBaseComponent C h z)),
      (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
          (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
            (pointClosureCycle C g m y)) (pointClosureCycle C h l z)).1
          ((tripleFibreProductAssoc f g h).inv.base v) =
        (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1)
          (pointClosureCycle C f n x)
          (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
            (pointClosureCycle C h l z))).1 v := by
    intro hxy hxyz hyz hxyz'
    rw [exteriorProductDedekindCycles_pointClosureCycle_assoc_left_apply C f g h n m l hC x y z
        hx hy hz hxy hxyz hbx hby hbz,
      exteriorProductDedekindCycles_pointClosureCycle_assoc_right_apply C f g h n m l hC x y z
        hx hy hz hyz hxyz' hbx hby hbz]
    exact tripleProductWeight_assoc C f g h (n + m + l - 2) x y z v
  have hzero : ∀ (h0 : ¬ (DominatesBaseComponent C f x ∨ DominatesBaseComponent C g y) ∨
        (¬ DominatesBaseComponent C h z ∧
          (¬ DominatesBaseComponent C f x ∨ ¬ DominatesBaseComponent C g y)))
      (h0' : ¬ (DominatesBaseComponent C g y ∨ DominatesBaseComponent C h z) ∨
        (¬ DominatesBaseComponent C f x ∧
          (¬ DominatesBaseComponent C g y ∨ ¬ DominatesBaseComponent C h z))),
      (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
          (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
            (pointClosureCycle C g m y)) (pointClosureCycle C h l z)).1
          ((tripleFibreProductAssoc f g h).inv.base v) =
        (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1)
          (pointClosureCycle C f n x)
          (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
            (pointClosureCycle C h l z))).1 v := by
    intro h0 h0'
    rw [exteriorProductDedekindCycles_pointClosureCycle_assoc_left_eq_zero C f g h n m l x y z
        hx hy h0,
      exteriorProductDedekindCycles_pointClosureCycle_assoc_right_eq_zero C f g h n m l x y z
        hy hz h0']
  by_cases hdx : DominatesBaseComponent C f x <;> by_cases hdy : DominatesBaseComponent C g y <;>
    by_cases hdz : DominatesBaseComponent C h z
  · exact hval (Or.inl hdx) (Or.inl hdz) (Or.inl hdy) (Or.inl hdx)
  · exact hval (Or.inl hdx) (Or.inr ⟨hdx, hdy⟩) (Or.inl hdy) (Or.inl hdx)
  · exact hval (Or.inl hdx) (Or.inl hdz) (Or.inr hdz) (Or.inl hdx)
  · exact hzero (Or.inr ⟨hdz, Or.inr hdy⟩) (Or.inl fun h' ↦ h'.elim hdy hdz)
  · exact hval (Or.inr hdy) (Or.inl hdz) (Or.inl hdy) (Or.inr ⟨hdy, hdz⟩)
  · exact hzero (Or.inr ⟨hdz, Or.inl hdx⟩) (Or.inr ⟨hdx, Or.inr hdz⟩)
  · exact hzero (Or.inl fun h' ↦ h'.elim hdx hdy) (Or.inr ⟨hdx, Or.inl hdy⟩)
  · exact hzero (Or.inl fun h' ↦ h'.elim hdx hdy) (Or.inl fun h' ↦ h'.elim hdy hdz)

end PrimeAssociativity

/-! ### Associativity of the exterior product of cycles -/

section CycleAssociativity

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S) [LocallyOfFiniteType h] (n m l : ℤ)

/-- Proper pushforward along the associator reads a cycle at the transported point. -/
theorem properPushforward_tripleFibreProductAssoc_apply {d : ℤ}
    (c : CycleGroup C (pullback.fst (pullback.fst f g ≫ f) h ≫ (pullback.fst f g ≫ f)) d)
    (v : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (properPushforward C (pullback.fst (pullback.fst f g ≫ f) h ≫ (pullback.fst f g ≫ f))
        (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleFibreProductAssoc f g h).hom
        (tripleFibreProductAssoc_hom_structureMorphism f g h) d c).1 v =
      c.1 ((tripleFibreProductAssoc f g h).inv.base v) := by
  conv_lhs => rw [← tripleProductAssoc_hom_base_inv_base f g h v]
  exact properPushforward_apply_image_of_isClosedImmersion C _ _ _ _ _ c _

/-- **Stacks 0FC8, at the level of cycles.** Over a base as in Stacks section 42.63 the exterior
product of cycles is associative: for `α ∈ Z_n(X)`, `β ∈ Z_m(Y)` and `γ ∈ Z_l(Z)`, the pushforward
of `(α × β) × γ` along the associator `(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)` is `α × (β × γ)`. -/
theorem isExteriorProductDedekindAssociative (hC : IsDedekindChowBase C) :
    IsExteriorProductDedekindAssociative C f g h n m l := by
  intro α β γ
  refine Function.locallyFinsuppWithin.ext fun v ↦ ?_
  change (properPushforward C _ _ _ _ _ _).1 v = _
  rw [properPushforward_tripleFibreProductAssoc_apply]
  set u := (tripleFibreProductAssoc f g h).inv.base v with hu
  set x₀ := (pullback.fst f (pullback.fst g h ≫ g)).base v with hx₀
  set t₀ := (pullback.snd f (pullback.fst g h ≫ g)).base v with ht₀
  set y₀ := (pullback.fst g h).base t₀ with hy₀
  set z₀ := (pullback.snd g h).base t₀ with hz₀
  set a₀ := (pullback.fst (pullback.fst f g ≫ f) h).base u with ha₀
  have hxa : (pullback.fst f g).base a₀ = x₀ := fst_fst_tripleProductAssoc_inv f g h v
  have hya : (pullback.snd f g).base a₀ = y₀ := snd_fst_tripleProductAssoc_inv f g h v
  have hzu : (pullback.snd (pullback.fst f g ≫ f) h).base u = z₀ :=
    snd_tripleProductAssoc_inv f g h v
  have hself : ∀ {T : Type u} [TopologicalSpace T] (t : T), t ∈ closure ({t} : Set T) :=
    fun t ↦ subset_closure rfl
  have H1 : ∀ (x : X) (y : Y) (z : Z), relativeDimension C.dimensionFunction f x = n →
      relativeDimension C.dimensionFunction g y = m →
      relativeDimension C.dimensionFunction h z = l →
      (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
          (exteriorProductDedekindCycles C f g n m (pointClosureCycle C f n x)
            (pointClosureCycle C g m y)) (pointClosureCycle C h l z)).1 u =
        (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1)
          (pointClosureCycle C f n x)
          (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
            (pointClosureCycle C h l z))).1 v :=
    fun x y z hx hy hz ↦
      exteriorProductDedekindCycles_pointClosureCycle_assoc C f g h n m l hC x y z hx hy hz v
  have H2 : ∀ (y : Y) (z : Z), relativeDimension C.dimensionFunction g y = m →
      relativeDimension C.dimensionFunction h z = l → ∀ α' : CycleGroup C f n,
      (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
          (exteriorProductDedekindCycles C f g n m α' (pointClosureCycle C g m y))
          (pointClosureCycle C h l z)).1 u =
        (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1) α'
          (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
            (pointClosureCycle C h l z))).1 v := by
    intro y z hy hz
    have key := addMonoidHom_ext_of_pointClosureCycle C f n
      (AddMonoidHom.mk' (fun α' ↦ (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h
          (n + m - 1) l (exteriorProductDedekindCycles C f g n m α' (pointClosureCycle C g m y))
          (pointClosureCycle C h l z)).1 u)
        (fun a b ↦ by simp only [map_add, AddMonoidHom.add_apply]; rfl))
      (AddMonoidHom.mk' (fun α' ↦ (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n
          (m + l - 1) α' (exteriorProductDedekindCycles C g h m l (pointClosureCycle C g m y)
            (pointClosureCycle C h l z))).1 v)
        (fun a b ↦ by simp only [map_add, AddMonoidHom.add_apply]; rfl))
      x₀
      (fun α' hα' ↦ exteriorProductDedekindCycles_apply_eq_zero_of_left C _ h _ l _ _ a₀
        (fun w hw ↦ exteriorProductDedekindCycles_apply_eq_zero_of_left C f g n m α' _ x₀ hα' w
          (hxa ▸ mem_closure_singleton_map (pullback.fst f g).continuous hw)) u (hself a₀))
      (fun α' hα' ↦ exteriorProductDedekindCycles_apply_eq_zero_of_left C f _ n _ α' _ x₀ hα' v
        (hself x₀))
      (fun x _ hx ↦ H1 x y z hx hy hz)
    exact DFunLike.congr_fun key
  have H3 : ∀ z : Z, relativeDimension C.dimensionFunction h z = l →
      ∀ (α' : CycleGroup C f n) (β' : CycleGroup C g m),
      (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h (n + m - 1) l
          (exteriorProductDedekindCycles C f g n m α' β') (pointClosureCycle C h l z)).1 u =
        (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n (m + l - 1) α'
          (exteriorProductDedekindCycles C g h m l β' (pointClosureCycle C h l z))).1 v := by
    intro z hz α'
    have key := addMonoidHom_ext_of_pointClosureCycle C g m
      (AddMonoidHom.mk' (fun β' ↦ (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h
          (n + m - 1) l (exteriorProductDedekindCycles C f g n m α' β')
          (pointClosureCycle C h l z)).1 u)
        (fun a b ↦ by simp only [map_add, AddMonoidHom.add_apply]; rfl))
      (AddMonoidHom.mk' (fun β' ↦ (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n
          (m + l - 1) α' (exteriorProductDedekindCycles C g h m l β'
            (pointClosureCycle C h l z))).1 v)
        (fun a b ↦ by simp only [map_add, AddMonoidHom.add_apply]; rfl))
      y₀
      (fun β' hβ' ↦ exteriorProductDedekindCycles_apply_eq_zero_of_left C _ h _ l _ _ a₀
        (fun w hw ↦ exteriorProductDedekindCycles_apply_eq_zero_of_right C f g n m α' β' y₀ hβ' w
          (hya ▸ mem_closure_singleton_map (pullback.snd f g).continuous hw)) u (hself a₀))
      (fun β' hβ' ↦ exteriorProductDedekindCycles_apply_eq_zero_of_right C f _ n _ α' _ t₀
        (fun t ht ↦ exteriorProductDedekindCycles_apply_eq_zero_of_left C g h m l β' _ y₀ hβ' t
          (mem_closure_singleton_map (pullback.fst g h).continuous ht)) v (hself t₀))
      (fun y _ hy ↦ H2 y z hy hz α')
    exact DFunLike.congr_fun key
  have key := addMonoidHom_ext_of_pointClosureCycle C h l
    (AddMonoidHom.mk' (fun γ' ↦ (exteriorProductDedekindCycles C (pullback.fst f g ≫ f) h
        (n + m - 1) l (exteriorProductDedekindCycles C f g n m α β) γ').1 u)
      (fun a b ↦ by simp only [map_add]; rfl))
    (AddMonoidHom.mk' (fun γ' ↦ (exteriorProductDedekindCycles C f (pullback.fst g h ≫ g) n
        (m + l - 1) α (exteriorProductDedekindCycles C g h m l β γ')).1 v)
      (fun a b ↦ by simp only [map_add]; rfl))
    z₀
    (fun γ' hγ' ↦ exteriorProductDedekindCycles_apply_eq_zero_of_right C _ h _ l _ γ' z₀ hγ' u
      (hzu ▸ hself _))
    (fun γ' hγ' ↦ exteriorProductDedekindCycles_apply_eq_zero_of_right C f _ n _ α _ t₀
      (fun t ht ↦ exteriorProductDedekindCycles_apply_eq_zero_of_right C g h m l β γ' z₀ hγ' t
        (mem_closure_singleton_map (pullback.snd g h).continuous ht)) v (hself t₀))
    (fun z _ hz ↦ H3 z hz α β)
  exact DFunLike.congr_fun key γ

end CycleAssociativity

/-! ### Associativity on Chow groups -/

section ChowAssociativity

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S) [LocallyOfFiniteType h] (n m l : ℤ)

/-- **Associativity of the exterior product.** Let `(S, δ)` be as in Stacks section 42.63,
let `X`, `Y`, `Z` be locally of finite type over `S`, and let `a ∈ CH_n(X)`, `b ∈ CH_m(Y)`,
`c ∈ CH_l(Z)`. Then `(a × b) × c = a × (b × c)` in `CH_*(X ×_S Y ×_S Z)`.

The two sides live on the two bracketings `(X ×_S Y) ×_S Z` and `X ×_S (Y ×_S Z)` of the triple
fibre product and in the two spellings `(n + m - 1) + l - 1` and `n + (m + l - 1) - 1` of the same
delta-dimension, so the left side is carried across by proper pushforward along the associator of
the fibre product and by the equality of the two degrees. -/
@[stacks 0FC8]
theorem exteriorProductDedekindChow_assoc_of_isDedekindChowBase (hC : IsDedekindChowBase C)
    (a : chowGroup C f n) (b : chowGroup C g m) (c : chowGroup C h l) :
    exteriorProductDedekind_degree_assoc n m l ▸
        properChowPushforward C
          (pullback.fst (pullback.fst f g ≫ f) h ≫ (pullback.fst f g ≫ f))
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f)
          (tripleFibreProductAssoc f g h).hom
          (tripleFibreProductAssoc_hom_structureMorphism f g h)
          (n + m - 1 + l - 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (tripleFibreProductAssoc f g h).hom C _ _
            (tripleFibreProductAssoc_hom_structureMorphism f g h) (n + m - 1 + l - 1))
          (exteriorProductDedekindChow C (pullback.fst f g ≫ f) h (n + m - 1) l
            (exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase C
              (pullback.fst f g ≫ f) h (n + m - 1) l hC)
            (exteriorProductDedekindChow C f g n m
              (exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase C f g n m hC)
              a b) c) =
      exteriorProductDedekindChow C f (pullback.fst g h ≫ g) n (m + l - 1)
        (exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase C f
          (pullback.fst g h ≫ g) n (m + l - 1) hC) a
        (exteriorProductDedekindChow C g h m l
          (exteriorProductFactorsThroughRationalEquivalence_of_isDedekindChowBase C g h m l hC)
          b c) := by
  induction a using QuotientAddGroup.induction_on with
  | H α =>
    induction b using QuotientAddGroup.induction_on with
    | H β =>
      induction c using QuotientAddGroup.induction_on with
      | H γ =>
        exact exteriorProductDedekindChow_assoc C f g h n m l _ _ _ _ _
          (isExteriorProductDedekindAssociative C f g h n m l hC) α β γ

end ChowAssociativity

end Stacks.Chow

end
