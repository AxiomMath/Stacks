module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProduct

/-!
# The exterior product of cycles over a Dedekind base

Section 42.63 of the Stacks Project works over a base scheme `S` which is locally Noetherian and
has an open covering by spectra of Dedekind domains, with the dimension function `δ(s) = 0` for
`s` closed and `δ(s) = 1` otherwise. Such an `(S, δ)` is a special case of Situation 42.7.1. In
that setting the exterior product of an `n`-cycle on `X` and an `m`-cycle on `Y` is a cycle of
delta-dimension `n + m - 1` on `X ×_S Y`, one less than over a field, because the two factors
share the one-dimensional base. The defining rule is: for integral closed subschemes `X' ⊆ X`
and `Y' ⊆ Y` of delta-dimensions `n` and `m`,

* `[X'] × [Y'] = [X' ×_S Y']_{n+m-1}` if `X'` or `Y'` dominates an irreducible component of `S`,
* `[X'] × [Y'] = 0` if neither `X'` nor `Y'` dominates an irreducible component of `S`.

This file constructs the resulting bilinear map on cycle groups,

  `× : Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m-1}(X ×_S Y)`,

whose coefficient at a point `z` of `X ×_S Y` is a sum over all pairs of components of the two
cycles.

## Main definitions

* `Stacks.Chow.IsDedekindChowBase` — the standing hypothesis of Stacks section 42.63 on the base
  situation: locally the spectrum of a Dedekind domain, with `δ` equal to `0` at closed points
  and to `1` elsewhere.
* `Stacks.Chow.DominatesBaseComponent` — the reduced closure of a point dominates an irreducible
  component of the base.
* `Stacks.Chow.exteriorProductDedekindTerm` — the contribution of one pair of components.
* `Stacks.Chow.exteriorProductDedekindCoeff` — the coefficient function of the exterior product.
* `Stacks.Chow.exteriorProductDedekindCycles` — **Stacks 0FC4, the cycle-level map**
  `Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m-1}(X ×_S Y)`.

## Main results

* `Stacks.Chow.exteriorProductDedekindTerm_eq_zero_of_relativeDimension_ne` — a pair contributes
  at `z` only in delta-dimension `n + m - 1`.
* `Stacks.Chow.mem_closure_of_exteriorProductDedekindTerm_ne_zero` — a contributing pair has
  `pr_X z` in the closure of its first entry and `pr_Y z` in the closure of its second.
* `Stacks.Chow.exteriorProductDedekindTerm_support_finite` — at each point only finitely many
  pairs contribute, so the defining sum is a finite sum.
* `Stacks.Chow.exteriorProductDedekindCoeff_locallyFiniteSupport`,
  `Stacks.Chow.exteriorProductDedekindCoeff_mem_cyclesOfDimension` — the coefficient function is
  a cycle of delta-dimension `n + m - 1`.
* `Stacks.Chow.exteriorProductDedekindCycles_apply` — the coefficient formula.

## Implementation notes

The product of two reduced point closures is the closed subscheme of
`Stacks.Chow.exteriorProductIdeal`, and its multiplicities are read off by
`Stacks.Chow.closedSubschemeCycleCoeff` at delta-dimension `n + m - 1`. The dominance condition
of the defining rule is carried explicitly in `Stacks.Chow.exteriorProductDedekindTerm`.

Nothing in this file uses `Stacks.Chow.IsDedekindChowBase`: the cycle-level map is defined over
any base situation once the target degree `n + m - 1` is fixed.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Chow

/-! ### The base of section 42.63 -/

/-- The standing hypothesis of Stacks section 42.63: the base situation is locally the spectrum
of a Dedekind domain, and its dimension function is `0` at the closed points and `1` elsewhere.
Such a situation is a special case of Situation 42.7.1. -/
def IsDedekindChowBase (C : ChowSituation.{u}) : Prop :=
  (∀ s : C.S, ∃ U : C.S.Opens,
      s ∈ (U : Set C.S) ∧ IsAffineOpen U ∧ IsDedekindDomain (C.S.presheaf.obj (op U))) ∧
    (∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) ∧
    (∀ s : C.S, ¬ IsClosed ({s} : Set C.S) → C.dimensionFunction s = 1)

/-- The reduced closure of a point `x` of a scheme locally of finite type over the base
dominates an irreducible component of the base: the closure of the image of `x` is one of the
irreducible components of the base scheme. -/
def DominatesBaseComponent (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) (x : X) :
    Prop :=
  closure ({f.base x} : Set C.S) ∈ irreducibleComponents C.S

/-! ### The coefficient function -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)

/-- The contribution of the pair of components indexed by `(x, y)` to the coefficient at `z` of
the exterior product of `α` and `β` over a Dedekind base: the product of the two coefficients
with the multiplicity of `z` in the delta-dimension `n + m - 1` cycle of
`closure {x} ×_S closure {y}`, and zero unless one of the two closures dominates an irreducible
component of the base. -/
def exteriorProductDedekindTerm (α : CycleGroup C f n) (β : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) (p : X × Y) : ℤ :=
  open Classical in
  if DominatesBaseComponent C f p.1 ∨ DominatesBaseComponent C g p.2 then
    α.1 p.1 * β.1 p.2 *
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (exteriorProductIdeal f g p.1 p.2).subschemeι (n + m - 1) z
  else 0

/-- **The coefficient function of the exterior product over a Dedekind base.** At `z` it is the
sum, over all pairs of components of `α` and `β` at least one of which dominates an irreducible
component of the base, of the product of the two coefficients with the multiplicity of `z` in
the delta-dimension `n + m - 1` cycle of the fibre product of the two reduced closures. -/
def exteriorProductDedekindCoeff (α : CycleGroup C f n) (β : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) : ℤ :=
  ∑ᶠ p : X × Y, exteriorProductDedekindTerm C f g n m α β z p

/-! ### Grading -/

/-- A pair contributes to the coefficient at `z` only when the relative dimension of `z` is
`n + m - 1`. -/
theorem exteriorProductDedekindTerm_eq_zero_of_relativeDimension_ne (α : CycleGroup C f n)
    (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) (p : X × Y)
    (hz : relativeDimension C.dimensionFunction (pullback.fst f g ≫ f) z ≠ n + m - 1) :
    exteriorProductDedekindTerm C f g n m α β z p = 0 := by
  classical
  have hcoeff : closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      (exteriorProductIdeal f g p.1 p.2).subschemeι (n + m - 1) z = 0 := by
    unfold closedSubschemeCycleCoeff
    rw [dite_eq_right]
    exact fun h ↦ absurd h.choose_spec.2 hz
  simp only [exteriorProductDedekindTerm, hcoeff, mul_zero, ite_self]

/-- The coefficient of the exterior product vanishes at every point whose relative dimension is
not `n + m - 1`. -/
theorem exteriorProductDedekindCoeff_eq_zero_of_relativeDimension_ne (α : CycleGroup C f n)
    (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u}))
    (hz : relativeDimension C.dimensionFunction (pullback.fst f g ≫ f) z ≠ n + m - 1) :
    exteriorProductDedekindCoeff C f g n m α β z = 0 := by
  unfold exteriorProductDedekindCoeff
  rw [finsum_eq_zero_of_forall_eq_zero]
  exact fun p ↦ exteriorProductDedekindTerm_eq_zero_of_relativeDimension_ne C f g n m α β z p hz

/-! ### Finiteness of the defining sum -/

/-- A contributing pair has nonzero coefficients in both cycles and a nonzero multiplicity. -/
private theorem coeff_mul_ne_zero_and_cycleCoeff_ne_zero_of_exteriorProductDedekindTerm_ne_zero
    (α : CycleGroup C f n) (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) (p : X × Y)
    (hp : exteriorProductDedekindTerm C f g n m α β z p ≠ 0) :
    α.1 p.1 * β.1 p.2 ≠ 0 ∧ closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      (exteriorProductIdeal f g p.1 p.2).subschemeι (n + m - 1) z ≠ 0 := by
  classical
  unfold exteriorProductDedekindTerm at hp
  split_ifs at hp
  · exact mul_ne_zero_iff.1 hp
  · exact absurd rfl hp

/-- A contributing pair has `pr_X z` in the closure of its first entry and `pr_Y z` in the
closure of its second. -/
theorem mem_closure_of_exteriorProductDedekindTerm_ne_zero (α : CycleGroup C f n)
    (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) (p : X × Y)
    (hp : exteriorProductDedekindTerm C f g n m α β z p ≠ 0) :
    (pullback.fst f g).base z ∈ closure ({p.1} : Set X) ∧
      (pullback.snd f g).base z ∈ closure ({p.2} : Set Y) := by
  classical
  have hcoeff :=
    (coeff_mul_ne_zero_and_cycleCoeff_ne_zero_of_exteriorProductDedekindTerm_ne_zero
      C f g n m α β z p hp).2
  have hrange : z ∈ Set.range (exteriorProductIdeal f g p.1 p.2).subschemeι.base := by
    unfold closedSubschemeCycleCoeff at hcoeff
    split_ifs at hcoeff with h
    · obtain ⟨w, hw⟩ := h
      exact ⟨w.1, hw.1⟩
    · exact absurd rfl hcoeff
  rwa [Scheme.IdealSheafData.range_subschemeι, exteriorProductIdeal,
    Scheme.IdealSheafData.support_sup, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_comap] at hrange

/-- A point whose closure contains `w` lies in every open neighbourhood of `w`. -/
private theorem mem_of_mem_closure_singleton {T : Type u} [TopologicalSpace T] {w x : T}
    (hx : w ∈ closure ({x} : Set T)) {U : Set T} (hU : IsOpen U) (hwU : w ∈ U) : x ∈ U := by
  obtain ⟨t, htU, htx⟩ := mem_closure_iff.1 hx U hU hwU
  exact Set.mem_of_eq_of_mem (Set.eq_of_mem_singleton htx).symm htU

/-- There is a neighbourhood of `z` on which every contributing pair is drawn from one fixed
finite set of pairs. -/
private theorem exists_open_finset_exteriorProductDedekindTerm (α : CycleGroup C f n)
    (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) :
    ∃ (N : Set (pullback f g : Scheme.{u})) (_ : N ∈ nhds z) (s : Finset (X × Y)),
      ∀ w ∈ N, ∀ p : X × Y,
        exteriorProductDedekindTerm C f g n m α β w p ≠ 0 → p ∈ s := by
  classical
  obtain ⟨V, hV, hVfin⟩ :=
    Function.locallyFinsupp.locallyFiniteSupport α.1 ((pullback.fst f g).base z)
  obtain ⟨W, hW, hWfin⟩ :=
    Function.locallyFinsupp.locallyFiniteSupport β.1 ((pullback.snd f g).base z)
  obtain ⟨V₀, hV₀V, hV₀open, hzV₀⟩ := mem_nhds_iff.1 hV
  obtain ⟨W₀, hW₀W, hW₀open, hzW₀⟩ := mem_nhds_iff.1 hW
  refine ⟨(pullback.fst f g).base ⁻¹' V₀ ∩ (pullback.snd f g).base ⁻¹' W₀,
    Filter.inter_mem ((pullback.fst f g).continuous.continuousAt
        (mem_nhds_iff.2 ⟨V₀, subset_rfl, hV₀open, hzV₀⟩))
      ((pullback.snd f g).continuous.continuousAt
        (mem_nhds_iff.2 ⟨W₀, subset_rfl, hW₀open, hzW₀⟩)),
    hVfin.toFinset ×ˢ hWfin.toFinset, ?_⟩
  rintro w ⟨hwV, hwW⟩ p hp
  obtain ⟨hp1, hp2⟩ := mem_closure_of_exteriorProductDedekindTerm_ne_zero C f g n m α β w p hp
  have hαβ :=
    (coeff_mul_ne_zero_and_cycleCoeff_ne_zero_of_exteriorProductDedekindTerm_ne_zero
      C f g n m α β w p hp).1
  exact Finset.mem_product.2
    ⟨hVfin.mem_toFinset.2 ⟨hV₀V (mem_of_mem_closure_singleton hp1 hV₀open hwV),
      (mul_ne_zero_iff.1 hαβ).1⟩,
    hWfin.mem_toFinset.2 ⟨hW₀W (mem_of_mem_closure_singleton hp2 hW₀open hwW),
      (mul_ne_zero_iff.1 hαβ).2⟩⟩

/-- At each point only finitely many pairs of components contribute, so the sum defining the
coefficient of the exterior product is a finite sum. -/
theorem exteriorProductDedekindTerm_support_finite (α : CycleGroup C f n)
    (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) :
    (Function.support (exteriorProductDedekindTerm C f g n m α β z)).Finite := by
  classical
  obtain ⟨N, hN, s, hs⟩ := exists_open_finset_exteriorProductDedekindTerm C f g n m α β z
  exact s.finite_toSet.subset fun p hp ↦ hs z (mem_of_mem_nhds hN) p hp

/-! ### Local finiteness -/

/-- The coefficient function of the exterior product over a Dedekind base has locally finite
support. -/
theorem exteriorProductDedekindCoeff_locallyFiniteSupport (α : CycleGroup C f n)
    (β : CycleGroup C g m) :
    LocallyFiniteSupport (exteriorProductDedekindCoeff C f g n m α β) := by
  classical
  intro z
  obtain ⟨N, hN, s, hs⟩ := exists_open_finset_exteriorProductDedekindTerm C f g n m α β z
  obtain ⟨M, hM, hMfin⟩ :=
    exists_nhds_finite_of_finset s
      (fun p w ↦ exteriorProductDedekindTerm C f g n m α β w p)
      (fun p _ w ↦ by
        obtain ⟨N', hN', hN'fin⟩ :=
          closedSubschemeCycleCoeff_locallyFiniteSupport C (pullback.fst f g ≫ f)
            (exteriorProductIdeal f g p.1 p.2).subschemeι (n + m - 1) w
        refine ⟨N', hN', hN'fin.subset ?_⟩
        rintro v ⟨hvN', hvsupp⟩
        refine ⟨hvN', fun hzero ↦ hvsupp ?_⟩
        unfold exteriorProductDedekindTerm
        split_ifs with hdom
        · change α.1 p.1 * β.1 p.2 * _ = 0
          rw [hzero, mul_zero]
        · rfl)
      z
  refine ⟨N ∩ M, Filter.inter_mem hN hM, hMfin.subset ?_⟩
  rintro w ⟨⟨hwN, hwM⟩, hwsupp⟩
  refine ⟨hwM, ?_⟩
  change ∃ p ∈ s, exteriorProductDedekindTerm C f g n m α β w p ≠ 0
  by_contra hforall
  push Not at hforall
  exact hwsupp (finsum_eq_zero_of_forall_eq_zero fun p ↦
    not_ne_iff.1 fun hp ↦ hp (hforall p (hs w hwN p hp)))

/-- The coefficient function of the exterior product over a Dedekind base is a cycle of
delta-dimension `n + m - 1`. -/
theorem exteriorProductDedekindCoeff_mem_cyclesOfDimension (α : CycleGroup C f n)
    (β : CycleGroup C g m) :
    (⟨exteriorProductDedekindCoeff C f g n m α β, fun _ _ ↦ trivial, fun z _ ↦
      exteriorProductDedekindCoeff_locallyFiniteSupport C f g n m α β z⟩ :
        AlgebraicCycle (pullback f g : Scheme.{u}) ℤ) ∈
      cyclesOfDimension C (pullback.fst f g ≫ f) (n + m - 1) := by
  rw [mem_cyclesOfDimension]
  intro Z hZ
  change exteriorProductDedekindCoeff C f g n m α β Z.isIrreducible.genericPoint ≠ 0 at hZ
  rw [deltaDimension_eq_of_isGenericPoint C (pullback.fst f g ≫ f) Z
    Z.isIrreducible.genericPoint
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
  by_contra hne
  exact hZ
    (exteriorProductDedekindCoeff_eq_zero_of_relativeDimension_ne C f g n m α β _ hne)

/-! ### Bilinearity -/

/-- The contribution of a pair is additive in the second cycle. -/
private theorem exteriorProductDedekindTerm_add_right (α : CycleGroup C f n)
    (β γ : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) (p : X × Y) :
    exteriorProductDedekindTerm C f g n m α (β + γ) z p =
      exteriorProductDedekindTerm C f g n m α β z p +
        exteriorProductDedekindTerm C f g n m α γ z p := by
  classical
  unfold exteriorProductDedekindTerm
  split_ifs with h
  · change α.1 p.1 * (β.1 p.2 + γ.1 p.2) * _ = _
    ring
  · rw [add_zero]

/-- The contribution of a pair is additive in the first cycle. -/
private theorem exteriorProductDedekindTerm_add_left (α α' : CycleGroup C f n)
    (β : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) (p : X × Y) :
    exteriorProductDedekindTerm C f g n m (α + α') β z p =
      exteriorProductDedekindTerm C f g n m α β z p +
        exteriorProductDedekindTerm C f g n m α' β z p := by
  classical
  unfold exteriorProductDedekindTerm
  split_ifs with h
  · change (α.1 p.1 + α'.1 p.1) * β.1 p.2 * _ = _
    ring
  · rw [add_zero]

/-- The contribution of a pair vanishes when the second cycle is zero. -/
private theorem exteriorProductDedekindTerm_zero_right (α : CycleGroup C f n)
    (z : (pullback f g : Scheme.{u})) (p : X × Y) :
    exteriorProductDedekindTerm C f g n m α (0 : CycleGroup C g m) z p = 0 := by
  have h := exteriorProductDedekindTerm_add_right C f g n m α 0 0 z p
  simpa using h

/-- The contribution of a pair vanishes when the first cycle is zero. -/
private theorem exteriorProductDedekindTerm_zero_left (β : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) (p : X × Y) :
    exteriorProductDedekindTerm C f g n m (0 : CycleGroup C f n) β z p = 0 := by
  have h := exteriorProductDedekindTerm_add_left C f g n m 0 0 β z p
  simpa using h

/-! ### The cycle-level exterior product -/

/-- **Stacks 0FC4, the cycle-level map.** The exterior product of cycles over a base of
delta-dimension one,

  `× : Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m-1}(X ×_S Y)`,

given by the defining rule of Stacks section 42.63: on the fundamental cycles of integral closed
subschemes `X' ⊆ X` and `Y' ⊆ Y` of delta-dimensions `n` and `m` it is `[X' ×_S Y']_{n+m-1}`
when one of them dominates an irreducible component of the base, and `0` when neither does. -/
def exteriorProductDedekindCycles :
    CycleGroup C f n →+ CycleGroup C g m →+ CycleGroup C (pullback.fst f g ≫ f) (n + m - 1) where
  toFun α :=
    { toFun := fun β ↦ ⟨⟨exteriorProductDedekindCoeff C f g n m α β, fun _ _ ↦ trivial,
          fun z _ ↦ exteriorProductDedekindCoeff_locallyFiniteSupport C f g n m α β z⟩,
        exteriorProductDedekindCoeff_mem_cyclesOfDimension C f g n m α β⟩
      map_zero' := by
        ext z
        change exteriorProductDedekindCoeff C f g n m α 0 z = 0
        unfold exteriorProductDedekindCoeff
        exact finsum_eq_zero_of_forall_eq_zero
          (exteriorProductDedekindTerm_zero_right C f g n m α z)
      map_add' β γ := by
        ext z
        change exteriorProductDedekindCoeff C f g n m α (β + γ) z =
          exteriorProductDedekindCoeff C f g n m α β z +
            exteriorProductDedekindCoeff C f g n m α γ z
        unfold exteriorProductDedekindCoeff
        rw [funext (exteriorProductDedekindTerm_add_right C f g n m α β γ z)]
        exact finsum_add_distrib
          (exteriorProductDedekindTerm_support_finite C f g n m α β z)
          (exteriorProductDedekindTerm_support_finite C f g n m α γ z) }
  map_zero' := by
    ext β z
    change exteriorProductDedekindCoeff C f g n m 0 β z = 0
    unfold exteriorProductDedekindCoeff
    exact finsum_eq_zero_of_forall_eq_zero
      (exteriorProductDedekindTerm_zero_left C f g n m β z)
  map_add' α α' := by
    ext β z
    change exteriorProductDedekindCoeff C f g n m (α + α') β z =
      exteriorProductDedekindCoeff C f g n m α β z +
        exteriorProductDedekindCoeff C f g n m α' β z
    unfold exteriorProductDedekindCoeff
    rw [funext (exteriorProductDedekindTerm_add_left C f g n m α α' β z)]
    exact finsum_add_distrib
      (exteriorProductDedekindTerm_support_finite C f g n m α β z)
      (exteriorProductDedekindTerm_support_finite C f g n m α' β z)

/-- The coefficient formula for the exterior product of cycles over a Dedekind base. -/
@[simp]
theorem exteriorProductDedekindCycles_apply (α : CycleGroup C f n) (β : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) :
    (exteriorProductDedekindCycles C f g n m α β).1 z =
      ∑ᶠ p : X × Y, exteriorProductDedekindTerm C f g n m α β z p :=
  rfl

end Stacks.Chow

end
