module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.DiagonalProductCoefficient
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.DiagonalPushforward
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.ProperIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to the diagonal

Let `X` be a nonsingular variety over an algebraically closed field `k`, let `α` be an `r`-cycle
and `β` an `s`-cycle on `X`, and assume that `α` and `β` intersect properly. Then the exterior
product `α × β` and the cycle `[Δ]` of the diagonal intersect properly on `X ×_k X`, the proper
pushforward of `α · β` along the diagonal is `[Δ] · α × β`, and — when `X` is proper over `k` —
pushing `[Δ] · α × β` forward along the first projection returns `α · β`.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.reductionToDiagonal` — **Stacks 0B0U**, all three
  parts.
* `properPushforward_diagonal_torFormulaCycleIntersectionProduct` in this namespace, and its
  companion `..._of_eq` — part (2) on its own, with the dimension index as a natural number and
  as the integer `r + s - dim X`.
* `torFormulaCycleIntersectionProduct_mem_cyclesOfDimension` in this namespace
  — the intersection product of two cycles is a cycle of the expected delta-dimension, with no
  hypothesis; this is what makes the two pushforwards of parts (2) and (3) available.
* `Stacks.Intersection.ReductionToDiagonal.properPushforward_diagonal_apply` and
  `properPushforward_diagonal_apply_eq_zero` — the coefficients of a pushforward along the
  diagonal.
* `Stacks.Intersection.ReductionToDiagonal.exteriorProduct_apply_productPointAt` and
  `eq_productPointAt_of_exteriorProduct_ne_zero` — the components of `α × β` are exactly the
  products of a component of `α` with a component of `β`, each with weight one.

## Implementation notes

Part (2) is proved coefficientwise rather than by reducing to prime cycles: on a variety a cycle
has finitely many components, so each side is a finite sum over those components
(`AlgebraicGeometry.TorFormula.cycleIntersectionProduct_apply` and
`cycleIntersectionProduct_single_left_apply`), and the two sums are matched by the injection
`(a, b) ↦` the generic point of `closure {a} ×_k closure {b}`. The summand belonging to a pair is
`Stacks.Intersection.ReductionToDiagonal.torSubvarietyProductOfBound_diagonal_apply`, which is
the source's equality of multiplicities.

Below the dimension of `X` the index `r + s - dim X` is negative and both sides vanish, since
over a field every point has nonnegative relative dimension; that degenerate case is where
`..._of_eq` differs from the natural-number form.

## References

* [Stacks Project, Lemma 43.19.2 (Tag 0B0U)](https://stacks.math.columbia.edu/tag/0B0U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Intersection.ReductionToDiagonal

/-! ### Preliminaries on proper intersection and dimension -/

/-- Proper intersection of two irreducible closed subsets is a symmetric relation. -/
theorem intersectProperly_symm {Y : Scheme.{u}} {W V : IrreducibleCloseds Y}
    (h : AlgebraicGeometry.IntersectProperly W V) :
    AlgebraicGeometry.IntersectProperly V W := by
  rw [AlgebraicGeometry.intersectProperly_iff] at h ⊢
  rwa [Set.inter_comm, add_comm (topologicalKrullDim (V : Set Y))]

/-- Proper intersection of two cycles is a symmetric relation. -/
theorem cycle_intersectProperly_symm {Y : Scheme.{u}} {a b : AlgebraicCycle Y ℤ}
    (h : AlgebraicCycle.IntersectProperly a b) :
    AlgebraicCycle.IntersectProperly b a :=
  fun W V hW hV => intersectProperly_symm (h V W hV hW)

/-- **The Tor-formula intersection product of two cycles is an `n`-cycle.** Each summand of the
double sum is one — the alternating sum of Tag 0AZR where the delta-dimension bound holds and the
zero cycle where it does not — and the `n`-cycles form a subgroup. -/
theorem torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (n : ℤ) (α β : AlgebraicCycle X ℤ) :
    torFormulaCycleIntersectionProduct C f hX n α β ∈ cyclesOfDimension C f n := by
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct]
  refine finsum_induction _ (AddSubgroup.zero_mem _)
    (fun a b ha hb ↦ AddSubgroup.add_mem _ ha hb) fun q ↦ ?_
  by_cases hb : TorSupportBound C f hX n q.1 q.2
  · rw [cycleIntersectionProductSummand,
      torFormulaSubvarietyProductTotal_eq_of_bound C f hX n hb]
    exact AddSubgroup.zsmul_mem _
      (intersectionProductCycle_mem_cyclesOfDimension C f hX _ _ _ _ n hb) _
  · rw [cycleIntersectionProductSummand,
      torFormulaSubvarietyProductTotal_eq_zero C f hX n hb, smul_zero]
    exact AddSubgroup.zero_mem _

/-- Every point carrying a nonzero coefficient of an `n`-cycle has relative dimension `n`. -/
private theorem relativeDimension_eq_of_mem_cyclesOfDimension {C : ChowSituation.{u}}
    {X : Scheme.{u}} {f : X ⟶ C.S} [LocallyOfFiniteType f] {n : ℤ} {c : AlgebraicCycle X ℤ}
    (hc : c ∈ cyclesOfDimension C f n) {x : X} (hx : c x ≠ 0) :
    relativeDimension C.dimensionFunction f x = n :=
  (mem_cyclesOfDimension_iff_forall_point C f n c).1 hc x hx

/-- Over a field there are no cycles in negative delta-dimension: the relative dimension of every
point is nonnegative. -/
theorem eq_zero_of_mem_cyclesOfDimension_of_neg (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] {n : ℤ} (hn : n < 0)
    {c : AlgebraicCycle X ℤ} (hc : c ∈ cyclesOfDimension (fieldChowSituation k) f n) :
    c = 0 := by
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  by_contra hx
  have hc' := relativeDimension_eq_of_mem_cyclesOfDimension hc (by simpa using hx)
  have h0 := relativeDimension_fieldChowSituation_nonneg k f x
  omega

/-! ### Proper pushforward along the diagonal -/

/-- **The coefficient of a pushforward along the diagonal.** The diagonal is a closed immersion,
so it is injective with trivial residue field extensions and it preserves relative dimension;
the coefficient of `Δ_* c` at `Δ(z)` is therefore the coefficient of `c` at `z`. -/
theorem properPushforward_diagonal_apply (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsSeparated f]
    [LocallyOfFiniteType (pullback.fst f f ≫ f)] (n : ℤ) (c : CycleGroup C f n) (z : X) :
    letI : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
    (properPushforward C f (pullback.fst f f ≫ f) (pullback.diagonal f)
        (diagonal_comp_fst_comp f) n c).1 ((pullback.diagonal f).base z) = c.1 z := by
  let : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  have hpre : (pullback.diagonal f).base ⁻¹' {(pullback.diagonal f).base z} = {z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => (pullback.diagonal f).isClosedEmbedding.injective h, fun h => h ▸ rfl⟩
  rw [properPushforward_apply, hpre, finsum_mem_singleton,
    relativeDimension_diagonal C.dimensionFunction f z, ite_eq_left rfl,
    residueDegree_eq_one_of_isClosedImmersion (pullback.diagonal f) z]
  simp

/-- **A pushforward along the diagonal vanishes off the diagonal.** -/
theorem properPushforward_diagonal_apply_eq_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsSeparated f]
    [LocallyOfFiniteType (pullback.fst f f ≫ f)] (n : ℤ) (c : CycleGroup C f n)
    {q : (pullback f f : Scheme.{u})} (hq : q ∉ Set.range (pullback.diagonal f).base) :
    letI : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
    (properPushforward C f (pullback.fst f f ≫ f) (pullback.diagonal f)
        (diagonal_comp_fst_comp f) n c).1 q = 0 := by
  let : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  have hpre : (pullback.diagonal f).base ⁻¹' {q} = ∅ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => hq ⟨w, h⟩
  rw [properPushforward_apply, hpre, finsum_mem_empty]

/-! ### The exterior product of two cycles, component by component -/

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **The coefficient of `α × β` at the generic point of a product of two components** is the
product of the two coefficients: the product of two closed subvarieties enters with weight one. -/
theorem exteriorProduct_apply_productPointAt (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f]
    (r s : ℤ) (α : CycleGroup (fieldChowSituation k) f r)
    (β : CycleGroup (fieldChowSituation k) f s) {a b : X} (ha : α.1 a ≠ 0) (hb : β.1 b ≠ 0) :
    (exteriorProduct (fieldChowSituation k) f f r s α β).1 (productPointAt f a b) =
      α.1 a * β.1 b := by
  have hw : exteriorProductWeight (fieldChowSituation k) f f (r + s) a b
      (productPointAt f a b) = 1 := by
    have h := exteriorProductWeight_productPointAt f a b
    rwa [relativeDimension_eq_of_mem_cyclesOfDimension α.2 ha,
      relativeDimension_eq_of_mem_cyclesOfDimension β.2 hb] at h
  rw [exteriorProduct_apply, fst_productPointAt, snd_productPointAt, hw, mul_one]

/-- **Every point carrying a nonzero coefficient of `α × β` is the generic point of the product
of a component of `α` with a component of `β`.** -/
theorem eq_productPointAt_of_exteriorProduct_ne_zero (f : X ⟶ Spec (CommRingCat.of k))
    [IsVariety k f] (r s : ℤ) (α : CycleGroup (fieldChowSituation k) f r)
    (β : CycleGroup (fieldChowSituation k) f s) {v : (pullback f f : Scheme.{u})}
    (hv : (exteriorProduct (fieldChowSituation k) f f r s α β).1 v ≠ 0) :
    α.1 ((pullback.fst f f).base v) ≠ 0 ∧ β.1 ((pullback.snd f f).base v) ≠ 0 ∧
      v = productPointAt f ((pullback.fst f f).base v) ((pullback.snd f f).base v) := by
  rw [exteriorProduct_apply] at hv
  obtain ⟨hprod, hweight⟩ := mul_ne_zero_iff.1 hv
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hprod
  refine ⟨ha, hb, ?_⟩
  by_contra hne
  exact hweight (exteriorProductWeight_eq_zero_of_ne f _ _ (r + s) hne)

/-- The generic point of the product of two reduced point closures determines the two points, so
the map forming it is injective. -/
theorem productPointAt_injective (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f]
    {a b a' b' : X} (h : productPointAt f a b = productPointAt f a' b') : a = a' ∧ b = b' :=
  ⟨by rw [← fst_productPointAt f a b, ← fst_productPointAt f a' b', h],
    by rw [← snd_productPointAt f a b, ← snd_productPointAt f a' b', h]⟩

/-! ### Dimensions of the components -/

omit [IsAlgClosed k] in
/-- A component of an `r`-cycle over a field has dimension `r`. -/
theorem topologicalKrullDim_closure_eq_of_ne_zero (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (r : ℕ) (α : CycleGroup (fieldChowSituation k) f (r : ℤ)) {a : X}
    (ha : α.1 a ≠ 0) : topologicalKrullDim (closure ({a} : Set X)) = (r : WithBot ℕ∞) := by
  rw [topologicalKrullDim_closure_singleton_eq k f a,
    relativeDimension_eq_of_mem_cyclesOfDimension α.2 ha]
  simp

omit [IsAlgClosed k] in
/-- The relative dimension of the generic point of an integral scheme over a field is the
dimension of the scheme. -/
theorem relativeDimension_genericPoint_eq (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsIntegral X] (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X) = (d : ℤ) := by
  have h := topologicalKrullDim_closure_singleton_eq k f (genericPoint X)
  rw [genericPoint_spec X,
    (Homeomorph.Set.univ (X : Type u)).isHomeomorph.topologicalKrullDim_eq, hd] at h
  have h0 := relativeDimension_fieldChowSituation_nonneg k f (genericPoint X)
  have hnat : d =
      (relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X)).toNat :=
    mod_cast h
  omega

/-! ### Part (2): the pushforward of `α · β` along the diagonal -/

/-- **Part (2) of Stacks 0B0U.** On a nonsingular variety `X` over an algebraically closed field,
for cycles `α`, `β` of dimensions `r`, `s` intersecting properly and `n = r + s - dim X`, the
proper pushforward of `α · β` along the diagonal is the intersection product `[Δ] · α × β` on
`X ×_k X`.

Both sides are read coefficientwise. Away from the diagonal both vanish, because `Δ · V ×_k W`
is supported on `Δ ∩ (V ×_k W) = Δ(V ∩ W)`. At a point `Δ(z)` the left side is the coefficient
of `α · β` at `z`, since the diagonal is a closed immersion, and the right side is a sum over the
components of `α × β`; those are exactly the products `V ×_k W` of a component of `α` with a
component of `β`, each with weight one, and the summand belonging to such a pair is
`(Δ · V ×_k W)(Δ(z)) = (V · W)(z)` by
`Stacks.Intersection.ReductionToDiagonal.torSubvarietyProductOfBound_diagonal_apply`. -/
theorem properPushforward_diagonal_torFormulaCycleIntersectionProduct
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian (pullback f f : Scheme.{u})] (hX : IsRegular X)
    (hP : IsRegular (pullback f f : Scheme.{u})) (dX n r s : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hn : (r : ℤ) + (s : ℤ) = (dX : ℤ) + (n : ℤ))
    (α : CycleGroup (fieldChowSituation k) f (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) f (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hprod : torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX (n : ℤ) α.1 β.1 ∈
      cyclesOfDimension (fieldChowSituation k) f (n : ℤ)) :
    letI : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
    (properPushforward (fieldChowSituation k) f (pullback.fst f f ≫ f) (pullback.diagonal f)
          (diagonal_comp_fst_comp f) (n : ℤ) ⟨_, hprod⟩).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) (pullback.fst f f ≫ f) hP (n : ℤ)
        (diagonalCycle f)
        (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 := by
  let : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  let : DecidableEq (pullback f f : Scheme.{u}) := Classical.decEq _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f ≫ f)
  have hαfin := finite_support_of_compactSpace α.1
  have hβfin := finite_support_of_compactSpace β.1
  have hABfin := finite_support_of_compactSpace
    (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1
  -- The dimension of the product and of the two kinds of component.
  have hdP : topologicalKrullDim (pullback f f : Scheme.{u}) = ((2 * dX : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_pullback_of_isVariety k f f, hdX]
    push_cast
    ring
  have hdimD : topologicalKrullDim (closure ({(pullback.diagonal f).base (genericPoint X)} :
      Set (pullback f f : Scheme.{u}))) = (dX : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_singleton_eq k (pullback.fst f f ≫ f) _,
      relativeDimension_diagonal, relativeDimension_genericPoint_eq f dX hdX]
    simp
  -- The two delta-dimension bounds, from proper intersection.
  have hboundX : ∀ a b : X, α.1 a ≠ 0 → β.1 b ≠ 0 →
      TorSupportBound (fieldChowSituation k) f hX (n : ℤ) a b := by
    intro a b ha hb
    refine torSupportBound_of_intersectProperly k f hX a b hdX ?_ ?_
    · rw [topologicalKrullDim_closure_eq_of_ne_zero f r α ha,
        topologicalKrullDim_closure_eq_of_ne_zero f s β hb, ← Nat.cast_add, ← Nat.cast_add]
      exact congrArg (fun m : ℕ => (m : WithBot ℕ∞)) (by omega)
    · exact hαβ _ _ (by rwa [genericPoint_closure_singleton])
        (by rwa [genericPoint_closure_singleton])
  have hprop1 := cycle_intersectProperly_symm
    (intersectProperly_exteriorProduct_diagonalCycle k f r s α β hαβ)
  have hboundP : ∀ v : (pullback f f : Scheme.{u}),
      (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 v ≠ 0 →
      TorSupportBound (fieldChowSituation k) (pullback.fst f f ≫ f) hP (n : ℤ)
        ((pullback.diagonal f).base (genericPoint X)) v := by
    intro v hv
    have hrv := relativeDimension_eq_of_mem_cyclesOfDimension
      (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).2 hv
    refine torSupportBound_of_intersectProperly k (pullback.fst f f ≫ f) hP _ _ hdP ?_ ?_
    · have htn : ((r : ℤ) + (s : ℤ)).toNat = r + s := by omega
      have hnat : dX + (r + s) = 2 * dX + n := by omega
      rw [hdimD, topologicalKrullDim_closure_singleton_eq k (pullback.fst f f ≫ f) v, hrv, htn,
        ← Nat.cast_add, ← Nat.cast_add, hnat]
    · refine hprop1 _ _ ?_ ?_
      · rw [genericPoint_closure_singleton, diagonalCycle_apply_genericPoint]
        exact one_ne_zero
      · rwa [genericPoint_closure_singleton]
  -- The diagonal cycle is a prime cycle.
  rw [show diagonalCycle f = Function.locallyFinsuppWithin.single
    ((pullback.diagonal f).base (genericPoint X)) (1 : ℤ) from rfl]
  refine Function.locallyFinsuppWithin.ext fun q => ?_
  refine Eq.trans ?_ (cycleIntersectionProduct_single_left_apply
    (torFormulaSubvarietyProductTotal (fieldChowSituation k) (pullback.fst f f ≫ f) hP (n : ℤ))
    hABfin ((pullback.diagonal f).base (genericPoint X)) q).symm
  by_cases hq : q ∈ Set.range (pullback.diagonal f).base
  · obtain ⟨z, rfl⟩ := hq
    refine Eq.trans (properPushforward_diagonal_apply (fieldChowSituation k) f (n : ℤ)
      ⟨_, hprod⟩ z) ?_
    refine Eq.trans (cycleIntersectionProduct_apply _ hαfin hβfin z) ?_
    have hne : ∀ {a b : X}, α.1 a ≠ 0 → β.1 b ≠ 0 →
        (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1
          (productPointAt f a b) ≠ 0 := fun ha hb =>
      (exteriorProduct_apply_productPointAt f (r : ℤ) (s : ℤ) α β ha hb).trans_ne
        (mul_ne_zero ha hb)
    have hS : hABfin.toFinset =
        (hαfin.toFinset ×ˢ hβfin.toFinset).image fun p : X × X => productPointAt f p.1 p.2 := by
      ext v
      simp only [Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset,
        Function.mem_support]
      constructor
      · intro hv
        obtain ⟨ha, hb, hveq⟩ :=
          eq_productPointAt_of_exteriorProduct_ne_zero f (r : ℤ) (s : ℤ) α β hv
        exact ⟨((pullback.fst f f).base v, (pullback.snd f f).base v), ⟨ha, hb⟩, hveq.symm⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact hne ha hb
    have hinj : ∀ p ∈ hαfin.toFinset ×ˢ hβfin.toFinset,
        ∀ p' ∈ hαfin.toFinset ×ˢ hβfin.toFinset,
          productPointAt f p.1 p.2 = productPointAt f p'.1 p'.2 → p = p' :=
      fun p _ p' _ hpp => Prod.ext_iff.2 (productPointAt_injective f hpp)
    rw [hS, Finset.sum_image hinj, Finset.sum_product]
    refine (Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_).symm
    have ha' : α.1 a ≠ 0 := hαfin.mem_toFinset.1 ha
    have hb' : β.1 b ≠ 0 := hβfin.mem_toFinset.1 hb
    rw [exteriorProduct_apply_productPointAt f (r : ℤ) (s : ℤ) α β ha' hb',
      torFormulaSubvarietyProductTotal_eq_of_bound (fieldChowSituation k)
        (pullback.fst f f ≫ f) hP (n : ℤ) (hboundP _ (hne ha' hb')),
      torFormulaSubvarietyProductTotal_eq_of_bound (fieldChowSituation k) f hX (n : ℤ)
        (hboundX a b ha' hb'),
      torSubvarietyProductOfBound_diagonal_apply f hX hP (n : ℤ) a b dX (le_of_eq hdX)
        (2 * dX) (le_of_eq hdP) (hboundX a b ha' hb') (hboundP _ (hne ha' hb')) z]
  · refine Eq.trans (properPushforward_diagonal_apply_eq_zero (fieldChowSituation k) f (n : ℤ)
      ⟨_, hprod⟩ hq) ?_
    refine (Finset.sum_eq_zero fun v hv => ?_).symm
    have hv' : (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 v ≠ 0 :=
      hABfin.mem_toFinset.1 hv
    rw [torFormulaSubvarietyProductTotal_eq_of_bound (fieldChowSituation k)
        (pullback.fst f f ≫ f) hP (n : ℤ) (hboundP v hv'),
      torSubvarietyProductOfBound_diagonal_apply_eq_zero f hP (n : ℤ) v (2 * dX)
        (le_of_eq hdP) (hboundP v hv') hq, mul_zero]

/-- **Part (2) of Stacks 0B0U, with the dimension index written as the integer `r + s - dim X`.**
Below the dimension of `X` the index is negative, and then both sides vanish because over a field
there are no cycles in negative delta-dimension. -/
theorem properPushforward_diagonal_torFormulaCycleIntersectionProduct_of_eq
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian (pullback f f : Scheme.{u})] (hX : IsRegular X)
    (hP : IsRegular (pullback f f : Scheme.{u})) (dX r s : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (n : ℤ)
    (hn : (r : ℤ) + (s : ℤ) = (dX : ℤ) + n)
    (α : CycleGroup (fieldChowSituation k) f (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) f (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1)
    (hprod : torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n α.1 β.1 ∈
      cyclesOfDimension (fieldChowSituation k) f n) :
    letI : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
    (properPushforward (fieldChowSituation k) f (pullback.fst f f ≫ f) (pullback.diagonal f)
          (diagonal_comp_fst_comp f) n ⟨_, hprod⟩).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) (pullback.fst f f ≫ f) hP n
        (diagonalCycle f)
        (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 := by
  let : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨n₀, rfl⟩ : ∃ n₀ : ℕ, n = (n₀ : ℤ) := ⟨n.toNat, by omega⟩
    exact properPushforward_diagonal_torFormulaCycleIntersectionProduct f hX hP dX n₀ r s hdX
      hn α β hαβ hprod
  · have hz2 : torFormulaCycleIntersectionProduct (fieldChowSituation k)
        (pullback.fst f f ≫ f) hP n (diagonalCycle f)
        (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 = 0 :=
      eq_zero_of_mem_cyclesOfDimension_of_neg k (pullback.fst f f ≫ f) h0
        (torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k)
          (pullback.fst f f ≫ f) hP n _ _)
    have hzero : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n α.1 β.1,
        hprod⟩ : CycleGroup (fieldChowSituation k) f n) = 0 :=
      Subtype.ext (eq_zero_of_mem_cyclesOfDimension_of_neg k f h0 hprod)
    rw [hz2, hzero, properPushforward_zero]
    rfl

/-! ### The whole of Stacks 0B0U -/

/-- **Stacks Project, Tag 0B0U: reduction to the diagonal.** Let `X` be a nonsingular variety
over an algebraically closed field `k`. Let `α` be an `r`-cycle and `β` an `s`-cycle on `X`, and
assume `α` and `β` intersect properly. Then

1. the exterior product `α × β` and the cycle `[Δ]` of the diagonal intersect properly on
   `X ×_k X`;
2. `Δ_*(α · β) = [Δ] · α × β` as cycles on `X ×_k X`;
3. if `X` is proper over `k` then `pr_{1,*}([Δ] · α × β) = α · β`, for `pr₁` the first
   projection.

The intersection products are the ones of Section 43.17 computed by the Tor formula of Section
43.14, `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` (Tag 0B08), in the
expected dimension `r + s - dim X`. Everything beyond the source's hypotheses is asserted among
the conclusions rather than assumed: the natural number `dX` carrying the dimension of `X`, which
exists by `AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isVariety` and is unique,
so that the index `r + s - dX` is the source's `r + s - dim X`; the regularity of `X ×_k X`; and
the delta-dimension of each of the two intersection products, which the two pushforwards need of
their argument. -/
@[stacks 0B0U "all three parts, for a nonsingular variety over an algebraically closed field \
— the chapter's convention, and what makes a product of two closed subvarieties a closed \
subvariety (Stacks 05P3), which part (2) needs. (1) `α × β` and `[Δ]` intersect properly; (2) \
`Δ_*(α · β) = [Δ] · α × β` on `X ×_k X`; (3) `pr_{1,*}([Δ] · α × β) = α · β` when `X` is proper \
over the field, the source's own hypothesis for that part. Both intersection products are the \
Section 43.17 product of Stacks 0B08 computed by the Tor formula of Section 43.14, \
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct`, in the source's dimension \
`r + s - dim X`; proper pushforward is `Stacks.Chow.properPushforward` (Stacks 02R4). The \
hypotheses are exactly the source's: the natural number `dX` holding `dim X`, the regularity of \
`X ×_k X` and the delta-dimension of each of the two products are all asserted among the \
conclusions. The dimensions `r` and `s` are natural numbers, as the dimensions of the \
subvarieties the cycles are supported on."]
theorem reductionToDiagonal (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsVariety k f] (hX : IsRegular X) (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) f (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) f (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    haveI : IsLocallyNoetherian (pullback f f : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
    letI : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
    AlgebraicCycle.IntersectProperly
        (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 (diagonalCycle f) ∧
      ∃ dX : ℕ, topologicalKrullDim X = (dX : WithBot ℕ∞) ∧
        ∃ hP : IsRegular (pullback f f : Scheme.{u}),
          ∃ hprod : torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX
              ((r : ℤ) + (s : ℤ) - (dX : ℤ)) α.1 β.1 ∈
              cyclesOfDimension (fieldChowSituation k) f ((r : ℤ) + (s : ℤ) - (dX : ℤ)),
            (properPushforward (fieldChowSituation k) f (pullback.fst f f ≫ f)
                  (pullback.diagonal f) (diagonal_comp_fst_comp f)
                  ((r : ℤ) + (s : ℤ) - (dX : ℤ)) ⟨_, hprod⟩).1 =
                torFormulaCycleIntersectionProduct (fieldChowSituation k) (pullback.fst f f ≫ f)
                  hP ((r : ℤ) + (s : ℤ) - (dX : ℤ)) (diagonalCycle f)
                  (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 ∧
              ∀ [IsProper f],
                ∃ hdiag : torFormulaCycleIntersectionProduct (fieldChowSituation k)
                    (pullback.fst f f ≫ f) hP ((r : ℤ) + (s : ℤ) - (dX : ℤ)) (diagonalCycle f)
                    (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1 ∈
                    cyclesOfDimension (fieldChowSituation k) (pullback.fst f f ≫ f)
                      ((r : ℤ) + (s : ℤ) - (dX : ℤ)),
                  (properPushforward (fieldChowSituation k) (pullback.fst f f ≫ f) f
                      (pullback.fst f f) rfl ((r : ℤ) + (s : ℤ) - (dX : ℤ)) ⟨_, hdiag⟩).1 =
                    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX
                      ((r : ℤ) + (s : ℤ) - (dX : ℤ)) α.1 β.1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (pullback f f : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  let : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  obtain ⟨dX, hdX⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety k f
  have hP : IsRegular (pullback f f : Scheme.{u}) := isRegular_pullback_of_isRegular f f hX hX
  have hprod := torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k) f
    hX ((r : ℤ) + (s : ℤ) - (dX : ℤ)) α.1 β.1
  have hpart2 := properPushforward_diagonal_torFormulaCycleIntersectionProduct_of_eq f hX hP
    dX r s hdX ((r : ℤ) + (s : ℤ) - (dX : ℤ)) (by ring) α β hαβ hprod
  refine ⟨intersectProperly_exteriorProduct_diagonalCycle k f r s α β hαβ, dX, hdX, hP, hprod,
    hpart2, ?_⟩
  intro _
  have hdiag := torFormulaCycleIntersectionProduct_mem_cyclesOfDimension (fieldChowSituation k)
    (pullback.fst f f ≫ f) hP ((r : ℤ) + (s : ℤ) - (dX : ℤ)) (diagonalCycle f)
    (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1
  refine ⟨hdiag, ?_⟩
  have hbundle : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k)
        (pullback.fst f f ≫ f) hP ((r : ℤ) + (s : ℤ) - (dX : ℤ)) (diagonalCycle f)
        (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1, hdiag⟩ :
      CycleGroup (fieldChowSituation k) (pullback.fst f f ≫ f)
        ((r : ℤ) + (s : ℤ) - (dX : ℤ))) =
      properPushforward (fieldChowSituation k) f (pullback.fst f f ≫ f) (pullback.diagonal f)
        (diagonal_comp_fst_comp f) ((r : ℤ) + (s : ℤ) - (dX : ℤ)) ⟨_, hprod⟩ :=
    Subtype.ext hpart2.symm
  rw [hbundle]
  exact congrArg Subtype.val (properPushforward_fst_properPushforward_diagonal
    (fieldChowSituation k) f f (pullback.fst f f ≫ f) (diagonal_comp_fst_comp f) rfl
    ((r : ℤ) + (s : ℤ) - (dX : ℤ)) ⟨_, hprod⟩)

end Stacks.Intersection.ReductionToDiagonal

end
