module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceLocalDimension
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Saturated

/-!
# Distance from the closed point of a local spectrum

For a catenary Noetherian local ring, the distance from its closed point to a prime
equals the dimension of the closure of that prime. Without catenarity the two can differ, but
one half of the comparison survives: a prime whose closure has dimension at least two is still
at distance at least two.

## Main results

* `Stacks.Algebraization.distanceFunction_closedPoint_eq_coheight`
  computes the distance from the closed point of the affine spectrum, for `A` catenary.
* `Stacks.Algebraization.two_le_distanceFunction_closedPoint_of_two_le_coheight`
  bounds the distance below by two at a prime of coheight at least two, with no catenarity
  hypothesis. With the general upper bound of
  `Stacks.Algebraization.distanceFunction_le_closureLocalDimension` it pins the identification
  of the distance with the dimension of the closure at the value one, where no catenarity is
  needed.

## Implementation notes

The lower bound inspects an arbitrary zigzag. A zigzag with two or more descending legs already
has weight at least two. One with none has weight the codimension of the closed point in the
closure of the prime, which a two-step chain of irreducible closed subsets bounds below by two.
One with a single descending leg either has a strict last ascending leg, which contributes one
on top of its descending leg, or else its middle lower endpoint is the closure of the prime
itself; concatenating the two-step chain with one realizing the descending codimension then
makes the first ascending codimension exceed the descending one by two. Only the last case uses
that the closed point is least for the specialization order, which is where locality enters.

The dimension of the closure of a prime is expressed as its order-theoretic
coheight in the prime spectrum. The closed subset is the singleton containing
the unique closed point. The two inequalities come from the general lower bound by a
dimension function and the general upper bound by the local dimension: a catenary
Noetherian local ring carries the dimension function `deltaDim`, whose value at the closed
point is zero.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- A point of the affine spectrum of `A`, read as a prime ideal of `A`. -/
private def specPointToPrimeSpectrum {A : Type u} [CommRing A]
    (x : Spec (.of A)) : PrimeSpectrum A :=
  OrderDual.ofDual (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A) x)

private theorem specializes_specPointToPrimeSpectrum_iff
    {A : Type u} [CommRing A] (x y : Spec (.of A)) :
    x ⤳ y ↔ specPointToPrimeSpectrum x ⤳ specPointToPrimeSpectrum y := by
  rw [← AlgebraicGeometry.Scheme.le_iff_specializes,
    ← PrimeSpectrum.le_iff_specializes]
  exact (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A)).map_rel_iff.symm

private theorem specPointToPrimeSpectrum_injective {A : Type u} [CommRing A] :
    Function.Injective (specPointToPrimeSpectrum (A := A)) :=
  fun _ _ h => (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A)).injective (OrderDual.ext h)

private theorem specPointToPrimeSpectrum_surjective {A : Type u} [CommRing A] :
    Function.Surjective (specPointToPrimeSpectrum (A := A)) :=
  fun p => ⟨OrderDual.ofDual (AlgebraicGeometry.primeSpectrumOrderIsoSpec A p), rfl⟩

private theorem immediate_specPointToPrimeSpectrum
    {A : Type u} [CommRing A] (x y : Spec (.of A))
    (h : IsImmediateSpecialization x y) :
    TopologicalSpace.IsImmediateSpecialization
      (specPointToPrimeSpectrum x) (specPointToPrimeSpectrum y) := by
  rcases (TopologicalSpace.isImmediateSpecialization_iff x y).mp h with
    ⟨hxy, hne, hmid⟩
  refine ⟨(specializes_specPointToPrimeSpectrum_iff x y).mp hxy,
    specPointToPrimeSpectrum_injective.ne hne, fun z hxz hzy => ?_⟩
  obtain ⟨z', rfl⟩ := specPointToPrimeSpectrum_surjective z
  exact (hmid z' ((specializes_specPointToPrimeSpectrum_iff x z').mpr hxz)
    ((specializes_specPointToPrimeSpectrum_iff z' y).mpr hzy)).imp
      (congrArg specPointToPrimeSpectrum) (congrArg specPointToPrimeSpectrum)

/-- **Stacks Project, Tag 0EIY.** The distance from the closed point of a catenary Noetherian
local spectrum is the dimension of the closure of the given prime. -/
@[stacks 0EIY "local_catenary_eq_dimension"]
public theorem distanceFunction_closedPoint_eq_coheight
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hcat : Ring.IsCatenary A) (y : PrimeSpectrum A) :
    distanceFunction (Spec (.of A))
      ⟨{IsLocalRing.closedPoint A}, IsLocalRing.isClosed_singleton_closedPoint A⟩ y =
        Order.coheight y := by
  let δ : DimensionFunction (Spec (.of A)) := by
    have hdim := (catenary_iff_isDimensionFunction A).mp
      (_root_.isCatenaryRingSaturated_of_isCatenary hcat)
    refine ⟨fun x => deltaDim (specPointToPrimeSpectrum x), ?_, ?_⟩
    · intro x y hxy hne
      exact hdim.1 _ _ ((specializes_specPointToPrimeSpectrum_iff x y).mp hxy)
        (specPointToPrimeSpectrum_injective.ne hne)
    · intro x y hxy
      exact hdim.2 _ _ (immediate_specPointToPrimeSpectrum x y hxy)
  let ys : Spec (.of A) := OrderDual.ofDual (primeSpectrumOrderIsoSpec A y)
  let ms : Spec (.of A) :=
    OrderDual.ofDual (primeSpectrumOrderIsoSpec A (IsLocalRing.closedPoint A))
  have hys : specPointToPrimeSpectrum ys = y := rfl
  have hms : specPointToPrimeSpectrum ms = IsLocalRing.closedPoint A := rfl
  let Z : Closeds (Spec (.of A)) := ⟨{ms}, IsLocalRing.isClosed_singleton_closedPoint A⟩
  have hmax : IsGreatest (δ '' (Z : Set (Spec (.of A)))) 0 := by
    change IsGreatest (δ '' ({ms} : Set (Spec (.of A)))) 0
    have hδm : δ ms = 0 := by
      change deltaDim (specPointToPrimeSpectrum ms) = 0
      rw [show specPointToPrimeSpectrum ms = (⊤ : PrimeSpectrum A) from rfl]
      simp [deltaDim, dimQuotient]
    rw [Set.image_singleton, hδm]
    exact isGreatest_singleton
  have hzy : ms ∈ closure {ys} := ((specializes_specPointToPrimeSpectrum_iff ys ms).mpr
    (by simpa [hys, hms] using IsLocalRing.specializes_closedPoint y)).mem_closure
  have hup := distanceFunction_le_closureLocalDimension (Spec (.of A)) Z ys ms hzy
    (Set.mem_singleton ms : ms ∈ ({ms} : Set (Spec (.of A))))
  have hlower : (Order.coheight y : ℕ∞) ≤ distanceFunction (Spec (.of A)) Z ys := by
    have hcast : ((δ ys).toNat : ℕ∞) = Order.coheight y := by
      change ((deltaDim (specPointToPrimeSpectrum ys)).toNat : ℕ∞) = _
      rw [hys]
      unfold deltaDim dimQuotient
      rw [Int.toNat_natCast]
      exact ENat.natCast_toNat (coheight_lt_top_of_noetherianLocal y).ne
    exact hcast.symm.trans_le (by
      simpa using distanceFunction_ge_dimensionFunction_sub_max (Spec (.of A)) Z δ 0 hmax ys)
  have hupper : distanceFunction (Spec (.of A)) Z ys ≤ Order.coheight y := by
    let e := AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A)
    let f : ↥(closure ({ys} : Set (Spec (.of A)))) ≃o OrderDual ↥(Set.Ici y) := {
      toFun x := OrderDual.toDual ⟨specPointToPrimeSpectrum x.1,
        (by
          change y ≤ specPointToPrimeSpectrum x.1
          exact (PrimeSpectrum.le_iff_specializes _ _).mpr <|
            (specializes_specPointToPrimeSpectrum_iff ys x.1).mp
              (specializes_iff_mem_closure.mpr x.2))⟩
      invFun q := by
        let p : Set.Ici y := OrderDual.ofDual q
        refine ⟨e.symm (OrderDual.toDual (p : PrimeSpectrum A)), ?_⟩
        apply specializes_iff_mem_closure.mp
        apply (specializes_specPointToPrimeSpectrum_iff ys _).mpr
        rw [hys]
        exact (PrimeSpectrum.le_iff_specializes _ _).mp p.2
      left_inv x := by
        apply Subtype.ext
        change e.symm (e x.1) = x.1
        exact e.symm_apply_apply _
      right_inv q := by
        apply OrderDual.ext
        apply Subtype.ext
        simp [e, specPointToPrimeSpectrum,
          AlgebraicGeometry.specOrderIsoPrimeSpectrum]
      map_rel_iff' {a b} := by
        change e a.1 ≤ e b.1 ↔ a.1 ≤ b.1
        exact e.map_rel_iff
    }
    have hpoint :
        Order.coheight (⟨ms, hzy⟩ : ↥(closure ({ys} : Set (Spec (.of A))))) =
          Order.coheight y := by
      have htop : (OrderDual.ofDual (f ⟨ms, hzy⟩) : Set.Ici y) = ⊤ := by
        apply Subtype.ext
        change specPointToPrimeSpectrum ms = (⊤ : PrimeSpectrum A)
        rw [hms]
        rfl
      calc
        Order.coheight (⟨ms, hzy⟩ : ↥(closure ({ys} : Set (Spec (.of A))))) =
            Order.height (OrderDual.ofDual (f ⟨ms, hzy⟩) : Set.Ici y) := by
              simpa only [Order.height_ofDual] using
                (Order.coheight_orderIso f ⟨ms, hzy⟩).symm
        _ = Order.height (⊤ : Set.Ici y) := by rw [htop]
        _ = Order.coheight y := WithBot.coe_inj.mp
          ((Order.height_top_eq_krullDim).trans (Order.coheight_eq_krullDim_Ici y).symm)
    rw [← hpoint]
    simpa using hup
  change distanceFunction (Spec (.of A)) Z ys = Order.coheight y
  exact le_antisymm hupper hlower

/-! ### Distance two from the closed point, with no catenarity hypothesis -/

/-- The singleton closure of a point, as an irreducible closed subset, is the image of that
point under the inverse of the sobriety equivalence. -/
private theorem closureSingleton_eq_symm {Y : Scheme.{u}} (x : Y) :
    IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x :=
  TopologicalSpace.IrreducibleCloseds.ext rfl

/-- Singleton closures are strictly monotone for the specialization order. -/
private theorem closureSingleton_lt_closureSingleton {Y : Scheme.{u}} {a b : Y} (h : a < b) :
    IrreducibleCloseds.closureSingleton a < IrreducibleCloseds.closureSingleton b := by
  rw [closureSingleton_eq_symm, closureSingleton_eq_symm]
  exact (irreducibleSetEquivPoints (α := Y)).symm.lt_iff_lt.mpr h

/-- Two strict specializations give a chain of length two between the singleton closures of the
outer two points. -/
private theorem exists_chain_two_of_lt_lt {Y : Scheme.{u}} {a b c : Y}
    (h1 : a < b) (h2 : b < c) :
    ∃ p : LTSeries (IrreducibleCloseds Y),
      p.head = IrreducibleCloseds.closureSingleton a ∧
        p.last = IrreducibleCloseds.closureSingleton c ∧ p.length = 2 := by
  refine ⟨⟨2, fun i => if i.val = 0 then IrreducibleCloseds.closureSingleton a
    else if i.val = 1 then IrreducibleCloseds.closureSingleton b
    else IrreducibleCloseds.closureSingleton c, ?_⟩, rfl, rfl, rfl⟩
  intro i
  match i with
  | ⟨0, _⟩ => simpa using closureSingleton_lt_closureSingleton h1
  | ⟨1, _⟩ => simpa using closureSingleton_lt_closureSingleton h2

/-- A least point for the specialization order has its singleton closure inside every
irreducible closed subset. -/
private theorem closureSingleton_le_of_isBot {Y : Scheme.{u}} {a : Y}
    (ha : ∀ x : Y, a ≤ x) (C : IrreducibleCloseds Y) :
    IrreducibleCloseds.closureSingleton a ≤ C := by
  rw [closureSingleton_eq_symm, ← (irreducibleSetEquivPoints (α := Y)).symm_apply_apply C]
  exact (irreducibleSetEquivPoints (α := Y)).symm.le_iff_le.mpr (ha _)

/-- An irreducible closed subset contained in a least point is the closure of that point. -/
private theorem eq_closureSingleton_of_subset_singleton {Y : Scheme.{u}} {a : Y}
    (ha : ∀ x : Y, a ≤ x) (C : IrreducibleCloseds Y)
    (hC : (C : Set Y) ⊆ ({a} : Set Y)) :
    C = IrreducibleCloseds.closureSingleton a :=
  le_antisymm
    (by
      rw [← SetLike.coe_subset_coe, IrreducibleCloseds.coe_closureSingleton]
      exact hC.trans subset_closure)
    (closureSingleton_le_of_isBot ha C)

/-- The weight of a system is at least the number of its descending legs plus the net
ascending-minus-descending codimension from any index onwards. -/
private theorem add_sub_le_weight {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) (i : Fin (s.k + 1)) :
    s.k + ((∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
      (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0)) ≤ s.weight :=
  Nat.add_le_add_left (Finset.le_sup (f := fun i : Fin (s.k + 1) =>
    (∑ j : Fin (s.k + 1), if i.val ≤ j.val then s.upCodimension j else 0) -
    (∑ j : Fin s.k, if i.val ≤ j.val then s.downCodimension j else 0))
    (Finset.mem_univ i)) s.k

/-- The weight of a system is at least the number of its descending legs plus the codimension
of its last ascending leg: the summand at the last index carries no descending correction. -/
private theorem add_upCodimension_last_le_weight {Y : Scheme.{u}} [IsNoetherian Y]
    {Z : Closeds Y} {y : Y} (s : DistanceSystem Y Z y) :
    s.k + s.upCodimension (Fin.last s.k) ≤ s.weight := by
  have hup : (∑ j : Fin (s.k + 1),
      if (Fin.last s.k).val ≤ j.val then s.upCodimension j else 0) =
      s.upCodimension (Fin.last s.k) :=
    (Finset.sum_eq_single_of_mem (Fin.last s.k) (Finset.mem_univ _)
      fun b _ hb => ite_eq_right (not_le.mpr (Fin.val_lt_last hb))).trans (by simp)
  have hdown : (∑ j : Fin s.k,
      if (Fin.last s.k).val ≤ j.val then s.downCodimension j else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => ite_eq_right (not_le.mpr j.isLt)
  have hterm := add_sub_le_weight s (Fin.last s.k)
  rwa [hup, hdown, Nat.sub_zero] at hterm

/-- Every system from a least point `m` to a point `yy` whose closure carries a chain of length
two has weight at least two.

Three cases. A system with two or more descending legs already has weight at least two. One with
none has weight the codimension of `m` in the closure of `yy`, which the chain bounds below by
two. One with a single descending leg either has a strict last ascending leg, contributing one
to the weight on top of its single descending leg, or else its middle lower endpoint is the
closure of `yy` itself; concatenating the chain with one realizing the descending codimension
then makes the first ascending codimension exceed the descending one by two. -/
private theorem two_le_weight_of_chain_two {Y : Scheme.{u}} [IsNoetherian Y]
    {m yy : Y} (hbot : ∀ x : Y, m ≤ x)
    {Z : Closeds Y} (hZ : (Z : Set Y) = ({m} : Set Y))
    (pch : LTSeries (IrreducibleCloseds Y))
    (hchead : pch.head = IrreducibleCloseds.closureSingleton m)
    (hchlast : pch.last = IrreducibleCloseds.closureSingleton yy)
    (hchlen : pch.length = 2)
    (s : DistanceSystem Y Z yy) : 2 ≤ s.weight := by
  classical
  have hVzero : s.V ⟨0, Nat.zero_lt_succ s.k⟩ = IrreducibleCloseds.closureSingleton m :=
    eq_closureSingleton_of_subset_singleton hbot _ (by rw [← hZ]; exact s.V_zero_subset)
  have hWlast : s.W (Fin.last s.k) = IrreducibleCloseds.closureSingleton yy :=
    s.W_last_eq_closureSingleton
  rcases Nat.lt_or_ge s.k 2 with hk2 | hk2
  · rcases Nat.lt_or_ge s.k 1 with hk1 | hk1
    · have hk0 : s.k = 0 := by omega
      have hlast0 : Fin.last s.k = (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) :=
        Fin.ext (by simp [hk0])
      have hVl : s.V (Fin.last s.k) = IrreducibleCloseds.closureSingleton m := by
        rw [hlast0]; exact hVzero
      have hup : 2 ≤ s.upCodimension (Fin.last s.k) := by
        have h : ((2 : ℕ) : ℕ∞) ≤ ((s.upCodimension (Fin.last s.k) : ℕ) : ℕ∞) := by
          rw [DistanceSystem.upCodimension_natCast, hVl, hWlast, ← hchlen]
          exact_mod_cast IrreducibleClosedsCodim.length_le_topCodim _ _ pch hchead hchlast
        exact_mod_cast h
      exact le_trans (by omega) (add_upCodimension_last_le_weight s)
    · have hk1' : s.k = 1 := by omega
      rcases Nat.lt_or_ge 0 (s.upCodimension (Fin.last s.k)) with hpos | hzero
      · exact le_trans (by omega) (add_upCodimension_last_le_weight s)
      · have hup1 : s.upCodimension (Fin.last s.k) = 0 := by omega
        have hVi1 : s.V (Fin.last s.k) = IrreducibleCloseds.closureSingleton yy := by
          rcases eq_or_lt_of_le (s.V_le_W (Fin.last s.k)) with heq | hlt
          · rw [heq, hWlast]
          · exact absurd (s.upCodimension_pos_of_lt (Fin.last s.k) hlt) (by omega)
        have hcast : Fin.castSucc (⟨0, by omega⟩ : Fin s.k) =
            (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) := Fin.ext (by simp)
        have hsucc : Fin.succ (⟨0, by omega⟩ : Fin s.k) = Fin.last s.k :=
          Fin.ext (by simp [hk1'])
        have hle : IrreducibleCloseds.closureSingleton yy ≤
            s.W (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) := by
          have hnext := s.V_next_le_W (⟨0, by omega⟩ : Fin s.k)
          rw [hsucc, hcast, hVi1] at hnext
          exact hnext
        obtain ⟨p2, hp2head, hp2last, hp2len⟩ :=
          exists_chain_length_eq_topCodim (IrreducibleCloseds.closureSingleton yy)
            (s.W (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1))) hle (topCodim_ne_top Y _ _)
        have hdownval : s.downCodimension (⟨0, by omega⟩ : Fin s.k) = p2.length := by
          have h : ((s.downCodimension (⟨0, by omega⟩ : Fin s.k) : ℕ) : ℕ∞) =
              ((p2.length : ℕ) : ℕ∞) := by
            rw [DistanceSystem.downCodimension_natCast, hsucc, hcast, hVi1, ← hp2len]
          exact_mod_cast h
        have hconnect : pch.last = p2.head := by rw [hchlast, hp2head]
        have hsmash : ((pch.smash p2 hconnect).length : ℕ∞) ≤
            IrreducibleClosedsCodim.topCodim
              (s.V (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)))
              (s.W (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1))) := by
          refine IrreducibleClosedsCodim.length_le_topCodim _ _ _ ?_ ?_
          · rw [RelSeries.head_smash, hchead, hVzero]
          · rw [RelSeries.last_smash, hp2last]
        have hupi0 : 2 + p2.length ≤
            s.upCodimension (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) := by
          have hlen : (pch.smash p2 hconnect).length = 2 + p2.length := by
            change pch.length + p2.length = 2 + p2.length
            rw [hchlen]
          rw [hlen] at hsmash
          have h : (((2 + p2.length : ℕ)) : ℕ∞) ≤
              ((s.upCodimension (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) : ℕ) : ℕ∞) := by
            rw [DistanceSystem.upCodimension_natCast]
            exact hsmash
          exact_mod_cast h
        have hupsum : s.upCodimension (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) +
            s.upCodimension (Fin.last s.k) ≤
            ∑ j : Fin (s.k + 1),
              if (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)).val ≤ j.val then
                s.upCodimension j else 0 := by
          rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
            ite_eq_left (Nat.zero_le j.val)), ← Finset.sum_pair
            (show (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)) ≠ Fin.last s.k from
              fun hcon => absurd (congrArg Fin.val hcon) (by simp [hk1']))]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        have hdownsum : (∑ j : Fin s.k,
            if (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1)).val ≤ j.val then
              s.downCodimension j else 0) = p2.length := by
          rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
            ite_eq_left (Nat.zero_le j.val)), Finset.sum_eq_single_of_mem
            (⟨0, by omega⟩ : Fin s.k) (Finset.mem_univ _)
            (fun b _ hb => absurd (Fin.ext (show b.val = 0 by have := b.isLt; omega)) hb)]
          exact hdownval
        have hterm := add_sub_le_weight s (⟨0, Nat.zero_lt_succ s.k⟩ : Fin (s.k + 1))
        rw [hdownsum] at hterm
        omega
  · exact le_trans hk2 (le_trans (Nat.le_add_right _ _)
      (add_upCodimension_last_le_weight s))

/-- **No catenarity hypothesis.** A prime of a Noetherian local ring whose closure has dimension
at least two lies at distance at least two from the closed point.

Contrast `distanceFunction_closedPoint_eq_coheight`, which identifies the distance with the
dimension of the closure at every value and asks for `A` catenary. Together with the general
upper bound `distanceFunction_le_closureLocalDimension` this pins the identification at the
value one with no catenarity at all: the distance is one exactly when the closure of the prime
has dimension one. That is what confines the use of catenarity, in the unwinding of the
`(2, 3)`-inequalities of Stacks 0EJA, to the points at distance two. -/
public theorem two_le_distanceFunction_closedPoint_of_two_le_coheight
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (y : PrimeSpectrum A)
    (h : 2 ≤ Order.coheight y) :
    (2 : ℕ∞) ≤ distanceFunction (Spec (.of A))
      ⟨{IsLocalRing.closedPoint A}, IsLocalRing.isClosed_singleton_closedPoint A⟩ y := by
  classical
  have htopm : (IsLocalRing.closedPoint A : PrimeSpectrum A) = (⊤ : PrimeSpectrum A) := rfl
  obtain ⟨q, hyq, hqtop⟩ : ∃ q : PrimeSpectrum A, y < q ∧ q < ⊤ := by
    by_contra hcon
    have hle : Order.coheight y ≤ ((1 : ℕ) : ℕ∞) := by
      rw [Order.coheight_le_coe_iff]
      intro z hz
      have hztop : z = ⊤ := by
        by_contra hzne
        exact hcon ⟨z, hz, lt_of_le_of_ne le_top hzne⟩
      rw [hztop, Order.coheight_top]
      norm_num
    exact absurd (le_trans h hle) (by norm_num)
  let ys : Spec (.of A) := OrderDual.ofDual (primeSpectrumOrderIsoSpec A y)
  let qs : Spec (.of A) := OrderDual.ofDual (primeSpectrumOrderIsoSpec A q)
  let ms : Spec (.of A) :=
    OrderDual.ofDual (primeSpectrumOrderIsoSpec A (IsLocalRing.closedPoint A))
  have hbot : ∀ x : Spec (.of A), ms ≤ x := by
    intro x
    rw [← (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A)).le_iff_le]
    change OrderDual.toDual (IsLocalRing.closedPoint A) ≤
      OrderDual.toDual (specPointToPrimeSpectrum x)
    rw [OrderDual.toDual_le_toDual, htopm]
    exact le_top
  have hlt1 : ms < qs := by
    rw [← (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A)).lt_iff_lt]
    change OrderDual.toDual (IsLocalRing.closedPoint A) < OrderDual.toDual q
    rw [OrderDual.toDual_lt_toDual, htopm]
    exact hqtop
  have hlt2 : qs < ys := by
    rw [← (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of A)).lt_iff_lt]
    change OrderDual.toDual q < OrderDual.toDual y
    rw [OrderDual.toDual_lt_toDual]
    exact hyq
  obtain ⟨pch, hchead, hchlast, hchlen⟩ := exists_chain_two_of_lt_lt hlt1 hlt2
  let Z : Closeds (Spec (.of A)) := ⟨{ms}, IsLocalRing.isClosed_singleton_closedPoint A⟩
  have hZcoe : (Z : Set (Spec (.of A))) = ({ms} : Set (Spec (.of A))) := rfl
  have hmeet : (connectedComponent ys ∩ (Z : Set (Spec (.of A)))).Nonempty :=
    ⟨ms, closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent (Scheme.le_iff_specializes.mp (hbot ys)).mem_closure,
      (Set.mem_singleton ms : ms ∈ ({ms} : Set (Spec (.of A))))⟩
  change (2 : ℕ∞) ≤ distanceFunction (Spec (.of A)) Z ys
  rw [distanceFunction_eq_iInf_of_nonempty (Spec (.of A)) Z ys hmeet]
  refine le_iInf fun s => ?_
  exact_mod_cast two_le_weight_of_chain_two hbot hZcoe pch hchead hchlast hchlen s

end Stacks.Algebraization
