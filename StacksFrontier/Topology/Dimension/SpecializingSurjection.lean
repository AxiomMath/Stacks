module

public import Mathlib.Topology.KrullDimension

/-!
# Dimension does not drop along a specializing or generalizing surjection

Let `f : X → Y` be a continuous surjection of topological spaces with `Y` sober, and suppose
that either specializations or generalizations lift along `f`. Then the Krull dimension of `Y`
is at most that of `X`.

Soberness of `Y` is `[QuasiSober Y] [T0Space Y]`: every irreducible closed subset has a generic
point, and `T0Space` makes it unique. Lifting of specializations and of generalizations are
Mathlib's `SpecializingMap` and `GeneralizingMap`. The dimension is Mathlib's
`topologicalKrullDim`, the Krull dimension of the poset `TopologicalSpace.IrreducibleCloseds` of
irreducible closed subsets, so the inequality to prove is that every strict chain of irreducible
closed subsets of `Y` is matched by one at least as long in `X`.

## Main definitions

* `TopologicalSpace.IrreducibleCloseds.closureSingleton`: the closure of a point, as an
  irreducible closed subset.

## Main results

* `Topology.exists_lift_specializes_chain`: a specialization chain in `Y` lifts to one in `X`.
* `Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap`: the
  Krull dimension of `Y` is at most that of `X`.
* `Topology.topologicalKrullDim_le_height_closureSingleton_of_specializingMap`: if
  specializations lift along `f` and `x₀` lies over a generic point of `Y`, then the Krull
  dimension of `Y` is at most the height of `closure {x₀}`.
-/

@[expose] public section

open TopologicalSpace

namespace TopologicalSpace.IrreducibleCloseds

/-- The closure of a singleton `{x}`, viewed as an irreducible closed subset of `X`. -/
noncomputable def closureSingleton {X : Type*} [TopologicalSpace X] (x : X) :
    IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- The underlying set of `closureSingleton x` is `closure {x}`. -/
@[simp]
lemma coe_closureSingleton {X : Type*} [TopologicalSpace X] (x : X) :
    (closureSingleton x : Set X) = closure {x} :=
  rfl

end TopologicalSpace.IrreducibleCloseds

namespace Topology

/-- The generic points of a strict chain of irreducible closed subsets form a chain for the
specialization relation: the generic point of the larger member specializes to the generic
point of the smaller one. -/
lemma specializes_succ_castSucc_of_isGenericPoint
    {Y : Type*} [TopologicalSpace Y]
    (p : LTSeries (IrreducibleCloseds Y)) (y : Fin (p.length + 1) → Y)
    (hy : ∀ i, IsGenericPoint (y i) (p.toFun i).carrier) (i : Fin p.length) :
    y i.succ ⤳ y i.castSucc := by
  have h2 : (p.toFun i.castSucc).carrier ⊆ (p.toFun i.succ).carrier := (p.step i).le
  rw [specializes_iff_mem_closure, hy i.succ]
  exact h2 (by rw [← hy i.castSucc]; exact subset_closure rfl)

/-- Reverse induction for the specializing case: a point above the last member of a
specialization chain in `Y` extends to a full chain in `X` above it. -/
private lemma exists_chain_of_specializingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : SpecializingMap f)
    {n : ℕ} (y : Fin (n + 1) → Y) (hspec : ∀ i : Fin n, y i.succ ⤳ y i.castSucc)
    (xLast : X) (hxLast : f xLast = y (Fin.last n)) :
    ∃ x : Fin (n + 1) → X, x (Fin.last n) = xLast ∧ (∀ i, f (x i) = y i) ∧
      (∀ i : Fin n, x i.succ ⤳ x i.castSucc) := by
  induction n generalizing xLast with
  | zero =>
    exact ⟨fun _ => xLast, rfl, fun i => by fin_cases i; exact hxLast, fun i => i.elim0⟩
  | succ n ih =>
    have hlast : (Fin.last n : Fin (n + 1)).succ = Fin.last (n + 1) := by ext; simp [Fin.last]
    have hstep : f xLast ⤳ y (Fin.last n).castSucc := by
      have h := hspec (Fin.last n)
      rw [hlast] at h
      exact hxLast ▸ h
    obtain ⟨xPrev, hxPrev, hfxPrev⟩ := hf hstep
    have hspec' : ∀ i : Fin n, (y ∘ Fin.castSucc) i.succ ⤳ (y ∘ Fin.castSucc) i.castSucc :=
      fun i => by simpa only [Function.comp_apply, Fin.succ_castSucc] using hspec i.castSucc
    obtain ⟨x', hx'Last, hfx', hx'spec⟩ :=
      ih (y ∘ Fin.castSucc) hspec' xPrev (by simpa only [Function.comp_apply] using hfxPrev)
    refine ⟨Fin.snoc x' xLast, Fin.snoc_last _ _, ?_, ?_⟩
    · refine Fin.lastCases ?_ fun j => ?_
      · rw [Fin.snoc_last]
        exact hxLast
      · rw [Fin.snoc_castSucc]
        simpa only [Function.comp_apply] using hfx' j
    · refine Fin.lastCases ?_ fun j => ?_
      · rw [hlast, Fin.snoc_last, Fin.snoc_castSucc, hx'Last]
        exact hxPrev
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hx'spec j

/-- Forward induction for the generalizing case: a point above the first member of a
specialization chain in `Y` extends to a full chain in `X` above it. -/
lemma exists_chain_of_generalizingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : GeneralizingMap f)
    {n : ℕ} (y : Fin (n + 1) → Y) (hspec : ∀ i : Fin n, y i.succ ⤳ y i.castSucc)
    (xFirst : X) (hxFirst : f xFirst = y 0) :
    ∃ x : Fin (n + 1) → X, x 0 = xFirst ∧ (∀ i, f (x i) = y i) ∧
      (∀ i : Fin n, x i.succ ⤳ x i.castSucc) := by
  induction n generalizing xFirst with
  | zero =>
    exact ⟨fun _ => xFirst, rfl, fun i => by fin_cases i; exact hxFirst, fun i => i.elim0⟩
  | succ n ih =>
    have hstep : y (Fin.succ 0) ⤳ f xFirst := by
      have h := hspec 0
      rw [Fin.castSucc_zero] at h
      exact hxFirst ▸ h
    obtain ⟨xNext, hxNext, hfxNext⟩ := hf hstep
    have hspec' : ∀ i : Fin n, (y ∘ Fin.succ) i.succ ⤳ (y ∘ Fin.succ) i.castSucc :=
      fun i => by simpa only [Function.comp_apply, Fin.succ_castSucc] using hspec i.succ
    obtain ⟨x', hx'First, hfx', hx'spec⟩ :=
      ih (y ∘ Fin.succ) hspec' xNext (by simpa only [Function.comp_apply] using hfxNext)
    refine ⟨Fin.cons xFirst x', Fin.cons_zero .., ?_, ?_⟩
    · refine Fin.cases (by simpa using hxFirst) fun j => ?_
      simpa only [Fin.cons_succ, Function.comp_apply] using hfx' j
    · refine Fin.cases ?_ fun j => ?_
      · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hx'First]
        exact hxNext
      · simpa only [Fin.cons_succ, Fin.castSucc_succ] using hx'spec j

/-- A specialization chain in `Y` lifts, along a continuous surjection whose specializations or
generalizations lift, to a specialization chain in `X` of the same length above it. -/
lemma exists_lift_specializes_chain
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hsurj : Function.Surjective f)
    (h : SpecializingMap f ∨ GeneralizingMap f)
    {n : ℕ} (y : Fin (n + 1) → Y) (hspec : ∀ i : Fin n, y i.succ ⤳ y i.castSucc) :
    ∃ x : Fin (n + 1) → X, (∀ i, f (x i) = y i) ∧ (∀ i : Fin n, x i.succ ⤳ x i.castSucc) := by
  rcases h with hf | hf
  · obtain ⟨xLast, hxLast⟩ := hsurj (y (Fin.last n))
    obtain ⟨x, -, hfx, hxspec⟩ := exists_chain_of_specializingMap f hf y hspec xLast hxLast
    exact ⟨x, hfx, hxspec⟩
  · obtain ⟨xFirst, hxFirst⟩ := hsurj (y 0)
    obtain ⟨x, -, hfx, hxspec⟩ := exists_chain_of_generalizingMap f hf y hspec xFirst hxFirst
    exact ⟨x, hfx, hxspec⟩

/-- If `x` specializes to `y`, then `closure {y}` is contained in `closure {x}`. -/
private lemma closureSingleton_le_of_specializes {X : Type*} [TopologicalSpace X] {x y : X}
    (h : x ⤳ y) : IrreducibleCloseds.closureSingleton y ≤ IrreducibleCloseds.closureSingleton x :=
  specializes_iff_closure_subset.mp h

/-- Every member of a chain of irreducible closed subsets of a sober space has a generic
point. -/
private lemma exists_isGenericPoint_chain {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    (p : LTSeries (IrreducibleCloseds Y)) :
    ∃ y : Fin (p.length + 1) → Y, ∀ i, IsGenericPoint (y i) (p.toFun i).carrier :=
  ⟨fun i => (p.toFun i).isIrreducible'.genericPoint, fun i =>
    (p.toFun i).isIrreducible'.isGenericPoint_genericPoint (p.toFun i).isClosed'⟩

/-- The chain of singleton closures of a lifted specialization chain is strictly increasing. -/
lemma closureSingleton_lt_closureSingleton_of_isGenericPoint
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f)
    (p : LTSeries (IrreducibleCloseds Y)) (y : Fin (p.length + 1) → Y)
    (hy : ∀ i, IsGenericPoint (y i) (p.toFun i).carrier)
    (x : Fin (p.length + 1) → X) (hfx : ∀ i, f (x i) = y i)
    (hxspec : ∀ i : Fin p.length, x i.succ ⤳ x i.castSucc) (i : Fin p.length) :
    IrreducibleCloseds.closureSingleton (x i.castSucc) <
      IrreducibleCloseds.closureSingleton (x i.succ) := by
  refine lt_of_le_of_ne ?_ ?_
  · exact closureSingleton_le_of_specializes (hxspec i)
  · intro heq
    have hclosure : closure ({x i.castSucc} : Set X) = closure {x i.succ} := by
      have := congr_arg (·.carrier) heq
      simpa only [IrreducibleCloseds.closureSingleton] using this
    have h1 : x i.castSucc ⤳ x i.succ := by
      rw [specializes_iff_mem_closure, hclosure]
      exact subset_closure rfl
    have hy_eq : y i.castSucc = y i.succ :=
      (hfx i.castSucc).symm.trans (((h1.antisymm (hxspec i)).map hf).eq.trans (hfx i.succ))
    have hcarrier : (p.toFun i.castSucc).carrier = (p.toFun i.succ).carrier := by
      rw [← hy i.castSucc, ← hy i.succ, hy_eq]
    exact (p.step i).ne (IrreducibleCloseds.ext hcarrier)

/-- Let `f : X → Y` be a continuous surjection of topological spaces with `Y`
sober. If specializations lift along `f`, or generalizations lift along `f`, then the Krull
dimension of `Y` is at most the Krull dimension of `X`. -/
@[stacks 02JF]
theorem topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f)
    (h : SpecializingMap f ∨ GeneralizingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim
  simp only [Order.krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨y, hy⟩ := exists_isGenericPoint_chain p
  obtain ⟨x, hfx, hxspec⟩ := exists_lift_specializes_chain f hsurj h y
    (specializes_succ_castSucc_of_isGenericPoint p y hy)
  exact le_iSup (fun r : LTSeries (IrreducibleCloseds X) => (↑r.length : WithBot ℕ∞))
    ⟨p.length, fun i => IrreducibleCloseds.closureSingleton (x i),
      closureSingleton_lt_closureSingleton_of_isGenericPoint f hf p y hy x hfx hxspec⟩

/-- If specializations lift along `f` and `x₀` lies over a generic point of `Y`, then the Krull
dimension of `Y` is at most the height of the closure of `x₀`. -/
lemma topologicalKrullDim_le_height_closureSingleton_of_specializingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (h : SpecializingMap f)
    {x₀ : X} {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) (hx₀ : f x₀ = η) :
    topologicalKrullDim Y ≤
      (Order.height (IrreducibleCloseds.closureSingleton x₀) : WithBot ℕ∞) := by
  unfold topologicalKrullDim
  simp only [Order.krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨y, hy⟩ := exists_isGenericPoint_chain p
  obtain ⟨xl, hx₀xl, hfxl⟩ := h (hx₀ ▸ hη.specializes (Set.mem_univ (y (Fin.last p.length))))
  obtain ⟨x, hxlast, hfx, hxspec⟩ := exists_chain_of_specializingMap f h y
    (specializes_succ_castSucc_of_isGenericPoint p y hy) xl hfxl
  refine WithBot.coe_mono (Order.length_le_height
    (p := ⟨p.length, fun i => IrreducibleCloseds.closureSingleton (x i),
      closureSingleton_lt_closureSingleton_of_isGenericPoint f hf p y hy x hfx hxspec⟩)
    (x := IrreducibleCloseds.closureSingleton x₀) ?_)
  change IrreducibleCloseds.closureSingleton (x (Fin.last p.length)) ≤ _
  rw [hxlast]
  exact closureSingleton_le_of_specializes hx₀xl

end Topology
