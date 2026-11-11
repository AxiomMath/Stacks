module

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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Stacks 006Y — The direct-sum-over-points presheaf

Let `X` be a topological space and `M : X → Type u` a family of abelian
groups indexed by the points of `X`. The presheaf
`F : U ↦ ⨁_{x ∈ U} M x` with the natural restriction maps is **not** a sheaf
in general. The Stacks text gives the canonical counterexample: take `X` to
be an infinite discrete space and `M` the constant family `ℤ`; on the
singleton cover the sheaf condition would force `F(X) = ∏ ℤ`, but by
definition `F(X) = ⨁ ℤ`, and the constant family `(1, 1, …)` has infinite
support so it does not arise from any element of the direct sum.

The Stacks example also asserts, leaving the proof as an exercise, that `F`
*is* a sheaf when every open of `X` is quasi-compact. This is part of the
assertion of tag 006Y and is proved here as
`directSumOverPointsPresheaf_isSheaf_of_isCompact`: a compatible family on a
cover of `U` glues pointwise, and the gluing has finite support because `U`
is covered by finitely many members of the cover.

The complete statement of tag 006Y, both clauses, is
`directSumOverPointsPresheaf_not_isSheaf_in_general_and_isSheaf_of_isCompact`.
-/

@[expose] public section

open TopologicalSpace TopCat Opposite CategoryTheory

universe u

/-- Auxiliary restriction map: for opens `U ≤ V` in `X`, the natural
projection `(Π₀ x : V, M x.1) → (Π₀ x : U, M x.1)` that forgets components
outside `U`. -/
noncomputable def restrictMap {X : TopCat.{u}} (M : X → Type u)
    [∀ x, AddCommGroup (M x)] {U V : Opens X} (h : U ≤ V) :
    (Π₀ x : V, M x.1) → (Π₀ x : U, M x.1) := fun f =>
  DFinsupp.comapDomain (β := fun x : V => M x.1)
    (Set.inclusion (s := (U : Set X)) (t := (V : Set X)) h)
    (Set.inclusion_injective _) f

/-- The components of a restricted section are the components of the original one: `restrictMap`
evaluated at `x : U` is the value of `f` at `x` regarded as a point of `V`. -/
@[simp] lemma restrictMap_apply {X : TopCat.{u}} (M : X → Type u)
    [∀ x, AddCommGroup (M x)] {U V : Opens X} (h : U ≤ V)
    (f : Π₀ x : V, M x.1) (x : U) :
    restrictMap M h f x = f ⟨x.1, h x.2⟩ := rfl

/-- The presheaf `U ↦ ⨁_{x ∈ U} M x` (encoded as `Π₀ x : U, M x`)
on a topological space `X` with point-indexed family `M`.
The restriction map for `U ≤ V` projects a direct sum supported on `V`
to one supported on `U` by forgetting the components outside `U`. -/
noncomputable def directSumOverPointsPresheaf {X : TopCat.{u}}
    (M : X → Type u) [∀ x, AddCommGroup (M x)] :
    TopCat.Presheaf (Type u) X where
  obj U := Π₀ x : (unop U : Opens X), M x.1
  map {U V} i := ↾(restrictMap M i.unop.le)
  map_id U := by
    apply TypeCat.homEquiv.injective
    funext f
    refine DFinsupp.ext fun x => ?_
    rfl
  map_comp {U V W} i j := by
    apply TypeCat.homEquiv.injective
    funext f
    refine DFinsupp.ext fun x => ?_
    rfl

/-- A dependent function with finite support on an infinite index type vanishes somewhere. -/
lemma DFinsupp.exists_apply_eq_zero {ι : Type*} [Infinite ι] {β : ι → Type*} [∀ i, Zero (β i)]
    (f : Π₀ i, β i) : ∃ i, f i = 0 := by
  by_contra hc
  simp only [not_exists] at hc
  exact Set.infinite_univ (f.finite_support.subset fun i _ => hc i)

/-- On an infinite discrete space, the presheaf `U ↦ ⨁_{x ∈ U} M x` is not a sheaf as soon as
every `M x` has a nonzero element: the singleton opens cover `X`, the chosen elements form a
compatible family on that cover, and any gluing would be nonzero at every point of `X`. -/
theorem directSumOverPointsPresheaf_not_isSheaf_of_infinite_discrete {X : TopCat.{u}}
    [DiscreteTopology (↑X : Type u)] [Infinite (↑X : Type u)] (M : X → Type u)
    [∀ x, AddCommGroup (M x)] (m : ∀ x, M x) (hm : ∀ x, m x ≠ 0) :
    ¬ (directSumOverPointsPresheaf M).IsSheaf := by
  classical
  let U : (↑X : Type u) → Opens (↑X : Type u) := fun n => ⟨{n}, isOpen_discrete _⟩
  have hcover : iSup U = ⊤ := le_antisymm le_top fun n _ => Opens.mem_iSup.mpr ⟨n, rfl⟩
  let sec : ∀ n : (↑X : Type u),
      ToType ((directSumOverPointsPresheaf M).obj (op (U n))) := fun n =>
    show Π₀ x : (U n : Opens (↑X : Type u)), M x.1 from
      DFinsupp.single (⟨n, rfl⟩ : (U n : Opens (↑X : Type u))) (m n)
  have hcompat : (directSumOverPointsPresheaf M).IsCompatible U sec := by
    intro n p
    refine DFinsupp.ext fun x => ?_
    obtain ⟨hxn, hxp⟩ := x.2
    have hnp : n = p := hxn.symm.trans hxp
    subst hnp
    rfl
  intro hSh
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types] at hSh
  obtain ⟨s, hglue, _⟩ := hSh U sec hcompat
  let s' : Π₀ x : (iSup U : Opens (↑X : Type u)), M x.1 :=
    show Π₀ x : (iSup U : Opens (↑X : Type u)), M x.1 from s
  have hmem : ∀ n : (↑X : Type u), n ∈ (iSup U : Opens (↑X : Type u)) := by
    intro n; rw [hcover]; trivial
  have hval : ∀ n : (↑X : Type u), s' ⟨n, hmem n⟩ = m n := by
    intro n
    have h := congrArg
      (fun f : Π₀ x : (U n : Opens (↑X : Type u)), M x.1 =>
        f (⟨n, rfl⟩ : (U n : Opens (↑X : Type u)))) (hglue n)
    -- Only reduce the RHS; the LHS is definitionally `s' ⟨n, _⟩`, closed by `exact`.
    simp only [sec, DFinsupp.single_eq_same] at h
    exact h
  have : Infinite (iSup U : Opens (↑X : Type u)) :=
    Infinite.of_injective (fun n => ⟨n, hmem n⟩) fun a b hab => Subtype.ext_iff.mp hab
  obtain ⟨x, hx⟩ := DFinsupp.exists_apply_eq_zero s'
  exact hm x.1 ((hval x.1).symm.trans hx)

/-- Clause (a) of Stacks Tag 006Y. Let `X` be a topological space and `M : X → Type u`
be a family of abelian groups indexed by the points of `X`. The presheaf
`U ↦ ⨁_{x ∈ U} M x` is **not** a sheaf in general: there exists a
topological space `X` and a family `M` for which the presheaf fails to be
a sheaf.

The witness is `X = ULift ℕ` with the discrete topology and the constant
family `M_x = ULift ℤ`. The singleton sets `{n}` form an open cover of `X`,
and the family of sections `s_n = (n ↦ 1)` is compatible (pairwise
intersections are empty). However, any gluing would have to take value
`1 ≠ 0` at every point of `X`, contradicting the finite-support property
of the direct sum.

This is clause (a) of tag 006Y; the complete statement is
`directSumOverPointsPresheaf_not_isSheaf_in_general_and_isSheaf_of_isCompact`. -/
theorem directSumOverPointsPresheaf_not_isSheaf_in_general :
    ∃ (X : TopCat.{u}) (M : X → Type u) (_ : ∀ x, AddCommGroup (M x)),
      ¬ (directSumOverPointsPresheaf (X := X) M).IsSheaf := by
  let X : TopCat.{u} := TopCat.of (ULift.{u, 0} ℕ)
  have : DiscreteTopology (↑X : Type u) := (inferInstance : DiscreteTopology (ULift.{u, 0} ℕ))
  have : Infinite (↑X : Type u) := (inferInstance : Infinite (ULift.{u, 0} ℕ))
  let M : (↑X : Type u) → Type u := fun _ => ULift.{u, 0} ℤ
  refine ⟨X, M, fun _ => inferInstance, ?_⟩
  exact directSumOverPointsPresheaf_not_isSheaf_of_infinite_discrete M (fun _ => ULift.up 1)
    fun _ h => one_ne_zero (congrArg ULift.down h)

/-- If every open subset of `X` is quasi-compact, then the presheaf `U ↦ ⨁_{x ∈ U} M x` is a
sheaf, for every family `M` of abelian groups. A compatible family of sections on a cover of `U`
determines a unique function on `U`, and that function has finite support because finitely many
members of the cover already cover `U`. This is clause (b) of Stacks Tag 006Y. -/
theorem directSumOverPointsPresheaf_isSheaf_of_isCompact {X : TopCat.{u}}
    (hX : ∀ U : Opens X, IsCompact (U : Set X)) (M : X → Type u) [∀ x, AddCommGroup (M x)] :
    (directSumOverPointsPresheaf M).IsSheaf := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι U sf hcompat
  let g : ∀ i, Π₀ y : (U i : Opens X), M y.1 := fun i => sf i
  have hagree : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      g i ⟨x, hi⟩ = g j ⟨x, hj⟩ := fun i j x hi hj =>
    congrArg (fun f : Π₀ y : (U i ⊓ U j : Opens X), M y.1 => f ⟨x, hi, hj⟩) (hcompat i j)
  have hmem : ∀ x : (iSup U : Opens X), ∃ i, x.1 ∈ U i := fun x => Opens.mem_iSup.mp x.2
  choose idx hidx using hmem
  let s0 : ∀ x : (iSup U : Opens X), M x.1 := fun x => g (idx x) ⟨x.1, hidx x⟩
  have hs0 : ∀ i (x : (iSup U : Opens X)) (hi : x.1 ∈ U i), s0 x = g i ⟨x.1, hi⟩ :=
    fun i x hi => hagree _ _ _ _ _
  obtain ⟨t, ht⟩ := (hX (iSup U)).elim_finite_subcover (fun i => (U i : Set X))
    (fun i => (U i).isOpen) (fun x hx => Set.mem_iUnion.mpr (Opens.mem_iSup.mp hx))
  let S : Set (iSup U : Opens X) := ⋃ i ∈ t,
    (fun y : (U i : Opens X) => (⟨y.1, le_iSup U i y.2⟩ : (iSup U : Opens X))) ''
      {y | g i y ≠ 0}
  have hS : S.Finite := t.finite_toSet.biUnion fun i _ => (g i).finite_support.image _
  have hsupp : ∀ x, x ∈ S ∨ s0 x = 0 := by
    intro x
    by_cases hx : s0 x = 0
    · exact Or.inr hx
    left
    obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.mp (ht x.2)
    exact Set.mem_iUnion₂.mpr
      ⟨i, hit, ⟨x.1, hi⟩, fun h => hx ((hs0 i x hi).trans h), Subtype.ext rfl⟩
  let s : Π₀ x : (iSup U : Opens X), M x.1 :=
    ⟨s0, Trunc.mk ⟨hS.toFinset.val, fun x =>
      (hsupp x).imp_left fun h => Finset.mem_val.mpr (hS.mem_toFinset.mpr h)⟩⟩
  refine ⟨s, fun i => ?_, fun s' hs' => ?_⟩
  · refine DFinsupp.ext fun y => ?_
    exact hs0 i ⟨y.1, le_iSup U i y.2⟩ y.2
  · refine DFinsupp.ext fun x => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
    have h := congrArg (fun f : Π₀ y : (U i : Opens X), M y.1 => f ⟨x.1, hi⟩) (hs' i)
    exact h.trans (hs0 i x hi).symm

/-- **Stacks Tag 006Y.** Let `X` be a topological space and `M_x` an abelian group for each
`x ∈ X`, and let `F` be the presheaf `U ↦ ⨁_{x ∈ U} M_x`. Then
(a) `F` is not a sheaf in general: there are a space `X` and a family `M` for which `F` is not a
sheaf (an infinite discrete space with `M_x = ℤ`);
(b) if every open subset of `X` is quasi-compact, then `F` is a sheaf, for every family `M`. -/
@[stacks 006Y]
theorem directSumOverPointsPresheaf_not_isSheaf_in_general_and_isSheaf_of_isCompact :
    (∃ (X : TopCat.{u}) (M : X → Type u) (_ : ∀ x, AddCommGroup (M x)),
      ¬ (directSumOverPointsPresheaf (X := X) M).IsSheaf) ∧
    ∀ X : TopCat.{u}, (∀ U : Opens X, IsCompact (U : Set X)) →
      ∀ (M : X → Type u) [∀ x, AddCommGroup (M x)], (directSumOverPointsPresheaf M).IsSheaf :=
  ⟨directSumOverPointsPresheaf_not_isSheaf_in_general,
    fun _ hX M _ => directSumOverPointsPresheaf_isSheaf_of_isCompact hX M⟩
