module

public import Mathlib.SetTheory.ZFC.VonNeumann
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute

/-!
# Reflection Principle (Stacks tag 000G)

Given a finite family of formulas of set theory `φᵢ` with `n` free variables and
a set `M₀`, there is a limit ordinal `α` such that `M₀ ⊆ V_α` and every `φᵢ` is
absolute for `V_α` on parameters drawn from `V_α`, where `V_α = ZFSet.vonNeumann α`
is the von Neumann hierarchy from Mathlib (notation `V_ α`).
-/

@[expose] public section

open Order ZFSet

universe u

/-! ## Formulas of set theory -/

/-- A first-order formula in the language of set theory with `n` free variables indexed by
`Fin n`: atomic membership and equality between variables, closed under the propositional
connectives and under both quantifiers (which bind the last variable). -/
inductive SetFormula : ℕ → Type
  | mem {n : ℕ} (i j : Fin n) : SetFormula n
  | eq  {n : ℕ} (i j : Fin n) : SetFormula n
  | not {n : ℕ} : SetFormula n → SetFormula n
  | and {n : ℕ} : SetFormula n → SetFormula n → SetFormula n
  | or  {n : ℕ} : SetFormula n → SetFormula n → SetFormula n
  | imp {n : ℕ} : SetFormula n → SetFormula n → SetFormula n
  | iff {n : ℕ} : SetFormula n → SetFormula n → SetFormula n
  | all {n : ℕ} : SetFormula (n + 1) → SetFormula n
  | ex  {n : ℕ} : SetFormula (n + 1) → SetFormula n

/-- Satisfaction of `φ : SetFormula n` in the full universe of sets, on the assignment
`x : Fin n → ZFSet`. Both quantifiers range over all of `ZFSet`. -/
def SetFormula.realize : {n : ℕ} → SetFormula n → (Fin n → ZFSet) → Prop
  | _, .mem i j, x => x i ∈ x j
  | _, .eq  i j, x => x i = x j
  | _, .not φ,   x => ¬ φ.realize x
  | _, .and φ ψ, x => φ.realize x ∧ ψ.realize x
  | _, .or  φ ψ, x => φ.realize x ∨ ψ.realize x
  | _, .imp φ ψ, x => φ.realize x → ψ.realize x
  | _, .iff φ ψ, x => φ.realize x ↔ ψ.realize x
  | _, .all φ,   x => ∀ a : ZFSet, φ.realize (Fin.snoc x a)
  | _, .ex  φ,   x => ∃ a : ZFSet, φ.realize (Fin.snoc x a)

/-- Satisfaction of `φ : SetFormula n` relativized to a set `M`: the atomic and
propositional cases agree with `SetFormula.realize`, but each quantifier ranges over the
elements of `M` only. -/
def SetFormula.realizeIn :
    {n : ℕ} → SetFormula n → ZFSet → (Fin n → ZFSet) → Prop
  | _, .mem i j, _, x => x i ∈ x j
  | _, .eq  i j, _, x => x i = x j
  | _, .not φ,   M, x => ¬ φ.realizeIn M x
  | _, .and φ ψ, M, x => φ.realizeIn M x ∧ ψ.realizeIn M x
  | _, .or  φ ψ, M, x => φ.realizeIn M x ∨ ψ.realizeIn M x
  | _, .imp φ ψ, M, x => φ.realizeIn M x → ψ.realizeIn M x
  | _, .iff φ ψ, M, x => φ.realizeIn M x ↔ ψ.realizeIn M x
  | _, .all φ,   M, x => ∀ a : ZFSet, a ∈ M → φ.realizeIn M (Fin.snoc x a)
  | _, .ex  φ,   M, x => ∃ a : ZFSet, a ∈ M ∧ φ.realizeIn M (Fin.snoc x a)

/-- `Reflects α ψ` means: `V_ α` (the von Neumann hierarchy) agrees with the full
universe on `ψ` when evaluated on parameters drawn from `V_ α`. -/
def Reflects (α : Ordinal.{u}) {k : ℕ} (ψ : SetFormula k) : Prop :=
  ∀ x : Fin k → ZFSet, (∀ j, x j ∈ V_ α) → (ψ.realizeIn (V_ α) x ↔ ψ.realize x)

/-! ## The von Neumann hierarchy -/

/-- Every set is contained in some stage of the von Neumann hierarchy, namely the stage
given by its own rank. -/
lemma exists_subset_vonNeumann (s : ZFSet.{u}) : ∃ β : Ordinal.{u}, s ⊆ V_ β :=
  ⟨s.rank, subset_vonNeumann_self s⟩

private lemma snoc_mem_vonNeumann {k : ℕ} {α : Ordinal.{u}}
    {x : Fin k → ZFSet.{u}} {a : ZFSet.{u}}
    (hx : ∀ j, x j ∈ V_ α) (ha : a ∈ V_ α) :
    ∀ j : Fin (k + 1), (Fin.snoc x a : Fin (k + 1) → ZFSet.{u}) j ∈ V_ α := by
  refine Fin.lastCases ?_ fun i => ?_
  · simpa using ha
  · simpa using hx i

/-! ## Skolem functions -/

/-- A Skolem-style function: it consumes `arity` many sets and returns a set. -/
structure SkolemFn : Type (u + 1) where
  /-- The number of arguments the function takes. -/
  arity : ℕ
  /-- The underlying function on tuples of sets. -/
  toFun : (Fin arity → ZFSet.{u}) → ZFSet.{u}

/-- `ClosedUnder M L` means each function in `L` maps tuples from `M` into `M`. -/
def ClosedUnder (M : ZFSet.{u}) (L : List SkolemFn.{u}) : Prop :=
  ∀ s ∈ L, ∀ x : Fin s.arity → ZFSet, (∀ j, x j ∈ M) → s.toFun x ∈ M

/-- A witness for `∃ a, φ (x, a)`: some `a` making `φ` true at `Fin.snoc x a` when one
exists, and `∅` otherwise. -/
noncomputable def SetFormula.exWitness {n : ℕ} (φ : SetFormula (n + 1))
    (x : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  letI := Classical.propDecidable (∃ a : ZFSet.{u}, φ.realize (Fin.snoc x a))
  if h : ∃ a : ZFSet.{u}, φ.realize (Fin.snoc x a) then h.choose else ∅

/-- `φ.exWitness x` is a genuine witness as soon as some witness exists. -/
lemma SetFormula.realize_snoc_exWitness {n : ℕ} {φ : SetFormula (n + 1)}
    {x : Fin n → ZFSet.{u}} (h : ∃ a : ZFSet.{u}, φ.realize (Fin.snoc x a)) :
    φ.realize (Fin.snoc x (φ.exWitness x)) := by
  simp only [SetFormula.exWitness, h, dite_true]
  exact h.choose_spec

/-- The Skolem functions of a formula: one witness function for each quantifier occurring
in it, the function attached to `∀` producing a counterexample to the quantified body. -/
noncomputable def Skolems : {n : ℕ} → SetFormula n → List SkolemFn.{u}
  | _, .mem _ _ => []
  | _, .eq  _ _ => []
  | _, .not φ   => Skolems φ
  | _, .and φ ψ => Skolems φ ++ Skolems ψ
  | _, .or  φ ψ => Skolems φ ++ Skolems ψ
  | _, .imp φ ψ => Skolems φ ++ Skolems ψ
  | _, .iff φ ψ => Skolems φ ++ Skolems ψ
  | n, .all φ   => ⟨n, φ.not.exWitness⟩ :: Skolems φ
  | n, .ex  φ   => ⟨n, φ.exWitness⟩ :: Skolems φ

/-- Closure under a list of Skolem functions is inherited by any sublist. -/
lemma closedUnder_of_subset {M : ZFSet.{u}} {L L' : List SkolemFn.{u}}
    (hLL' : ∀ s ∈ L, s ∈ L') (hL' : ClosedUnder M L') :
    ClosedUnder M L :=
  fun s hs => hL' s (hLL' s hs)

private lemma ClosedUnder.of_append_left {M : ZFSet.{u}} {L L' : List SkolemFn.{u}}
    (h : ClosedUnder M (L ++ L')) : ClosedUnder M L :=
  closedUnder_of_subset (fun _ => List.mem_append_left _) h

private lemma ClosedUnder.of_append_right {M : ZFSet.{u}} {L L' : List SkolemFn.{u}}
    (h : ClosedUnder M (L ++ L')) : ClosedUnder M L' :=
  closedUnder_of_subset (fun _ => List.mem_append_right _) h

private lemma ClosedUnder.tail {M : ZFSet.{u}} {s : SkolemFn.{u}} {L : List SkolemFn.{u}}
    (h : ClosedUnder M (s :: L)) : ClosedUnder M L :=
  closedUnder_of_subset (fun _ => List.mem_cons_of_mem _) h

/-- A reflected formula stays reflected after extending the parameters by an element of `V_ α`. -/
private lemma Reflects.snoc_iff {α : Ordinal.{u}} {k : ℕ} {φ : SetFormula (k + 1)}
    (h : Reflects α φ) {x : Fin k → ZFSet.{u}} {a : ZFSet.{u}}
    (hx : ∀ j, x j ∈ V_ α) (ha : a ∈ V_ α) :
    φ.realizeIn (V_ α) (Fin.snoc x a) ↔ φ.realize (Fin.snoc x a) :=
  h _ (snoc_mem_vonNeumann hx ha)

private lemma reflects_ex_of_closedUnder {α : Ordinal.{u}} {k : ℕ} (φ : SetFormula (k + 1))
    (h_cl : ClosedUnder (V_ α) (Skolems (SetFormula.ex φ)))
    (ih : ClosedUnder (V_ α) (Skolems φ) → Reflects α φ) :
    Reflects α (SetFormula.ex φ) := by
  have refl_φ : Reflects α φ := ih h_cl.tail
  intro x hx
  rw [SetFormula.realizeIn, SetFormula.realize]
  refine ⟨fun ⟨a, ha, hφ⟩ => ⟨a, (refl_φ.snoc_iff hx ha).mp hφ⟩, fun hex => ?_⟩
  have hW : φ.exWitness x ∈ V_ α := h_cl _ List.mem_cons_self x hx
  exact ⟨_, hW, (refl_φ.snoc_iff hx hW).mpr
    (SetFormula.realize_snoc_exWitness hex)⟩

private lemma reflects_all_of_closedUnder {α : Ordinal.{u}} {k : ℕ} (φ : SetFormula (k + 1))
    (h_cl : ClosedUnder (V_ α) (Skolems (SetFormula.all φ)))
    (ih : ClosedUnder (V_ α) (Skolems φ) → Reflects α φ) :
    Reflects α (SetFormula.all φ) := by
  have refl_φ : Reflects α φ := ih h_cl.tail
  intro x hx
  rw [SetFormula.realizeIn, SetFormula.realize]
  refine ⟨fun hM => ?_, fun hR a ha => (refl_φ.snoc_iff hx ha).mpr (hR a)⟩
  by_contra hneg
  push Not at hneg
  have hW : φ.not.exWitness x ∈ V_ α := h_cl _ List.mem_cons_self x hx
  exact SetFormula.realize_snoc_exWitness (φ := φ.not) hneg
    ((refl_φ.snoc_iff hx hW).mp (hM _ hW))

/-- The key reflection criterion: if `V_ α` is closed under the Skolem functions of `ψ`,
then `V_ α` reflects `ψ`. The proof is an induction on `ψ`, the quantifier cases using
closure to produce a witness inside `V_ α`. -/
lemma reflects_of_closedUnder {α : Ordinal.{u}} {k : ℕ} (ψ : SetFormula k)
    (h_cl : ClosedUnder (V_ α) (Skolems ψ)) :
    Reflects α ψ := by
  induction ψ with
  | mem _ _ => exact fun _ _ => Iff.rfl
  | eq _ _ => exact fun _ _ => Iff.rfl
  | not φ ih => exact fun x hx => not_congr (ih h_cl x hx)
  | and φ ψ ihφ ihψ =>
    exact fun x hx => and_congr (ihφ h_cl.of_append_left x hx) (ihψ h_cl.of_append_right x hx)
  | or φ ψ ihφ ihψ =>
    exact fun x hx => or_congr (ihφ h_cl.of_append_left x hx) (ihψ h_cl.of_append_right x hx)
  | imp φ ψ ihφ ihψ =>
    exact fun x hx => imp_congr (ihφ h_cl.of_append_left x hx) (ihψ h_cl.of_append_right x hx)
  | iff φ ψ ihφ ihψ =>
    exact fun x hx => iff_congr (ihφ h_cl.of_append_left x hx) (ihψ h_cl.of_append_right x hx)
  | all φ ih => exact reflects_all_of_closedUnder φ h_cl ih
  | ex φ ih => exact reflects_ex_of_closedUnder φ h_cl ih

/-! ## Closure ordinals -/

private lemma exists_skolem_step (s : SkolemFn.{u}) (γ : Ordinal.{u}) :
    ∃ δ : Ordinal.{u}, ∀ x : Fin s.arity → ZFSet.{u},
      (∀ j, x j ∈ V_ γ) → s.toFun x ∈ V_ δ := by
  have : Small.{u} ↥(V_ γ) := small_coe _
  let e : Shrink.{u} (Fin s.arity → ↥(V_ γ)) ≃ (Fin s.arity → ↥(V_ γ)) := (equivShrink _).symm
  let f : Shrink.{u} (Fin s.arity → ↥(V_ γ)) → Ordinal.{u} :=
    fun i => succ (rank (s.toFun fun j => (e i j).val))
  refine ⟨⨆ i, f i, fun x hx =>
    vonNeumann_subset_of_le ?_ (mem_vonNeumann_succ (s.toFun x))⟩
  let ix : Fin s.arity → ↥(V_ γ) := fun j => ⟨x j, hx j⟩
  have hf : f (e.symm ix) = succ (rank (s.toFun x)) := by
    simp only [f]
    rw [e.apply_symm_apply]
  exact hf ▸ le_ciSup (f := f) (Ordinal.bddAbove_of_small (s := Set.range f)) _

private lemma exists_closure_step (L : List SkolemFn.{u}) (γ : Ordinal.{u}) :
    ∃ δ : Ordinal.{u}, γ < δ ∧ ∀ s ∈ L, ∀ x : Fin s.arity → ZFSet.{u},
      (∀ j, x j ∈ V_ γ) → s.toFun x ∈ V_ δ := by
  induction L with
  | nil => exact ⟨γ + 1, lt_succ γ, fun s hs => (List.not_mem_nil hs).elim⟩
  | cons s rest ih =>
    obtain ⟨δ₁, hδ₁⟩ := exists_skolem_step s γ
    obtain ⟨δ₂, -, hδ₂⟩ := ih
    refine ⟨max (max δ₁ δ₂) (γ + 1),
      lt_of_lt_of_le (lt_succ γ) (le_max_right _ _), fun t ht x hx => ?_⟩
    rcases List.mem_cons.mp ht with rfl | h_in
    · exact vonNeumann_subset_of_le ((le_max_left δ₁ δ₂).trans (le_max_left _ _)) (hδ₁ x hx)
    · exact vonNeumann_subset_of_le ((le_max_right δ₁ δ₂).trans (le_max_left _ _))
        (hδ₂ t h_in x hx)

private lemma isSuccLimit_iSup_of_strictMono_nat (s : ℕ → Ordinal.{u})
    (hs : StrictMono s) : IsSuccLimit (⨆ n : ℕ, s n) := by
  refine ⟨?_, ?_⟩
  · exact fun hmin => absurd (hmin bot_le) (not_le_of_gt
      ((lt_of_le_of_lt bot_le (hs Nat.zero_lt_one)).trans_le (Ordinal.le_iSup s 1)))
  rw [isSuccPrelimit_iff_succ_ne]
  intro γ h
  have hle : ∀ n, s n ≤ γ := fun n => lt_succ_iff.mp
    (((hs n.lt_succ_self).trans_le (Ordinal.le_iSup s (n + 1))).trans_eq h.symm)
  exact absurd (h ▸ Ordinal.iSup_le hle) (not_le.mpr (lt_succ γ))

private lemma exists_succLimit_closure_step (L : List SkolemFn.{u}) (β : Ordinal.{u}) :
    ∃ α : Ordinal.{u}, β ≤ α ∧ IsSuccLimit α ∧
      ∀ γ < α, ∃ δ < α, ∀ s ∈ L, ∀ x : Fin s.arity → ZFSet.{u},
        (∀ j, x j ∈ V_ γ) → s.toFun x ∈ V_ δ := by
  choose step hstep_lt hstep using fun γ => exists_closure_step L γ
  let seq : ℕ → Ordinal.{u} := fun n => Nat.rec β (fun _ prev => step prev) n
  have hlt : ∀ n, seq n < seq (n + 1) := fun n => hstep_lt (seq n)
  refine ⟨⨆ n : ℕ, seq n, Ordinal.le_iSup seq 0,
    isSuccLimit_iSup_of_strictMono_nat seq (strictMono_nat_of_lt_succ hlt), fun γ hγ => ?_⟩
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hγ
  exact ⟨seq (n + 1), (hlt (n + 1)).trans_le (Ordinal.le_iSup seq (n + 2)),
    fun s hs x hxγ => hstep (seq n) s hs x fun j => vonNeumann_subset_of_le hn.le (hxγ j)⟩

private lemma empty_mem_vonNeumann_of_isSuccLimit {α : Ordinal.{u}}
    (hα : IsSuccLimit α) : (∅ : ZFSet.{u}) ∈ V_ α := by
  rw [mem_vonNeumann, rank_empty]
  exact hα.bot_lt

private lemma exists_common_lt_isSuccLimit {α : Ordinal.{u}} (hα : IsSuccLimit α) {k : ℕ}
    (x : Fin k → ZFSet.{u}) (hx : ∀ j, x j ∈ V_ α) :
    ∃ γ : Ordinal.{u}, γ < α ∧ ∀ j, x j ∈ V_ γ := by
  -- For each `j`, `x j ∈ V_ α` gives `rank (x j) < α`; since `α` is a limit,
  -- `succ (rank (x j)) < α` and `x j ∈ V_ (succ (rank (x j)))`. Take the max.
  have hj : ∀ j, ∃ β : Ordinal.{u}, β < α ∧ x j ∈ V_ β := fun j =>
    ⟨succ (rank (x j)), hα.succ_lt (mem_vonNeumann.mp (hx j)), mem_vonNeumann_succ (x j)⟩
  choose γ_fn hγ_lt hγ_mem using hj
  exact ⟨Finset.univ.sup γ_fn, (Finset.sup_lt_iff hα.bot_lt).mpr fun j _ => hγ_lt j, fun j =>
    vonNeumann_subset_of_le (Finset.le_sup (Finset.mem_univ j)) (hγ_mem j)⟩

/-- Above any ordinal `β` there is a successor limit ordinal `α` with `∅ ∈ V_ α` and with
`V_ α` closed under a given finite list of Skolem functions. -/
lemma exists_closure_ordinal (β : Ordinal.{u}) (L : List SkolemFn.{u}) :
    ∃ α : Ordinal.{u}, β ≤ α ∧ IsSuccLimit α ∧ (∅ : ZFSet.{u}) ∈ V_ α ∧
      ClosedUnder (V_ α) L := by
  obtain ⟨α, hβα, hSL, hclose⟩ := exists_succLimit_closure_step L β
  refine ⟨α, hβα, hSL, empty_mem_vonNeumann_of_isSuccLimit hSL, fun s hs x hx => ?_⟩
  obtain ⟨γ, hγα, hxγ⟩ := exists_common_lt_isSuccLimit hSL x hx
  obtain ⟨δ, hδα, hclose_δ⟩ := hclose γ hγα
  exact vonNeumann_subset_of_le hδα.le (hclose_δ s hs x hxγ)

/-- Simultaneous reflection: for any finite family `φ` of formulas in `n` free variables
and any ordinal `β`, some successor limit ordinal `α ≥ β` reflects every `φ i`. -/
lemma exists_reflects_family (n m : ℕ) (φ : Fin m → SetFormula n) (β : Ordinal.{u}) :
    ∃ α : Ordinal.{u}, β ≤ α ∧ IsSuccLimit α ∧ ∀ i : Fin m, Reflects α (φ i) := by
  obtain ⟨α, hβα, hlim, _, hcl⟩ :=
    exists_closure_ordinal β ((List.finRange m).flatMap fun i => Skolems (φ i))
  exact ⟨α, hβα, hlim, fun i => reflects_of_closedUnder (φ i)
    (closedUnder_of_subset (fun s hs => List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hs⟩) hcl)⟩

/-- **Reflection principle, formula by formula.** Given a finite family of set-theory
formulas `φᵢ` with `n` free variables and any set `M₀`, there is a limit
ordinal `α` such that `M₀ ⊆ V_α` and for every parameter tuple in `V_α` and
every `i`, the relativization `φᵢ^{V_α}` agrees with `φᵢ` on the full universe.
Here `V_ α = ZFSet.vonNeumann α` is the von Neumann hierarchy from Mathlib. -/
@[stacks 000G "each formula separately, with `M = V_α`"]
theorem reflection_principle
    (n m : ℕ) (φ : Fin m → SetFormula n) (M₀ : ZFSet.{u}) :
    ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧ M₀ ⊆ V_ α ∧
      ∀ (x : Fin n → ZFSet),
        (∀ j, x j ∈ V_ α) →
        ∀ i : Fin m,
          (φ i).realizeIn (V_ α) x ↔ (φ i).realize x := by
  obtain ⟨β, hβ⟩ := exists_subset_vonNeumann M₀
  obtain ⟨α, hαβ, hLim, hRefl⟩ := exists_reflects_family n m φ β
  exact ⟨α, hLim, hβ.trans (vonNeumann_subset_of_le hαβ), fun x hx i => hRefl i x hx⟩

/-- **Stacks 000G — Reflection principle.** Given a finite family `φ₁, …, φₘ` of formulas of
set theory in the free variables `x₁, …, xₙ` and a set `M₀`, there is a set `M` with
`M₀ ⊆ M` such that for all `x₁, …, xₙ ∈ M`, the conjunction of the relativizations `φᵢ^M`
holds if and only if the conjunction of the `φᵢ` holds in the universe of sets; moreover
`M = V_α` for a limit ordinal `α`. -/
@[stacks 000G]
theorem exists_superset_forall_realizeIn_iff_forall_realize
    (n m : ℕ) (φ : Fin m → SetFormula n) (M₀ : ZFSet.{u}) :
    ∃ M : ZFSet.{u}, M₀ ⊆ M ∧
      (∀ x : Fin n → ZFSet.{u}, (∀ j, x j ∈ M) →
        ((∀ i : Fin m, (φ i).realizeIn M x) ↔ ∀ i : Fin m, (φ i).realize x)) ∧
      ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧ M = V_ α := by
  obtain ⟨α, hLim, hM₀, hRefl⟩ := reflection_principle n m φ M₀
  exact ⟨V_ α, hM₀, fun x hx => forall_congr' fun i => hRefl x hx i, α, hLim, rfl⟩
