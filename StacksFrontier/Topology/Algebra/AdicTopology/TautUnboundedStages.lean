module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Cardinal.Finsupp
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientDirectedLimit

/-!
# A taut homomorphism whose stages are unbounded

Given a nonempty linear order `ι` and a family of types `V γ`, this file builds a taut
continuous homomorphism `φ : A →+* C` of weakly admissible topological rings, with a family
`I γ` of weak ideals of definition of `A` cofinal among its open ideals, such that the stage
`C ⧸ closure (I γ • C)` contains a copy of `V γ` and is bounded by the stage of `A` together
with the modules at the indices up to `γ` only. It is the algebraic input of the refutation, over
a site with singular cutoff, of the implication (3) ⟹ (2) of Stacks 0AN5
(`StacksFrontier.AlgebraicGeometry.FormalSpace.TautNotRepresentable`).

## Implementation notes

* The source. `A` is the inverse limit of the rings
  `Stage γ = 𝔽₂[X (α, i) : α ∈ ι, i ∈ ℕ] ⧸ (X (α, i) for γ < α, X (α, i) ^ 2)`, whose transition
  maps have nil kernels; `TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family`
  makes it weakly admissible with surjective projections `π γ : A → Stage γ` whose kernels
  `I γ` form a fundamental system of weak ideals of definition.
* The modules. `Fiber T` is the `𝔽₂`-vector space on `Finset ℕ × T`, and `X (α, i)` acts on
  the copy at the index `α` by contraction by `i` and on the other copies by zero. The
  contractions commute and square to zero, so `A` acts on the copy at `α` through `Stage α`.
* The target. `C` is the completion over `A`
  (`TopologicalRing.CompletionOver`, Stacks 0AN6) of the square-zero extension of `A` by
  `⨁ α, Fiber (V α)`, so `C` is weakly admissible and `A → C` is taut
  (`TopologicalRing.isTaut_canonicalMap`), and the stage of `C` at `γ` is the stage of the
  extension at `I γ`.

## Main results

* `TopologicalRing.TautUnboundedStages.card_fib_le_card_quotient`: the copy at `γ` survives in
  the stage at `γ`, because `I γ` acts on it by zero.
* `TopologicalRing.TautUnboundedStages.inr_single_mem_extIdeal`: a copy at an index `α > γ` dies
  in the stage at `γ`. Each basis vector `e S ⊗ t` is `X (α, i) • e (S ∪ {i}) ⊗ t` for any
  `i ∉ S`, and `X (α, i)` lies in `I γ`; so the copy at `α` is divisible by `I γ`, however
  small the stage of `A` at `γ` is.
* `TopologicalRing.TautUnboundedStages.card_quotient_le`: hence the stage at `γ` is no larger than
  `Stage γ` times the modules at the indices up to `γ`.
* `TopologicalRing.TautUnboundedStages.exists_isTaut_card_stage`: there is a continuous taut
  homomorphism of weakly admissible rings whose stage at `γ` contains a copy of `V γ` and is no
  larger than `Stage γ` together with the modules at the indices up to `γ`.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
-/

@[expose] public noncomputable section

open Cardinal MvPolynomial

namespace TopologicalRing.TautUnboundedStages

universe u

/-! ### The stages of the source -/

section Stages

variable (ι : Type u) [LinearOrder ι]

/-- The polynomial ring over `𝔽₂` on generators `X (α, i)`, `α : ι`, `i : ℕ`. -/
abbrev Gens : Type u := MvPolynomial (ι × ℕ) (ZMod 2)

/-- The ideal of the stage `γ`: it kills the generators `X (α, i)` with `γ < α` and the squares
of all generators. -/
def stageIdeal (γ : ι) : Ideal (Gens ι) :=
  Ideal.span ({x | ∃ g : ι × ℕ, γ < g.1 ∧ x = X g} ∪ Set.range fun g : ι × ℕ => X g ^ 2)

/-- The ideals `stageIdeal ι γ` are antitone in `γ`. -/
theorem stageIdeal_antitone {β γ : ι} (h : β ≤ γ) : stageIdeal ι γ ≤ stageIdeal ι β :=
  Ideal.span_mono (Set.union_subset_union (fun _ ⟨g, hg, hx⟩ => ⟨g, h.trans_lt hg, hx⟩) le_rfl)

/-- A generator `X g` with `γ < g.1` lies in the ideal of the stage `γ`. -/
theorem X_mem_stageIdeal {γ : ι} {g : ι × ℕ} (h : γ < g.1) : X g ∈ stageIdeal ι γ :=
  Ideal.subset_span (Or.inl ⟨g, h, rfl⟩)

/-- The square of every generator lies in the ideal of every stage. -/
theorem X_sq_mem_stageIdeal (γ : ι) (g : ι × ℕ) : X g ^ 2 ∈ stageIdeal ι γ :=
  Ideal.subset_span (Or.inr ⟨g, rfl⟩)

/-- The ring of the stage `γ`. -/
abbrev Stage (γ : ι) : Type u := Gens ι ⧸ stageIdeal ι γ

/-- The transition map between two stages. -/
def stageMap {β γ : ι} (h : β ≤ γ) : Stage ι γ →+* Stage ι β :=
  Ideal.Quotient.factor (stageIdeal_antitone ι h)

/-- The transition map sends the class of a polynomial to its class. -/
theorem stageMap_mk {β γ : ι} (h : β ≤ γ) (x : Gens ι) :
    stageMap ι h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
  Ideal.Quotient.factor_mk _ x

/-- The ideal of any stage is contained in the radical of the ideal of any other stage. -/
theorem stageIdeal_le_radical {β γ : ι} : stageIdeal ι β ≤ (stageIdeal ι γ).radical := by
  refine Ideal.span_le.2 ?_
  rintro x (⟨g, -, rfl⟩ | ⟨g, rfl⟩)
  · exact ⟨2, X_sq_mem_stageIdeal ι γ g⟩
  · exact Ideal.le_radical (X_sq_mem_stageIdeal ι γ g)

/-- The kernel of each transition map is locally nilpotent. -/
theorem ker_stageMap_locallyNilpotent {β γ : ι} (h : β ≤ γ) :
    (RingHom.ker (stageMap ι h)).LocallyNilpotent := by
  intro y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, stageMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  obtain ⟨n, hn⟩ := stageIdeal_le_radical ι (γ := γ) hy
  exact ⟨n, by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem]⟩

/-- Each stage has cardinality at most `max #ι ℵ₀`. -/
theorem card_stage_le (γ : ι) : #(Stage ι γ) ≤ max #ι ℵ₀ := by
  calc #(Stage ι γ) ≤ #(Gens ι) :=
        Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := stageIdeal ι γ))
    _ ≤ lift.{u} #(ZMod 2) ⊔ lift.{0} #(ι × ℕ) ⊔ ℵ₀ := MvPolynomial.cardinalMk_le_max_lift
    _ ≤ max #ι ℵ₀ := by
      refine max_le (max_le ?_ ?_) (le_max_right _ _)
      · exact (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0).trans (le_max_right _ _)
      · rw [Cardinal.lift_uzero, Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat,
          Cardinal.lift_aleph0]
        exact (Cardinal.mul_le_max _ _).trans (by simp)

end Stages

/-! ### The modules carried by the target -/

section Fiber

/-- The `𝔽₂`-vector space on the pairs of a finite set of natural numbers and an element of
`T`. -/
abbrev Fiber (T : Type u) : Type u := (Finset ℕ × T) →₀ ZMod 2

variable (T : Type u)

/-- The basis vector of `Fiber T` at a pair. -/
def basisVec (p : Finset ℕ × T) : Fiber T := Finsupp.single p 1

/-- Contraction by `i`: the basis vector at `(S, t)` goes to the one at `(S \ {i}, t)` when
`i ∈ S`, and to zero otherwise. -/
def contract (i : ℕ) : Module.End (ZMod 2) (Fiber T) :=
  Finsupp.linearCombination (ZMod 2) fun p : Finset ℕ × T =>
    if i ∈ p.1 then basisVec T (p.1.erase i, p.2) else 0

/-- Contraction by `i` on a basis vector. -/
theorem contract_basisVec (i : ℕ) (p : Finset ℕ × T) :
    contract T i (basisVec T p) = if i ∈ p.1 then basisVec T (p.1.erase i, p.2) else 0 := by
  rw [contract, basisVec, Finsupp.linearCombination_single, one_smul]

/-- Contraction by `i` on a scalar multiple of a basis vector. -/
theorem contract_single (i : ℕ) (q : Finset ℕ × T) (c : ZMod 2) :
    contract T i (Finsupp.single q c) =
      if i ∈ q.1 then Finsupp.single (q.1.erase i, q.2) c else 0 := by
  rw [contract, Finsupp.linearCombination_single]
  split_ifs <;> simp [basisVec]

/-- Two endomorphisms of `Fiber T` agreeing on every basis vector are equal. -/
theorem fiber_ext {f g : Module.End (ZMod 2) (Fiber T)}
    (h : ∀ p, f (basisVec T p) = g (basisVec T p)) : f = g :=
  Finsupp.lhom_ext' fun p => LinearMap.ext_ring (h p)

/-- Contractions commute. -/
theorem contract_comm (i j : ℕ) : contract T i * contract T j = contract T j * contract T i := by
  refine fiber_ext T fun p => ?_
  simp only [Module.End.mul_apply, contract_basisVec]
  by_cases hij : i = j
  · subst hij
    rfl
  by_cases hi : i ∈ p.1 <;> by_cases hj : j ∈ p.1 <;>
    simp [hi, hj, contract_basisVec, Finset.mem_erase, hij, Ne.symm hij, Finset.erase_right_comm]

/-- Each contraction squares to zero. -/
theorem contract_mul_self (i : ℕ) : contract T i * contract T i = 0 := by
  refine fiber_ext T fun p => ?_
  simp only [Module.End.mul_apply, contract_basisVec]
  by_cases hi : i ∈ p.1 <;> simp [hi, contract_basisVec]

/-- For `i ∉ S`, the basis vector at `(S, t)` is the contraction by `i` of the one at
`(insert i S, t)`. -/
theorem basisVec_eq_contract {i : ℕ} (p : Finset ℕ × T) (hi : i ∉ p.1) :
    basisVec T p = contract T i (basisVec T (insert i p.1, p.2)) := by
  rw [contract_basisVec, ite_eq_left (Finset.mem_insert_self i p.1), Finset.erase_insert hi]

/-- The map `t ↦ basisVec T (∅, t)` is injective. -/
theorem basisVec_injective : Function.Injective fun t : T => basisVec T (∅, t) := by
  intro t t' h
  have := Finsupp.single_left_injective (one_ne_zero (α := ZMod 2)) h
  exact (Prod.mk.inj this).2

/-- `Fiber T` has cardinality at most `max #T ℵ₀`. -/
theorem card_fiber_le : #(Fiber T) ≤ max #T ℵ₀ := by
  classical
  calc #(Fiber T) ≤ #(Finset ((Finset ℕ × T) × ZMod 2)) :=
        Cardinal.mk_le_of_injective (Finsupp.graph_injective (Finset ℕ × T) (ZMod 2))
    _ ≤ #(List ((Finset ℕ × T) × ZMod 2)) :=
        Cardinal.mk_le_of_surjective List.toFinset_surjective
    _ ≤ max ℵ₀ #((Finset ℕ × T) × ZMod 2) := Cardinal.mk_list_le_max _
    _ ≤ max #T ℵ₀ := by
      refine max_le (le_max_right _ _) ?_
      have h1 : #(Finset ℕ) ≤ ℵ₀ := Cardinal.mk_le_aleph0
      have h2 : #(ZMod 2) ≤ ℵ₀ := Cardinal.mk_le_aleph0
      rw [Cardinal.mk_prod, Cardinal.mk_prod]
      simp only [Cardinal.lift_uzero]
      refine (Cardinal.mul_le_max _ _).trans (max_le (max_le ?_ ?_) (le_max_right _ _))
      · refine (Cardinal.mul_le_max _ _).trans (max_le (max_le ?_ (le_max_left _ _))
          (le_max_right _ _))
        exact (Cardinal.lift_le_aleph0.2 h1).trans (le_max_right _ _)
      · exact (Cardinal.lift_le_aleph0.2 h2).trans (le_max_right _ _)

end Fiber

/-! ### The action of the stages on the modules -/

section Action

variable {ι : Type u} [LinearOrder ι] (T : Type u)

/-- The action of the generator `X g` on the module at the index `α`: contraction by `g.2` when
`g.1 = α`, and zero otherwise. -/
def genAction (α : ι) (g : ι × ℕ) : Module.End (ZMod 2) (Fiber T) :=
  if g.1 = α then contract T g.2 else 0

/-- The actions of the generators on the module at the index `α` commute. -/
theorem genAction_comm (α : ι) (g h : ι × ℕ) :
    genAction T α g * genAction T α h = genAction T α h * genAction T α g := by
  unfold genAction
  split_ifs <;> simp [contract_comm]

/-- The action of each generator squares to zero. -/
theorem genAction_mul_self (α : ι) (g : ι × ℕ) : genAction T α g * genAction T α g = 0 := by
  unfold genAction
  split_ifs <;> simp [contract_mul_self]

/-- The subalgebra of endomorphisms generated by the actions of the generators. -/
abbrev actionAlg (α : ι) : Subalgebra (ZMod 2) (Module.End (ZMod 2) (Fiber T)) :=
  Algebra.adjoin (ZMod 2) (Set.range (genAction T α))

/-- The subalgebra `actionAlg T α` is commutative. -/
instance (α : ι) : IsMulCommutative (actionAlg T α) :=
  Algebra.isMulCommutative_adjoin (ZMod 2) (by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ -
    exact genAction_comm T α g h)

open scoped IsMulCommutative in
/-- The action of the polynomial ring on the module at the index `α`. -/
def actionHom (α : ι) : Gens ι →+* Module.End (ZMod 2) (Fiber T) :=
  (actionAlg T α).val.toRingHom.comp
    (MvPolynomial.aeval fun g =>
      (⟨genAction T α g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ : actionAlg T α)).toRingHom

/-- The generator `X g` acts on the module at the index `α` by `genAction T α g`. -/
theorem actionHom_X (α : ι) (g : ι × ℕ) : actionHom T α (X g) = genAction T α g := by
  simp [actionHom]

/-- The ideal of the stage `α` acts by zero on the module at the index `α`. -/
theorem stageIdeal_le_ker_actionHom (α : ι) : stageIdeal ι α ≤ RingHom.ker (actionHom T α) := by
  refine Ideal.span_le.2 ?_
  rintro x (⟨g, hg, rfl⟩ | ⟨g, rfl⟩)
  · change actionHom T α (X g) = 0
    rw [actionHom_X, genAction, ite_eq_right (ne_of_gt hg)]
  · change actionHom T α (X g ^ 2) = 0
    rw [map_pow, actionHom_X, pow_two, genAction_mul_self]

/-- The action of the stage `α` on the module at the index `α`. -/
def stageAction (α : ι) : Stage ι α →+* Module.End (ZMod 2) (Fiber T) :=
  Ideal.Quotient.lift _ (actionHom T α) fun _ hx => stageIdeal_le_ker_actionHom T α hx

/-- The class of a polynomial acts as the polynomial does. -/
theorem stageAction_mk (α : ι) (x : Gens ι) :
    stageAction T α (Ideal.Quotient.mk _ x) = actionHom T α x :=
  Ideal.Quotient.lift_mk _ _ _

end Action

/-! ### The target ring -/

section Target

variable {ι : Type u} [LinearOrder ι] (V : ι → Type u) {A : Type u} [CommRing A]
  (π : ∀ γ : ι, A →+* Stage ι γ)

/-- The action of `A` on the module at the index `α`, through its stage `α`. -/
def fiberAction (α : ι) : A →+* Module.End (ZMod 2) (Fiber (V α)) :=
  (stageAction (V α) α).comp (π α)

/-- The module at the index `α`, with `A` acting through its stage `α`. -/
def Fib (_π : ∀ γ : ι, A →+* Stage ι γ) (α : ι) : Type u := Fiber (V α)

/-- The additive group structure of `Fib V π α` is that of `Fiber (V α)`. -/
instance (α : ι) : AddCommGroup (Fib V π α) := inferInstanceAs (AddCommGroup (Fiber (V α)))

/-- `A` acts on `Fib V π α` through `fiberAction V π α`. -/
instance (α : ι) : Module A (Fib V π α) :=
  Module.compHom (Fiber (V α)) (fiberAction V π α)

/-- The scalar multiplication of `A` on `Fib V π α` is the action `fiberAction V π α`. -/
theorem fib_smul_def (α : ι) (a : A) (d : Fib V π α) :
    a • d = (fiberAction V π α a : Module.End (ZMod 2) (Fiber (V α))) d := rfl

/-- The module of the target: the direct sum of the modules at all indices. -/
abbrev Mod : Type u := Π₀ α : ι, Fib V π α

/-- The right action of `A` on `Mod V π`, equal to the left action. -/
instance : Module Aᵐᵒᵖ (Mod V π) :=
  Module.compHom _ (RingHom.fromOpposite (RingHom.id A) fun _ _ => Commute.all _ _)

/-- The left and right actions of `A` on `Mod V π` agree. -/
instance : IsCentralScalar A (Mod V π) := ⟨fun _ _ => rfl⟩

/-- The square-zero extension of `A` by that module. -/
abbrev Ext : Type u := TrivSqZeroExt A (Mod V π)

/-- The structure map of the square-zero extension. -/
abbrev extMap : A →+* Ext V π := TrivSqZeroExt.inlHom A (Mod V π)

/-- The ideal of the target ring extended from the kernel of the stage `γ`. -/
abbrev extIdeal (γ : ι) : Ideal (Ext V π) := (RingHom.ker (π γ)).map (extMap V π)

variable {V π}

/-- The kernel of the stage `α` acts by zero on the module at the index `α`. -/
theorem fiberAction_eq_zero_of_mem_ker {α : ι} {a : A} (ha : a ∈ RingHom.ker (π α)) :
    fiberAction V π α a = 0 := by
  rw [fiberAction, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]

/-- An element of the kernel of the stage `α` annihilates `Fib V π α`. -/
theorem smul_eq_zero_of_mem_ker {α : ι} {a : A} (ha : a ∈ RingHom.ker (π α)) (d : Fib V π α) :
    a • d = 0 := by
  rw [fib_smul_def, fiberAction_eq_zero_of_mem_ker ha]
  rfl

/-- The elements of the ideal extended from the kernel of the stage `γ` have zero component at
`γ`. -/
theorem snd_apply_eq_zero_of_mem_extIdeal {γ : ι} {z : Ext V π} (hz : z ∈ extIdeal V π γ) :
    (z.snd : Π₀ α : ι, Fib V π α) γ = 0 := by
  suffices h : z.fst ∈ RingHom.ker (π γ) ∧ (z.snd : Π₀ α : ι, Fib V π α) γ = 0 from h.2
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg, rfl⟩
  · exact ⟨zero_mem _, rfl⟩
  · intro x y _ _ hx hy
    refine ⟨add_mem hx.1 hy.1, ?_⟩
    change (x.snd + y.snd : Π₀ α : ι, Fib V π α) γ = 0
    rw [DFinsupp.add_apply, hx.2, hy.2, add_zero]
  · intro r x _ hx
    refine ⟨?_, ?_⟩
    · change (r * x).fst ∈ _
      rw [TrivSqZeroExt.fst_mul]
      exact Ideal.mul_mem_left _ _ hx.1
    · change ((r * x).snd : Π₀ α : ι, Fib V π α) γ = 0
      rw [TrivSqZeroExt.snd_mul]
      change (r.fst • x.snd + x.fst • r.snd : Π₀ α : ι, Fib V π α) γ = 0
      rw [DFinsupp.add_apply, DFinsupp.smul_apply, DFinsupp.smul_apply, hx.2, smul_zero,
        smul_eq_zero_of_mem_ker hx.1, zero_add]

/-- **The module at the index `γ` survives in the stage `γ` of the target.** -/
theorem card_fib_le_card_quotient (γ : ι) :
    #(Fib V π γ) ≤ #(Ext V π ⧸ extIdeal V π γ) := by
  classical
  refine Cardinal.mk_le_of_injective (f := fun d : Fib V π γ =>
    Ideal.Quotient.mk (extIdeal V π γ)
      (TrivSqZeroExt.inr (DFinsupp.single γ d : Π₀ α : ι, Fib V π α))) ?_
  intro d d' h
  have hmem := Ideal.Quotient.eq.mp h
  rw [← TrivSqZeroExt.inr_sub, ← DFinsupp.single_sub] at hmem
  have := snd_apply_eq_zero_of_mem_extIdeal hmem
  rw [TrivSqZeroExt.snd_inr, DFinsupp.single_eq_same] at this
  exact sub_eq_zero.mp this

variable (hπ : ∀ γ, Function.Surjective (π γ))
  (hcomp : ∀ ⦃β γ : ι⦄ (h : β ≤ γ) (a : A), stageMap ι h (π γ a) = π β a)
include hπ hcomp

/-- Above the stage `γ`, every contraction is the action of an element of the kernel of the
stage `γ`. -/
theorem exists_mem_ker_fiberAction_eq_contract {γ α : ι} (hγα : γ < α) (i : ℕ) :
    ∃ g ∈ RingHom.ker (π γ), fiberAction V π α g = contract (V α) i := by
  obtain ⟨g, hg⟩ := hπ α (Ideal.Quotient.mk _ (X (α, i)))
  refine ⟨g, ?_, ?_⟩
  · rw [RingHom.mem_ker, ← hcomp hγα.le, hg, stageMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact X_mem_stageIdeal ι hγα
  · rw [fiberAction, RingHom.comp_apply, hg, stageAction_mk, actionHom_X, genAction,
      ite_eq_left rfl]

/-- **Above the stage `γ` the modules die in the stage `γ` of the target.** -/
theorem inr_single_mem_extIdeal {γ α : ι} (hγα : γ < α) (d : Fib V π α) :
    TrivSqZeroExt.inr (DFinsupp.single α d : Π₀ β : ι, Fib V π β) ∈ extIdeal V π γ := by
  let φ : Fib V π α →+ Ext V π :=
    (TrivSqZeroExt.inrHom A (Mod V π)).toAddMonoidHom.comp (DFinsupp.singleAddHom (Fib V π) α)
  let N : AddSubgroup (Fib V π α) := (extIdeal V π γ).toAddSubgroup.comap φ
  change d ∈ N
  induction d using Finsupp.induction_linear with
  | zero => exact N.zero_mem
  | add d d' hd hd' => exact N.add_mem hd hd'
  | single q c =>
    obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset q.1
    obtain ⟨g, hg, hgc⟩ := exists_mem_ker_fiberAction_eq_contract hπ hcomp hγα i
    have hd : (Finsupp.single q c : Fiber (V α)) =
        g • (show Fib V π α from Finsupp.single (insert i q.1, q.2) c) := by
      rw [fib_smul_def, hgc, contract_single, ite_eq_left (Finset.mem_insert_self i q.1),
        Finset.erase_insert hi]
    change φ (Finsupp.single q c) ∈ extIdeal V π γ
    rw [hd]
    change TrivSqZeroExt.inr (DFinsupp.single α
      (g • (show Fib V π α from Finsupp.single (insert i q.1, q.2) c)) : Mod V π) ∈
        extIdeal V π γ
    rw [DFinsupp.single_smul, ← TrivSqZeroExt.inl_mul_inr]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hg)

/-- A vector of the module of the target supported above the stage `γ` dies in the stage `γ`. -/
theorem inr_mem_extIdeal_of_eq_zero {γ : ι} (m : Mod V π) (hm : ∀ α, α ≤ γ → m α = 0) :
    TrivSqZeroExt.inr m ∈ extIdeal V π γ := by
  induction m using DFinsupp.induction with
  | h0 =>
    rw [TrivSqZeroExt.inr_zero]
    exact zero_mem _
  | ha i b f hf hb ih =>
    have hi : γ < i := by
      by_contra hle
      have := hm i (not_lt.mp hle)
      rw [DFinsupp.add_apply, DFinsupp.single_eq_same, hf, add_zero] at this
      exact hb this
    rw [TrivSqZeroExt.inr_add]
    refine add_mem (inr_single_mem_extIdeal hπ hcomp hi b) (ih fun α hα => ?_)
    have := hm α hα
    rwa [DFinsupp.add_apply, DFinsupp.single_eq_of_ne (ne_of_lt (hα.trans_lt hi)),
      zero_add] at this

/-- **The stage `γ` of the target is no larger than the stage `γ` of the source together with
the modules at the indices up to `γ`.** -/
theorem card_quotient_le (γ : ι) :
    #(Ext V π ⧸ extIdeal V π γ) ≤
      #(Stage ι γ) * #(Π₀ α : {α : ι // α ≤ γ}, Fib V π α) := by
  classical
  let Sm := {m : Mod V π // ∀ α, ¬ α ≤ γ → m α = 0}
  have hsec : ∀ y : Stage ι γ, π γ (Function.surjInv (hπ γ) y) = y :=
    Function.surjInv_eq (hπ γ)
  let F : Stage ι γ × Sm → Ext V π ⧸ extIdeal V π γ := fun x =>
    Ideal.Quotient.mk _ (TrivSqZeroExt.inl (Function.surjInv (hπ γ) x.1) +
      TrivSqZeroExt.inr x.2.1)
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨(π γ r.fst, ⟨r.snd.filter (· ≤ γ), fun α hα => DFinsupp.filter_apply_neg _ hα⟩),
      ?_⟩
    refine Ideal.Quotient.eq.mpr ?_
    have hfst : TrivSqZeroExt.inl (Function.surjInv (hπ γ) (π γ r.fst) - r.fst) ∈
        extIdeal V π γ := by
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, map_sub, hsec, sub_self]
    have hsnd : TrivSqZeroExt.inr (-(r.snd.filter fun α => ¬ α ≤ γ)) ∈
        extIdeal V π γ := by
      refine inr_mem_extIdeal_of_eq_zero hπ hcomp _ fun α hα => ?_
      rw [DFinsupp.neg_apply, DFinsupp.filter_apply_neg (p := fun α => ¬ α ≤ γ) _
        (not_not.mpr hα), neg_zero]
    convert add_mem hfst hsnd using 1
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero]
    · simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      refine eq_neg_of_add_eq_zero_left ?_
      rw [sub_add_eq_add_sub, DFinsupp.filter_add_filter_not, sub_self]
  have hinj : Function.Injective fun m : Sm =>
      (m.1.subtypeDomain (· ≤ γ) : Π₀ α : {α : ι // α ≤ γ}, Fib V π α) := by
    intro m m' h
    refine Subtype.ext (DFinsupp.ext fun α => ?_)
    by_cases hα : α ≤ γ
    · exact DFunLike.congr_fun h ⟨α, hα⟩
    · rw [m.2 α hα, m'.2 α hα]
  calc #(Ext V π ⧸ extIdeal V π γ) ≤ #(Stage ι γ × Sm) := Cardinal.mk_le_of_surjective hF
    _ = #(Stage ι γ) * #Sm := by rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    _ ≤ _ := by
      gcongr
      exact Cardinal.mk_le_of_injective hinj

end Target

/-! ### The taut homomorphism -/

open TopologicalRing.CompletionOver in
/-- **A taut homomorphism of weakly admissible rings whose stages see prescribed modules.** Let
`ι` be a nonempty linear order and `V` a family of types indexed by it. There are weakly
admissible topological rings `A` and `C`, a continuous taut homomorphism `φ : A →+* C`, and a
family `I` of weak ideals of definition of `A`, cofinal among the open ideals, such that the
stage of `C` at the closure of `I γ • C` contains a copy of `V γ` and is no larger than the
stage of a polynomial ring over `𝔽₂` on `ι × ℕ` together with the modules at the indices up to
`γ`. -/
theorem exists_isTaut_card_stage (ι : Type u) [LinearOrder ι] [Nonempty ι] (V : ι → Type u) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C)
      (_ : IsTopologicalRing C) (_ : IsLinearTopology C C) (φ : A →+* C) (I : ι → Ideal A),
      TopologicalRing.IsWeaklyAdmissible A ∧ TopologicalRing.IsWeaklyAdmissible C ∧
      Continuous φ ∧ RingHom.IsTaut φ ∧
      (∀ γ, TopologicalRing.IsWeakIdealOfDefinition (I γ)) ∧
      (∀ J : Ideal A, IsOpen (J : Set A) → ∃ γ, I γ ≤ J) ∧
      (∀ γ, #(A ⧸ I γ) ≤ #(Stage ι γ)) ∧
      (∀ K : Ideal C, IsOpen (K : Set C) → ∃ γ, ((I γ).map φ).closure ≤ K) ∧
      (∀ γ, #(V γ) ≤ #(C ⧸ ((I γ).map φ).closure)) ∧
      (∀ γ, #(C ⧸ ((I γ).map φ).closure) ≤
        #(Stage ι γ) * #(∀ α : {α : ι // α ≤ γ}, Fiber (V α))) := by
  classical
  obtain ⟨A, _, _, _, _, π, hA, hπ, hcomp, hker, hbasis⟩ :=
    exists_isWeaklyAdmissible_proj_of_surjective_family (Λ := Gens ι) (R := Stage ι)
      (τ := fun _ _ h => stageMap ι h) (ρ := fun γ => Ideal.Quotient.mk (stageIdeal ι γ))
      (fun _ _ h => ker_stageMap_locallyNilpotent ι h)
      (fun _ => Ideal.Quotient.mk_surjective) (fun _ _ h x => stageMap_mk ι h x)
  let f := extMap V π
  let J : ι → WeakIdealOfDefinitionIndex A := fun γ => ⟨RingHom.ker (π γ), hker γ⟩
  -- the stage of `C` at `γ` is the stage of the square-zero extension at `γ`
  have hcard : ∀ γ, #(CompletionOver f ⧸ ((RingHom.ker (π γ)).map (canonicalMap f)).closure) =
      #(Ext V π ⧸ extIdeal V π γ) := fun γ => by
    rw [← ker_projection_eq_closure f (J γ)]
    exact Cardinal.mk_congr
      (RingHom.quotientKerEquivOfSurjective (projection_surjective f (J γ))).toEquiv
  have hopen : ∀ L : Ideal A, IsOpen (L : Set A) → ∃ γ, RingHom.ker (π γ) ≤ L := by
    intro L hL
    obtain ⟨γ, -, hγ⟩ := hbasis.mem_iff.mp (hL.mem_nhds L.zero_mem)
    exact ⟨γ, hγ⟩
  have htaut := isTaut_canonicalMap f hA.1
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, CompletionOver f,
    inferInstance, inferInstance, inferInstance, inferInstance, canonicalMap f,
    fun γ => RingHom.ker (π γ), hA, completionOver_isWeaklyAdmissible f hA,
    continuous_canonicalMap f, htaut, hker, hopen, fun γ => (Cardinal.mk_congr
      (RingHom.quotientKerEquivOfSurjective (hπ γ)).toEquiv).le, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨L, hL, hLK⟩ := (htaut.2.mem_iff).mp (hK.mem_nhds K.zero_mem)
    obtain ⟨γ, hγ⟩ := hopen L hL
    refine ⟨γ, fun x hx => hLK ?_⟩
    change x ∈ closure (((L.map (canonicalMap f)) : Ideal _) : Set _)
    exact closure_mono (Ideal.map_mono hγ) hx
  · intro γ
    rw [hcard γ]
    exact (Cardinal.mk_le_of_injective (basisVec_injective (V γ))).trans
      (card_fib_le_card_quotient (V := V) (π := π) γ)
  · intro γ
    rw [hcard γ]
    refine (card_quotient_le hπ (fun _ _ h a => hcomp h a) γ).trans ?_
    gcongr
    exact Cardinal.mk_le_of_injective (f := fun d : Π₀ α : {α : ι // α ≤ γ}, Fib V π α =>
      (fun α => d α : ∀ α : {α : ι // α ≤ γ}, Fiber (V α))) DFunLike.coe_injective

end TopologicalRing.TautUnboundedStages

end
