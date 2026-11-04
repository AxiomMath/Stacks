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
public import Mathlib.Topology.Sheaves.Init

/-!
# Rainwater's lemma

## Main results

* `rainwater_lemma` (Stacks 090B): a surjective continuous selfmap of a Hausdorff space other
  than the identity admits a proper closed subset `E` with `X = E ∪ f '' E`.
-/

@[expose] public section

/-- **Stacks 090B** (Rainwater's lemma). Let `f : X → X` be a surjective
continuous selfmap of a Hausdorff topological space. If `f` is not `id_X`, then
there exists a proper closed subset `E ⊂ X` such that `X = E ∪ f(E)`. -/
@[stacks 090B]
theorem rainwater_lemma
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : X → X) (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (hf_ne_id : f ≠ id) :
    ∃ E : Set X, IsClosed E ∧ E ≠ Set.univ ∧ Set.univ = E ∪ f '' E := by
  -- Pick a point where `f` differs from the identity.
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ x := Function.ne_iff.mp hf_ne_id
  -- Separate `x₀` and `f x₀` by disjoint open neighbourhoods `U` and `V`.
  obtain ⟨U, V, hU, hV, hxU, hfxV, hUV⟩ := t2_separation hx₀.symm
  -- The closed set `E = Uᶜ ∪ (f⁻¹ V)ᶜ` does the job.
  refine ⟨Uᶜ ∪ (f ⁻¹' V)ᶜ,
    hU.isClosed_compl.union (hV.preimage hf_cont).isClosed_compl, ?_, ?_⟩
  · -- `E ≠ univ`, since `x₀` lies in `U` and `f x₀` lies in `V`.
    intro hE
    rcases (hE ▸ Set.mem_univ x₀ : x₀ ∈ Uᶜ ∪ (f ⁻¹' V)ᶜ) with h | h
    · exact h hxU
    · exact h hfxV
  · -- `X = E ∪ f '' E`: any `x ∈ U` is hit by some `y` with `f y ∉ V`.
    refine (Set.eq_univ_of_forall fun x => ?_).symm
    by_cases hx : x ∈ U
    · have hxV : x ∉ V := fun hv => Set.disjoint_iff.mp hUV ⟨hx, hv⟩
      obtain ⟨y, hy⟩ := hf_surj x
      exact Or.inr ⟨y, Or.inr fun hy_in => hxV (hy ▸ hy_in), hy⟩
    · exact Or.inl (Or.inl hx)
