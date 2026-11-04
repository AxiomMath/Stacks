module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Coheight of a point outside a dense open of a Noetherian surface

On a Noetherian scheme of dimension at most two, a point outside a dense open subset has
coheight one or two: it cannot be zero, because a point of coheight zero is the generic point of
an irreducible component and every irreducible component meets a dense open set, and it is
bounded by the dimension through `AlgebraicGeometry.coheight_le_topologicalKrullDim`.

In dimension exactly two, a point of coheight two is closed, and it is the only point of the
closure of its own generic point.

## Main results

* `AlgebraicGeometry.coheight_eq_one_or_two_of_notMem_dense` and
  `AlgebraicGeometry.ringKrullDim_stalk_eq_one_or_two_of_notMem_dense`: the coheight, equivalently
  the local dimension, of a point outside a dense open of a Noetherian scheme of dimension at most
  two.
* `AlgebraicGeometry.eq_genericPoint_of_coheight_two`: on a scheme of dimension at most two, a
  point of coheight two is the only point of any set it is a generic point of.
* `AlgebraicGeometry.isClosed_singleton_of_coheight_two`: on a scheme of dimension at most two, a
  point of coheight two is closed.

## Implementation notes

The three statements about coheight two share one argument — a strict specialization raises
coheight by at least one, and the coheight is bounded by the dimension — which is isolated as
`AlgebraicGeometry.not_lt_of_coheight_two` rather than repeated. The source proof repeats the
dimension bound four times inline; here it is
`AlgebraicGeometry.coheight_le_topologicalKrullDim`.

The coheight-two hypotheses are stated with `topologicalKrullDim X ≤ 2` rather than with
equality: nothing in the arguments needs a point realizing the dimension, and the inequality is
what the consumer has in the Noetherian case.

Coheight lives in `ℕ∞` while the topological Krull dimension lives in `WithBot ℕ∞`, so the bound
is proved in `WithBot ℕ∞` and transported by `WithBot.coe_le_coe`; the finiteness of the coheight
has to be extracted separately before a case split on its value is available.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

-- `AlgebraicGeometry.coheight_le_topologicalKrullDim` was proved here a second time, with the
-- same statement and a different proof (through the supremum of the stalks' Krull dimensions
-- rather than the order-isomorphism with the irreducible closed subsets).  The canonical copy is
-- in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension`, whose import
-- closure is 271 modules against this file's 449 and which owns the codimension vocabulary; this
-- file now imports it.  Neither file imported the other, which is why two copies of one name
-- could coexist.
/-- On a scheme of dimension at most two, every point has coheight at most two. -/
private theorem coheight_le_two_of_topologicalKrullDim_le_two {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 2) (x : X) : Order.coheight x ≤ 2 :=
  WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans hdim)

/-- On a scheme of dimension at most two, no point of coheight two is a strict specialization of
another point: that would force a point of coheight at least three. -/
theorem not_lt_of_coheight_two {X : Scheme.{u}} (hdim : topologicalKrullDim X ≤ 2) {x y : X}
    (hy : Order.coheight y = 2) : ¬ x < y := by
  intro hlt
  have hco := coheight_le_two_of_topologicalKrullDim_le_two hdim x
  have hcontra : (2 : ℕ∞) + 1 ≤ 2 := by
    simpa [hy] using (Order.coheight_add_one_le hlt).trans hco
  norm_num at hcontra

/-- A point outside a dense open subset of a Noetherian scheme of dimension at most two has
coheight one or two. -/
theorem coheight_eq_one_or_two_of_notMem_dense {X : Scheme.{u}} [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 2) {U : X.Opens} (hU : Dense (U : Set X)) {x : X}
    (hxU : x ∉ U) : Order.coheight x = 1 ∨ Order.coheight x = 2 := by
  have hco := coheight_le_two_of_topologicalKrullDim_le_two hdim x
  have hzero : Order.coheight x ≠ 0 := by
    intro hx0
    have hxGen : x ∈ genericPoints X :=
      Stacks.Chow.mem_genericPoints_of_isMax (Order.coheight_eq_zero.mp hx0)
    obtain ⟨V, hVopen, hVne, hVsub⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
        (closure ({x} : Set X)) hxGen
    obtain ⟨y, hyV, hyU⟩ := (dense_iff_inter_open.mp hU) V hVopen hVne
    exact hxU ((isGenericPoint_closure (x := x)).mem_open_set_iff U.2 |>.2
      ⟨y, hVsub hyV, hyU⟩)
  have hfinite : Order.coheight x ≠ ⊤ := fun h => by simp [h] at hco
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hnle : n ≤ 2 := by
    rw [← hn] at hco
    exact_mod_cast hco
  have hnzero : n ≠ 0 := fun hz =>
    hzero (hn.symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) hz))
  rcases show n = 1 ∨ n = 2 by omega with h1 | h2
  · exact Or.inl (hn.symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) h1))
  · exact Or.inr (hn.symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) h2))

/-- A point outside a dense open subset of a Noetherian scheme of dimension at most two has a
local ring of Krull dimension one or two. -/
theorem ringKrullDim_stalk_eq_one_or_two_of_notMem_dense {X : Scheme.{u}} [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 2) (U : X.Opens) (hU : Dense (U : Set X)) (x : X)
    (hxU : x ∉ U) :
    ringKrullDim (X.presheaf.stalk x) = 1 ∨ ringKrullDim (X.presheaf.stalk x) = 2 := by
  rw [ringKrullDim_stalk_eq_coheight]
  rcases coheight_eq_one_or_two_of_notMem_dense hdim hU hxU with h | h
  · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inr (by rw [h]; norm_num)

/-- On a scheme of dimension at most two, a point of coheight two is the only point of any set
of which it is a generic point. -/
theorem eq_genericPoint_of_coheight_two {X : Scheme.{u}} (hdim : topologicalKrullDim X ≤ 2)
    {D : Set X} {x y : X} (hD : IsGenericPoint y D) (hy : Order.coheight y = 2) (hx : x ∈ D) :
    x = y := by
  by_contra hne
  have hxy : x ≤ y := Scheme.le_iff_specializes.mpr (hD.specializes hx)
  have hyx : ¬ y ≤ x := fun hyx => hne (inseparable_iff_specializes_and.mpr
    ⟨Scheme.le_iff_specializes.mp hxy, Scheme.le_iff_specializes.mp hyx⟩).eq.symm
  exact not_lt_of_coheight_two hdim hy (lt_of_le_not_ge hxy hyx)

/-- On a scheme of dimension at most two, a point of coheight two is closed. -/
theorem isClosed_singleton_of_coheight_two {X : Scheme.{u}} (hdim : topologicalKrullDim X ≤ 2)
    {x : X} (hx : Order.coheight x = 2) : IsClosed ({x} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  exact eq_genericPoint_of_coheight_two hdim isGenericPoint_closure hx hy

end AlgebraicGeometry

end
