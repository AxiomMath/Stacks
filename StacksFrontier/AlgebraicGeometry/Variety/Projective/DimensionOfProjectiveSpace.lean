module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.Topology.Dimension.Codimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of the projective space of a vector space

The projective space `𝐏(V) = Proj (Sym_k V)` of a finite-dimensional vector space `V` over a
field `k` has Krull dimension `dim_k V - 1`, written additively as
`dim 𝐏(V) + 1 = dim_k V`. A basis of `V` indexed by `Fin (n + 1)` identifies `𝐏(V)` with
`Proj k[T₀, …, Tₙ]`, whose dimension is `n`, and dimension is a topological invariant.

Consequently an irreducible closed subset of `𝐏(V)` of codimension at least `2` has dimension
at most `dim_k V - 3`: height plus coheight in the poset of irreducible closed subsets is
bounded by the Krull dimension of the whole space.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_projectiveSpaceOfModule_of_basis`: the dimension of
  `𝐏(V)` is `n` when `V` has a basis indexed by `Fin (n + 1)`.
* `AlgebraicGeometry.topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq`: the same, from
  `dim_k V = n + 1`.
* `AlgebraicGeometry.topologicalKrullDim_projectiveSpaceOfModule_add_one`: the subtraction-free
  form `dim 𝐏(V) + 1 = dim_k V` for `V` nonzero and finite-dimensional.
* `AlgebraicGeometry.topologicalKrullDim_add_codimension_le_projectiveSpaceOfModule`: dimension
  plus codimension of an irreducible closed subset is at most the dimension of `𝐏(V)`.
* `AlgebraicGeometry.topologicalKrullDim_add_two_le_of_two_le_codimension`: an irreducible
  closed subset of codimension at least `2` satisfies `dim B + 2 + 1 ≤ dim_k V`.

## Implementation notes

Dimensions are `topologicalKrullDim`, valued in `WithBot ℕ∞`, so every statement is additive:
no truncated subtraction appears. The graded-algebra instance on a polynomial ring is
`MvPolynomial.gradedAlgebra`, supplied as a local instance as in the files that state the
dimension of `Proj` of a polynomial ring.

The ring and the module are taken in a single universe, as the coordinate comparison
`AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial` requires.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- The projective space of a vector space with a basis indexed by `Fin (n + 1)` has Krull
dimension `n`: it is isomorphic to `Proj k[T₀, …, Tₙ]`, which has dimension `n`. -/
theorem topologicalKrullDim_projectiveSpaceOfModule_of_basis {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) k V) :
    topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom.homeomorph.isHomeomorph]
  simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := n + 1) n.succ_pos

/-- The projective space of a vector space of dimension `n + 1` has Krull dimension `n`. -/
theorem topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq [FiniteDimensional k V]
    {n : ℕ} (hV : Module.finrank k V = n + 1) :
    topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
  topologicalKrullDim_projectiveSpaceOfModule_of_basis (Module.finBasisOfFinrankEq k V hV)

/-- A nonzero finite-dimensional vector space has dimension `n + 1` for some `n`. -/
private theorem exists_finrank_eq_add_one [FiniteDimensional k V] [Nontrivial V] :
    ∃ n, Module.finrank k V = n + 1 :=
  Nat.exists_eq_succ_of_ne_zero Module.finrank_pos.ne'

/-- **The dimension of the projective space of a nonzero finite-dimensional vector space `V` is
one less than the dimension of `V`**, stated without subtraction as
`dim 𝐏(V) + 1 = dim_k V`. -/
theorem topologicalKrullDim_projectiveSpaceOfModule_add_one [FiniteDimensional k V]
    [Nontrivial V] :
    topologicalKrullDim (projectiveSpaceOfModule k V) + 1 =
      (Module.finrank k V : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_finrank_eq_add_one (k := k) (V := V)
  rw [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn, hn]
  push_cast
  rfl

/-- In any topological space the dimension of an irreducible closed subset plus its codimension
is at most the dimension of the whole space. -/
@[ega "0 14.2.2" "(ii), special case"]
theorem topologicalKrullDim_add_codimension_le {T : Type*} [TopologicalSpace T]
    (B : IrreducibleCloseds T) :
    topologicalKrullDim (B : Set T) + (codimension B : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  have : Nonempty (IrreducibleCloseds T) := ⟨B⟩
  rw [topologicalKrullDim_coe_eq_height B, codimension_eq_coheight,
    ← WithBot.coe_add (Order.height B) (Order.coheight B)]
  rw [show topologicalKrullDim T = Order.krullDim (IrreducibleCloseds T) from rfl,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) B)

/-- The dimension of an irreducible closed subset of the projective space of a vector space of
dimension `n + 1`, plus its codimension, is at most `n`. -/
theorem topologicalKrullDim_add_codimension_le_projectiveSpaceOfModule [FiniteDimensional k V]
    {n : ℕ} (hV : Module.finrank k V = n + 1)
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) :
    topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) +
      (codimension B : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
  (topologicalKrullDim_add_codimension_le B).trans_eq
    (topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV)

/-- **An irreducible closed subset of codimension at least `2` in the projective space of a
finite-dimensional vector space `V` has dimension at most `dim_k V - 3`**, stated without
subtraction as `dim B + 2 + 1 ≤ dim_k V`. -/
theorem topologicalKrullDim_add_two_le_of_two_le_codimension [FiniteDimensional k V]
    [Nontrivial V] (B : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hB : 2 ≤ codimension B) :
    topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) + 2 + 1 ≤
      (Module.finrank k V : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_finrank_eq_add_one (k := k) (V := V)
  have hle : topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) + 2 ≤
      (n : WithBot ℕ∞) :=
    le_trans (add_le_add le_rfl (by simpa using WithBot.coe_le_coe.mpr hB))
      (topologicalKrullDim_add_codimension_le_projectiveSpaceOfModule hn B)
  refine le_trans (add_le_add hle (le_refl (1 : WithBot ℕ∞))) ?_
  rw [hn]
  push_cast
  exact le_rfl

end AlgebraicGeometry

end
