module

public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.ProjHeightOne
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.DimensionOne
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksCore.Tactic.StacksAttribute

/-!
# The homogeneous ideal of a plane curve is principal

Let `k` be a field. A *plane curve* is a curve isomorphic to a closed subscheme of
`P^2_k = Proj k[T₀, T₁, T₂]`, and such a subscheme is recovered from its homogeneous ideal
`I(Z) = Ker(k[T₀, T₁, T₂] ⟶ ⨁_{n ≥ 0} Γ(Z, 𝒪_Z(n)))` as `Z = V₊(I(Z))`. This file proves
**Tag 0BYB**: if `Z ⊆ P^2_k` is a closed subscheme which is equidimensional of dimension one
and has no embedded points — equivalently, which is Cohen--Macaulay — then `I(Z)` is principal.
That is what makes every plane curve the zero scheme of a single homogeneous equation `F`, the
starting point for the degree, the genus and the smoothness criteria of the plane-curve section.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.projectivePlane_idealOfClosedSubscheme_isPrincipal`:
  **Tag 0BYB**, the principality statement.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints`: **Tag 0BYB**, the parenthetical
  statement — for such a `Z` the absence of embedded points is Cohen--Macaulayness.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.projectivePlane_idealOfClosedSubscheme_isPrincipal_of_isCohenMacaulay`: the principality
  statement read through the parenthetical.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.projectivePlane_exists_homogeneous_eq_idealOfClosedSubscheme`: the generator made explicit,
  `I(Z) = (F)` with `F` homogeneous of some degree `d`.
* `topologicalKrullDim_le_of_forall_mem_irreducibleComponents`: a bound on the dimension of a
  topological space satisfied by all of its irreducible components bounds the dimension of the
  space.
* `topologicalKrullDim_eq_one_of_forall_mem_irreducibleComponents`: a nonempty space all of whose
  irreducible components have dimension one has dimension one.
* `TopologicalSpace.Equidimensional.of_forall_topologicalKrullDim_eq`: a space all of whose
  irreducible components have one and the same dimension is equidimensional.

## Implementation notes

Both halves are specializations of results in the library and no projective geometry is redone here.
Principality is [Stacks, Tag 0BXU], that is
`projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_dimension`,
at `n = 2`: that result is stated for a closed subscheme of `P^n_k` all of whose irreducible
components have dimension `n - 1`, written without subtraction as `dim W + 1 = n`, which for
`n = 2` is `dim W = 1`. The explicit generator comes the same way from
`projectiveSpace_exists_homogeneous_eq_idealOfClosedSubscheme_of_codimension_one`, whose
codimension hypothesis is supplied by `projectiveSpace_codimension_closureSingleton_eq_one`.

The parenthetical is [Stacks, Tag 0BXG] —
`isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one` — whose hypotheses are
met for free: `Z` is locally Noetherian because a closed immersion is locally of finite type and
`Proj` of a Noetherian graded ring is Noetherian, and `dim Z ≤ 1` because every irreducible
component of `Z` has dimension one. The latter step is
`topologicalKrullDim_le_of_forall_mem_irreducibleComponents`, which the repository has had only
in private copies; it is stated publicly here, and its proof is the public
`topologicalKrullDim_coe_eq_height` applied to the irreducible component containing a given
irreducible closed subset.

Dimensions are `topologicalKrullDim`, valued in `WithBot ℕ∞`, and the hypothesis is that every
irreducible component has dimension exactly `1`; the vacuous case is the empty subscheme, as in
Tag 0BXU. By `TopologicalSpace.Equidimensional.of_forall_topologicalKrullDim_eq` this is the
source's "equidimensional of dimension `1`" in the sense of [Stacks, Tag 0058].

## References

* [Stacks Project, Tag 0BYB](https://stacks.math.columbia.edu/tag/0BYB)
* [Stacks Project, Tag 0BXU](https://stacks.math.columbia.edu/tag/0BXU)
* [Stacks Project, Tag 0BXG](https://stacks.math.columbia.edu/tag/0BXG)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-! ### Bounding the dimension of a space by the dimensions of its components -/

/-- **A bound on the dimensions of all irreducible components bounds the dimension of the
space.** Every irreducible closed subset of a topological space is contained in an irreducible
component, so its height in the lattice of irreducible closed subsets is at most the height of
that component, which is the dimension of the component as a subspace. -/
theorem topologicalKrullDim_le_of_forall_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] {d : WithBot ℕ∞}
    (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W ≤ d) :
    topologicalKrullDim T ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨W, hW, hZW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (Z : Set T) Z.isIrreducible
  let W' : IrreducibleCloseds T := ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩
  calc (Order.height Z : WithBot ℕ∞) ≤ (Order.height W' : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.height_mono (show Z ≤ W' from hZW))
    _ = topologicalKrullDim (W : Set T) := (topologicalKrullDim_coe_eq_height W').symm
    _ ≤ d := h W hW

/-- **A nonempty space all of whose irreducible components have dimension one has dimension
one.** Together with `TopologicalSpace.Equidimensional.of_forall_topologicalKrullDim_eq` this
says that the hypothesis "equidimensional of dimension one" of [Stacks, Tag 0058] on a nonempty
space already fixes the dimension of the space. -/
@[ega "0 14.1.3" "special case"]
theorem topologicalKrullDim_eq_one_of_forall_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] [Nonempty T]
    (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W = 1) :
    topologicalKrullDim T = 1 := by
  refine le_antisymm (topologicalKrullDim_le_of_forall_mem_irreducibleComponents
    fun W hW => le_of_eq (h W hW)) ?_
  obtain ⟨x⟩ := ‹Nonempty T›
  obtain ⟨W, hW, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({x} : Set T) isIrreducible_singleton
  exact (h W hW).symm.trans_le (topologicalKrullDim_subspace_le T W)

/-- **A space whose irreducible components all have one and the same dimension is
equidimensional.** This is what the phrase "equidimensional of dimension `d`" of
[Stacks, Tag 0058] amounts to once the common dimension is named. -/
theorem TopologicalSpace.Equidimensional.of_forall_topologicalKrullDim_eq {T : Type*}
    [TopologicalSpace T] {d : WithBot ℕ∞}
    (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W = d) :
    TopologicalSpace.Equidimensional T :=
  fun _ hA _ hB => (h _ hA).trans (h _ hB).symm

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] {Z : Scheme.{u}}
  (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]

/-! ### Tag 0BYB -/

/-- **Stacks Project, Tag 0BYB.** Let `k` be a field and let `Z` be a closed subscheme of
`P^2_k = Proj k[T₀, T₁, T₂]` which is equidimensional of dimension one and has no embedded
points. Then the homogeneous ideal `I(Z) ⊆ k[T₀, T₁, T₂]` corresponding to `Z` is principal.

Equidimensionality of dimension one is the hypothesis that every irreducible component of `Z`
has `topologicalKrullDim` equal to `1`; see
`TopologicalSpace.Equidimensional.of_forall_topologicalKrullDim_eq`. This is Tag 0BXU, the
statement for `P^n_k` with components of dimension `n - 1`, at `n = 2`. For the equivalent
Cohen--Macaulay form of the hypothesis see
`projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints`, and for the generator written out see
`projectivePlane_exists_homogeneous_eq_idealOfClosedSubscheme`. -/
@[stacks 0BYB]
theorem projectivePlane_idealOfClosedSubscheme_isPrincipal (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) i).IsPrincipal :=
  projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_dimension k 2 i hno
    fun W hW => by rw [hdim W hW]; rfl

include i in
/-- **Stacks Project, Tag 0BYB, the parenthetical statement.** A closed subscheme `Z` of
`P^2_k` which is equidimensional of dimension one has no embedded points precisely when it is
Cohen--Macaulay.

This is Tag 0BXG for schemes of dimension at most one. Both of its hypotheses are automatic
here: `Z` is locally Noetherian because `i` is a closed immersion, hence locally of finite type,
into the Noetherian scheme `P^2_k`; and `dim Z ≤ 1` because every irreducible component of `Z`
has dimension one. -/
@[stacks 0BYB]
theorem projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1) :
    IsCohenMacaulay Z ↔ HasNoEmbeddedPoints Z :=
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one Z
    (topologicalKrullDim_le_of_forall_mem_irreducibleComponents
      fun W hW => le_of_eq (hdim W hW))

/-- **Tag 0BYB with the Cohen--Macaulay hypothesis.** The homogeneous ideal of a
Cohen--Macaulay closed subscheme of `P^2_k` which is equidimensional of dimension one is
principal.

This is `projectivePlane_idealOfClosedSubscheme_isPrincipal` read through the parenthetical
statement `projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints`; those two carry the tag
between them and this restatement is not tagged. -/
theorem projectivePlane_idealOfClosedSubscheme_isPrincipal_of_isCohenMacaulay
    (hCM : IsCohenMacaulay Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) i).IsPrincipal :=
  projectivePlane_idealOfClosedSubscheme_isPrincipal k i
    ((projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints k i hdim).mp hCM) hdim

/-- **Tag 0BYB with a homogeneous equation.** The homogeneous ideal of a closed subscheme of
`P^2_k` which is equidimensional of dimension one and has no embedded points is generated by a
single homogeneous polynomial `F ∈ k[T₀, T₁, T₂]`.

This is the form in which the plane-curve section uses Tag 0BYB, writing `I(Z) = (F)` and
reading off the degree of `F`; the statement of the tag asserts only principality, so the tag
is not placed here. -/
theorem projectivePlane_exists_homogeneous_eq_idealOfClosedSubscheme
    (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin 3) k),
      F ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k d ∧
        idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
          Ideal.span {F} :=
  projectiveSpace_exists_homogeneous_eq_idealOfClosedSubscheme_of_codimension_one k 2 i hno
    fun W hW _ hx => projectiveSpace_codimension_closureSingleton_eq_one k 2 i hx
      (by rw [hdim W hW]; rfl)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
