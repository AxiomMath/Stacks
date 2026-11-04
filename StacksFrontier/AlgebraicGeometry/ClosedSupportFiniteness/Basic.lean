module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Devissage
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# Finite dimensionality of the cohomology of a module supported on a proper closed subset

Let `X` be a proper scheme over a field `k`. For a coherent module `𝒢'` on a closed subscheme
`i : W ⟶ X` contained in a zero-dimensional closed subset, every `Hⁿ(X, i_* 𝒢')` is a
finite-dimensional `k`-vector space, and so is `Hⁿ(X, 𝒢)` for any `𝒢 ≅ i_* 𝒢'`. On an
irreducible proper curve this gives the finite dimensionality of the cohomology of every coherent
module whose support lies in a proper closed subset and which is pushed forward from a closed
subscheme of that subset.

## Main results

* `topologicalKrullDim_le_of_range_subset`: the source of a closed immersion whose image lies in
  `Z` has dimension at most that of `Z`.
* `isFinite_of_isProper_of_topologicalKrullDim_le_zero`: a proper morphism out of a
  zero-dimensional scheme is finite.
* `finiteDimensional_cohomologyOverField_pushforward_of_topologicalKrullDim_le_zero`: the
  cohomology of `i_* 𝒢'` is finite-dimensional when `W` is zero-dimensional.
* `finiteDimensional_cohomologyOverField_of_iso_pushforward`: the same for any module isomorphic to
  such an `i_* 𝒢'`, with the dimension bound on a closed set containing the image of `i`.
* `forall_finiteDimensional_cohomologyOverField_of_exists_pushforward`: on an irreducible proper
  curve, the cohomology of a coherent module supported in a proper closed subset is
  finite-dimensional, provided every such module is pushed forward from a closed subscheme of that
  subset.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

/-! ### The dimension of the source of a closed immersion -/

/-- The source of a closed immersion whose image lies in `Z` has dimension at most that of `Z`. -/
theorem topologicalKrullDim_le_of_range_subset {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (Z : Set X) (hrange : Set.range i.base ⊆ Z) :
    topologicalKrullDim (W : Type u) ≤ topologicalKrullDim Z := by
  have hcomp : Topology.IsInducing
      ((Subtype.val : Z → X) ∘ fun w : (W : Type u) => (⟨i.base w, hrange ⟨w, rfl⟩⟩ : Z)) :=
    (IsClosedImmersion.isClosedEmbedding i).isEmbedding.isInducing
  exact (Topology.IsInducing.subtypeVal.of_comp_iff.mp hcomp).topologicalKrullDim_le

/-! ### Finiteness over the base from the dimension of the source -/

/-- A proper morphism out of a zero-dimensional scheme is finite. -/
theorem isFinite_of_isProper_of_topologicalKrullDim_le_zero {W Y : Scheme.{u}} (g : W ⟶ Y)
    [IsProper g] (hdim : topologicalKrullDim (W : Type u) ≤ 0) : IsFinite g :=
  isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero g fun y => by
    simpa using le_trans (le_trans (g.fiberHomeo y).isInducing.topologicalKrullDim_le
      (topologicalKrullDim_subspace_le _ _)) hdim

/-! ### Cohomology of a module pushed forward from a zero-dimensional closed subscheme -/

/-- For a closed immersion `i : W ⟶ X` with `W` zero-dimensional, into a proper scheme over a
field `k`, and a coherent module `G` on `W`, the cohomology `Hⁿ(X, i_* G)` is finite-dimensional
over `k`. -/
theorem finiteDimensional_cohomologyOverField_pushforward_of_topologicalKrullDim_le_zero
    (k : Type u) [Field k] {W X : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim (W : Type u) ≤ 0)
    (G : W.Modules) [G.IsCoherent] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G) n) :=
  have : IsFinite (i ≫ f) := isFinite_of_isProper_of_topologicalKrullDim_le_zero (i ≫ f) hdim
  finiteDimensional_cohomologyOverField_pushforward_of_isFinite k i f G n

/-- For a proper scheme `X` over a field `k`, a closed immersion `i : W ⟶ X` whose image lies in
a closed set `Z` of dimension at most zero, and a module `G` on `X` isomorphic to `i_* G'` for a
coherent module `G'` on `W`, the cohomology `Hⁿ(X, G)` is finite-dimensional over `k`. -/
theorem finiteDimensional_cohomologyOverField_of_iso_pushforward (k : Type u) [Field k]
    {W X : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) [IsProper f]
    (Z : Set X) (hZ : topologicalKrullDim Z ≤ 0) (hrange : Set.range i.base ⊆ Z)
    (G : X.Modules) (G' : W.Modules) [G'.IsCoherent]
    (e : (Scheme.Modules.pushforward i).obj G' ≅ G) (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f G n) :=
  have : FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G') n) :=
    finiteDimensional_cohomologyOverField_pushforward_of_topologicalKrullDim_le_zero k i f
      (le_trans (topologicalKrullDim_le_of_range_subset i Z hrange) hZ) G' n
  Module.Finite.equiv (cohomologyOverFieldIso k f e n).toLinearEquiv

/-! ### Modules supported on a proper closed subset of a curve -/

/-- Let `X` be an irreducible proper scheme of dimension at most one over a field `k`, and
suppose every coherent module on `X` with support in a proper closed subset `Z` is isomorphic to
the direct image of a coherent module on a closed subscheme whose image lies in `Z`. Then every
coherent module with support in a proper closed subset has finite-dimensional cohomology in every
degree. -/
theorem forall_finiteDimensional_cohomologyOverField_of_exists_pushforward (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IrreducibleSpace (X : Type u)]
    (hdimX : topologicalKrullDim (X : Type u) ≤ 1)
    (hpres : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (G' : W.Modules)
          (_ : SheafOfModules.IsCoherent G'), Set.range i.base ⊆ Z ∧
            Nonempty ((Scheme.Modules.pushforward i).obj G' ≅ G)) :
    ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ n, FiniteDimensional k (cohomologyOverField k f G n) := by
  intro G Z hZ hne hsub hG n
  obtain ⟨W, i, _, G', _, hrange, ⟨e⟩⟩ := hpres G Z hZ hne hsub hG
  exact finiteDimensional_cohomologyOverField_of_iso_pushforward k i f Z
    (topologicalKrullDim_le_zero_of_isClosed_of_ne_univ hdimX Z hZ hne) hrange G G' e n

end AlgebraicGeometry

end
