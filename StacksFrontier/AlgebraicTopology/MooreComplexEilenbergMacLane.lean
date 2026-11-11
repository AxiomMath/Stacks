module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import StacksFrontier.AlgebraicTopology.MooreComplex

/-!
# The homology of the Moore complex of `K(A, k)`

Let `C` be an abelian category, let `A` be an object of `C` and let `k ≥ 0` be an integer. The
Eilenberg-MacLane object `K(A, k) = i_{k!}U` of [Stacks, Tag 0191] is isomorphic to `Γ₀` of the
chain complex `A` concentrated in degree `k`, for `Γ₀` the inverse of the Dold-Kan equivalence:
the unit of the Dold-Kan equivalence identifies `K(A, k)` with `Γ₀ N(K(A, k))`, and `N(K(A, k))`
is `A` concentrated in degree `k` by [Stacks, Tag 0199]. Consequently the Moore complex
`s(K(A, k))` has homology `A` in degree `k` and `0` in every other degree.

## Main results

* `AlgebraicTopology.eilenbergMacLaneIsoΓ₀Single`: `K(A, k)` is isomorphic to `Γ₀` of the complex
  `A` concentrated in degree `k`.
* `AlgebraicTopology.homology_alternatingFaceMapComplex_eilenbergMacLane`: the Moore complex of
  `K(A, k)` has homology `A` in degree `k`, and zero homology in every other degree.

## References

* [Stacks, Tag 0197](https://stacks.math.columbia.edu/tag/0197)
-/

section

open CategoryTheory Limits

universe v u

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Eilenberg-MacLane object `K(A, k) = i_{k!}U` of an object `A` of an abelian category is
isomorphic to `Γ₀.obj L`, for `L` the chain complex `A` concentrated in degree `k` and `Γ₀` the
inverse of the Dold-Kan equivalence: the unit of the Dold-Kan equivalence identifies `K(A, k)`
with `Γ₀.obj N(K(A, k))`, and `N(K(A, k))` is `A` concentrated in degree `k` by [Stacks, Tag 0199].
-/
public noncomputable def eilenbergMacLaneIsoΓ₀Single (A : C) (k : ℕ) :
    SimplicialObject.eilenbergMacLane A k ≅
      DoldKan.Γ₀.obj ((HomologicalComplex.single C (ComplexShape.down ℕ) k).obj A) :=
  have h : Nonempty ((normalizedMooreComplex C).obj (SimplicialObject.eilenbergMacLane A k) ≅
      (HomologicalComplex.single C (ComplexShape.down ℕ) k).obj A) :=
    isIsomorphic_normalizedMooreComplex_eilenbergMacLane_single A k
  (Abelian.DoldKan.equivalence.unitIso.app (SimplicialObject.eilenbergMacLane A k)).trans
    (Abelian.DoldKan.equivalence.inverse.mapIso h.some)

/-- **Stacks 0197**.
Let `C` be an abelian category, let `A` be an object of `C` and let `k ≥ 0` be an integer. The
Moore complex `s(K(A, k))` of the Eilenberg-MacLane object `K(A, k) = i_{k!}U` has homology
`H_k(s(K(A, k))) ≅ A` and `H_i(s(K(A, k))) = 0` for every `i ≠ k`. -/
@[stacks 0197]
public theorem homology_alternatingFaceMapComplex_eilenbergMacLane (A : C) (k : ℕ) :
    IsIsomorphic (((alternatingFaceMapComplex C).obj
        (SimplicialObject.eilenbergMacLane A k)).homology k) A ∧
      ∀ i ≠ k, IsZero (((alternatingFaceMapComplex C).obj
        (SimplicialObject.eilenbergMacLane A k)).homology i) := by
  have e := (alternatingFaceMapComplex C).mapIso (eilenbergMacLaneIsoΓ₀Single A k)
  obtain ⟨⟨h₁⟩, h₂⟩ := DoldKan.homology_alternatingFaceMapComplex_Γ₀_single A k
  exact ⟨⟨(HomologicalComplex.homologyMapIso e k).trans h₁⟩,
    fun i hi => (h₂ i hi).of_iso (HomologicalComplex.homologyMapIso e i)⟩

end AlgebraicTopology

end
