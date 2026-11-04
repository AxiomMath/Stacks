module

public import Mathlib.GroupTheory.GroupAction.Transitive
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison

/-!
# A finite étale cover with transitive geometric fibre is connected

Let `S` be a connected scheme with a geometric point `s` and let `T` be a finite étale cover of
`S` whose geometric fibre at `s` carries a transitive action of `π₁(S, s̄)`. Then `T` is
connected, both as an object of the Galois category of finite étale covers and as a topological
space.

This is the direction of Stacks 0BN3 which the library did not have. The converse — that the
fibre of a connected cover is transitive — is
`CategoryTheory.isPretransitive_fiber_of_isConnected`, and the two notions of connectedness are
interchanged by `AlgebraicGeometry.isConnected_iff_connectedSpace_left`. The transitivity
hypothesis is spelled as the existence, for each point of the fibre, of an element of
`π₁(S, s̄)` carrying a fixed point to it, because that is the form in which Stacks 0BND (1)
delivers it.

## Main results

* `AlgebraicGeometry.isPretransitive_finiteEtaleFiber_of_exists_smul_eq`: the hypothesis read as
  `MulAction.IsPretransitive`.
* `AlgebraicGeometry.isConnected_finiteEtaleOver_of_exists_smul_eq`: the cover is a connected
  object of the Galois category.
* `AlgebraicGeometry.connectedSpace_left_of_exists_smul_eq`: its underlying space is connected.

## References

* [Stacks Project, Tag 0BN3](https://stacks.math.columbia.edu/tag/0BN3)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} [ConnectedSpace S] {s : GeometricPoint S} {T : FiniteEtaleOver S}
  {y : (finiteEtaleFiberFunctor s).obj T}

/-- An action with a point whose orbit is everything is transitive. -/
theorem isPretransitive_finiteEtaleFiber_of_exists_smul_eq
    (htrans : ∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) :
    MulAction.IsPretransitive (EtaleFundamentalGroup S s)
      ((finiteEtaleFiberFunctor s).obj T) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨σa, hσa⟩ := htrans a
  obtain ⟨σb, hσb⟩ := htrans b
  exact ⟨σb * σa⁻¹, by rw [← hσa, ← hσb, smul_smul, mul_assoc, inv_mul_cancel, mul_one]⟩

/-- **A finite étale cover whose geometric fibre is transitive is a connected object of the
Galois category of finite étale covers.** -/
theorem isConnected_finiteEtaleOver_of_exists_smul_eq
    (htrans : ∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) :
    PreGaloisCategory.IsConnected T := by
  have hpre2 : MulAction.IsPretransitive (Aut (finiteEtaleFiberFintypeFunctor S s))
      ((finiteEtaleFiberFintypeFunctor S s).obj T) := by
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨σ, hσ⟩ :=
      (isPretransitive_finiteEtaleFiber_of_exists_smul_eq htrans).exists_smul_eq a b
    obtain ⟨g, hg⟩ := (autMulEquivEtaleFundamentalGroup S s).surjective σ
    refine ⟨g, ?_⟩
    rw [← hg] at hσ
    exact hσ
  have : Nonempty ((finiteEtaleFiberFintypeFunctor S s).obj T) := ⟨y⟩
  let _ : IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor S s)) :=
    Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor s
  exact CategoryTheory.isConnected_of_fiber_pretransitive
    (finiteEtaleFiberFintypeFunctor S s) T

/-- **A finite étale cover whose geometric fibre is transitive has connected underlying
space.** -/
theorem connectedSpace_left_of_exists_smul_eq
    (htrans : ∀ z, ∃ σ : EtaleFundamentalGroup S s, σ • y = z) :
    ConnectedSpace T.left :=
  connectedSpace_left_of_isConnected T (isConnected_finiteEtaleOver_of_exists_smul_eq htrans)

end AlgebraicGeometry

end
