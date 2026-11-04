module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.GenericAnnihilator
public import StacksFrontier.AlgebraicGeometry.StalkBridge.Basic

/-!
# The stalk of a direct image along a closed immersion at the generic point

Let `i : Z ⟶ X` be a closed immersion with `Z` integral and let `ξ` be the generic point of `Z`.
For every `𝒪_Z`-module `N`, the stalk of `i_* N` at `i ξ` is annihilated by the maximal ideal of
`𝒪_{X,i ξ}`: a scalar from `𝒪_X` acts on `i_* N` through the comorphism `i^♯`, and since
`𝒪_{Z,ξ}` is a field, the kernel of the surjection `𝒪_{X,i ξ} ⟶ 𝒪_{Z,ξ}` is the maximal ideal.

## Main results

* `Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk.stalkKilledByMaximalIdeal_pushforward`:
  the statement above, for the predicate `Stacks.ClosedImmersion.StalkKilledByMaximalIdeal`.
* `Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk.isMaximalIdealAnnihilated_pushforward`:
  the same for the predicate
  `Stacks.AlgebraicGeometry.Tag01YEStalkBridge.IsMaximalIdealAnnihilated`.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk

/-- **Every scalar that a morphism kills annihilates the sections of a direct image.** If
`b ∈ Γ(X, V)` maps to zero in `Γ(Z, i⁻¹ V)`, then `b` acts as zero on the sections of `i_* N`
over `V`. -/
theorem smul_pushforward_eq_zero_of_app_eq_zero {Z X : _root_.AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (N : Z.Modules) (V : X.Opens) (b : Γ(X, V)) (hb : i.app V b = 0)
    (m : Γ((Scheme.Modules.pushforward i).obj N, V)) :
    b • m = 0 := by
  let _ : Module Γ(Z, i ⁻¹ᵁ V) Γ((Scheme.Modules.pushforward i).obj N, V) :=
    inferInstanceAs (Module Γ(Z, i ⁻¹ᵁ V) Γ(N, i ⁻¹ᵁ V))
  show (i.app V b) • m = 0
  rw [hb, zero_smul]

/-- **The stalk of `i_* N` at the image of the generic point of an integral closed subscheme is
annihilated by the maximal ideal**, for every `𝒪_Z`-module `N`. -/
theorem isMaximalIdealAnnihilated_pushforward {Z X : _root_.AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (N : Z.Modules) :
    Tag01YEStalkBridge.IsMaximalIdealAnnihilated
      ((Scheme.Modules.pushforward i).obj N) (i.base ξ) :=
  Tag01YEStalkBridge.isMaximalIdealAnnihilated_of_app_killed i ξ hξ _
    fun V b hb m => smul_pushforward_eq_zero_of_app_eq_zero i N V.1 b hb m

/-- **The stalk of `i_* N` at the image of the generic point of an integral closed subscheme is
annihilated by the maximal ideal**, for every `𝒪_Z`-module `N`, stated with
`Stacks.ClosedImmersion.StalkKilledByMaximalIdeal`. -/
theorem stalkKilledByMaximalIdeal_pushforward {Z X : _root_.AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (N : Z.Modules) :
    Stacks.ClosedImmersion.StalkKilledByMaximalIdeal
      ((Scheme.Modules.pushforward i).obj N) (i.base ξ) :=
  isMaximalIdealAnnihilated_pushforward i ξ hξ N

end Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk

end
