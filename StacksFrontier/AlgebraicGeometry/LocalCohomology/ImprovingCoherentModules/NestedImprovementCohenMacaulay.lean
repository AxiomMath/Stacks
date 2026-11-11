module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovementExistence
public import StacksCore.Tactic.StacksAttribute

/-!
# Improving a coherent module along a nested pair: the complete statement

Let `X` be a Noetherian scheme which locally has a dualizing complex and let `T' ⊆ T ⊆ X` be
subsets stable under specialization such that every immediate specialization `x ⤳ x'` with
`x' ∈ T'` has `x ∈ T`.  A coherent `𝒪_X`-module `F` has a unique improvement `F ⟶ F''` along
`T' ⊆ T` (`AlgebraicGeometry.IsNestedImprovement`), and its pullback along a Cohen-Macaulay
morphism `f : Y ⟶ X` with `Y` Noetherian is an improvement along `f⁻¹ T' ⊆ f⁻¹ T`.

## Main results

* `AlgebraicGeometry.existsUnique_isNestedImprovement_and_pullback_of_hasDualizingComplex`:
  **[Stacks, Tag 0EI4]**, every clause in one statement.

## References

* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EI4.** Let `X` be a Noetherian scheme which locally has a dualizing
complex, let `T' ⊆ T ⊆ X` be stable under specialization and such that every immediate
specialization `x ⤳ x'` with `x' ∈ T'` has `x ∈ T`, and let `F` be a coherent `𝒪_X`-module.
Then there is a map `φ : F ⟶ F''` to a coherent module such that

1. `F_x ⟶ F''_x` is an isomorphism for `x ∉ T`,
2. `F_x ⟶ F''_x` is surjective and `depth F''_x ≥ 1` for `x ∈ T`, `x ∉ T'`,
3. `depth F''_x ≥ 2` for `x ∈ T'`,

(this is `AlgebraicGeometry.IsNestedImprovement T T' φ`); it is unique, in that any other such
map `F ⟶ H` is carried to it by a unique isomorphism `F'' ≅ H` under `F`; and for every
Cohen-Macaulay morphism `f : Y ⟶ X` with `Y` Noetherian, the pullback `f^* F ⟶ f^* F''` has the
same properties with respect to `f⁻¹ T' ⊆ f⁻¹ T`.

The Cohen-Macaulay hypothesis is `AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` of
[Stacks, Tag 045R], whose definition presupposes, as the source's does, that the fibres of `f`
are locally Noetherian; that is the argument `hfib`. -/
@[stacks 0EI4 "existence and uniqueness, up to a unique isomorphism under F, of the map F to F'' \
with conditions (1), (2), (3), together with the assertion that its pullback along a \
Cohen-Macaulay morphism with Noetherian source satisfies (1), (2), (3) with respect to the \
inverse images of T' and T; at the hypotheses of the source"]
public theorem existsUnique_isNestedImprovement_and_pullback_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T T' : Set X) (hTT' : T' ⊆ T)
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsNestedImprovement T T' φ ∧
      (∀ (H : X.Modules) (ψ : F ⟶ H), IsNestedImprovement T T' ψ →
        ∃! e : G ≅ H, φ ≫ e.hom = ψ) ∧
      ∀ (Y : Scheme.{u}) [IsNoetherian Y] (f : Y ⟶ X)
        (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)), f.IsCohenMacaulay hfib →
        IsNestedImprovement (f.base ⁻¹' T) (f.base ⁻¹' T')
          ((Scheme.Modules.pullback f).map φ) := by
  obtain ⟨G, φ, hφ, huniq⟩ :=
    existsUnique_isNestedImprovement_of_hasDualizingComplex X hdual T T' hTT' hT hT' himm F
  exact ⟨G, φ, hφ, huniq, fun Y _ f hfib hcm => isNestedImprovement_pullback φ hφ f hfib hcm⟩

end AlgebraicGeometry

end
