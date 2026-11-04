module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat surjective descent of invertibility for sheaves of modules

Let `ε : X₁ ⟶ X` be a flat morphism of schemes which is surjective on points, and let
`φ : F ⟶ G` be a homomorphism of `𝒪_X`-modules.  If the inverse image `ε^*φ` is an isomorphism
of `𝒪_{X₁}`-modules, then `φ` is already an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_of_flat_surjective`: **a
  homomorphism of sheaves of modules whose inverse image along a flat surjection is an
  isomorphism is itself an isomorphism.**

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 05A9](https://stacks.math.columbia.edu/tag/05A9)
* [Stacks Project, Tag 02VW](https://stacks.math.columbia.edu/tag/02VW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Invertibility of a homomorphism of sheaves of modules descends along a flat surjection.**
Let `ε : X₁ ⟶ X` be a flat morphism of schemes which is surjective on points.  A homomorphism
`φ : F ⟶ G` of `𝒪_X`-modules whose inverse image `ε^*φ` is an isomorphism is itself an
isomorphism. -/
@[ega "IV 2.2.9" "special case"]
public theorem isIso_of_isIso_pullback_of_flat_surjective {X X₁ : Scheme.{u}} (ε : X₁ ⟶ X)
    [Flat ε] [Surjective ε] {F G : X.Modules} (φ : F ⟶ G)
    (h : IsIso ((Scheme.Modules.pullback ε).map φ)) : IsIso φ := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap φ).2 fun x => ?_
  obtain ⟨x₁, rfl⟩ := ε.surjective x
  have hx₁ := (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    ((Scheme.Modules.pullback ε).map φ)).1 h x₁
  exact ⟨(injective_stalkMap_modulePullback_iff ε φ x₁).1 hx₁.1,
    (surjective_stalkMap_modulePullback_iff ε φ x₁).1 hx₁.2⟩

end AlgebraicGeometry.Scheme.Modules

end
