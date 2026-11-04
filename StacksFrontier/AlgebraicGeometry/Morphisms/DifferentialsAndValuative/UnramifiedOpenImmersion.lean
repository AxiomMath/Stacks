module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs

/-!
# Open immersions are G-unramified

Every open immersion of schemes is G-unramified.

## Main results

* `AlgebraicGeometry.gUnramified_of_isOpenImmersion`: an open immersion of schemes is
  G-unramified.

## References

* [Stacks Project, Tag 02GB](https://stacks.math.columbia.edu/tag/02GB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An open immersion of schemes is G-unramified. -/
@[stacks 02GB]
public instance gUnramified_of_isOpenImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsOpenImmersion f] : GUnramified f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨U, hU, hxU, f ''ᵁ U, hU.image_of_isOpenImmersion f,
    (f.preimage_image_eq U).ge, ?_⟩
  let : Algebra Γ(S, f ''ᵁ U) Γ(X, U) :=
    (f.appLE (f ''ᵁ U) U (f.preimage_image_eq U).ge).hom.toAlgebra
  have : IsIso (f.appLE (f ''ᵁ U) U (f.preimage_image_eq U).ge) := by
    rw [← Scheme.Hom.appIso_hom' f U]; infer_instance
  let algIso := AlgEquiv.ofBijective (Algebra.ofId Γ(S, f ''ᵁ U) Γ(X, U))
    (ConcreteCategory.bijective_of_isIso
      (f.appLE (f ''ᵁ U) U (f.preimage_image_eq U).ge))
  exact Algebra.GUnramified.mk (Algebra.FormallyUnramified.of_equiv algIso)
    (Algebra.FinitePresentation.equiv algIso)

end AlgebraicGeometry

end
