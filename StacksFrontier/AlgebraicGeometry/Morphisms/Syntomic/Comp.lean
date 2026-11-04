module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic

/-!
# Composition of syntomic morphisms

The composite of two syntomic morphisms of schemes is syntomic.

## Main results

* `AlgebraicGeometry.syntomic_isStableUnderComposition` states that syntomic morphisms are
  stable under composition.

## Implementation notes

The assertion is expressed as a `MorphismProperty.IsStableUnderComposition` instance, so the
syntomicity of a composite is available canonically through the morphism-property API. The
proof picks affine opens witnessing syntomicity of the second morphism, shrinks the source
chart to an affine open inside the preimage, and composes the resulting algebra tower.

## References

* [Stacks Project, Tag 01UH](https://stacks.math.columbia.edu/tag/01UH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The composite of two syntomic morphisms is syntomic. -/
private theorem syntomic_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Syntomic f) (hg : Syntomic g) : Syntomic (f ≫ g) := by
  intro x
  obtain ⟨⟨V, hV⟩, hxV, ⟨⟨W, hW⟩, hVW, hRingG⟩⟩ := hg (f x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (by simpa using hxV)
      (V.2.preimage f.continuous)
  have hUW : U ≤ (f ≫ g) ⁻¹ᵁ W := fun y hy => hVW (hUV hy)
  have hfAffine := ((syntomic_tfae f).out 1 2).mp hf
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Z, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
  have : Algebra.Syntomic Γ(Y, V) Γ(X, U) := hfAffine U hU V hV hUV
  have : Algebra.Syntomic Γ(Z, W) Γ(Y, V) := hRingG
  let : Algebra Γ(Z, W) Γ(X, U) := (f ≫ g).appLE W U hUW |>.hom.toAlgebra
  have : IsScalarTower Γ(Z, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change ((f ≫ g).appLE W U hUW).hom r =
        (f.appLE V U hUV).hom ((g.appLE W V hVW).hom r)
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
      exact congrArg (fun h : Γ(Z, W) →+* Γ(X, U) => h r)
        (congrArg CommRingCat.Hom.hom
          (Scheme.Hom.appLE_comp_appLE f g W V U hVW hUV).symm)
  exact ⟨⟨U, hU⟩, hxU, ⟨⟨W, hW⟩, hUW,
    Algebra.Syntomic.comp Γ(Z, W) Γ(Y, V) Γ(X, U)⟩⟩

/-- **Stacks Project, Tag 01UH.** Syntomic morphisms of schemes are stable under composition. -/
@[stacks 01UH]
instance syntomic_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@Syntomic.{u}) where
  comp_mem _f _g hf hg := syntomic_comp hf hg

end AlgebraicGeometry
