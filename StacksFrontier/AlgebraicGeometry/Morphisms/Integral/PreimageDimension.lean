module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension

/-!
# The dimension of the preimage of a closed subset under an integral morphism

An integral morphism does not raise dimension
(`AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom`). This file reads that off for the
preimage of a closed subset of the target: give the closed subset its reduced induced structure,
whose scheme-theoretic preimage is the fibre product, so the morphism from the preimage is a base
change of the original one and is integral again.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_preimage_le_of_isIntegralHom`: the preimage of a closed
  subset under an integral morphism has at most the dimension of that subset.

## Implementation notes

The statement lives in its own module rather than beside
`AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension`, because the identification of the
underlying space of the subscheme cut out by an ideal sheaf with the support of that ideal sheaf
is `Stacks.Chow.topologicalKrullDim_subscheme`, whose module already imports that one.

This is the form Stacks 0B0E uses: the closed subscheme `C ∩ X = π^{-1}(π(Z))` has dimension at
most that of `π(Z)`, which is `dim Z` because `π` is finite.

## References

* [Stacks Project, Tag 0ECG](https://stacks.math.columbia.edu/tag/0ECG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The preimage of a closed subset under an integral morphism has at most its dimension.**
Give the closed subset its reduced induced structure; its scheme-theoretic preimage is the fibre
product, so the morphism from the preimage to it is a base change of the original morphism and is
integral, and the inequality for schemes applies. The underlying space of a subscheme cut out by
an ideal sheaf is the support of that ideal sheaf, which identifies the two sides. -/
theorem topologicalKrullDim_preimage_le_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {S : Set Y} (hS : IsClosed S) :
    topologicalKrullDim (f.base ⁻¹' S) ≤ topologicalKrullDim S := by
  set I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩
  have hIsupp : (I.support : Set Y) = S :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨S, hS⟩
  have hJsupp : ((I.comap f).support : Set X) = f.base ⁻¹' S := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hIsupp]
  have h := topologicalKrullDim_le_of_isIntegralHom
    ((I.comapIso f).hom ≫ Limits.pullback.snd f I.subschemeι)
  rw [Stacks.Chow.topologicalKrullDim_subscheme, Stacks.Chow.topologicalKrullDim_subscheme,
    hIsupp, hJsupp] at h
  exact h

end AlgebraicGeometry

end
