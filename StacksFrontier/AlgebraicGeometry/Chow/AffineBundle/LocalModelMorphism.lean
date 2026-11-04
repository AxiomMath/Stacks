module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelBaseChange

/-!
# The structure morphism of the local model of an affine bundle

The local model `B[z₁, z₂]/(z₁z₂ - f)` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModel` is free, hence flat, and of finite
type over `B`. This file reads those two facts as properties of the morphism of schemes
`Spec(B[z₁, z₂]/(z₁z₂ - f)) ⟶ Spec B`, which is the form in which an affine-local presentation of
the scheme of [Stacks, Tag 0F97] would consume them.

## Main definitions

* `Stacks.AffineBundle.localModelSpecMap` — **the structure morphism
  `Spec(B[z₁, z₂]/(z₁z₂ - f)) ⟶ Spec B`.**

## Main results

* `Stacks.AffineBundle.flat_localModelSpecMap` — **the structure morphism is flat.**
* `Stacks.AffineBundle.locallyOfFiniteType_localModelSpecMap` — **the structure morphism is
  locally of finite type.**

## Implementation notes

Both are the `Spec` criterion of a `HasRingHomProperty`, with the ring-level statement supplied by
`Stacks.AffineBundle.instFlatLocalModel` and `Stacks.AffineBundle.instFiniteTypeLocalModel`
through `RingHom.flat_algebraMap_iff` and `RingHom.finiteType_algebraMap`.

*What this does not give.* The **relative dimension** of this morphism does not follow from the
two properties above. `AlgebraicGeometry.RelativeDimension` is defined in this repository by
`topologicalKrullDim` of the fibres, so flatness together with being locally of finite type says
nothing about its value: it has to be computed from the fibres. That computation is
`Stacks.AffineBundle.relativeDimension_localModelSpecMap` in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelRelativeDimension`. By
`Stacks.AffineBundle.baseChangeEquiv` the fibre over a prime `p` of `B` is the local model over the
residue field `κ(p)` of the image of `f`, which is `κ(p)[z, z^{-1}]` when `f ∉ p` and
`κ(p)[z₁, z₂]/(z₁z₂)` when `f ∈ p`; both are hypersurfaces in the affine plane over a field, hence
equidimensional of Krull dimension one, and that is how the value `1` is obtained there, with no
case distinction on `f`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AffineBundle

variable (B : Type u) [CommRing B] (f : B)

/-- **The structure morphism `Spec(B[z₁, z₂]/(z₁z₂ - f)) ⟶ Spec B` of the local model.** -/
def localModelSpecMap :
    Spec (CommRingCat.of (LocalModel B f)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (LocalModel B f)))

/-- **The structure morphism of the local model is flat**, the local model being free over the
base. -/
instance flat_localModelSpecMap : AlgebraicGeometry.Flat (localModelSpecMap B f) := by
  refine AlgebraicGeometry.Flat.SpecMap_iff.mpr ?_
  have hf : (algebraMap B (LocalModel B f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  simpa only [CommRingCat.hom_ofHom] using hf

/-- **The structure morphism of the local model is locally of finite type**, the local model being
a quotient of a polynomial ring in two variables over the base. -/
instance locallyOfFiniteType_localModelSpecMap :
    LocallyOfFiniteType (localModelSpecMap B f) := by
  refine AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr ?_
  have hf : (algebraMap B (LocalModel B f)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  simpa only [CommRingCat.hom_ofHom] using hf

end Stacks.AffineBundle

end
