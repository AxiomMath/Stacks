module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.BaseChangeFlat

/-!
# Faithful flatness from flat self-base change

If both coprojections of an algebra into its tensor square are flat and the structure map is
universally injective, then the structure map is faithfully flat.

The two coprojections are `Algebra.TensorProduct.includeLeft` and
`Algebra.TensorProduct.includeRight`. Flatness of the left one says `C ⊗[B] C` is flat over `C`
for the left algebra structure, which descends to flatness of `C` over `B` along the
universally injective map `B → C`. Universal injectivity also forces `B ⊗[B] N` to be trivial
whenever `C ⊗[B] N` is, so base change along `B → C` reflects triviality of modules; together
with flatness that is faithful flatness.

## Main results

* `Algebra.faithfullyFlat_of_flat_selfTensor_of_universallyInjective`: faithful flatness of the
  structure map.

## References

* [Stacks Project, Tag 0GRM](https://stacks.math.columbia.edu/tag/0GRM)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

/-- A universally injective ring map whose two self-base-change coprojections are flat is
faithfully flat. -/
@[stacks 0GRM]
theorem faithfullyFlat_of_flat_selfTensor_of_universallyInjective
    {B : Type u} [CommRing B] {C : Type u} [CommRing C] [Algebra B C]
    (hleft : ((Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C).toRingHom).Flat)
    (_hright : ((Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom).Flat)
    (hBC : Algebra.UniversallyInjective B C) :
    (algebraMap B C).FaithfullyFlat := by
  have hflatB : Module.Flat B C := by
    let : Algebra C (C ⊗[B] C) := Algebra.TensorProduct.leftAlgebra
    have hflatC : Module.Flat C (C ⊗[B] C) :=
      RingHom.flat_algebraMap_iff.mp (by
        convert hleft using 1
        ext c
        rfl)
    exact (Module.flat_iff_baseChange_of_universallyInjective hBC C).mpr hflatC
  apply RingHom.faithfullyFlat_algebraMap_iff.mpr
  refine (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality B C).mpr
    ⟨hflatB, ?_⟩
  intro N _ _ h
  have : Subsingleton (B ⊗[B] N) := (hBC N).subsingleton
  exact (_root_.TensorProduct.lid B N).toEquiv.subsingleton_congr.mp this

end Algebra

end
