module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentityPieces

/-!
# Pure tensors killed by a map into a complex concentrated in degree zero

Let `K` and `L` be complexes of `S`-modules and `q : L ⟶ M[0]` a chain map into a module placed in
degree zero.  The map `K ⊗ L ⟶ K ⊗ M[0]` induced by `q` on the tensor product complex kills every
pure tensor `k ⊗ z` of bidegree `(a, b)` with `b ≠ 0`, since `M[0]` vanishes in degree `b`.  This
is one of the pieces of the chain-level identity behind [Stacks, Tag 0E2A].

## Main results

* `Dualizing.mapBifunctorMap_f_ι_tmul_eq_zero_of_single` — the vanishing.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

/-- On the summand of bidegree `(a, b)` with `b ≠ 0`, a map into a complex concentrated in degree
zero kills every pure tensor. -/
theorem mapBifunctorMap_f_ι_tmul_eq_zero_of_single.{u₁, w₁} {S : Type u₁} [CommRing S]
    (K : CochainComplex (ModuleCat.{max u₁ w₁} S) ℤ)
    {L : CochainComplex (ModuleCat.{max u₁ w₁} S) ℤ} {M : ModuleCat.{max u₁ w₁} S}
    (q : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{max u₁ w₁} S) 0).obj M)
    (a b n : ℤ) (hab : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (hb : b ≠ 0) (k : K.X a) (z : L.X b) :
    ((HomologicalComplex.mapBifunctorMap (𝟙 K) q (moduleTensor.{u₁, w₁} S)
        (ComplexShape.up ℤ)).f n).hom
      ((HomologicalComplex.ιMapBifunctor K L (moduleTensor.{u₁, w₁} S) (ComplexShape.up ℤ)
        a b n hab).hom (k ⊗ₜ[S] z)) = 0 := by
  rw [mapBifunctorMap_f_ι_tmul]
  have hq : q.f b = 0 :=
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M b hb).eq_of_tgt _ _
  rw [hq, ModuleCat.hom_zero, LinearMap.zero_apply, TensorProduct.tmul_zero]
  exact (HomologicalComplex.ιMapBifunctor _ _ (moduleTensor.{u₁, w₁} S) (ComplexShape.up ℤ)
    a b n hab).hom.map_zero

end Dualizing

end
