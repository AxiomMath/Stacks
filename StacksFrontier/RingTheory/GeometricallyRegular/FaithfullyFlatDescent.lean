module

public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent

@[expose] public section

universe u v w

/-!
# Geometric regularity descends along a faithfully flat map of algebras

Let `k` be a field and let `A → B` be a faithfully flat map of `k`-algebras. If `B` is
geometrically regular over `k`, then so is `A`.

## Main results

* `Stacks.GeometricallyRegular.FlatDescent.solution`: a `k`-algebra admitting a faithfully flat
  `k`-algebra which is geometrically regular over `k` is itself geometrically regular over `k`.
* `Algebra.IsGeometricallyRegular.of_faithfullyFlat`: the same statement, in the namespace
  `Algebra`.

## References

* [Stacks 07NH](https://stacks.math.columbia.edu/tag/07NH)
-/

open scoped TensorProduct

@[expose] public section

namespace Stacks.GeometricallyRegular.FlatDescent

/-- Extending the scalars of `B` from `A` to `A ⊗[k] K` gives the base change of `B` from `k` to
`K`: the ring isomorphism `(A ⊗[k] K) ⊗[A] B ≃+* K ⊗[k] B`. -/
private def baseChangeCompRingEquiv (k A B K : Type*) [CommRing k] [CommRing A] [CommRing B]
    [CommRing K] [Algebra k A] [Algebra k B] [Algebra k K] [Algebra A B] [IsScalarTower k A B] :
    ((A ⊗[k] K) ⊗[A] B) ≃+* (K ⊗[k] B) :=
  ((Algebra.TensorProduct.comm A B (A ⊗[k] K)).symm.trans
    (Algebra.TensorProduct.cancelBaseChange k A A B K)).toRingEquiv.trans
      (Algebra.TensorProduct.comm k B K).toRingEquiv

/-- Regularity of a base change descends along a faithfully flat map: if `A → B` is a faithfully
flat map of `k`-algebras and `K` is a `k`-algebra with `K ⊗[k] B` regular, then `K ⊗[k] A` is
regular. -/
private theorem isRegularRing_tensorProduct_of_faithfullyFlat {k A K : Type*} (B : Type*)
    [CommRing k] [CommRing A] [CommRing B] [CommRing K] [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [IsScalarTower k A B] [Module.FaithfullyFlat A B] [IsRegularRing (K ⊗[k] B)] :
    IsRegularRing (K ⊗[k] A) :=
  have : IsRegularRing ((A ⊗[k] K) ⊗[A] B) := .of_ringEquiv (baseChangeCompRingEquiv k A B K).symm
  have : IsRegularRing (A ⊗[k] K) := .of_faithfullyFlat ((A ⊗[k] K) ⊗[A] B)
  .of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv

/-- Let `k` be a field and let `A → B` be a faithfully flat map of `k`-algebras. If `B` is
geometrically regular over `k`, then so is `A`. -/
public theorem solution {k : Type u} {A : Type v} (B : Type w)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Module.FaithfullyFlat A B] [Algebra.IsGeometricallyRegular k B] :
    Algebra.IsGeometricallyRegular k A :=
  ⟨fun _ ↦ isRegularRing_tensorProduct_of_faithfullyFlat B⟩

end Stacks.GeometricallyRegular.FlatDescent

end

@[expose] public section

namespace Algebra

/-- **Geometric regularity descends through faithfully flat maps of algebras.**
Let `k` be a field and let `A → B` be a faithfully flat map of `k`-algebras. If `B` is
geometrically regular over `k`, then so is `A`. -/
@[stacks 07NH "The source's faithfully flat `k`-algebra map `A → B` is `Algebra A B` with \
  `IsScalarTower k A B` and `Module.FaithfullyFlat A B`, the latter being \
  `(algebraMap A B).FaithfullyFlat` by `RingHom.faithfullyFlat_algebraMap_iff`; geometric \
  regularity is `Algebra.IsGeometricallyRegular` (Definition 0382), which already implies the \
  Noetherianness the source assumes. Named after the sibling 07NG, \
  `IsRegularRing.of_faithfullyFlat`. See the module docstring."]
public theorem IsGeometricallyRegular.of_faithfullyFlat {k : Type u} {A : Type v} (B : Type w)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Module.FaithfullyFlat A B] [IsGeometricallyRegular k B] :
    IsGeometricallyRegular k A :=
  Stacks.GeometricallyRegular.FlatDescent.solution B

end Algebra

end
