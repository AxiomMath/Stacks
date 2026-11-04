module

public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor

@[expose] public noncomputable section

/-!
# The canonical derived tensor product as a `DerivedTensorData.DerivedTensorProduct`

The statements of tag 0G3N and its consequences in
`StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor` are quantified over a bundle
`DerivedTensorData.DerivedTensorProduct R`: a bifunctor on `D(R)` whose restriction along a
module in degree zero is the total left derived functor of termwise tensoring by that module,
together with the comparison maps exhibiting it as such and the shift and triangulated
structures on those restrictions. This file exhibits such a bundle, so that those statements
are not vacuous: it is the canonical derived tensor product of Stacks 0BYI, certified by the
canonical 0652 comparison of
`StacksFrontier.Homology.TorAmplitude.CanonicalCertificate`.

## Main definitions

* `DerivedTensorData.canonicalDerivedTensorProduct`: the canonical derived tensor product of
  Stacks 0BYI, read as a `DerivedTensorData.DerivedTensorProduct`.
* `DerivedTensorData.canonicalSymmetry`: its symmetry, the Koszul braiding of Stacks 0BYI.

## Main results

* `Stacks.AdicSystem.IdealPowerTensorComparison.derivedTensor_idealPowers_proIsomorphic`
  (tag 0G3N) and
  `Stacks.AdicSystem.IdealPowerDerivedTensor.idealPowerInclusion_factors_through_derivedTensor`
  (tag 0928), each stated for the canonical derived tensor product rather than for an assumed
  bundle. The forms general in the bundle carry the suffix `_of_data`.

## Implementation notes

The two universe parameters of `DerivedTensorData.DerivedTensorProduct` are taken equal: the
canonical derived tensor product of Stacks 0BYI is a bifunctor on `D(ModuleCat.{u} R)` for
`R : Type u`, because Mathlib's monoidal structure on `ModuleCat` requires the module universe
to agree with the ring's.

The `comparison` field's type is stated with `DerivedTensorData.tensorModuleRight`, while the
canonical comparison map is stated with `StacksDraft.TorAmplitude.tensorModuleRight`. These are
two separate declarations with identical bodies, in two modules neither of which imports the
other; both are exposed, so the two types are definitionally equal, and the fields below are
given by terms whose elaboration performs that unfolding.

Stacks 0BYI is registered by `StacksFrontier.Homology.Tor.DerivedTensor`; the structure
instantiated here is the bundle declared in
`StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor`.

## References

* [The Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [The Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [The Stacks Project, Tag 0G3N](https://stacks.math.columbia.edu/tag/0G3N)
-/

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedTensorData

/-- The canonical derived tensor product of Stacks 0BYI, read as a derived tensor product in the
sense of `DerivedTensorData.DerivedTensorProduct`: its bifunctor, the canonical 0652 comparison
with termwise tensoring by a module in degree zero, the universal property identifying each
restriction with a total left derived functor, and the shift and triangulated structures coming
from exactness in the first variable. -/
public def canonicalDerivedTensorProduct (A : Type u) [CommRing A] :
    DerivedTensorProduct.{u, u} A where
  tensor := (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
  comparison M := StacksDraft.TorAmplitude.canonicalTensorComparison A M
  isLeftDerived M := StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A M
  commShift _ :=
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).commShift_left _
  triangulated _ :=
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).exact_left _

/-- The symmetry of the canonical derived tensor product: the Koszul braiding of Stacks 0BYI,
whose representatives on K-flat complexes are the signed interchange maps. -/
public def canonicalSymmetry (A : Type u) [CommRing A] :
    (canonicalDerivedTensorProduct A).tensor ≅ (canonicalDerivedTensorProduct A).tensor.flip :=
  (CochainComplex.DerivedTensor.derivedTensorProductKoszulBraiding A).iso

end DerivedTensorData

namespace Stacks.AdicSystem.IdealPowerTensorComparison

open CategoryTheory.Limits Opposite

/-- **Stacks Project, Tag 0G3N.** For a bounded complex of finite modules over a Noetherian
ring, the inverse system of maps `Iⁿ ⊗ᴸ M → Iⁿ M` formed from the canonical derived tensor
product is an isomorphism of pro-objects in the derived category. The displayed identities are
the two-sided inverse identities after cofinal refinement. -/
@[stacks 0G3N]
public theorem derivedTensor_idealPowers_proIsomorphic {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → IsZero (M.X i))
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    ∃ (t : ∀ n, idealPowerComplex M I (n + 1) ⟶ idealPowerComplex M I n)
      (_ht : ∀ n, t n ≫ image.ι (idealPowerMultiplication M I n) =
        image.ι (idealPowerMultiplication M I (n + 1)))
      (α : derivedTensorIdealSystem (DerivedTensorData.canonicalDerivedTensorProduct A)
          (DerivedTensorData.canonicalSymmetry A) M I ⟶ idealPowerSystem M I t),
      (∀ n, α.app (op n) = derivedToIdealPowerMap
        (DerivedTensorData.canonicalDerivedTensorProduct A)
        (DerivedTensorData.canonicalSymmetry A) M I n) ∧
      ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
        (s : (idealPowerSystem M I t).obj (op m) ⟶
          (derivedTensorIdealSystem (DerivedTensorData.canonicalDerivedTensorProduct A)
            (DerivedTensorData.canonicalSymmetry A) M I).obj (op n)),
        α.app (op m) ≫ s =
            (derivedTensorIdealSystem (DerivedTensorData.canonicalDerivedTensorProduct A)
              (DerivedTensorData.canonicalSymmetry A) M I).map (homOfLE h).op ∧
          s ≫ α.app (op n) = (idealPowerSystem M I t).map (homOfLE h).op :=
  derivedTensor_idealPowers_proIsomorphic_of_data _ _ I M hbounded hfinite

end Stacks.AdicSystem.IdealPowerTensorComparison

namespace Stacks.AdicSystem.IdealPowerDerivedTensor

open CategoryTheory.Limits Opposite

universe v

/-- **Stacks Project, Tag 0928.** For a finite module over a Noetherian ring, the inclusion of
some positive ideal power factors through the canonical map from the canonical derived tensor
product with the ideal. The index `n` represents the positive exponent `n + 1`. -/
@[stacks 0928]
public theorem idealPowerInclusion_factors_through_derivedTensor
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{v} A) [Module.Finite A M] :
    letI := Module.Finite.small.{u} A M
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (Shrink.{u} M))
    ∃ n : ℕ,
      ∃ f : DerivedCategory.Q.obj
          (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerComplex K I n) ⟶
          (Stacks.AdicSystem.IdealPowerTensorComparison.derivedTensorIdealSystem
            (DerivedTensorData.canonicalDerivedTensorProduct A)
            (DerivedTensorData.canonicalSymmetry A) K I).obj (op 0),
        f ≫
            (Stacks.AdicSystem.IdealPowerTensorComparison.derivedToIdealPowerMap
                (DerivedTensorData.canonicalDerivedTensorProduct A)
                (DerivedTensorData.canonicalSymmetry A) K I 0 ≫
              DerivedCategory.Q.map
                (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I
                  0))) =
          DerivedCategory.Q.map
            (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I n))
              :=
  idealPowerInclusion_factors_through_derivedTensor_of_data _ _ I M

end Stacks.AdicSystem.IdealPowerDerivedTensor

end
