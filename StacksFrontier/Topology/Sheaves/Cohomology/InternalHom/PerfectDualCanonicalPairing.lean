module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedPullbackOfADual
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Moving a perfect factor across the derived tensor product of Tag 06YU

Let `(X, O_X)` be a ringed space and `K` a perfect object of `D(O_X)` with dual
`K^∨ = RSheafHom(K, O_X)`. `Stacks.SheafOfModules.exactPairingDerivedDual` (Stacks 0FPC) makes
`(K, K^∨)` an exact pairing for `Stacks.SheafOfModules.derivedMonoidalStructure`, whose tensor
product is `Stacks.SheafOfModules.derivedTensor` on the nose. The derived tensor product used by
Fourier–Mukai transforms, the projection formula and the derived pullback is instead
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the tensor product on the nose of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`; the two bifunctors are not
definitionally equal, and are compared by `Stacks.SheafOfModules.derivedTensorCanonicalIso`.

Both monoidal structures are re-seatings of the one monoidal structure
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, with the same unit, so the exact pairing
transports from the first to the second: that is
`Stacks.SheafOfModules.exactPairingDerivedDualCanonical`
(`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedPullbackOfADual`).
With it, Mathlib's
`CategoryTheory.tensorRightHomEquiv`, `CategoryTheory.tensorLeftHomEquiv` and their naturality
apply verbatim to `derivedTensorProductFunctor`, together with the associator and the Koszul
braiding of `canonicalDerivedMonoidal` and `canonicalDerivedSymmetric` (and
`CategoryTheory.BraidedCategory.exactPairing_swap` for the pairing `(K^∨, K)`).

## Main definitions

* `Stacks.SheafOfModules.derivedTensorRightHomEquiv`,
  `Stacks.SheafOfModules.derivedTensorLeftHomEquiv`: `Hom(A ⊗^L K, B) = Hom(A, B ⊗^L K^∨)` and
  `Hom(K ⊗^L A, B) = Hom(A, K^∨ ⊗^L B)` for `derivedTensorProductFunctor`. Their naturality is
  Mathlib's `tensorRightHomEquiv_naturality` and `tensorLeftHomEquiv_naturality`, read with the
  same local instances.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K : DerivedCategory (StructureSheafModules Rc))

/-- **`Hom(A ⊗^L K, B) = Hom(A, B ⊗^L K^∨)`** for a perfect `K`, with `⊗^L` the derived tensor
product of Tag 06YU: Mathlib's `CategoryTheory.tensorRightHomEquiv` for the exact pairing
`exactPairingDerivedDualCanonical`. -/
def derivedTensorRightHomEquiv (hK : (ringedSite Rc).IsPerfect K)
    (A B : DerivedCategory (StructureSheafModules Rc)) :
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj A).obj K ⟶ B) ≃
      (A ⟶ ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj B).obj
        (derivedDual Rc K)) :=
  @tensorRightHomEquiv _ _ (DerivedMonoidal.canonicalDerivedMonoidal Rc) A K (derivedDual Rc K) B
    (exactPairingDerivedDualCanonical Rc K hK)

/-- **`Hom(K ⊗^L A, B) = Hom(A, K^∨ ⊗^L B)`** for a perfect `K`, with `⊗^L` the derived tensor
product of Tag 06YU: Mathlib's `CategoryTheory.tensorLeftHomEquiv` for the exact pairing
`(K^∨, K)`, the swap (`CategoryTheory.BraidedCategory.exactPairing_swap`, for the Koszul symmetry
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`) of
`exactPairingDerivedDualCanonical`. -/
def derivedTensorLeftHomEquiv (hK : (ringedSite Rc).IsPerfect K)
    (A B : DerivedCategory (StructureSheafModules Rc)) :
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj K).obj A ⟶ B) ≃
      (A ⟶ ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj
        (derivedDual Rc K)).obj B) :=
  @tensorLeftHomEquiv _ _ (DerivedMonoidal.canonicalDerivedMonoidal Rc) A (derivedDual Rc K) K B
    (@BraidedCategory.exactPairing_swap _ _ (DerivedMonoidal.canonicalDerivedMonoidal Rc)
      (DerivedMonoidal.canonicalDerivedSymmetric Rc).toBraidedCategory K (derivedDual Rc K)
      (exactPairingDerivedDualCanonical Rc K hK))

end Stacks.SheafOfModules

end
