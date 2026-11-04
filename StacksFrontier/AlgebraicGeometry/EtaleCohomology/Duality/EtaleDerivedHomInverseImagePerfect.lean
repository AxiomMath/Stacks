module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleDerivedHomInverseImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleDerivedLocallyConstantPerfect
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TransportedHomComparisonDualizable
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAssociatorOfToposHom
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualLeftDual
public import StacksFrontier.CategoryTheory.Monoidal.ReseatExactPairing

/-!
# The inverse image of `RHom` out of a perfect complex on `D(X_étale, Λ)`

Let `g : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. The comparison of
Stacks 08JF for the étale inverse image,

`g⁻¹ RHom_Λ(K, M) ⟶ RHom_Λ(g⁻¹K, g⁻¹M)`

(`Stacks.EtaleCohomology.etaleDerivedInverseImageHomComparison`, the transpose of `g⁻¹` of the
evaluation read through the comparison `etaleDerivedInverseImageTensorIso` of Stacks 07A4), is an
isomorphism whenever `K` is perfect on the constant ringed site `(Y_étale, Λ̲)`, for every `M`
(`Stacks.EtaleCohomology.isIso_etaleDerivedInverseImageHomComparison_of_isPerfect`). Over a field
`Λ` this applies to every bounded `K` whose cohomology sheaves are locally constant of finite type
(`isIso_etaleDerivedInverseImageHomComparison_of_isFiniteTypeLocallyConstant`), in particular at
a geometric point `g = x.hom`, as in the stalk computation of the duality morphism of a smooth
proper curve in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## The route

A perfect object is dualizable (Stacks 0FPU,
`AlgebraicGeometry.RingedSite.derivedDualExactPairing`), and a functor carrying a tensor comparison
compatible with the associativity constraints carries internal Homs out of a dualizable object to
internal Homs (`StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizableAssociative`). The
comparison of Stacks 07A4 for a morphism of ringed topoi is compatible with the associativity
constraints (`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator`); its
compatibility with the unit constraints is not needed — any isomorphism `Lg^*(Λ̲) ≅ Λ̲` is
enough, and `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral` is one.
The pairing of Stacks 0FPU is read in the monoidal structure
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, whose tensor product is the
derived tensor product `etaleDerivedTensor` is built from, on the nose, by
`CategoryTheory.MonoidalCategory.exactPairingReseatOfReseat`; the whole statement is then an
instance of `TensorHomAdjunction.isIso_transportHomComparison_of_exactPairing`.

The statements consume `Stacks.EtaleCohomology.etaleDerivedHom`, defined in the standard model
`HasDerivedCategory.standard` of the derived category, as a local instance.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleDerivedInverseImageHomComparison_of_isPerfect`.
* `isIso_etaleDerivedInverseImageHomComparison_of_isFiniteTypeLocallyConstant`:
  the case of locally constant cohomology over a field.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **Stacks 08JF for the étale inverse image, out of a perfect complex.** For a morphism of
schemes `g : X ⟶ Y`, a complex `K` on `Y_étale` which is perfect on the constant ringed site
`(Y_étale, Λ̲)` and any `M`, the comparison `g⁻¹ RHom_Λ(K, M) ⟶ RHom_Λ(g⁻¹K, g⁻¹M)` is an
isomorphism. -/
theorem isIso_etaleDerivedInverseImageHomComparison_of_isPerfect
    (K M : DerivedCategory (EtaleModules.{u, r} Λ Y))
    (hK : (etaleRingedSite.{u, r} Λ Y).IsPerfect
      ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K)) :
    IsIso (etaleDerivedInverseImageHomComparison.{u, r} Λ g K M) := by
  obtain ⟨p, -, -⟩ := AlgebraicGeometry.RingedSite.exists_exactPairing_derivedDual _ _ hK
  let iY := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (etaleRingedSite.{u, r} Λ Y).O
  let iX := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal
    (etaleRingedSite.{u, r} Λ X).O
  have hp : ExactPairing ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K)
      (AlgebraicGeometry.RingedSite.derivedDual (etaleRingedSite.{u, r} Λ Y)
        ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K)) :=
    @MonoidalCategory.exactPairingReseatOfReseat _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (etaleRingedSite.{u, r} Λ Y).O)
      _ _ _ _ _ _ _ _ p
  rw [etaleDerivedInverseImageHomComparison]
  have key := TensorHomAdjunction.isIso_transportHomComparison_of_exactPairing
    (etaleDerivedEquivalence.{u, r} Λ Y) (etaleDerivedEquivalence.{u, r} Λ X)
    (Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal _)
    (Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal _)
    (etaleDerivedInverseImageTensorIso.{u, r} Λ g)
    (etaleRingedDerivedPullbackIso.{u, r} Λ g)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (etaleRingedToposHom.{u, r} Λ g)) rfl
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom _)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom _)
    (fun A B E =>
      heq_of_eq (Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom_eq _ A B E))
    (fun A B E =>
      heq_of_eq (Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom_eq _ A B E))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator
      (etaleRingedToposHom.{u, r} Λ g))
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral
      (etaleRingedToposHom.{u, r} Λ g))
    (etaleTensorHomAdjunction.{u, r} Λ Y) (etaleTensorHomAdjunction.{u, r} Λ X) K M
    (AlgebraicGeometry.RingedSite.derivedDual (etaleRingedSite.{u, r} Λ Y)
        ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K))
  convert key using 3

/-- **The comparison of Stacks 08JF is an isomorphism out of a complex with locally constant
cohomology of finite type over a field.** Let `Λ` be a field and `K` a bounded complex on
`Y_étale` whose cohomology sheaves are locally constant of finite type. Then for every morphism
`g : X ⟶ Y` (in particular for a geometric point) and every `M`,
`g⁻¹ RHom(K, M) ⟶ RHom(g⁻¹K, g⁻¹M)` is an isomorphism: `K` is perfect on `(Y_étale, Λ̲)`
(`isPerfect_etaleDerivedEquivalence_functor_obj`). -/
theorem isIso_etaleDerivedInverseImageHomComparison_of_isFiniteTypeLocallyConstant
    (Λ : Type) [Field Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K M : DerivedCategory (EtaleModules.{u, 0} Λ Y)) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      Y.smallEtaleTopology Λ ((DerivedCategory.homologyFunctor _ n).obj K)) :
    IsIso (etaleDerivedInverseImageHomComparison.{u, 0} Λ g K M) :=
  isIso_etaleDerivedInverseImageHomComparison_of_isPerfect Λ g K M
    (isPerfect_etaleDerivedEquivalence_functor_obj K a b hK)

end Stacks.EtaleCohomology

end
