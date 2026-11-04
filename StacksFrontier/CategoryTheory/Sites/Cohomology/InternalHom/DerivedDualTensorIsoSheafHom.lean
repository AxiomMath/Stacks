module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect

/-!
# The isomorphism `K^∨ ⊗^𝐋 M ≅ R𝓗om(K, M)` on a ringed site, with the dual on the left

`AlgebraicGeometry.RingedSite.derivedDualTensorIsoSheafHom` is an isomorphism of objects
`K^∨ ⊗^𝐋_𝒪 M ≅ R𝓗om(K, M)` for a perfect object `K` of the derived category of a ringed site,
obtained from `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` of [Stacks, Tag 08JJ]
by braiding and reading across the two packagings of the derived tensor product. As a
consequence, `AlgebraicGeometry.RingedSite.subsingleton_hom_of_isZero_homology_derivedTensorDual`
states that vanishing of the zeroth homology of the global sections of `K^∨ ⊗^𝐋 M` forces
`Hom(K, M)` to be a subsingleton.

## Main results

* `AlgebraicGeometry.RingedSite.derivedDualTensorIsoSheafHom` — `K^∨ ⊗^𝐋 M ≅ R𝓗om(K, M)` for a
  perfect `K`.
* `AlgebraicGeometry.RingedSite.subsingleton_hom_of_isZero_homology_derivedTensorDual` —
  `H⁰(C, K^∨ ⊗^𝐋 M) = 0` implies `Hom(K, M)` is a subsingleton.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

universe u

section OnARingedSite

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections (derivedModuleGlobalSections)
open Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- `K^∨ ⊗^𝐋_𝒪 M ≅ R𝓗om(K, M)` for a perfect `K`, at the structure-sheaf-indexed derived
tensor product: the isomorphism of [Stacks, Tag 08JJ],
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`, braided and read across the two
packagings of the derived tensor product. -/
def derivedDualTensorIsoSheafHom (K M : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
        (derivedDual X K)).obj M ≅ ((derivedSheafHomBifunctor X).obj (op K)).obj M :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso X
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)
      (derivedDual X K) M ≪≫
    (derivedTensorObjIso X M (derivedDual X K)).symm ≪≫
      derivedDualTensorSheafHomIso X K M hK

/-- Vanishing of `H⁰(C, K^∨ ⊗^𝐋 M)` forces `Hom_{D(𝒪)}(K, M)` to vanish, for a perfect `K`. -/
theorem subsingleton_hom_of_isZero_homology_derivedTensorDual
    (K M : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))) (hK : X.IsPerfect K)
    (h : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
          (derivedDual X K)).obj M)))) :
    Subsingleton (K ⟶ M) := by
  have h' : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj M))) :=
    h.of_iso (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections X).mapIso
        (derivedDualTensorIsoSheafHom X K M hK))).symm)
  have : Subsingleton
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((derivedSheafHomBifunctor X).obj (op K)).obj M)) : Type u) :=
    AddCommGrpCat.subsingleton_of_isZero h'
  exact (derivedSheafHomGlobalSectionsEquiv X K M).toEquiv.symm.subsingleton

end AlgebraicGeometry.RingedSite

end OnARingedSite

end
