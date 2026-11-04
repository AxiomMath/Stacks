module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct

/-!
# The cup product on relative de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex of `φ`. Combining the cup product of Cohomology,
Section 0FKU with the wedge product

`∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•`

of Tag 0FM2 gives the `A(X)`-bilinear cup product of Section 50.4

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`.

The pairing along an arbitrary multiplication of complexes is
`AlgebraicGeometry.SheafOfModules.canonicalPairingModule`: the pairing of the global cup product
`Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace` of the ringed space `(X, A)`,
followed by the canonical map from the derived to the ordinary tensor product and by the
multiplication. This file reads it, along the wedge product, on the module realization
`AlgebraicGeometry.SheafOfModules.deRhamCohomology` of de Rham cohomology, element by element,
for an arbitrary package of algebras `B` and de Rham differential `D` on the sheaf of relative
differentials of `φ`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyToModule`: a de Rham cohomology class read
  as a class in the cohomology of the derived global sections of the de Rham complex, the module
  `canonicalPairingModule` is stated on; this is the identity on elements.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup`: **the cup product on de Rham
  cohomology**, `ξ ∪ η`, with `ξ` the first factor.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_add_left`,
  `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_add_right`,
  `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_smul_left` and
  `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_smul_right`: the cup product is bilinear
  over the ring `A(X)` of global sections of the base ring sheaf.

## Implementation notes

`deRhamCohomology B D n` is a module over the `RingCat`-valued section ring
`(underlyingRingSheaf A).obj.obj (op ⊤)`, while `canonicalPairingModule` is a morphism of modules
over the `CommRingCat`-valued `baseRing (baseRingedSpace A)`, the ring the tensor product is
formed over. The two rings, and the two module categories' objects, are definitionally equal, but
instance search does not cross between them, so the classes are passed through
`deRhamCohomologyToModule` before being tensored.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- A de Rham cohomology class, read as a class in the cohomology of the derived global sections
of the de Rham complex over the ringed space `(X, A)`, which is the module
`AlgebraicGeometry.SheafOfModules.canonicalPairingModule` is stated on. The two are the same
module, so this is the identity on elements. -/
abbrev deRhamCohomologyToModule (n : ℤ) (ξ : deRhamCohomology B D n) :
    cohomologyModule (moduleDerived (deRhamComplex B D)) n :=
  ξ

/-- **The cup product on relative de Rham cohomology**

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`

of Section 50.4: the cup product of Cohomology, Section 0FKU, i.e. the pairing of the global cup
product of the ringed space `(X, A)` followed by the canonical map from the derived to the
ordinary tensor product, composed with the wedge product `Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` of Tag 0FM2.
The class `ξ` is the first factor. -/
def deRhamCohomologyCup (i j : ℤ) (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    deRhamCohomology B D (i + j) :=
  (canonicalPairingModule (wedgeProduct B D) i j).hom
    (deRhamCohomologyToModule B D i ξ ⊗ₜ deRhamCohomologyToModule B D j η)

/-- The cup product on de Rham cohomology is additive in its first variable. -/
theorem deRhamCohomologyCup_add_left (i j : ℤ) (ξ ξ' : deRhamCohomology B D i)
    (η : deRhamCohomology B D j) :
    deRhamCohomologyCup B D i j (ξ + ξ') η =
      deRhamCohomologyCup B D i j ξ η + deRhamCohomologyCup B D i j ξ' η :=
  (congrArg _ (TensorProduct.add_tmul ..)).trans (map_add ..)

/-- The cup product on de Rham cohomology is additive in its second variable. -/
theorem deRhamCohomologyCup_add_right (i j : ℤ) (ξ : deRhamCohomology B D i)
    (η η' : deRhamCohomology B D j) :
    deRhamCohomologyCup B D i j ξ (η + η') =
      deRhamCohomologyCup B D i j ξ η + deRhamCohomologyCup B D i j ξ η' :=
  (congrArg _ (TensorProduct.tmul_add ..)).trans (map_add ..)

/-- The cup product on de Rham cohomology is linear over the global sections of the base ring
sheaf in its first variable. -/
theorem deRhamCohomologyCup_smul_left (i j : ℤ) (a : (underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    deRhamCohomologyCup B D i j (a • ξ) η = a • deRhamCohomologyCup B D i j ξ η := by
  let a' : Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A) := a
  exact (congrArg (canonicalPairingModule (wedgeProduct B D) i j).hom
    (TensorProduct.smul_tmul' a' (deRhamCohomologyToModule B D i ξ)
      (deRhamCohomologyToModule B D j η)).symm).trans (map_smul _ a' _)

/-- The cup product on de Rham cohomology is linear over the global sections of the base ring
sheaf in its second variable. -/
theorem deRhamCohomologyCup_smul_right (i j : ℤ) (a : (underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    deRhamCohomologyCup B D i j ξ (a • η) = a • deRhamCohomologyCup B D i j ξ η := by
  let a' : Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A) := a
  exact (congrArg (canonicalPairingModule (wedgeProduct B D) i j).hom
    (TensorProduct.tmul_smul a' (deRhamCohomologyToModule B D i ξ)
      (deRhamCohomologyToModule B D j η))).trans (map_smul _ a' _)

end AlgebraicGeometry.SheafOfModules

end
