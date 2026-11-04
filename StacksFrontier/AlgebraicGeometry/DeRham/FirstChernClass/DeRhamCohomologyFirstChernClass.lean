module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.RealizationChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HypercohomologyBridge

/-!
# The de Rham first Chern class in relative de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` with local
stalks and let `Ω^•` be the relative de Rham complex. The de Rham first Chern class
`c₁^{dR}(L)` of an invertible module ([Stacks, Section 0FLE]) is formed by logarithmic
differentiation in the abelian-sheaf realization `deRhamCohomologyAbelian` of de Rham cohomology,
because `d log` is only additive. The morphisms of Remark 0FU7 are attached to classes of
`deRhamCohomology`, the realization by derived global sections of sheaves of `A`-modules. This file
records the comparison of the two realizations ([Stacks, Tag 01F1]) and the first Chern class in
the second one.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology`: the
  identification `deRhamCohomologyAbelian B D n ≅ deRhamCohomology B D n` of abelian groups.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass`: **`c₁^{dR}(L)` as a class of
  `deRhamCohomology B D 2`**.

## References

* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The two realizations of relative de Rham cohomology agree** ([Stacks, Tag 01F1]): the
hypercohomology of the de Rham complex read in abelian sheaves is relative de Rham cohomology,
computed by derived global sections of sheaves of `A`-modules, with its module structure
forgotten. -/
def deRhamCohomologyAbelianIsoDeRhamCohomology (n : ℤ) :
    deRhamCohomologyAbelian B D n ≅
      (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (deRhamCohomology B D n) :=
  deRhamCohomologyAbelianIso B D n ≪≫
    (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).mapIso
      (hypercohomologyIsoDeRhamCohomology B D n)

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **The de Rham first Chern class `c₁^{dR}(L) ∈ H²_{dR}`** of an invertible module
([Stacks, Section 0FLE]), as a class of `deRhamCohomology B D 2`: the class
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelianOf` formed by logarithmic
differentiation, carried by the comparison of the two realizations. -/
def deRhamCohomologyFirstChernClass (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L) :
    deRhamCohomology B D 2 :=
  (deRhamCohomologyAbelianIsoDeRhamCohomology B D 2).hom.hom
    (deRhamFirstChernClassAbelianOf B D L hL)

end AlgebraicGeometry.SheafOfModules

end
