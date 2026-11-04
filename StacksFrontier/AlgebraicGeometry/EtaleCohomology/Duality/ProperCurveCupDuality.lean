module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor

/-!
# The duality map of a relative curve

Let `f : X ⟶ S` be a morphism of schemes, `ℓ` a prime and `Λ = ℤ/ℓ`. Write `E = f⁻¹Λ_S` in
`D(X_étale, Λ)` and `K = Rf_* E` in `D(S_étale, Λ)` (unbounded derived functors). This file
defines the objects through which relative Poincaré duality for a smooth proper curve
(`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, part of [Tag 03VH]) is reduced to an
isomorphism in `D(S_étale, Λ)`:

* the cup product `K ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ E)`: the abstract cup product of the adjunction
  `f⁻¹ ⊣ Rf_*` and of the comparison `f⁻¹(A ⊗^L B) ≅ f⁻¹A ⊗^L f⁻¹B`, both on `D(-_étale, Λ)`;
* for a multiplication `w : E ⊗^L_Λ E ⟶ E` and a trace `t : K ⟶ Λ_S[-2]`, the **duality map**
  `D_{w,t} : K ⟶ RHom_Λ(K, Λ_S[-2])`, adjoint to the pairing `(a, b) ↦ t(w_*(b ∪ a))`.

The statements consume the derived categories in the standard model
`HasDerivedCategory.standard`, as a local instance, as the étale derived tensor product and
internal Hom do.

## Main definitions

* `Stacks.EtaleCohomology.curveDualityUnit`, `Stacks.EtaleCohomology.curveDualityComplex`.
* `Stacks.EtaleCohomology.curveDualityCup`.
* `Stacks.EtaleCohomology.curveDualityMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor

variable (ℓ : ℕ) {S X : Scheme.{u}} (f : X ⟶ S)

/-- `E = f⁻¹Λ_S`, the inverse image of the constant sheaf `ℤ/ℓ` placed in degree zero. -/
abbrev curveDualityUnit : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) X) :=
  (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))

/-- `K = Rf_*(f⁻¹Λ_S)`, for the unbounded derived direct image. -/
abbrev curveDualityComplex : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S) :=
  (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj (curveDualityUnit ℓ f)

/-- **The cup product** `K ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ E)`: the abstract cup product of the
adjunction `f⁻¹ ⊣ Rf_*` and of the comparison `f⁻¹(A ⊗^L B) ≅ f⁻¹A ⊗^L f⁻¹B` of
[Stacks, Tag 07A4], adjoint to the comparison followed by the counit in both factors. -/
def curveDualityCup :
    ((etaleDerivedTensor.{u, 0} (ZMod ℓ) S).obj (curveDualityComplex ℓ f)).obj
        (curveDualityComplex ℓ f) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
        (((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
          (curveDualityUnit ℓ f)) :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
    (etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f)
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) S))
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) X))
    (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f).hom
    (curveDualityUnit ℓ f) (curveDualityUnit ℓ f)

/-- **The duality map** `D_{w,t} : K ⟶ RHom_Λ(K, Λ_S[-2])` of a multiplication
`w : E ⊗^L_Λ E ⟶ E` and a trace `t : K ⟶ Λ_S[-2]`: the adjoint, for the tensor–internal-Hom
adjunction of [Stacks, Tag 08J8], of the pairing `K ⊗^L K ⟶ Λ_S[-2]`, `(a, b) ↦ t(w_*(b ∪ a))`. -/
def curveDualityMap
    (w : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    curveDualityComplex ℓ f ⟶
      ((etaleDerivedHom.{u, 0} (ZMod ℓ) S).obj (op (curveDualityComplex ℓ f))).obj
        (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧) :=
  ((etaleTensorHomAdjunction.{u, 0} (ZMod ℓ) S).homEquiv _ _ _).symm
    ((etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S _ _).inv ≫ curveDualityCup ℓ f ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).map w ≫ t)

end Stacks.EtaleCohomology

end
