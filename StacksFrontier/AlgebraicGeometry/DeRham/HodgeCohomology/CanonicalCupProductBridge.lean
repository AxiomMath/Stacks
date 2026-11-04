module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CanonicalCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct

/-!
# The module and the abelian realizations of the Hodge cup product agree

The base has a cup product on Hodge cohomology, `AlgebraicGeometry.SheafOfModules.hodgeCup`, on
the groups `R^iΓ(X, Ω^p)` of the abelian realization: the pairing
`AlgebraicGeometry.SheafOfModules.canonicalPairing` along the wedge product
`AlgebraicGeometry.SheafOfModules.hodgeSingleWedge` of `Ω^p[0]` and `Ω^q[0]`. The cup product
`AlgebraicGeometry.SheafOfModules.hodgeComponentCup` is stated on the groups
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent` of the module realization, along an
arbitrary multiplication of forms. This file shows that along the wedge product the two are one
pairing, read through the comparison of the two realizations.

## Main results

* `AlgebraicGeometry.SheafOfModules.singleMultiplication_exteriorProductComponent`: the
  multiplication of complexes concentrated in degree `0` induced by the wedge product is
  `hodgeSingleWedge`.
* `AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso`: `R^iΓ(X, Ω^p) ≅ H^i(X, Ω^p)`.
* `AlgebraicGeometry.SheafOfModules.hodgeComponentCup_exteriorProductComponent`: **along the
  wedge product, `hodgeComponentCup` is `hodgeCup`** read through `hodgeComponentAbelianIso`.

## References

* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The multiplication of complexes concentrated in degree `0` induced by the wedge product of
Tag 0FM2 is the base's `hodgeSingleWedge`. -/
theorem singleMultiplication_exteriorProductComponent (p q : ℕ) :
    singleMultiplication (exteriorProductComponent B p q) = hodgeSingleWedge B D p q := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    show (HomologicalComplex.mkHomToSingle (K := HomologicalComplex.mapBifunctor
        (singleNat (deRhamTerm B p)) (singleNat (deRhamTerm B q))
        (sheafTensor.{u, u, u, u, u} A) (up ℕ))
        (singleMultiplicationX (exteriorProductComponent B p q))
        (fun i hi => by change i + 1 = 0 at hi; omega)).f 0 =
      (HomologicalComplex.mkHomToSingle (K := HomologicalComplex.mapBifunctor
        (singleNat (deRhamTerm B p)) (singleNat (deRhamTerm B q))
        (sheafTensor.{u, u, u, u, u} A) (up ℕ))
        (HomologicalComplex.mapBifunctorDesc fun a b h => hodgeSingleWedgeSummand B D p q a b h)
        (fun i hi => by change i + 1 = 0 at hi; omega)).f 0
    rw [HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomToSingle_f]
    refine congrArg (· ≫ _) (HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_)
    rw [singleMultiplicationX, HomologicalComplex.ι_mapBifunctorDesc]
    refine Eq.trans ?_ (HomologicalComplex.ι_mapBifunctorDesc
      (fun a b h => hodgeSingleWedgeSummand B D p q a b h) i₁ i₂ h).symm
    show _ = ((sheafTensor.{u, u, u, u, u} A).obj ((singleNat (deRhamTerm B p)).X i₁)).map
        (HomologicalComplex.singleObjXIsoOfEq (up ℕ) 0 (deRhamTerm B q) i₂
          (by change i₁ + i₂ = 0 at h; omega)).hom ≫
      ((sheafTensor.{u, u, u, u, u} A).map
        (HomologicalComplex.singleObjXIsoOfEq (up ℕ) 0 (deRhamTerm B p) i₁
          (by change i₁ + i₂ = 0 at h; omega)).hom).app (deRhamTerm B q) ≫
      exteriorProductComponent B p q
    rw [← Category.assoc, ← Category.assoc, NatTrans.naturality]
  · exact (HomologicalComplex.isZero_single_obj_X (up ℕ) 0 _ n hn).eq_of_tgt _ _

/-- **The Hodge cohomology group in the abelian realization is the Hodge cohomology group in the
module realization**: `R^iΓ(X, Ω^p) ≅ H^n(X, Ω^p)` for `n = i`, the comparison
`hodgeSingleCohomologyIso` of the base followed by the realization comparison
`moduleHypercohomologyIso` of Tag 01F1 and `hodgeComponentIso`. -/
def hodgeComponentAbelianIso (p i : ℕ) (n : ℤ) (hn : (i : ℤ) = n) :
    ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p) ≅
      (forget₂ (ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A)))
        AddCommGrpCat.{u}).obj (hodgeComponentBase B p n) :=
  hodgeSingleCohomologyIso B D p i n hn ≪≫ moduleHypercohomologyIso (hodgeSingle B D p) n ≪≫
    (forget₂ (ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A)))
      AddCommGrpCat.{u}).mapIso (hodgeComponentIso B p n)

/-- **The cup product of this file along the wedge product is the base's Hodge cup product
`hodgeCup`**, read through `hodgeComponentAbelianIso`: the two are the module and the abelian
realizations of one pairing, `canonicalPairingModule` along the wedge product of Tag 0FM2 on
`Ω^p[0]`, `Ω^q[0]`. -/
theorem hodgeComponentCup_exteriorProductComponent (p q i j : ℕ)
    (x : ((sectionsFunctor X.carrier ⊤).rightDerived i).obj ((deRhamAbelianComplex B D).X p))
    (y : ((sectionsFunctor X.carrier ⊤).rightDerived j).obj ((deRhamAbelianComplex B D).X q)) :
    hodgeComponentCup B (exteriorProductComponent B p q) (i : ℤ) (j : ℤ)
        (ofHodgeComponentBase B ((hodgeComponentAbelianIso B D p i i rfl).hom x))
        (ofHodgeComponentBase B ((hodgeComponentAbelianIso B D q j j rfl).hom y)) =
      ofHodgeComponentBase B ((hodgeComponentAbelianIso B D (p + q) (i + j) ((i : ℤ) + (j : ℤ))
        (by push_cast; rfl)).hom (hodgeCup B D p q (p + q) rfl i j (i + j) rfl x y)) := by
  rw [hodgeCup_eq, canonicalPairing, ← singleMultiplication_exteriorProductComponent B D]
  simp only [hodgeComponentCup, hodgeComponentAbelianIso, Iso.trans_hom,
    ConcreteCategory.comp_apply]
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  exact congrArg (fun t => ofHodgeComponentBase B
    ((hodgeComponentIso B (p + q) ((i : ℤ) + (j : ℤ))).hom.hom
      ((canonicalPairingModule (singleMultiplication (exteriorProductComponent B p q)) i j).hom t)))
    (congrArg₂ (· ⊗ₜ ·) (ModuleCat.inv_hom_apply _ _) (ModuleCat.inv_hom_apply _ _))

end AlgebraicGeometry.SheafOfModules

end
