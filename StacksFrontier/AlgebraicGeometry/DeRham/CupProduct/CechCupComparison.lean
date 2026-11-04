module

public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionWedge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareHypercohomologyClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyPairingPrecomp
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalDuality
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalPairingLaws
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBoundaryTensor

/-!
# The Čech cup product on de Rham cohomology is the cup product of Section 0FKU

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space and `Ω^•` the
relative de Rham complex. Two cup products on `H^*_{dR}` are in the library: the cup product
`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup` of Section 50.4, built from the global cup
product of Cohomology, Section 0FKU and the wedge product, and, when Čech cohomology computes the
hypercohomology of `Ω^•`, the cup product `AlgebraicGeometry.SheafOfModules.deRhamCechCup` of
representing Čech cocycles (Cohomology, Section 01FP). They agree: this is [Stacks, Tag 0FKV]
(`Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule`) at the pairing
`Ω^• ⊗ Ω^• ⟶ Tot(Ω^• ⊗ Ω^•)`, followed by the multiplication of the de Rham differential graded
algebra, which is the wedge product (`AlgebraicGeometry.SheafOfModules.dgAction_regular_deRham`).

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamCechPairing_eq_comp`: the de Rham pairing of Čech
  cochains is the sheaf-tensor pairing followed by the multiplication.
* `AlgebraicGeometry.SheafOfModules.deRhamCechCup_eq_deRhamCohomologyCup` and
  `AlgebraicGeometry.Scheme.Hom.deRhamCup_eq_deRhamCohomologyCup`: **the two cup products agree.**

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology
open scoped Stacks.StandardDerivedModel TensorProduct

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The bounded below de Rham complex, as a complex of modules over the structure sheaf of the
ringed space attached to the base ring sheaf. -/
abbrev deRhamPlusBase :
    CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf (baseRingedSpace A).sheaf)) :=
  deRhamComplexPlus (X := X) B D

/-- The multiplication of the de Rham differential graded algebra, as a morphism of bounded below
complexes `Tot(Ω^• ⊗ Ω^•) ⟶ Ω^•`. -/
abbrev deRhamPlusMul :
    Stacks.Cech.CupProductSquare.tensorPlus (baseRingedSpace A) (deRhamPlusBase B D)
      (deRhamPlusBase B D) ⟶ deRhamPlusBase B D :=
  ObjectProperty.homMk (dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule
    (deRhamDifferentialGradedAlgebra B D)))

/-- **The de Rham pairing is the sheaf-tensor pairing followed by the multiplication.** -/
theorem deRhamCechPairing_eq_comp :
    deRhamCechPairing B D = Stacks.Cech.LinearCupProduct.ComplexPairing.comp
      (sheafTensorPairingOf A (deRhamComplexPlus B D) (deRhamComplexPlus B D)
        (Stacks.Cech.CupProductSquare.tensorPlus (baseRingedSpace A) (deRhamPlusBase B D)
          (deRhamPlusBase B D)).2)
      ((Stacks.Cech.Refinement.sectionsComplex A).map (deRhamPlusMul B D).hom) := by
  refine Stacks.Cech.LinearCupProduct.ComplexPairing.ext' (D := deRhamCechPairing B D)
    fun a b n hn => ?_
  rw [Stacks.Cech.LinearCupProduct.ComplexPairing.comp_μ]
  refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
  refine (differentialGradedPairing_app_tmul (deRhamDifferentialGradedAlgebra B D) 0 a b n hn Z
    x y).trans ?_
  have key := ι_dgActionDesc (_root_.SheafOfModules.DifferentialGradedModule.regularModule
    (deRhamDifferentialGradedAlgebra B D)) a b n hn
  let x' : ((deRhamDifferentialGradedAlgebra B D).complex.X a).val.obj (op (unop Z).left) := x
  let y' : ((deRhamDifferentialGradedAlgebra B D).complex.X b).val.obj (op (unop Z).left) := y
  have hk := congrArg (fun φ => φ.val.app (op (unop Z).left)
    ((((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
        (𝟙 (ringSheaf A).obj)).unit.app
      (PresheafOfModules.tensorObj ((deRhamDifferentialGradedAlgebra B D).complex.X a).val
        ((deRhamDifferentialGradedAlgebra B D).complex.X b).val)).app (op (unop Z).left))
        (x' ⊗ₜ[A.obj.obj (op (unop Z).left)] y'))) key
  have e₃ : (dgActionComponent (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (deRhamDifferentialGradedAlgebra B D)) a b ≫
      ((deRhamDifferentialGradedAlgebra B D).complex.XIsoOfEq hn).hom).val.app (op (unop Z).left)
      ((((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app
      (PresheafOfModules.tensorObj ((deRhamDifferentialGradedAlgebra B D).complex.X a).val
        ((deRhamDifferentialGradedAlgebra B D).complex.X b).val)).app (op (unop Z).left))
        (x' ⊗ₜ[A.obj.obj (op (unop Z).left)] y')) =
      _root_.SheafOfModules.gradedCast
        (fun k ↦ ((deRhamDifferentialGradedAlgebra B D).complex.X k).val.obj (op (unop Z).left)) hn
        (((deRhamDifferentialGradedAlgebra B D).mul a b).app (op (unop Z).left) x' y') := by
    refine (XIsoOfEq_hom_val_app _ hn _ _).trans ?_
    exact congrArg _ (dgActionComponent_unit_apply
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (deRhamDifferentialGradedAlgebra B D)) a b (op (unop Z).left) x' y')
  exact (e₃.symm.trans hk.symm).trans rfl

/-- **The cup product of de Rham cohomology computed by Čech cocycles is the cup product of
Section 0FKU** ([Stacks, Tag 0FKV]). -/
theorem deRhamCechCup_eq_deRhamCohomologyCup (hK : CechComputes A (deRhamComplexPlus B D))
    (i j : ℤ) (x : deRhamCohomology B D i) (y : deRhamCohomology B D j) :
    deRhamCechCup B D hK i j (i + j) rfl x y = deRhamCohomologyCup B D i j x y := by
  rw [deRhamCechCup]
  have h₁ : cup A hK hK (deRhamCechPairing B D) i j (i + j) rfl
      ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
      ((hypercohomologyIsoDeRhamCohomology B D j).inv y) =
    hypercohomologyMap A (deRhamPlusMul B D) (i + j)
      (cup A hK hK (sheafTensorPairingOf A (deRhamComplexPlus B D) (deRhamComplexPlus B D)
        (Stacks.Cech.CupProductSquare.tensorPlus (baseRingedSpace A) (deRhamPlusBase B D)
          (deRhamPlusBase B D)).2) i j (i + j) rfl
      ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
      ((hypercohomologyIsoDeRhamCohomology B D j).inv y)) :=
    (congrArg (fun P => cup A hK hK P i j (i + j) rfl
      ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
      ((hypercohomologyIsoDeRhamCohomology B D j).inv y)) (deRhamCechPairing_eq_comp B D)).trans
      (cup_comp A hK hK _ (deRhamPlusMul B D) i j (i + j) rfl _ _)
  have e₁ := Stacks.Cech.CupProductSquare.hypercohomologyToCohomologyModule_hypercohomologyMap
    (baseRingedSpace A) (deRhamPlusMul B D) (i + j)
    (cup A hK hK (sheafTensorPairingOf A (deRhamComplexPlus B D) (deRhamComplexPlus B D)
        (Stacks.Cech.CupProductSquare.tensorPlus (baseRingedSpace A) (deRhamPlusBase B D)
          (deRhamPlusBase B D)).2) i j (i + j) rfl
      ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
      ((hypercohomologyIsoDeRhamCohomology B D j).inv y))
  have e₂ := Stacks.Cech.CupProductSquare.cupPairing_hypercohomologyToCohomologyModule
    (baseRingedSpace A) (deRhamPlusBase B D) (deRhamPlusBase B D) hK hK i j
    ((hypercohomologyIsoDeRhamCohomology B D i).inv x)
    ((hypercohomologyIsoDeRhamCohomology B D j).inv y)
  have hR : deRhamCohomologyCup B D i j x y =
      (ModuleCat.Hom.hom ((DerivedCategory.homologyFunctor
        (ModuleCat (Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A))) (i + j)).map
          ((Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A)).map
            (DerivedCategory.Q.map (deRhamPlusMul B D).hom))))
        ((Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing (deRhamPlusBase B D).obj
          (deRhamPlusBase B D).obj i j).hom (x ⊗ₜ y)) := by
    refine (congrArg (fun f => f.hom (x ⊗ₜ y))
      (canonicalPairingModule_eq (wedgeProduct B D) i j)).trans ?_
    exact congrArg (fun ψ => (cohomologyModuleMap (A := A) (i + j) ψ).hom
      ((Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing (S := baseRingedSpace A)
        ((deRhamComplex B D).extend embeddingUpNat) ((deRhamComplex B D).extend embeddingUpNat)
          i j).hom (x ⊗ₜ y))) (dgAction_regular_deRham B D).symm
  have hx := Iso.inv_hom_id_apply (hypercohomologyIsoDeRhamCohomology B D i) x
  have hy := Iso.inv_hom_id_apply (hypercohomologyIsoDeRhamCohomology B D j) y
  refine (congrArg (hypercohomologyIsoDeRhamCohomology B D (i + j)).hom h₁).trans ?_
  refine e₁.trans ?_
  refine (congrArg _ e₂.symm).trans ?_
  refine Eq.trans ?_ hR.symm
  congr 3

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (p : X ⟶ S) [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **The Čech cup product on `H^*_{dR}(X/S)` is the cup product of Section 0FM3**, for `X` of
affine diagonal. -/
theorem deRhamCup_eq_deRhamCohomologyCup (i j : ℤ) (x : deRhamCohomologyBaseModule p i)
    (y : deRhamCohomologyBaseModule p j) :
    deRhamCup p i j (i + j) rfl x y =
      SheafOfModules.deRhamCohomologyCup (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) i j x y :=
  SheafOfModules.deRhamCechCup_eq_deRhamCohomologyCup _ _ _ i j x y

end AlgebraicGeometry.Scheme.Hom
