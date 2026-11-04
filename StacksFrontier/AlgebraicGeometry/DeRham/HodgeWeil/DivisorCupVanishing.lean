module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorCupNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorCohomologyLift

/-!
# Cup product with a class dying along the log poles kills classes vanishing on the divisor

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, cut out by
`I`, for which the de Rham complex of log poles is defined (Tag 0FMV). Let
`a ∈ H^q(X, Ω^p_{X/S})` restrict to zero on `Y`, and let `c ∈ H^1(X, Ω^1_{X/S})` map to zero in
`H^1(X, Ω^1_{X/S}(log Y))`. Then `a ∪ c = 0` in `H^{q+1}(X, Ω^{p+1}_{X/S})`.

## Main results

* `Stacks.HodgeWeil.hodgeComponentCup_eq_zero_of_logPoles`: `a ∪ c = 0`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap totalCupPairing)
open AlgebraicGeometry.SheafOfModules (baseRingedSpace hodgeCohomologyComponent
  hodgeComponentCup toHodgeComponentBase exteriorProductComponent)
open scoped TensorProduct

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

include hI hlog in
/-- **Cup product with a class dying in `H^1(X, Ω^1(log Y))` kills the classes restricting to
zero on `Y`**: if `i^* a = 0` for `a ∈ H^q(X, Ω^p_{X/S})` and `c ∈ H^1(X, Ω^1_{X/S})` maps to
zero in `H^1(X, Ω^1_{X/S}(log Y))`, then `a ∪ c = 0`. -/
theorem hodgeComponentCup_eq_zero_of_logPoles (p : ℕ) (q : ℤ)
    (a : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q)
    (ha : hodgePullback I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I) p q a = 0)
    (c : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) 1 1)
    (hc : (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) ((HomologicalComplex.single _ (up ℤ) 0).map (logPolesFormsBaseInclusion f I 1))
        1).hom (toHodgeComponentBase _ c) = 0) :
    hodgeComponentCup (Scheme.Hom.deRhamAlgebras f)
      (exteriorProductComponent (Scheme.Hom.deRhamAlgebras f) p 1) q 1 a c = 0 := by
  obtain ⟨a₀, ha₀⟩ := exists_kernelForms_lift_of_hodgePullback_eq_zero f I p q a ha
  let a' : cohomologyModule (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u}
      f.base).obj S.sheaf)) (DerivedCategory.Q.obj (singleInt (kernelFormsBase f I p))) q := a₀
  have ha' : (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u}
      f.base).obj S.sheaf)) ((HomologicalComplex.single _ (up ℤ) 0).map
        (kernelFormsBaseInclusion f I p)) q).hom a' = toHodgeComponentBase _ a := ha₀
  refine (hodgeComponentCup_eq_totalCupPairing _ _ q 1 a c).trans ?_
  have e1 := cohomologyMap_singleIntMultiplication_totalCupPairing_map
    (kernelFormsBaseInclusion f I p)
    (𝟙 (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1))
    (((sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      S.sheaf)).map (kernelFormsBaseInclusion f I p)).app
        (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1) ≫
      exteriorProductComponent (formsAlgebras f) p 1)
    (exteriorProductComponent (formsAlgebras f) p 1)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp]) q 1 a' (toHodgeComponentBase _ c)
  have e2 := cohomologyMap_singleIntMultiplication_totalCupPairing_map
    (𝟙 (kernelFormsBase f I p)) (logPolesFormsBaseInclusion f I 1)
    (((sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      S.sheaf)).map (kernelFormsBaseInclusion f I p)).app
        (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1) ≫
      exteriorProductComponent (formsAlgebras f) p 1)
    (kernelLogWedge hI hlog p)
    (by rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      kernelLogWedge_comp_eq]) q 1 a' (toHodgeComponentBase _ c)
  have id1 : (cohomologyMap (S := baseRingedSpace
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
      ((HomologicalComplex.single _ (up ℤ) 0).map
        (𝟙 (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1))) 1).hom
        (toHodgeComponentBase _ c) = toHodgeComponentBase _ c :=
    (congrArg (fun φ => (cohomologyMap (S := baseRingedSpace
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) φ 1).hom
        (toHodgeComponentBase _ c)) (CategoryTheory.Functor.map_id _ _)).trans
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_id_apply _ _ _)
  have id2 : (cohomologyMap (S := baseRingedSpace
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
      ((HomologicalComplex.single _ (up ℤ) 0).map (𝟙 (kernelFormsBase f I p))) q).hom a' = a' :=
    (congrArg (fun φ => (cohomologyMap (S := baseRingedSpace
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) φ q).hom a')
      (CategoryTheory.Functor.map_id _ _)).trans
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_id_apply _ _ _)
  have hz : (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      S.sheaf)) (singleIntMultiplication (kernelLogWedge hI hlog p)) (q + 1)).hom
      ((totalCupPairing (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) (singleInt (kernelFormsBase f I p))
        (singleInt (Scheme.Hom.logPolesFormsBase f I 1)) q 1).hom
        (a' ⊗ₜ (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u}
          f.base).obj S.sheaf)) ((HomologicalComplex.single _ (up ℤ) 0).map
            (logPolesFormsBaseInclusion f I 1)) 1).hom (toHodgeComponentBase _ c))) = 0 :=
    (congrArg (fun z => (cohomologyMap (S := baseRingedSpace
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
      (singleIntMultiplication (kernelLogWedge hI hlog p)) (q + 1)).hom
        ((totalCupPairing (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u}
          f.base).obj S.sheaf)) (singleInt (kernelFormsBase f I p))
          (singleInt (Scheme.Hom.logPolesFormsBase f I 1)) q 1).hom (a' ⊗ₜ z))) hc).trans
      ((congrArg (fun z => (cohomologyMap (S := baseRingedSpace
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
        (singleIntMultiplication (kernelLogWedge hI hlog p)) (q + 1)).hom
          ((totalCupPairing (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u}
            f.base).obj S.sheaf)) (singleInt (kernelFormsBase f I p))
            (singleInt (Scheme.Hom.logPolesFormsBase f I 1)) q 1).hom z))
        (TensorProduct.tmul_zero _ a')).trans
        ((congrArg _ (map_zero _)).trans (map_zero _)))
  have hL : toHodgeComponentBase _ a ⊗ₜ[Stacks.Cohomology.GlobalKunneth.baseRing
        (baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))]
        toHodgeComponentBase _ c =
      (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) ((HomologicalComplex.single _ (up ℤ) 0).map (kernelFormsBaseInclusion f I p))
          q).hom a' ⊗ₜ[Stacks.Cohomology.GlobalKunneth.baseRing
        (baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))]
      (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) ((HomologicalComplex.single _ (up ℤ) 0).map
          (𝟙 (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) 1))) 1).hom
          (toHodgeComponentBase _ c) :=
    congrArg₂ (fun x y => x ⊗ₜ[Stacks.Cohomology.GlobalKunneth.baseRing
      (baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))] y)
      ha'.symm id1.symm
  refine (congrArg (fun z => (cohomologyMap (S := baseRingedSpace
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
    (singleIntMultiplication (exteriorProductComponent (formsAlgebras f) p 1)) (q + 1)).hom
      ((totalCupPairing (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) (singleInt _) (singleInt _) q 1).hom z)) hL).trans ?_
  refine e1.trans (e2.symm.trans ?_)
  refine (congrArg (fun z => (cohomologyMap (S := baseRingedSpace
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
    (singleIntMultiplication (kernelLogWedge hI hlog p)) (q + 1)).hom
      ((totalCupPairing (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) (singleInt _) (singleInt _) q 1).hom (z ⊗ₜ _))) id2).trans hz

end Stacks.HodgeWeil

end
