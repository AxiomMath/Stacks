module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ClassMorphismPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProductDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.UnitClassPullback
public import
  StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayShift

/-!
# The morphisms `ξ'` of Remark 0FU7 along a commutative square

Let `ι : X' ⟶ X` over `h₀ : S' ⟶ S` be a commutative square of schemes and
`c : Ω^•_{X/S} ⟶ Rh_*Ω^•_{X'/S'}` its canonical map. For `ξ ∈ H^n_{dR}(X/S)` with pullback
`ι^*ξ ∈ H^n_{dR}(X'/S')`, the morphisms `ξ'` and `(ι^*ξ)'` of Remark 0FU7 satisfy
`c ≫ Rh_*((ι^*ξ)') = ξ' ≫ c[n]`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamComparisonQ_comp_classMorphism`.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] structureSheafRing StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.Cohomology.UnitClassPullback

open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.GlobalKunneth (baseSections)
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

variable {W' W : RingedSpace.{u, u}} (h : W' ⟶ W)

/-- **The value at the unit of `φ ≫ c[n]`, across the Leray identification.** For
`c : M ⟶ Rh_*K` and `φ : 𝒪_W ⟶ M[n]`, the value at the unit of `φ ≫ c[n] : 𝒪_W ⟶ Rh_*(K[n])`,
carried to `H^0(W', K[n]) = H^n(W', K)`, is the image under `H^n(c)` and the Leray
identification of the value at the unit of `φ`, carried to `H^0(W, M[n]) = H^n(W, M)`. -/
theorem shiftHomologyIsoU_lerayMap_evalUnit_comp_shift
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing W'))}
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))}
    (c : M ⟶ (derivedPushforward h).obj K) (n : ℤ)
    (φ : DerivedCategory.Q.obj (unitComplex W 0) ⟶ M⟦n⟧) :
    (shiftHomologyIsoU (baseSections W') K n 0 n (add_zero n)).hom.hom
        (lerayMap h (K⟦n⟧) 0 (evalUnit _ 0
          (φ ≫ c⟦n⟧' ≫ ((derivedPushforward h).commShiftIso n).inv.app K))) =
      lerayMap h K n (((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map c)).hom
        ((shiftHomologyIsoU (baseSections W) M n 0 n (add_zero n)).hom.hom (evalUnit _ 0 φ))) := by
  have e₁ := ConcreteCategory.congr_hom (lerayCohomologyIso_shift h K n 0 n (add_zero n))
    (((DerivedCategory.homologyFunctor _ 0).map ((baseSections W).map
      (c⟦n⟧' ≫ ((derivedPushforward h).commShiftIso n).inv.app K))).hom (evalUnit _ 0 φ))
  have e₂ := ConcreteCategory.congr_hom
    (Stacks.DeRham.GysinCupHodge.shiftHomologyIsoU_naturality (baseSections W) c n 0 n (add_zero n))
    (evalUnit _ 0 φ)
  simp only [ConcreteCategory.comp_apply] at e₁ e₂
  have hm : (DerivedCategory.homologyFunctor _ 0).map ((baseSections W).map
        (c⟦n⟧' ≫ ((derivedPushforward h).commShiftIso n).inv.app K)) ≫
      (DerivedCategory.homologyFunctor _ 0).map ((baseSections W).map
        (((derivedPushforward h).commShiftIso n).hom.app K)) =
      (DerivedCategory.homologyFunctor _ 0).map ((baseSections W).map (c⟦n⟧')) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (fun g => (DerivedCategory.homologyFunctor _ 0).map ((baseSections W).map g))
      (Category.comp_id _)
  have e₃ := ConcreteCategory.congr_hom hm (evalUnit _ 0 φ)
  have e₄ : evalUnit _ 0 (φ ≫ c⟦n⟧' ≫ ((derivedPushforward h).commShiftIso n).inv.app K) =
      ((DerivedCategory.homologyFunctor _ 0).map ((baseSections W).map
        (c⟦n⟧' ≫ ((derivedPushforward h).commShiftIso n).inv.app K))).hom (evalUnit _ 0 φ) :=
    ConcreteCategory.congr_hom (congrArg (DerivedCategory.homologyFunctor _ 0).map
      ((baseSections W).map_comp _ _)) _ |>.trans
        (ConcreteCategory.congr_hom ((DerivedCategory.homologyFunctor _ 0).map_comp _ _) _)
  refine (congrArg (fun z => (shiftHomologyIsoU (baseSections W') K n 0 n (add_zero n)).hom.hom
    (lerayMap h (K⟦n⟧) 0 z)) e₄).trans ?_
  refine e₁.symm.trans ?_
  refine (congrArg (fun z => lerayMap h K n
    ((shiftHomologyIsoU (baseSections W) ((derivedPushforward h).obj K) n 0 n (add_zero n)).hom.hom
      z)) e₃).trans ?_
  exact congrArg (lerayMap h K n) e₂

end Stacks.Cohomology.UnitClassPullback

namespace AlgebraicGeometry.DeRhamLerayHirsch

open DeRhamKatzOdaCech (baseSheaf)

attribute [local instance] SheafOfModules.abelianModules SheafOfModules.hasSheafifyOpens
  SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X X' S S' : Scheme.{u}} (ι : X' ⟶ X) (p' : X' ⟶ S') (p : X ⟶ S) (h₀ : S' ⟶ S)
  (w : ι ≫ p = p' ≫ h₀)

/-- A scalar equal to `1` acts trivially. -/
private theorem smul_eq_self_of_eq_one {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {r : R} (hr : r = 1) (m : M) : r • m = m :=
  (congrArg (· • m) hr).trans (one_smul R m)

/-- The unit complex ring map sends the unit section in degree `0` to `1`. -/
private theorem unitComplexRingHom_unitSection {Y T : Scheme.{u}} (q : Y ⟶ T) :
    ((_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
      (X := SheafOfModules.baseSite (baseSheaf q)) (dga q)).f 0).val.app (op ⊤)
        (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection
          (SheafOfModules.baseRingedSpace (baseSheaf q)) 0) = (dga q).one.eval (op ⊤) := by
  have h₁ := _root_.SheafOfModules.DifferentialGradedAlgebra.unitAlgebraHomF_app_zero
    (dga q) (op ⊤)
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection
      (SheafOfModules.baseRingedSpace (baseSheaf q)) 0)
  have h₂ := Stacks.Cohomology.DerivedGlobalCupProduct.singleObjXSelf_hom_unitSection
    (X := SheafOfModules.baseRingedSpace (baseSheaf q)) 0
  exact h₁.trans (smul_eq_self_of_eq_one (by exact h₂) _)

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **The canonical map of de Rham complexes is unital**: composed with the unit
`p⁻¹𝒪_S ⟶ Ω^•_{X/S}` it is the structure map `p⁻¹𝒪_S ⟶ h_*(p'⁻¹𝒪_{S'})` followed by the direct
image of the unit of `Ω^•_{X'/S'}`. -/
theorem unitComplexRingHom_comp_dgaPushforward :
    Eq (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
        (X := SheafOfModules.baseSite (baseSheaf p)) (dga p) ≫ dgaPushforward ι p' p h₀ w)
      (Stacks.Cohomology.UnitClassPullback.unitToPushforward (squareMap ι p' p h₀ w) 0 ≫
        (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
          (squareMap ι p' p h₀ w)).map
          (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
            (X := SheafOfModules.baseSite (baseSheaf p')) (dga p'))) := by
  refine Stacks.Cohomology.DerivedGlobalCupProduct.unitComplex_hom_ext
    (X := SheafOfModules.baseRingedSpace (baseSheaf p)) _ _ ?_
  have e₂ : ((Stacks.Cohomology.UnitClassPullback.unitToPushforward (squareMap ι p' p h₀ w) 0).f
      0).val.app (op ⊤) (Stacks.Cohomology.DerivedGlobalCupProduct.unitSection
          (SheafOfModules.baseRingedSpace (baseSheaf p)) 0) =
      Stacks.Cohomology.DerivedGlobalCupProduct.unitSection
          (SheafOfModules.baseRingedSpace (baseSheaf p')) 0 :=
    Stacks.Cohomology.UnitClassPullback.unitToPushforward_unitSection _ 0
  have hL : HEq (((dgaPushforward ι p' p h₀ w).f 0).val.app (op ⊤) ((dga p).one.eval (op ⊤)))
      ((Scheme.Hom.relativeDifferentialFormsAlgebra p').one.eval (op (ι ⁻¹ᵁ ⊤))) :=
    (dgaPushforward_f_app_heq ι p' p h₀ w 0 0 rfl (op ⊤) _ _
      (SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ (op ⊤))).trans
      (heq_of_eq (Scheme.Hom.relativeDifferentialFormsPullback_one ι p p' h₀ w ⊤))
  have hR : HEq ((dga p').one.eval (op ⊤))
      ((Scheme.Hom.relativeDifferentialFormsAlgebra p').one.eval (op (ι ⁻¹ᵁ ⊤))) :=
    SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ (op ⊤)
  refine (congrArg (fun z => ((dgaPushforward ι p' p h₀ w).f 0).val.app (op ⊤) z)
    (unitComplexRingHom_unitSection p)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z =>
    ((_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
      (X := SheafOfModules.baseSite (baseSheaf p')) (dga p')).f 0).val.app (op ⊤) z) e₂).symm
  exact eq_of_heq (hL.trans (hR.symm.trans (heq_of_eq (unitComplexRingHom_unitSection p').symm)))

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **The canonical map is unital in the derived category**: composed with the unit
`p⁻¹𝒪_S ⟶ Ω^•_{X/S}`, the canonical map `c : Ω^•_{X/S} ⟶ Rh_*Ω^•_{X'/S'}` is
`v_h : p⁻¹𝒪_S ⟶ Rh_*(p'⁻¹𝒪_{S'})` followed by `Rh_*` of the unit of `Ω^•_{X'/S'}`. -/
theorem deRhamUnitHom_comp_dgaPushforward :
    Eq (SheafOfModules.deRhamUnitHom (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) ≫
        DerivedCategory.Q.map (dgaPushforward ι p' p h₀ w) ≫
          Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
            (squareMap ι p' p h₀ w) (dga p').complex)
      (Stacks.Cohomology.UnitClassPullback.unitToDerivedPushforward (squareMap ι p' p h₀ w) 0 ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          (squareMap ι p' p h₀ w)).map
          (SheafOfModules.deRhamUnitHom (Scheme.Hom.deRhamAlgebras p')
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')))) := by
  have h₁ := congrArg DerivedCategory.Q.map (unitComplexRingHom_comp_dgaPushforward ι p' p h₀ w)
  open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces in
  have h₂ := pushforwardComparisonQ_naturality
    (squareMap ι p' p h₀ w) (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
      (X := SheafOfModules.baseSite (baseSheaf p')) (dga p'))
  have h₃ := (DerivedCategory.Q.map_comp _ _).symm.trans (h₁.trans (DerivedCategory.Q.map_comp _ _))
  have h₄ := congrArg (DerivedCategory.Q.map
    (Stacks.Cohomology.UnitClassPullback.unitToPushforward (squareMap ι p' p h₀ w) 0) ≫ ·) h₂
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₃).trans
    ((Category.assoc _ _ _).trans (h₄.trans (Category.assoc _ _ _).symm)))

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **The formation of `ξ'` commutes with pullback along a commutative square** (the property of
Remark 0FU7 used in the proof of Proposition 0FMR): for `ξ ∈ H^n_{dR}(X/S)`, the canonical map
`c : Ω^•_{X/S} ⟶ Rh_*Ω^•_{X'/S'}` satisfies `c ≫ Rh_*((ι^*ξ)') = ξ' ≫ c[n]`. -/
theorem deRhamComparisonQ_comp_classMorphism (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n) :
    deRhamComparisonQ ι p' p h₀ w ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        (inverseImageBaseMap ι p' p h₀ w)).map
        (classMorphism p' n (deRhamPullbackSquare ι p' p h₀ w n ξ)) =
    classMorphism p n ξ ≫ (deRhamComparisonQ ι p' p h₀ w)⟦n⟧' ≫
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        (inverseImageBaseMap ι p' p h₀ w)).commShiftIso n).inv.app _ := by
  refine SheafOfModules.comp_derivedPushforward_map_eq_of_linear
    (S := SheafOfModules.baseRingedSpace (baseSheaf p))
    (S' := SheafOfModules.baseRingedSpace (baseSheaf p')) (squareMap ι p' p h₀ w)
    (dgaPushforward ι p' p h₀ w) (dgaPushforward_mul ι p' p h₀ w) n _
    (SheafOfModules.derivedForgetShiftedHom_derivedAction
      (S := SheafOfModules.baseRingedSpace (baseSheaf p)) (dga p) n
      (SheafOfModules.deRhamClassDerivedEquiv (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n ξ)) _
    (SheafOfModules.derivedForgetShiftedHom_derivedAction
      (S := SheafOfModules.baseRingedSpace (baseSheaf p')) (dga p') n
      (SheafOfModules.deRhamClassDerivedEquiv (Scheme.Hom.deRhamAlgebras p')
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')) n
          (deRhamPullbackSquare ι p' p h₀ w n ξ)))
    (SheafOfModules.deRhamUnitHom (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))
    (SheafOfModules.isIso_dgaUnitHom_derivedAction (dga p)) ?_
  have hU := deRhamUnitHom_comp_dgaPushforward ι p' p h₀ w
  have hu₁ := SheafOfModules.deRhamUnitHom_comp_deRhamClassMorphism (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n ξ
  have hu₂ := SheafOfModules.deRhamUnitHom_comp_deRhamClassMorphism (Scheme.Hom.deRhamAlgebras p')
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')) n
    (deRhamPullbackSquare ι p' p h₀ w n ξ)
  have hL := Stacks.Cohomology.UnitClassPullback.lerayCohomologyIso_evalUnit_classPushforward
    (squareMap ι p' p h₀ w) 0
    (SheafOfModules.deRhamDerivedClass (Scheme.Hom.deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')) n
      (deRhamPullbackSquare ι p' p h₀ w n ξ))
  have hR := Stacks.Cohomology.UnitClassPullback.shiftHomologyIsoU_lerayMap_evalUnit_comp_shift
    (squareMap ι p' p h₀ w)
    (DerivedCategory.Q.map (dgaPushforward ι p' p h₀ w) ≫
      Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
        (squareMap ι p' p h₀ w) (dga p').complex) n
    (SheafOfModules.deRhamDerivedClass (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n ξ)
  have hξ := deRhamPullbackSquare_eq_lerayMap ι p' p h₀ w n ξ
  have hev₁ := Equiv.ofBijective_apply_symm_apply
    (SheafOfModules.structureSheafEval (baseSheaf p) _)
    (SheafOfModules.structureSheafEval_bijective (baseSheaf p) _)
    ((SheafOfModules.deRhamShiftHomologyIso (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n 0 n (add_zero n)).inv ξ)
  have hev₂ := Equiv.ofBijective_apply_symm_apply
    (SheafOfModules.structureSheafEval (baseSheaf p') _)
    (SheafOfModules.structureSheafEval_bijective (baseSheaf p') _)
    ((SheafOfModules.deRhamShiftHomologyIso (Scheme.Hom.deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')) n 0 n (add_zero n)).inv
      (deRhamPullbackSquare ι p' p h₀ w n ξ))
  have eL := (Category.assoc _ _ _).symm.trans ((congrArg (fun g => g ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        (squareMap ι p' p h₀ w)).map (classMorphism p' n (deRhamPullbackSquare ι p' p h₀ w n ξ)))
      hU).trans ((Category.assoc _ _ _).trans (congrArg
        (Stacks.Cohomology.UnitClassPullback.unitToDerivedPushforward (squareMap ι p' p h₀ w) 0 ≫ ·)
        ((Functor.map_comp _ _ _).symm.trans (congrArg
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            (squareMap ι p' p h₀ w)).map hu₂)))))
  refine (SheafOfModules.structureSheafEval_bijective (baseSheaf p) _).1 ?_
  refine Stacks.Cohomology.LerayCupPairing.lerayMap_injective (squareMap ι p' p h₀ w) _ 0 ?_
  refine (ConcreteCategory.bijective_of_isIso (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (SheafOfModules.baseRingedSpace (baseSheaf p')))
    (DerivedCategory.Q.obj (dga p').complex) n 0 n (add_zero n)).hom).1 ?_
  refine (congrArg (fun φ => (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (SheafOfModules.baseRingedSpace (baseSheaf p')))
    (DerivedCategory.Q.obj (dga p').complex) n 0 n (add_zero n)).hom.hom
      (Stacks.Cohomology.LerayCupPairing.lerayMap (squareMap ι p' p h₀ w) _ 0
        (SheafOfModules.structureSheafEval (baseSheaf p) _ φ))) eL).trans ?_
  refine (congrArg (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (SheafOfModules.baseRingedSpace (baseSheaf p')))
    (DerivedCategory.Q.obj (dga p').complex) n 0 n (add_zero n)).hom.hom (hL.trans hev₂)).trans ?_
  refine (Iso.inv_hom_id_apply _ _).trans ?_
  refine hξ.trans ?_
  refine Eq.trans ?_ (congrArg (fun φ => (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
    (Stacks.Cohomology.GlobalKunneth.baseSections (SheafOfModules.baseRingedSpace (baseSheaf p')))
    (DerivedCategory.Q.obj (dga p').complex) n 0 n (add_zero n)).hom.hom
      (Stacks.Cohomology.LerayCupPairing.lerayMap (squareMap ι p' p h₀ w) _ 0
        (SheafOfModules.structureSheafEval (baseSheaf p) _ φ)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu₁))).symm
  refine Eq.trans ?_ hR.symm
  exact congrArg (fun z => Stacks.Cohomology.LerayCupPairing.lerayMap (squareMap ι p' p h₀ w) _ n
    (((DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Cohomology.GlobalKunneth.baseSections
          (SheafOfModules.baseRingedSpace (baseSheaf p))).map
        (DerivedCategory.Q.map (dgaPushforward ι p' p h₀ w) ≫
          Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
            (squareMap ι p' p h₀ w) (dga p').complex))).hom z))
    ((congrArg (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
      (Stacks.Cohomology.GlobalKunneth.baseSections (SheafOfModules.baseRingedSpace (baseSheaf p)))
      (DerivedCategory.Q.obj (dga p).complex) n 0 n (add_zero n)).hom.hom hev₁).trans
      (Iso.inv_hom_id_apply _ _)).symm

end AlgebraicGeometry.DeRhamLerayHirsch
