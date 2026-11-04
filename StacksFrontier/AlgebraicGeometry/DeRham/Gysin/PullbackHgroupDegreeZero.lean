module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeBridgeShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HomologySingleShiftGeneric
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObjectDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The pullback map on cohomology in degree zero

The pullback map `pullbackHgroup P φ : Hⁿ(X, ℳ) ⟶ Hⁿ(X', ℳ')` of [Stacks, Tag 01F9] attached to a
`G`-map `φ : ℳ ⟶ G_*ℳ'`, built from the canonical comparisons of [Stacks, Tag 01F8] and
[Stacks, Tag 01EZ], is in degree zero the map on global sections
`Γ(X, ℳ) ⟶ Γ(X, G_*ℳ') = Γ(X', ℳ')` induced by `φ`, read through `Γ = H⁰`.

## Main results

* `Stacks.DeRham.GysinCohomologyBaseChange.toRightDerivedZero_comp_pullbackHgroup_id`: the
  pullback map of the identity of `G_*ℳ'`.
* `Stacks.DeRham.GysinCohomologyBaseChange.toRightDerivedZero_comp_pullbackHgroup`: the pullback
  map of an arbitrary `G`-map.

## Implementation notes

The pullback map is built in the standard model of the derived category; the proof works with its
constituents, so the file opens the scope `Stacks.StandardDerivedModel`. The comparison is reduced,
through the units of the derived functors, the Leray comparison and the degree-zero description of
`cohomologyDerivedSingleIso`, to the identity of the degree-zero chain map of single complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin
open scoped Stacks.StandardDerivedModel

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-- **`H⁰` of a module placed in degree `0` on classes of sections**: `toRightDerivedZero`,
followed by the inverse of `cohomologyDerivedSingleIso`, is the class of the section as a cocycle
of `Γ(X, ℳ[0])`, carried into the derived category by the unit of derived global sections. -/
theorem toRightDerivedZero_comp_cohomologyDerivedSingleIso_inv_zero (X : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (secF (structureSheafRing X) ⊤).toRightDerivedZero.app M ≫
        (cohomologyDerivedSingleIso X M (0 : ℤ) 0 0 (by simp)).inv =
      Stacks.DerivedFunctor.singleZeroClass (secF (structureSheafRing X) ⊤) M ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((0 : ℕ) : ℤ)).map
          ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
            (((secF (structureSheafRing X) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor _ 0).obj M))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((0 : ℕ) : ℤ)).map
          ((derivedGlobalSectionsUnit X).app ((HomotopyCategory.singleFunctor _ 0).obj M)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((0 : ℕ) : ℤ)).map
          ((derivedGlobalSections X).map
            ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app M)) := by
  let := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
  have h₀ := GysinCupHodge.cohomologyDerivedSingleIso_hom_eq X M (0 : ℤ) 0 0 (by simp)
  have hz := GysinCupHodge.homology_single_shift_zero (derivedGlobalSections X) M (-(0 : ℤ)) 0
    (by simp) (by simp) (by simp)
  have h₀' := h₀.trans ((congrArg (· ≫ _) hz).trans (Category.id_comp _))
  have hinv := congrArg Iso.inv (Iso.ext h₀')
  have hgen := Stacks.DerivedFunctor.toRightDerivedZero_comp_homologyTotalRightDerivedSingleIso_inv
    (secF (structureSheafRing X) ⊤) (derivedGlobalSections X) (derivedGlobalSectionsUnit X)
    (Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves X) M
  rw [← hinv] at hgen
  exact hgen

/-- The algebra of `toRightDerivedZero_comp_pullbackHgroup_id`, at variables. -/
private lemma degreeZero_chase {V E : Type*} [Category* V] [Category* E] (HZ : V ⥤ E)
    {P P' : E} {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ C₀ C₁ C₂ : V}
    (zc : P ⟶ HZ.obj A₀) (qinv : A₀ ⟶ A₁) (αS : A₁ ⟶ A₂) (rsinv : A₂ ⟶ A₃) (rsm : A₃ ⟶ A₄)
    (lh : A₄ ⟶ A₅) (rqe : A₂ ⟶ B₂) (rpu : B₂ ⟶ B₃) (rrs : B₃ ⟶ A₄) (qfe : A₁ ⟶ B₁)
    (αG : B₁ ⟶ B₂) (qch : B₁ ⟶ C₁) (lU : C₁ ⟶ B₃) (lh' : B₃ ⟶ C₂) (rs' : C₂ ⟶ A₅)
    (α' : C₁ ⟶ C₂) (psi : P ⟶ P') (zc' : P' ⟶ HZ.obj C₀) (qinv' : C₀ ⟶ C₁)
    (f1 : rsinv ≫ rsm = rqe ≫ rpu ≫ rrs) (f2 : αS ≫ rqe = qfe ≫ αG)
    (f3 : αG ≫ rpu = qch ≫ lU) (f4 : rrs ≫ lh = lh' ≫ rs') (f5 : lU ≫ lh' = α')
    (f6 : zc ≫ HZ.map qinv ≫ HZ.map qfe ≫ HZ.map qch = psi ≫ zc' ≫ HZ.map qinv') :
    zc ≫ HZ.map qinv ≫ HZ.map αS ≫ HZ.map rsinv ≫ HZ.map (rsm ≫ lh) =
      psi ≫ zc' ≫ HZ.map qinv' ≫ HZ.map α' ≫ HZ.map rs' := by
  have key : αS ≫ rsinv ≫ rsm ≫ lh = qfe ≫ qch ≫ α' ≫ rs' := by
    rw [reassoc_of% f1, reassoc_of% f2, reassoc_of% f3, f4, reassoc_of% f5]
  have hk := congrArg HZ.map key
  simp only [Functor.map_comp] at hk
  simp only [Functor.map_comp]
  rw [hk, ← reassoc_of% f6]

/-- Cancelling an isomorphism inside a functor. At variables. -/
private lemma map_cancel_chase {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {P Q R S T : D} (a : P ⟶ Q) (b : Q ⟶ P) (c : P ⟶ R) (d : R ⟶ S) (f : S ⟶ T)
    (hab : a ≫ b = 𝟙 P) :
    H.map a ≫ H.map (b ≫ c ≫ d ≫ f) = H.map c ≫ H.map d ≫ H.map f := by
  rw [← H.map_comp, ← H.map_comp, ← H.map_comp, reassoc_of% hab]

/-- Cancelling an isomorphism in front of a morphism, inside a functor. At variables. -/
private lemma map_hom_inv_chase {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {P Q : D} {Z : E} (a : P ⟶ Q) (b : Q ⟶ P) (x : H.obj P ⟶ Z) (hab : a ≫ b = 𝟙 P) :
    H.map a ≫ H.map b ≫ x = x := by
  rw [← H.map_comp_assoc, hab, H.map_id, Category.id_comp]

/-- Removing four identities around a morphism. At variables. -/
private lemma id_chase {C : Type*} [Category* C] {A B : C} (i₁ i₂ : A ⟶ A) (x : A ⟶ B)
    (i₃ i₄ : B ⟶ B) (h₁ : i₁ = 𝟙 A) (h₂ : i₂ = 𝟙 A) (h₃ : i₃ = 𝟙 B) (h₄ : i₄ = 𝟙 B) :
    (((i₁ ≫ i₂) ≫ x) ≫ i₃) ≫ i₄ = x := by
  subst h₁ h₂ h₃ h₄
  simp

/-- The algebra of the comparison of the classes of a degree-zero cocycle, at variables. -/
private lemma classes_chase {V : Type*} [Category* V]
    {P P' Zc Zc' Hc Hc' D₀ D₀' D₁ D₁' HH HH' D₂ : V}
    (lc : P ⟶ Zc) (π : Zc ⟶ Hc) (dinv : Hc ⟶ D₀) (hz : D₀ ⟶ D₁) (qa : D₁ ⟶ D₂)
    (qb : D₂ ⟶ D₁') (lc' : P' ⟶ Zc') (π' : Zc' ⟶ Hc') (dinv' : Hc' ⟶ D₀') (hz' : D₀' ⟶ D₁')
    (psi : P ⟶ P') (hinv : Hc ⟶ HH) (hhinv : HH ⟶ D₁) (hinv' : Hc' ⟶ HH') (hhinv' : HH' ⟶ D₁')
    (hm : Hc ⟶ Hc') (hcm : HH ⟶ HH') (cm : Zc ⟶ Zc') (qx : D₁ ⟶ D₁')
    (hqx : qa ≫ qb = qx) (hA : dinv ≫ hz = hinv ≫ hhinv) (hA' : dinv' ≫ hz' = hinv' ≫ hhinv')
    (N1 : hcm ≫ hhinv' = hhinv ≫ qx) (N2 : hm ≫ hinv' = hinv ≫ hcm) (N3 : cm ≫ π' = π ≫ hm)
    (N4 : lc ≫ cm = psi ≫ lc') :
    (lc ≫ π ≫ dinv) ≫ hz ≫ qa ≫ qb = psi ≫ (lc' ≫ π' ≫ dinv') ≫ hz' := by
  simp only [Category.assoc]
  rw [hqx, reassoc_of% hA, ← N1, ← reassoc_of% N2, ← reassoc_of% N3, reassoc_of% N4, hA']

/-- **In degree zero the pullback map of the identity of `G_*ℳ'` is the identity on sections**
`Γ(X, G_*ℳ') = Γ(X', ℳ')`, read through `Γ = H⁰`. -/
theorem toRightDerivedZero_comp_pullbackHgroup_id {X X' : RingedSpace.{u, u}} (G : X' ⟶ X)
    (M' : RModules X') :
    (secF (structureSheafRing X) ⊤).toRightDerivedZero.app ((modulePushforward G).obj M') ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical G) 0 0 0 (by simp) (𝟙 _) =
      (pushforwardSectionsIso G).hom.app M' ≫
        (secF (structureSheafRing X') ⊤).toRightDerivedZero.app M' := by
  have h1 := toRightDerivedZero_comp_cohomologyDerivedSingleIso_inv_zero X
    ((modulePushforward G).obj M')
  have h2 := toRightDerivedZero_comp_cohomologyDerivedSingleIso_inv_zero X' M'
  rw [← cancel_mono (cohomologyDerivedSingleIso X' M' 0 0 0 (by simp)).inv]
  simp only [pullbackHgroup, derivedPushforwardMap, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  rw [reassoc_of% h1, h2]
  have hsm : ((CohomologyPullbackComparison.canonical G).singleMap 0).app M' =
      (DerivedCategory.singleFunctorIsoCompQh (RModules X) 0).hom.app
          ((modulePushforward G).obj M') ≫
        DerivedCategory.Qh.map (((modulePushforward G).mapHomotopyCategorySingleFunctor 0).inv.app
          M') ≫
        (derivedPushforwardUnit G).app ((HomotopyCategory.singleFunctor (RModules X') 0).obj M') ≫
        (derivedPushforward G).map ((DerivedCategory.singleFunctorIsoCompQh (RModules X') 0).inv.app
          M') := by
    simp [CohomologyPullbackComparison.canonical, singleToDerivedPushforward]
  have := isIso_lerayComparisonAb G
  have hleray : (CohomologyPullbackComparison.canonical G).leray.hom =
      inv (lerayComparisonAb G) := rfl
  have hfac := (derivedGlobalSections X').rightDerived_fac (derivedGlobalSectionsUnit X')
    (HomotopyCategory.quasiIso (RModules X') (ComplexShape.up ℤ)) _ (lerayUnitAb G)
  set K' := (HomotopyCategory.singleFunctor (RModules X') 0).obj M'
  set e := ((modulePushforward G).mapHomotopyCategorySingleFunctor 0).inv.app M'
  set c := Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso G) (ComplexShape.up ℤ)
  refine degreeZero_chase _ _ _ _ _ _ _
    ((derivedGlobalSections X).map (DerivedCategory.Qh.map e))
    ((derivedGlobalSections X).map ((derivedPushforwardUnit G).app K'))
    ((derivedGlobalSections X).map ((derivedPushforward G).map
      ((DerivedCategory.singleFunctorIsoCompQh (RModules X') 0).inv.app M')))
    (DerivedCategory.Qh.map ((secF (structureSheafRing X) ⊤).mapHomotopyCategory
      (ComplexShape.up ℤ) |>.map e))
    ((derivedGlobalSectionsUnit X).app (((modulePushforward G).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K'))
    (DerivedCategory.Qh.map (c.hom.app K')) ((lerayUnitAb G).app K')
    ((CohomologyPullbackComparison.canonical G).leray.hom.app (DerivedCategory.Qh.obj K'))
    _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the comparison of [Stacks, Tag 01F8] at `ℳ'`
    rw [hsm, CategoryTheory.Functor.map_id, Category.id_comp]
    exact map_cancel_chase (derivedGlobalSections X) _ _ _ _ _
      (Iso.inv_hom_id_app (DerivedCategory.singleFunctorIsoCompQh (RModules X) 0)
        ((modulePushforward G).obj M'))
  · exact ((derivedGlobalSectionsUnit X).naturality e).symm
  · simp only [lerayUnitAb, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    exact (map_hom_inv_chase DerivedCategory.Qh _ _ _ (Iso.hom_inv_id_app c K')).symm
  · exact (CohomologyPullbackComparison.canonical G).leray.hom.naturality
      ((DerivedCategory.singleFunctorIsoCompQh (RModules X') 0).inv.app M')
  · have h := congrArg (fun τ => τ.app K') hfac
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    rw [hleray, NatIso.isIso_inv_app, ← h]
    show ((derivedGlobalSectionsUnit X').app K' ≫ (lerayComparisonAb G).app
        (DerivedCategory.Qh.obj K')) ≫
          inv ((lerayComparisonAb G).app (DerivedCategory.Qh.obj K')) = _
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · have he : e = (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
          (ComplexShape.up ℤ) 0).inv.app M') := by
      have h₁ : (HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules (structureSheafRing X)) 0).hom.app ((modulePushforward G).obj M') =
            𝟙 _ := rfl
      have h₂ : ((modulePushforward G).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((CochainComplex.singleFunctor (SheafOfModules (structureSheafRing X')) 0).obj M') =
            𝟙 _ := rfl
      have h₃ : (HomotopyCategory.singleFunctorPostcompQuotientIso
          (SheafOfModules (structureSheafRing X')) 0).inv.app M' = 𝟙 _ := rfl
      simp only [e, Functor.mapHomotopyCategorySingleFunctor, Iso.trans_inv, Iso.symm_inv,
        Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Category.comp_id, h₁, h₂, h₃]
      exact id_chase _ _ _ _ _ rfl rfl rfl (CategoryTheory.Functor.map_id _ _)
    set C := ((secF (structureSheafRing X) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (SheafOfModules (structureSheafRing X)) 0).obj
        ((modulePushforward G).obj M'))
    set C' := ((secF (structureSheafRing X') ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (SheafOfModules (structureSheafRing X')) 0).obj M')
    set e₀ := (HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
      (ComplexShape.up ℤ) 0).inv.app M'
    set χ := ((secF (structureSheafRing X) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map e₀ ≫
      (Functor.mapHomologicalComplexCompIso (pushforwardSectionsIso G) (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor (SheafOfModules (structureSheafRing X')) 0).obj M')
    have hq : ((secF (structureSheafRing X) ⊤).mapHomotopyCategory (ComplexShape.up ℤ)).map e ≫
        c.hom.app K' = (HomotopyCategory.quotient _ _).map χ := by
      rw [he, Functor.map_comp]
      rfl
    refine classes_chase _ _ _ _ _ _ _ _ _ _ _
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).inv.app C)
      ((DerivedCategory.homologyFunctorFactorsh AddCommGrpCat.{u} 0).inv.app
        ((HomotopyCategory.quotient _ _).obj C))
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).inv.app C')
      ((DerivedCategory.homologyFunctorFactorsh AddCommGrpCat.{u} 0).inv.app
        ((HomotopyCategory.quotient _ _).obj C'))
      (HomologicalComplex.homologyMap χ 0)
      ((HomotopyCategory.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).map
        ((HomotopyCategory.quotient _ _).map χ))
      (HomologicalComplex.cyclesMap χ 0)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map χ)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← Functor.map_comp, ← Functor.map_comp, hq]
      rfl
    · exact Stacks.DerivedFunctor.homologyFunctorFactors_inv_app_comp_quotientCompQhIso_inv
        AddCommGrpCat.{u} C 0
    · exact Stacks.DerivedFunctor.homologyFunctorFactors_inv_app_comp_quotientCompQhIso_inv
        AddCommGrpCat.{u} C' 0
    · exact (DerivedCategory.homologyFunctorFactorsh AddCommGrpCat.{u} 0).inv.naturality
        ((HomotopyCategory.quotient _ _).map χ)
    · exact (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} (ComplexShape.up ℤ)
        0).inv.naturality χ
    · exact (HomologicalComplex.homologyπ_naturality χ 0).symm
    · rw [HomologicalComplex.liftCycles_comp_cyclesMap, HomologicalComplex.comp_liftCycles]
      congr 1

/-- **The pullback map on cohomology in degree zero is the map on global sections**: for a `G`-map
`φ : ℳ ⟶ G_*ℳ'`, the pullback map `H⁰(X, ℳ) ⟶ H⁰(X', ℳ')` of [Stacks, Tag 01F9] built from the
canonical comparisons carries the class of a global section `s` of `ℳ` to the class of `φ(s)`,
a global section of `G_*ℳ'`, that is, of `ℳ'`. -/
theorem toRightDerivedZero_comp_pullbackHgroup {X X' : RingedSpace.{u, u}} (G : X' ⟶ X)
    {M : RModules X} {M' : RModules X'} (φ : M ⟶ (modulePushforward G).obj M') :
    (secF (structureSheafRing X) ⊤).toRightDerivedZero.app M ≫
        pullbackHgroup (CohomologyPullbackComparison.canonical G) 0 0 0 (by simp) φ =
      (secF (structureSheafRing X) ⊤).map φ ≫ (pushforwardSectionsIso G).hom.app M' ≫
        (secF (structureSheafRing X') ⊤).toRightDerivedZero.app M' := by
  rw [pullbackHgroup_eq_map_comp, ← Category.assoc,
    ← (secF (structureSheafRing X) ⊤).toRightDerivedZero.naturality φ, Category.assoc,
    toRightDerivedZero_comp_pullbackHgroup_id]

end Stacks.DeRham.GysinCohomologyBaseChange

end
