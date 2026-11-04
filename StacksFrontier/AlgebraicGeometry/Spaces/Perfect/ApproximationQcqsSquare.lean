module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.ExcisionDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback

/-!
# Approximation across an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces, let
`T ⊆ |W| \ |U|` and let `(T, E, m)` be a triple as in Stacks 08HI. If approximation holds for
`(j⁻¹T, E|_V, m)` and the sheaves `Hⁱ(E)` for `i ≥ m` are supported on `T`, then approximation
holds for `(T, E, m)`: this is the content of Stacks 08HL, proved here with no further input.

Given an approximation `α : P ⟶ E|_V`, the object `P` restricts to zero on `U ×_W V`, so the unit
`P ⟶ (j_!P)|_V` of extension by zero is invertible and `j_!P` restricts to zero on `U`. The
approximation of `E` is the transpose `j_!P ⟶ E` of `α`. Perfectness of `j_!P`, its support and
the behaviour of the transpose on cohomology are checked on `U` and on `V`, where they are
respectively trivial and the corresponding properties of `P` and `α`.

## Main results

* `AlgebraicGeometry.Space.isZero_restrictInter_of_cohomologySupportedOn`: an object of `D(𝒪_V)`
  supported over `|W| \ |U|` restricts to zero on `U ×_W V`.
* `AlgebraicGeometry.Space.approximationHolds_of_eds`: the statement of Stacks 08HL.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The two composites `U ×_W V ⟶ W` of an elementary distinguished square agree on points. -/
theorem pointsMap_edsSnd_edsEtaleHom :
    pointsMap B S hS _ ((edsSnd B S hS hsq).hom ≫ (edsEtaleHom B S hS hsq).hom) =
      pointsMap B S hS _ ((edsFst B S hS hsq).hom ≫ (edsOpenHom B S hS hsq).hom) :=
  congrArg _ (pullback.condition (f := (edsOpenHom B S hS hsq).hom)
    (g := (edsEtaleHom B S hS hsq).hom)).symm

/-- **An object of `D(𝒪_V)` supported over `|W| \ |U|` restricts to zero on `U ×_W V`.** -/
theorem isZero_restrictInter_of_cohomologySupportedOn (T : Set (points B S hS W.1))
    (hT : T ⊆ (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ)
    (P : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hP : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (pointsMap B S hS V fV ⁻¹' T) P) :
    IsZero ((edsDerivedRestrictSnd B S hS hsq).obj P) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro i
  refine isZero_of_supportOfSheaf_eq_empty B S hS _ _ ?_
  rw [supportOfSheaf_homology_etaleRestrict]
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have hx' :
      pointsMap B S hS _ ((edsSnd B S hS hsq).hom ≫ (edsEtaleHom B S hS hsq).hom) x ∈ T := by
    rw [pointsMap_comp]
    exact hP i hx
  rw [pointsMap_edsSnd_edsEtaleHom] at hx'
  exact hT hx' ⟨pointsMap B S hS _ (edsFst B S hS hsq).hom x,
    (congrFun (pointsMap_comp B S hS _ _ _) x).symm⟩

/-- A cohomology sheaf of `E` supported over `|W| \ |U|` restricts to zero on `U`. -/
theorem isZero_restrictOpen_of_supportOfSheaf_subset (T : Set (points B S hS W.1))
    (hT : T ⊆ (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ)
    (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj F) ⊆ T) :
    IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj F) := by
  refine isZero_of_supportOfSheaf_eq_empty B S hS (edsOpen B S hS hsq) _ ?_
  rw [supportOfSheaf_toSheaf_etaleModulePullback]
  exact Set.eq_empty_of_forall_notMem fun x hx => hT (hF hx) ⟨x, rfl⟩

/-- **Stacks 08HL.** Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic
spaces, `T ⊆ |W| \ |U|` and `(T, E, m)` a triple as in Stacks 08HI. If approximation holds for
`(j⁻¹T, E|_V, m)` and the sheaves `Hⁱ(E)` are supported on `T` for every `i ≥ m`, then
approximation holds for `(T, E, m)`. -/
theorem approximationHolds_of_eds (T : Set (points B S hS W.1))
    (hT : T ⊆ (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2) (m : ℤ)
    (happ : ApproximationHolds B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (pointsMap B S hS V fV ⁻¹' T)
      ((quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj E) m)
    (hsupp : ∀ i : ℤ, m ≤ i → supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E.obj)) ⊆ T) :
    ApproximationHolds B S hS W.1 W.2 T E m := by
  obtain ⟨P, hPperf, hPsupp, α, hαiso, hαepi⟩ := happ
  have hP0 := isZero_restrictInter_of_cohomologySupportedOn B S hS hsq T hT P hPsupp
  let LU := etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let LV := etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  let adjS := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
  let Q := (edsDerivedShriekEtale B S hS hsq).obj P
  have hunit : IsIso (adjS.unit.app P) := isIso_derivedUnit_edsEtale_of_isZero_restrict B S hS hsq
    P ((forall_isZero_restrict_homology_iff B S hS hsq P).2 hP0)
  have hQU : IsZero (LU.mapDerivedCategory.obj Q) :=
    isZero_restrictOpen_derivedShriekEtale B S hS hsq P hP0
  let eV : P ≅ LV.mapDerivedCategory.obj Q := asIso (adjS.unit.app P)
  let α' : P ⟶ LV.mapDerivedCategory.obj E.obj := α
  have hα'epi : Epi ((DerivedCategory.homologyFunctor _ m).map α') := hαepi
  let β : Q ⟶ E.obj := (adjS.homEquiv P E.obj).symm α'
  have hβ : eV.hom ≫ LV.mapDerivedCategory.map β = α' :=
    (adjS.homEquiv_unit (f := β)).symm.trans ((adjS.homEquiv P E.obj).apply_symm_apply α')
  have hEU : ∀ i : ℤ, m ≤ i → IsZero (LU.obj ((DerivedCategory.homologyFunctor _ i).obj E.obj)) :=
    fun i hi => isZero_restrictOpen_of_supportOfSheaf_subset B S hS hsq T hT _ (hsupp i hi)
  have hQUi : ∀ i : ℤ, IsZero (LU.obj ((DerivedCategory.homologyFunctor _ i).obj Q)) := fun i =>
    ((DerivedCategory.homologyFunctor _ i).map_isZero hQU).of_iso
      ((LU.mapDerivedCategoryHomologyIso i).app Q).symm
  have hVmap : ∀ i : ℤ, LV.map ((DerivedCategory.homologyFunctor _ i).map β) =
      ((LV.mapDerivedCategoryHomologyIso i).app Q).inv ≫
        (DerivedCategory.homologyFunctor _ i).map (eV.inv ≫ α') ≫
          ((LV.mapDerivedCategoryHomologyIso i).app E.obj).hom := fun i => by
    rw [← hβ, Iso.inv_hom_id_assoc]
    exact (NatIso.naturality_1 (LV.mapDerivedCategoryHomologyIso i) β).symm
  refine ⟨Q, ?_, fun i => ?_, β, fun i hi => ?_, ?_⟩
  · refine isPerfect_of_forall_isPerfect_etaleRestrict B S hS
      (fun b : Bool => if b then edsOpen B S hS hsq else edsEtale B S hS hsq)
      (fun b => match b with
        | true => edsOpenHom B S hS hsq
        | false => edsEtaleHom B S hS hsq)
      (fun b => match b with
        | true => isEtale_edsOpenHom B S hS hsq
        | false => isEtale_edsEtaleHom B S hS hsq) ?_ Q ?_
    · intro x
      have hx : x ∈ Set.univ := Set.mem_univ x
      rw [← range_union_range_eds B S hS hsq] at hx
      rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩
    · rintro (_ | _)
      · exact isPerfect_of_iso B S hS hPperf eV
      · exact isPerfect_of_isZero B S hS hQU
  · refine supportOfSheaf_subset_of_eds B S hS hsq _ T ?_ ?_
    · rw [(supportOfSheaf_eq_empty_iff_isZero B S hS (edsOpen B S hS hsq) _).2 (hQUi i)]
      exact Set.empty_subset _
    · let e : LV.obj ((DerivedCategory.homologyFunctor _ i).obj Q) ≅
          (DerivedCategory.homologyFunctor _ i).obj P :=
        ((LV.mapDerivedCategoryHomologyIso i).app Q).symm ≪≫
          (DerivedCategory.homologyFunctor _ i).mapIso eV.symm
      have key : ∀ {F G : Sheaf (SmallEtale.topology B S hS V) AddCommGrpCat.{u}} (e : F ≅ G),
          supportOfSheaf B S hS V F ⊆ supportOfSheaf B S hS V G := fun e =>
        supportOfSheaf_subset_of_mono B S hS V hsq.isAlgebraicSpace e.hom
      exact (key ((SheafOfModules.toSheaf _).mapIso e)).trans (hPsupp i)
  · refine isIso_of_eds B S hS hsq _ ⟨0, (hQUi i).eq_of_src _ _, (hEU i hi.le).eq_of_src _ _⟩ ?_
    rw [hVmap i, Functor.map_comp]
    have : IsIso ((DerivedCategory.homologyFunctor _ i).map α') := hαiso i hi
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' IsIso.comp_isIso inferInstance)
  · refine epi_of_eds B S hS hsq _ ⟨fun g h _ => (hEU m le_rfl).eq_of_src g h⟩ ?_
    rw [hVmap m, Functor.map_comp]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' (epi_comp' (IsIso.epi_of_iso _) hα'epi)
      (IsIso.epi_of_iso _))

end AlgebraicGeometry.Space

end
