module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechHodgeClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.RefinementDerivedCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective

/-!
# Pullback of Čech classes

Let `h : (Z', 𝒪_{Z'}) ⟶ (Z, 𝒪_Z)` be a morphism of ringed spaces and `𝒰 = (Uᵢ)` an open covering
of `Z`, so that `h⁻¹𝒰 = (h⁻¹Uᵢ)` is an open covering of `Z'`. For a complex `𝒦'` of
`𝒪_{Z'}`-modules a section of `h_*𝒦'` over `U_{i₀} ∩ ⋯ ∩ U_{iₚ}` is a section of `𝒦'` over its
inverse image; restricting it to `h⁻¹U_{i₀} ∩ ⋯ ∩ h⁻¹U_{iₚ}` gives a morphism of total Čech
complexes `Tot(Č(𝒰, h_*𝒦')) ⟶ Tot(Č(h⁻¹𝒰, 𝒦'))`, linear over `Γ(Z, 𝒪_Z)`: the refinement map of
[Stacks, Tag 01FD] attached to the counit `h^*h_*𝒦' ⟶ 𝒦'`.

This file proves that the pullback `Hⁿ(Z, 𝒦) ⟶ Hⁿ(Z', 𝒦')` along a morphism of bounded below
complexes `φ : 𝒦 ⟶ h_*𝒦'` (`Stacks.HodgeWeil.cohomologyPullback`) carries the class, under the
comparison of [Stacks, Tag 08BN], of a class `x` of `Hⁿ(Tot(Č(𝒰, 𝒦)))` to the class of the image
of `x` in `Hⁿ(Tot(Č(h⁻¹𝒰, 𝒦')))`. Read on a Čech cocycle of a sheaf of modules placed in degree
`0`, the image of the cocycle is computed explicitly. For Hodge cohomology this says that the
pullback `g'^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S'})` of a commutative square
`g' ≫ f = f' ≫ g` of schemes (Tag 0FM4) sends the class of a Čech cocycle `c` of `Ω^p_{X/S}` on
`𝒰` to the class of the Čech cocycle of `Ω^p_{X'/S'}` on `g'⁻¹𝒰` obtained by pulling back the
forms `c_{i₀…i_q}` along `g'` and restricting them to `g'⁻¹U_{i₀} ∩ ⋯ ∩ g'⁻¹U_{i_q}`.

## Main definitions

* `Stacks.HodgeWeil.cechPullbackTotalMap`: the map `Tot(Č(𝒰, h_*𝒦')) ⟶ Tot(Č(h⁻¹𝒰, 𝒦'))`.
* `Stacks.HodgeWeil.cechPullbackHomology`: the induced map on cohomology, with values in the
  cohomology of `Tot(Č(h⁻¹𝒰, 𝒦'))` read over `Γ(Z, 𝒪_Z)`.
* `Stacks.HodgeWeil.preimageCochain`: a Čech cochain of `h_*𝒢'` on `𝒰`, read as a Čech cochain
  of `𝒢'` on `h⁻¹𝒰`.
* `Stacks.HodgeWeil.pullbackCochain`: the pullback of a Čech cochain of differential forms along
  a commutative square of schemes.

## Main results

* `Stacks.HodgeWeil.cohomologyPullback_cechBaseClass`: **the pullback of a Čech class is the Čech
  class of the image of the Čech cohomology class.**
* `Stacks.HodgeWeil.cohomologyPullback_cechSheafClass_of_preimageCochain`: the same for the class
  of an explicit Čech cocycle of a sheaf of modules.
* `Stacks.HodgeWeil.cechD_pullbackCochain_eq_zero`: the pullback of a Čech cocycle of differential
  forms is a Čech cocycle.
* `Stacks.HodgeWeil.hodgePullback_hodgeCechClass`: **the Hodge pullback of the class of a Čech
  cocycle is the class of the pulled back cocycle.**

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry ComplexShape
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.LerayCupPairing (restrictGlobal)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.CechDerived (cechBicomplex cechAugmentationInt)
open Stacks.Cohomology.CechRefinement (cechBicomplexRefinementMap cechComplexRefinementMapInt
  cechComplexRefinementMap cechComplexRefinementMap_comp_map_π
  cechComplexRefinementMapInt_naturality pushforwardCounit cechAugmentationInt_pushforwardCounit)
open RingedSpaceModuleAdjunction (modulePushforward)
open Stacks.Cech.Hypercohomology (singlePlus cochainOfAt sliceCochain cocycleClass)
open Stacks.Cohomology.CechSheaf (abSections coverObject SectionRing)
open Stacks.Cech.LinearCupProduct (ιTotalCechTo)
open Stacks.Cohomology (restrictGlobalScalars)
open Stacks.Cohomology.CechDerived (cechComplexNatFunctor)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard


section General

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  Stacks.Cohomology.CechSheaf.sectionsPresheaf Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover
  cechComplexNatFunctor
  Stacks.Cohomology.CechDerived.cechComplexIntFunctor ComplexShape.Embedding.extendFunctor
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {Z Z' : RingedSpace.{u, u}} (h : Z' ⟶ Z) {I : Type u} (U : I → Opens Z.carrier)
  (hU : (⊤ : Opens Z.carrier) = ⨆ i, U i)
  (hU' : (⊤ : Opens Z'.carrier) = ⨆ i, (Opens.map h.hom.base).obj (U i))

/-- **The Čech complex of `h_*𝒦'` on `𝒰` maps to that of `𝒦'` on `h⁻¹𝒰`**: the map of total
Čech complexes `Tot(Č(𝒰, h_*𝒦')) ⟶ Tot(Č(h⁻¹𝒰, 𝒦'))`, the target read over `Γ(Z, 𝒪_Z)`. On
the summand of a tuple it is the identification of the sections of `h_*𝒦'` over an intersection
of the `Uᵢ` with the sections of `𝒦'` over its inverse image, restricted to the intersection of
the inverse images. -/
def cechPullbackTotalMap (K' : CochainComplex (Modules Z') ℤ) :
    (Cech.Linear.totalCechComplexFunctor Z.carrier (ringCatSheaf Z) ⊤ U hU).obj
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K') ⟶
      ((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).obj
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K') :=
  HomologicalComplex₂.total.map ((HomologicalComplex₂.flipFunctor _ _ _).map
      (cechBicomplexRefinementMap h _ U hU' hU id (fun _ => le_rfl) K')) (up ℤ) ≫
    HomologicalComplex₂.TotalMap.totalMap (restrictGlobalScalars h)
      (cechBicomplex (ringCatSheaf Z') ⊤ _ hU' K').flip

/-- The map of total Čech complexes on the summand of bidegree `(p, q)`: the Čech refinement map
of the counit `h^*h_*𝒦'^q ⟶ 𝒦'^q` in Čech degree `p`. -/
theorem ιTotal_comp_cechPullbackTotalMap (K' : CochainComplex (Modules Z') ℤ) (p q n : ℤ)
    (hpq : p + q = n) :
    (cechBicomplex (ringCatSheaf Z) ⊤ U hU
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).flip.ιTotal (up ℤ) p q n
        hpq ≫ (cechPullbackTotalMap h U hU hU' K').f n =
      (cechComplexRefinementMapInt h (K'.X q) ((modulePushforward h).obj (K'.X q))
          (pushforwardCounit h (K'.X q)) (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id
          (fun _ => le_rfl)).f p ≫
        (restrictGlobalScalars h).map
          ((cechBicomplex (ringCatSheaf Z') ⊤ _ hU' K').flip.ιTotal (up ℤ) p q n hpq) := by
  have hmap := HomologicalComplex₂.TotalMap.ι_totalMapf
    (restrictGlobalScalars h) (cechBicomplex (ringCatSheaf Z') ⊤ _ hU' K').flip
    (c₁₂ := up ℤ) n p q hpq
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ (HomologicalComplex₂.TotalMap.totalMap
      (restrictGlobalScalars h)
      (cechBicomplex (ringCatSheaf Z') ⊤ _ hU' K').flip).f n)
    (HomologicalComplex₂.ιTotal_map _ _ _ (up ℤ) p q n hpq)) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) hmap

/-- **The map of total Čech complexes is natural in `𝒦'`.** -/
theorem cechPullbackTotalMap_naturality {K' L' : CochainComplex (Modules Z') ℤ} (a : K' ⟶ L') :
    (Cech.Linear.totalCechComplexFunctor Z.carrier (ringCatSheaf Z) ⊤ U hU).map
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).map a) ≫
      cechPullbackTotalMap h U hU hU' L' =
    cechPullbackTotalMap h U hU hU' K' ≫
      ((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).map
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').map a) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex₂.total.hom_ext (up ℤ) fun p q hpq => ?_
  have hnat := congrArg (fun k => HomologicalComplex.Hom.f k p)
    (cechComplexRefinementMapInt_naturality h (K'.X q) ((modulePushforward h).obj (K'.X q))
      (pushforwardCounit h (K'.X q)) (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id
      (fun _ => le_rfl) (pushforwardCounit h (L'.X q)) ((modulePushforward h).map (a.f q))
      (a.f q) (by
        dsimp only [pushforwardCounit]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id,
          Category.id_comp]))
  simp only [HomologicalComplex.comp_f] at hnat
  have eR := (Category.assoc _ _ _).symm.trans
    ((eq_whisker (ιTotal_comp_cechPullbackTotalMap h U hU hU' K' p q n hpq)
      ((((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).map
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').map a)).f n)).trans
      (Category.assoc _ _ _))
  have eT := ((restrictGlobalScalars h).map_comp _ _).symm.trans
    ((congrArg (restrictGlobalScalars h).map
      (HomologicalComplex₂.ιTotal_map _ _ ((HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
        (((Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').mapHomologicalComplex (up ℤ)).map a))
        (up ℤ) p q n hpq)).trans
      ((restrictGlobalScalars h).map_comp _ _))
  refine Eq.trans ?_ eR.symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (HomologicalComplex₂.ιTotal_map _ _
    ((HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ)).map
      (((Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringCatSheaf Z) ⊤ U
        hU).mapHomologicalComplex (up ℤ)).map
          (((modulePushforward h).mapHomologicalComplex (up ℤ)).map a)))
    (up ℤ) p q n hpq) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (ιTotal_comp_cechPullbackTotalMap h U hU hU' L' p q n hpq)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker hnat _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq _ eT.symm

/-- **The map of total Čech complexes is compatible with the augmentations** of
[Stacks, Tag 07M9]: `Γ(Z, h_*𝒦') = Γ(Z', 𝒦')`. -/
theorem sectionsToTotalCech_comp_cechPullbackTotalMap (K' : CochainComplex (Modules Z') ℤ) :
    (Cech.Linear.sectionsToTotalCech Z.carrier (ringCatSheaf Z) ⊤ U hU).app
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K') ≫
      cechPullbackTotalMap h U hU hU' K' =
    ((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).map
      ((Cech.Linear.sectionsToTotalCech Z'.carrier (ringCatSheaf Z') ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU').app K') := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have e1 := ιTotal_comp_cechPullbackTotalMap h U hU hU' K' 0 n n (zero_add n)
  have e2 := cechAugmentationInt_pushforwardCounit h (K'.X n)
    (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl)
  refine (HomologicalComplex.comp_f _ _ n).trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ (cechPullbackTotalMap h U hU hU' K').f n)
    (Cech.Linear.sectionsToTotalCech_app_f _ _ _ _ _ _ n)) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun z => cechAugmentationInt (ringCatSheaf Z) ⊤ U hU
    ((modulePushforward h).obj (K'.X n)) ≫ z) e1) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ (restrictGlobalScalars h).map
    ((cechBicomplex (ringCatSheaf Z') ⊤ _ hU' K').flip.ιTotal (up ℤ) 0 n n (zero_add n))) e2) ?_
  refine ((restrictGlobalScalars h).map_comp _ _).symm.trans ?_
  exact congrArg (restrictGlobalScalars h).map
    (Cech.Linear.sectionsToTotalCech_app_f _ _ _ _ _ _ n).symm

/-- **The map on cohomology of total Čech complexes**
`Hⁿ(Tot(Č(𝒰, h_*𝒦'))) ⟶ Hⁿ(Tot(Č(h⁻¹𝒰, 𝒦')))`, linear over `Γ(Z, 𝒪_Z)`: the map induced by
`cechPullbackTotalMap`, followed by the identification of the cohomology of a complex with
scalars restricted with the restriction of scalars of its cohomology. -/
def cechPullbackHomology (K' : CochainComplex (Modules Z') ℤ) (n : ℤ) :
    ((Cech.Linear.totalCechComplexFunctor Z.carrier (ringCatSheaf Z) ⊤ U hU).obj
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).homology n ⟶
      (restrictGlobal h).obj
        (((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').homology n) :=
  HomologicalComplex.homologyMap (cechPullbackTotalMap h U hU hU' K') n ≫
    ((((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').sc n).mapHomologyIso
        (restrictGlobal h)).hom

/-- The identification of the homology of a complex with scalars restricted is natural. -/
private theorem homologyMap_comp_mapHomologyIso_hom
    {A B : CochainComplex (ModuleCat (SectionRing (ringCatSheaf Z') ⊤)) ℤ} (f : A ⟶ B) (n : ℤ) :
    HomologicalComplex.homologyMap (((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).map f)
        n ≫ ((B.sc n).mapHomologyIso (restrictGlobal h)).hom =
      ((A.sc n).mapHomologyIso (restrictGlobal h)).hom ≫
        (restrictGlobal h).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (up ℤ) n).map f) (restrictGlobal h)

/-- **The map on cohomology of total Čech complexes is natural in `𝒦'`.** -/
theorem cechPullbackHomology_naturality {K' L' : CochainComplex (Modules Z') ℤ} (a : K' ⟶ L')
    (n : ℤ) :
    HomologicalComplex.homologyMap
        ((Cech.Linear.totalCechComplexFunctor Z.carrier (ringCatSheaf Z) ⊤ U hU).map
          (((modulePushforward h).mapHomologicalComplex (up ℤ)).map a)) n ≫
      cechPullbackHomology h U hU hU' L' n =
    cechPullbackHomology h U hU hU' K' n ≫
      (restrictGlobal h).map (HomologicalComplex.homologyMap
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').map a) n) := by
  have hc := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (cechPullbackTotalMap_naturality h U hU hU' a)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have hiso := homologyMap_comp_mapHomologyIso_hom h
    ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').map a) n
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker hc _).trans ((Category.assoc _ _ _).trans
    ((whisker_eq _ hiso).trans (Category.assoc _ _ _).symm)))

/-- **The map on cohomology of total Čech complexes after the augmentations**: on the classes of
global cocycles it is the identification `Γ(Z, h_*𝒦') = Γ(Z', 𝒦')`. -/
theorem homologyMap_sectionsToTotalCech_comp_cechPullbackHomology
    (K' : CochainComplex (Modules Z') ℤ) (n : ℤ) :
    HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z.carrier
        (ringCatSheaf Z) ⊤ U hU).app (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj
          K')) n ≫ cechPullbackHomology h U hU hU' K' n =
      ((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj K').sc
          n).mapHomologyIso (restrictGlobal h)).hom ≫
        (restrictGlobal h).map (HomologicalComplex.homologyMap
          ((Cech.Linear.sectionsToTotalCech Z'.carrier (ringCatSheaf Z') ⊤
            (fun i => (Opens.map h.hom.base).obj (U i)) hU').app K') n) := by
  have hc := (HomologicalComplex.homologyMap_comp ((Cech.Linear.sectionsToTotalCech
      Z.carrier (ringCatSheaf Z) ⊤ U hU).app (((modulePushforward h).mapHomologicalComplex
        (up ℤ)).obj K')) (cechPullbackTotalMap h U hU hU' K') n).symm.trans
    (congrArg (fun k => HomologicalComplex.homologyMap k n)
      (sectionsToTotalCech_comp_cechPullbackTotalMap h U hU hU' K'))
  have hiso := homologyMap_comp_mapHomologyIso_hom h
    ((Cech.Linear.sectionsToTotalCech Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').app K') n
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker hc _).trans hiso)

/-- `homologyMap_sectionsToTotalCech_comp_cechPullbackHomology` on the class of a global
cocycle `s`, read on `Z'` through the identification of cycles. -/
theorem cechPullbackHomology_homologyπ (K' : CochainComplex (Modules Z') ℤ) (n : ℤ)
    (s : ((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
      K').sc n).map (restrictGlobal h)).cycles) :
    (cechPullbackHomology h U hU hU' K' n).hom ((HomologicalComplex.homologyMap
        ((Cech.Linear.sectionsToTotalCech Z.carrier (ringCatSheaf Z) ⊤ U hU).app
          (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')) n).hom
        (((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
          K').sc n).map (restrictGlobal h)).homologyπ.hom s)) =
      (HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z'.carrier
          (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU').app K') n).hom
        ((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
          K').homologyπ n).hom (((((Cech.Linear.sectionsComplexFunctor Z'.carrier
            (ringCatSheaf Z') ⊤).obj K').sc n).mapCyclesIso (restrictGlobal h)).hom.hom s)) := by
  have h1 := ConcreteCategory.congr_hom
    (homologyMap_sectionsToTotalCech_comp_cechPullbackHomology h U hU hU' K' n)
    (((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
      K').sc n).map (restrictGlobal h)).homologyπ.hom s)
  have h2 := ConcreteCategory.congr_hom (ShortComplex.homologyπ_comp_mapHomologyIso_hom
    (((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj K').sc n)
    (restrictGlobal h)) s
  exact h1.trans (congrArg (HomologicalComplex.homologyMap
    ((Cech.Linear.sectionsToTotalCech Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').app K') n).hom h2)

/-- **The map on cohomology of total Čech complexes on the class of a cocycle**: the class of a
cocycle `w` of `Tot(Č(𝒰, h_*𝒦'))` goes to the class of any cocycle `w'` of
`Tot(Č(h⁻¹𝒰, 𝒦'))` whose value is the image of the value of `w`. -/
theorem cechPullbackHomology_cocycleClass (K' : CochainComplex (Modules Z') ℤ) (n : ℤ)
    (w : Stacks.Cech.Hypercohomology.unitModule
        (SectionRing (ringCatSheaf Z) ⊤) ⟶
      ((Cech.Linear.totalCechComplexFunctor Z.carrier (ringCatSheaf Z) ⊤ U hU).obj
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).X n)
    (hw : w ≫ ((Cech.Linear.totalCechComplexFunctor Z.carrier (ringCatSheaf Z) ⊤ U
      hU).obj (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).d n (n + 1) = 0)
    (w' : Stacks.Cech.Hypercohomology.unitModule
        (SectionRing (ringCatSheaf Z') ⊤) ⟶
      ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').X n)
    (hw' : w' ≫ ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').d n (n + 1) = 0)
    (hww : (w ≫ (cechPullbackTotalMap h U hU hU' K').f n).hom 1 = w'.hom 1) :
    (cechPullbackHomology h U hU hU' K' n).hom
        ((cocycleClass n w hw).hom 1) =
      (cocycleClass n w' hw').hom 1 := by
  have hw2 : (w ≫ (cechPullbackTotalMap h U hU hU' K').f n) ≫
      (((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).obj
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K')).d n (n + 1) = 0 :=
    (Category.assoc _ _ _).trans ((whisker_eq w ((cechPullbackTotalMap h U hU hU' K').comm n
      (n + 1))).trans ((Category.assoc _ _ _).symm.trans ((eq_whisker hw _).trans zero_comp)))
  have e0 := ConcreteCategory.congr_hom (Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap
    (cechPullbackTotalMap h U hU hU' K') n w hw) 1
  have e2 := ConcreteCategory.congr_hom (ShortComplex.homologyπ_comp_mapHomologyIso_hom
    (((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').sc n) (restrictGlobal h))
    ((HomologicalComplex.liftCycles _ (w ≫ (cechPullbackTotalMap h U hU hU' K').f n) (n + 1)
      (CochainComplex.next ℤ n) hw2).hom 1)
  have e3 : ((((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').sc n).mapCyclesIso
        (restrictGlobal h)).hom.hom
        ((HomologicalComplex.liftCycles _ (w ≫ (cechPullbackTotalMap h U hU hU' K').f n) (n + 1)
          (CochainComplex.next ℤ n) hw2).hom 1) =
      (HomologicalComplex.liftCycles _ w' (n + 1) (CochainComplex.next ℤ n) hw').hom 1 := by
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles
      ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K') n)).1 inferInstance
    refine (ConcreteCategory.congr_hom ((((Cech.Linear.totalCechComplexFunctor Z'.carrier
      (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').sc
        n).mapCyclesIso_hom_iCycles (restrictGlobal h)) _).trans ?_
    refine (ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i
      (((restrictGlobalScalars h).mapHomologicalComplex (up ℤ)).obj
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K'))
      (w ≫ (cechPullbackTotalMap h U hU hU' K').f n) (n + 1) (CochainComplex.next ℤ n) hw2)
      1).trans ?_
    exact hww.trans (ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i
      ((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K') w' (n + 1)
      (CochainComplex.next ℤ n) hw') 1).symm
  exact (congrArg ((((Cech.Linear.totalCechComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤
    (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj K').sc n).mapHomologyIso
      (restrictGlobal h)).hom.hom e0).trans (e2.trans (congrArg
        ((restrictGlobal h).map (HomologicalComplex.homologyπ _ n)).hom e3))

/-- The intersection of the inverse images of the members of a family of opens selected by a
tuple is contained in the inverse image of their intersection. -/
theorem cechInter_map_le {T T' : TopCat.{u}} (k : T' ⟶ T) {J : Type u} (W : J → Opens T)
    {m : ℕ} (s : Fin m → J) :
    CechCochains.inter (fun j => (Opens.map k).obj (W j)) s ≤
      (Opens.map k).obj (CechCochains.inter W s) := by
  intro z hz
  have hz' : ∀ a, z ∈ (Opens.map k).obj (W (s a)) := fun a =>
    (iInf_le (fun a => (Opens.map k).obj (W (s a))) a) hz
  show k z ∈ (⨅ a, W (s a) : Opens T)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact hz'

/-- **A Čech cochain of `h_*𝒢'` on `𝒰` read as a Čech cochain of `𝒢'` on `h⁻¹𝒰`**: a section of
`h_*𝒢'` over `⋂ⱼ U_{s j}` is a section of `𝒢'` over `h⁻¹(⋂ⱼ U_{s j})`, restricted to
`⋂ⱼ h⁻¹U_{s j}`. -/
def preimageCochain (G' : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) {q : ℕ}
    (d : CechCochains.Cochain U
      (abSections ((StacksDraft.KFlat.modulePushforward h).obj G')) q) :
    CechCochains.Cochain (fun i => (Opens.map h.hom.base).obj (U i))
      (abSections G') q :=
  fun s => CechCochains.restr (abSections G')
    (cechInter_map_le h.hom.base U s) (d s)

/-- The Čech refinement map of the counit in a nonnegative integer degree, read through the
identifications of the extended Čech complexes with the Čech complexes. -/
theorem extendXIso_inv_comp_cechComplexRefinementMapInt_f (G' : Modules Z') (p : ℕ) :
    (((cechComplexNatFunctor (ringCatSheaf Z) ⊤ U hU).obj
        ((modulePushforward h).obj G')).extendXIso ComplexShape.embeddingUpNat
          (i := p) (i' := (p : ℤ)) rfl).inv ≫
      (cechComplexRefinementMapInt h G' ((modulePushforward h).obj G') (pushforwardCounit h G')
        (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl)).f (p : ℤ) =
    (cechComplexRefinementMap h G' ((modulePushforward h).obj G') (pushforwardCounit h G')
        (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl)).f p ≫
      (restrictGlobalScalars h).map
        (((cechComplexNatFunctor (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj G').extendXIso
            ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv := by
  have e1 := HomologicalComplex.extendMap_f (cechComplexRefinementMap h G'
    ((modulePushforward h).obj G') (pushforwardCounit h G')
      (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl))
    ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl
  have e2 := Stacks.DerivedIndexing.extendXIso_inv_comp_mapExtendIso_hom_f
    (restrictGlobalScalars h) ComplexShape.embeddingUpNat
    ((cechComplexNatFunctor (ringCatSheaf Z') ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj G') (i := p) (i' := (p : ℤ)) rfl
  refine (whisker_eq _ (HomologicalComplex.comp_f _ _ _)).trans ?_
  refine (whisker_eq _ (eq_whisker e1 _)).trans ?_
  refine (whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (Category.assoc _ _ _)))).trans ?_
  refine (Iso.inv_hom_id_assoc _ _).trans ?_
  exact whisker_eq _ e2

/-- **The map of total Čech complexes on a homogeneous summand**: on the Čech `p`-cochains of
`h_*𝒦'^a` it is the Čech refinement map of the counit, followed by the inclusion of the
summand. -/
theorem extendXIso_inv_ιTotal_comp_cechPullbackTotalMap (K' : CochainComplex (Modules Z') ℤ)
    (p : ℕ) (a n : ℤ) (hpa : (p : ℤ) + a = n) :
    (((cechComplexNatFunctor (ringCatSheaf Z) ⊤ U hU).obj
        ((modulePushforward h).obj (K'.X a))).extendXIso ComplexShape.embeddingUpNat
          (i := p) (i' := (p : ℤ)) rfl).inv ≫
      (cechBicomplex (ringCatSheaf Z) ⊤ U hU
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).flip.ιTotal (up ℤ) p a n
        hpa ≫ (cechPullbackTotalMap h U hU hU' K').f n =
    (cechComplexRefinementMap h (K'.X a) ((modulePushforward h).obj (K'.X a))
        (pushforwardCounit h (K'.X a)) (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id
        (fun _ => le_rfl)).f p ≫
      (restrictGlobalScalars h).map
        ((((cechComplexNatFunctor (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj (K'.X a)).extendXIso
            ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv ≫
          (cechBicomplex (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
            K').flip.ιTotal (up ℤ) p a n hpa) := by
  have e1 := ιTotal_comp_cechPullbackTotalMap h U hU hU' K' p a n hpa
  have e2 := extendXIso_inv_comp_cechComplexRefinementMapInt_f h U hU hU' (K'.X a) p
  refine (whisker_eq _ e1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker e2 _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq _ ((restrictGlobalScalars h).map_comp _ _).symm

/-- **The Čech refinement map of the counit on the cochain of an explicit Čech cochain**: it is
the cochain of the same Čech cochain read on `h⁻¹𝒰`. -/
theorem cechComplexRefinementMap_sliceCochain
    (G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) {q : ℕ}
    (d : CechCochains.Cochain U
      (abSections ((StacksDraft.KFlat.modulePushforward h).obj G')) q) :
    ((cechComplexRefinementMap h G' ((modulePushforward h).obj G') (pushforwardCounit h G')
        (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl)).f q).hom
        (sliceCochain (O := Z.sheaf) U hU
          ((StacksDraft.KFlat.modulePushforward h).obj G') d) =
      sliceCochain (O := Z'.sheaf)
        (fun i => (Opens.map h.hom.base).obj (U i)) hU' G' (preimageCochain h U G' d) := by
  refine Stacks.Cohomology.CechSheaf.mcech_ext ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
    G' _ _ fun x => ?_
  rw [Stacks.Cech.Hypercohomology.mcomp_sliceCochain]
  have hπ := ConcreteCategory.congr_hom (cechComplexRefinementMap_comp_map_π
    (U := fun i => (Opens.map h.hom.base).obj (U i)) (V := U) (hU := hU') (hV := hU) (c := id)
    (hc := fun _ => le_rfl) h (pushforwardCounit h G') q x)
    (sliceCochain (O := Z.sheaf) U hU
      ((StacksDraft.KFlat.modulePushforward h).obj G') d)
  have hm := Stacks.Cohomology.CechSheaf.res_mcomp ⊤ U hU
    ((StacksDraft.KFlat.modulePushforward h).obj G')
    (sliceCochain (O := Z.sheaf) U hU
      ((StacksDraft.KFlat.modulePushforward h).obj G') d) x
  have hs := Stacks.Cech.Hypercohomology.mcomp_sliceCochain (O := Z.sheaf) U hU
    ((StacksDraft.KFlat.modulePushforward h).obj G') d x
  show Stacks.Cohomology.Basis.res (abSections G')
    (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU' x).ge
    (Stacks.Cohomology.CechSheaf.rawcomp ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU' G'
      _ x) = _
  refine (congrArg (Stacks.Cohomology.Basis.res (abSections G')
    (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU' x).ge) hπ).trans ?_
  have hsr := congrArg (fun k => NatTrans.app k (op (CategoryTheory.CechComplex.inter
      (coverObject U hU) (id ∘ x))))
    (Stacks.Cohomology.CechRefinement.sectionsRefinement_pushforwardCounit h G')
  refine (congrArg (fun k => Stacks.Cohomology.Basis.res
    (abSections G')
    (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤
      (fun i => (Opens.map h.hom.base).obj (U i)) hU' x).ge
    (ConcreteCategory.hom (CategoryTheory.CechComplex.π
      (coverObject U hU)
      (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ ((modulePushforward h).obj G')) q (id ∘ x) ≫
        k ≫ (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ G' ⋙
          restrictGlobalScalars h).map
          (Stacks.Cohomology.CechRefinement.refinementInclusion h
            (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl) q x).op)
      (sliceCochain (O := Z.sheaf) U hU
        ((StacksDraft.KFlat.modulePushforward h).obj G') d))) hsr).trans ?_
  show Stacks.Cohomology.Basis.res (abSections G')
      (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU' x).ge
      (Stacks.Cohomology.Basis.res (abSections G')
        (Stacks.Cohomology.CechRefinement.inter_le_map_inter h
          (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl) q x)
        (Stacks.Cohomology.CechSheaf.rawcomp ⊤ U hU ((StacksDraft.KFlat.modulePushforward h).obj G')
          (sliceCochain (O := Z.sheaf) U hU
            ((StacksDraft.KFlat.modulePushforward h).obj G') d) x)) = _
  rw [← hm, hs]
  show Stacks.Cohomology.Basis.res (abSections G')
      (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU' x).ge
      (Stacks.Cohomology.Basis.res (abSections G')
        (Stacks.Cohomology.CechRefinement.inter_le_map_inter h
          (fun i => (Opens.map h.hom.base).obj (U i)) U hU' hU id (fun _ => le_rfl) q x)
        (Stacks.Cohomology.Basis.res (abSections G')
          (show (Opens.map h.hom.base).obj (CategoryTheory.CechComplex.inter
              (coverObject U hU) x).left ≤
            (Opens.map h.hom.base).obj (Stacks.CategoryTheory.CechComplex.inter U x) from
            fun z hz => (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤ U hU x).le hz)
          (Stacks.Cohomology.Basis.res (abSections G')
            (show (Opens.map h.hom.base).obj (Stacks.CategoryTheory.CechComplex.inter U x) ≤
              (Opens.map h.hom.base).obj (CechCochains.inter U x) from
              fun z hz => (Stacks.Cech.cechComplexInter_eq U x).le hz) (d x)))) =
    Stacks.Cohomology.Basis.res (abSections G')
      (Stacks.Cech.cechComplexInter_eq (fun i => (Opens.map h.hom.base).obj (U i)) x).le
      (Stacks.Cohomology.Basis.res (abSections G')
        (cechInter_map_le h.hom.base U x) (d x))
  rw [Stacks.Cohomology.Basis.res_res, Stacks.Cohomology.Basis.res_res]
  exact (Stacks.Cohomology.Basis.res_res _ _ _ _).trans
    (Stacks.Cohomology.Basis.res_res _ _ _ _).symm

end General

section Cochains

open Stacks.Cech.Hypercohomology

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {T : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
  {J : Type u} (W : J → Opens T) (hW : ⊤ = ⨆ j, W j) (F : SheafOfModules.{u} (ringSheaf O))

/-- **The cochain of an explicit Čech cochain pushed along a morphism out of `ℱ[0]`**: for a
morphism of complexes `φ : ℱ[0] ⟶ 𝓛`, the image of the cochain attached to `c` is the cochain
attached to the image of `c` under the degree-`0` component of `φ`, placed in Čech degree `q`
and degree `0` of `𝓛`. -/
theorem cochainOfAt_comp_cech_map {L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ}
    (φ : (singlePlus O F 0).obj ⟶ L) {q : ℕ}
    (c : CechCochains.Cochain W (abSections F) q) :
    cochainOfAt W hW F 0 c ≫ ((cech O W hW).map φ).f ((q : ℤ) + 0) =
      sliceMor W hW (L.X 0) (Cohomology.CechOne.push W ((SheafOfModules.toSheaf _).map
          ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c) ≫
        ιTotalCechTo (coverObject W hW)
          (SectionRing (ringSheaf O) ⊤)
          ((Cech.Refinement.sectionsComplex O).obj L) q 0 ((q : ℤ) + 0) rfl := by
  have hι := Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map
    (coverObject W hW)
    (SectionRing (ringSheaf O) ⊤)
    ((Cech.Refinement.sectionsComplex O).map φ) q 0 _ rfl
  have hm := sliceMor_map W hW ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫
    φ.f 0) c
  have hc := (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp
    (coverObject W hW)
    (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor ⊤).map
      (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv)
    ((Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor ⊤).map (φ.f 0)) q).symm.trans
    (congrArg (fun k => Stacks.Cech.LinearCupProduct.cechCochainsMap
      (coverObject W hW)
      (SectionRing (ringSheaf O) ⊤) k q)
      ((Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor ⊤).map_comp
        (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv (φ.f 0)).symm)
  refine (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ hι))).trans ?_)
  refine (whisker_eq _ (Category.assoc _ _ _).symm).trans ?_
  refine (whisker_eq _ (eq_whisker hc _)).trans ?_
  exact (Category.assoc _ _ _).symm.trans (eq_whisker hm _)

/-- `cochainOfAt_comp_cech_map` on the generator. -/
theorem cochainOfAt_comp_cech_map_apply_one
    {L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ} (φ : (singlePlus O F 0).obj ⟶ L)
    {q : ℕ} (c : CechCochains.Cochain W (abSections F) q) :
    (cochainOfAt W hW F 0 c ≫ ((cech O W hW).map φ).f ((q : ℤ) + 0)).hom 1 =
      (ιTotalCechTo (coverObject W hW)
          (SectionRing (ringSheaf O) ⊤)
          ((Cech.Refinement.sectionsComplex O).obj L) q 0 ((q : ℤ) + 0) rfl).hom
        (sliceCochain W hW (L.X 0) (Cohomology.CechOne.push W
          ((SheafOfModules.toSheaf _).map
            ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c)) :=
  (ConcreteCategory.congr_hom (cochainOfAt_comp_cech_map W hW F φ c) 1).trans
    (congrArg (ιTotalCechTo
      (coverObject W hW)
      (SectionRing (ringSheaf O) ⊤)
      ((Cech.Refinement.sectionsComplex O).obj L) q 0 ((q : ℤ) + 0) rfl).hom
      (toMor_apply_one _))

/-- The cochain of the total Čech complex of `ℱ[0]` attached to an explicit Čech cochain, on the
generator. -/
theorem cochainOfAt_apply_one {q : ℕ}
    (c : CechCochains.Cochain W (abSections F) q) :
    (cochainOfAt W hW F 0 c).hom 1 =
      (ιTotalCechTo (coverObject W hW)
          (SectionRing (ringSheaf O) ⊤)
          ((Cech.Refinement.sectionsComplex O).obj (singlePlus O F 0).obj) q 0
          ((q : ℤ) + 0) rfl).hom
        (sliceCochain W hW ((singlePlus O F 0).obj.X 0) (Cohomology.CechOne.push W
          ((SheafOfModules.toSheaf _).map
            (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv).hom q c)) := by
  have hm := sliceMor_map W hW (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv c
  refine (ConcreteCategory.congr_hom ((Category.assoc _ _ _).symm.trans (eq_whisker hm _)) 1).trans
    ?_
  exact congrArg (ιTotalCechTo
    (coverObject W hW)
    (SectionRing (ringSheaf O) ⊤)
    ((Cech.Refinement.sectionsComplex O).obj (singlePlus O F 0).obj) q 0
      ((q : ℤ) + 0) rfl).hom (toMor_apply_one _)

/-- `cochainOfAt_comp_cech_map` on the generator, followed by a further morphism. -/
theorem cochainOfAt_comp_cech_map_comp_apply_one
    {L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ} (φ : (singlePlus O F 0).obj ⟶ L)
    {M : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)} {q : ℕ}
    (ψ : ((cech O W hW).obj L).X ((q : ℤ) + 0) ⟶ M)
    (c : CechCochains.Cochain W (abSections F) q) :
    (cochainOfAt W hW F 0 c ≫ ((cech O W hW).map φ).f ((q : ℤ) + 0) ≫ ψ).hom 1 =
      ψ.hom ((ιTotalCechTo
          (coverObject W hW)
          (SectionRing (ringSheaf O) ⊤)
          ((Cech.Refinement.sectionsComplex O).obj L) q 0 ((q : ℤ) + 0) rfl).hom
        (sliceCochain W hW (L.X 0) (Cohomology.CechOne.push W
          ((SheafOfModules.toSheaf _).map
            ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c))) :=
  congrArg ψ.hom (cochainOfAt_comp_cech_map_apply_one W hW F φ c)

end Cochains

section Classes

variable (S : RingedSpace.{u, u}) {J : Type u} (V : J → Opens S.carrier)
  (hV : (⊤ : Opens S.carrier) = ⨆ j, V j)

/-- **`cechBaseClass` is natural in the complex.** -/
theorem cechBaseClass_naturality
    {K L : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))} (f : K ⟶ L)
    (n : ℤ) :
    cechBaseClass S V hV K n ≫ (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Cohomology.GlobalKunneth.baseRing S)) n).map
        ((Cohomology.GlobalKunneth.baseSections S).map (DerivedCategory.Q.map f.hom)) =
      HomologicalComplex.homologyMap
        ((Cech.Linear.totalCechComplexFunctor S.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ V
          hV).map f.hom) n ≫ cechBaseClass S V hV L n := by
  have h1 := (Stacks.Cech.CupProductSquare.cechToBaseSections S V hV).naturality f
  have h2 := (DerivedCategory.homologyFunctorFactors _ n).inv.naturality
    ((Cech.Linear.totalCechComplexFunctor S.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ V
      hV).map f.hom)
  dsimp only [cechBaseClass]
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ ((DerivedCategory.homologyFunctor _ n).map_comp _ _).symm).trans ?_
  refine (whisker_eq _ (congrArg (DerivedCategory.homologyFunctor _ n).map h1.symm)).trans ?_
  refine (whisker_eq _ ((DerivedCategory.homologyFunctor _ n).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker h2.symm _).trans ?_
  exact Category.assoc _ _ _

/-- **The class of a total Čech class coming from a global cocycle is the class of the global
cocycle**: the comparison of [Stacks, Tag 08BN] after the augmentation of [Stacks, Tag 07M9]
is the unit `Γ(S, -) ⟶ RΓ(S, -)`. -/
theorem cechBaseClass_homologyMap_sectionsToTotalCech
    (T : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))) (n : ℤ)
    (s : (Cohomology.DerivedGlobalCupProduct.sectionsComplex S T.obj).cycles n) :
    (cechBaseClass S V hV T n).hom ((HomologicalComplex.homologyMap
        ((Cech.Linear.sectionsToTotalCech S.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ V
          hV).app T.obj) n).hom
        (((Cohomology.DerivedGlobalCupProduct.sectionsComplex S T.obj).homologyπ n).hom
          s)) =
      Stacks.Cohomology.DerivedGlobalCupProduct.globalClass T.obj n s := by
  have h2 := (DerivedCategory.homologyFunctorFactors _ n).inv.naturality
    ((Cech.Linear.sectionsToTotalCech S.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ V hV).app
      T.obj)
  have hpin := (Stacks.Cech.CupProductSquare.sectionsToTotalCech_comp_cechToBaseSectionsA S V hV
    T).trans (Stacks.Cech.CupProductSquare.sectionsToBaseSections_app_eq S T)
  have key : HomologicalComplex.homologyMap
        ((Cech.Linear.sectionsToTotalCech S.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ V
          hV).app T.obj) n ≫ cechBaseClass S V hV T n =
      (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
        (DerivedCategory.homologyFunctor _ n).map
          (Stacks.Cohomology.DerivedSectionsLeray.sectionsUnitQ S ⊤ T.obj) := by
    dsimp only [cechBaseClass]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker h2 _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine whisker_eq _ (((DerivedCategory.homologyFunctor _ n).map_comp _ _).symm.trans ?_)
    exact congrArg (DerivedCategory.homologyFunctor _ n).map hpin
  exact ConcreteCategory.congr_hom key _

end Classes

section Pullback

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  Stacks.Cohomology.CechSheaf.sectionsPresheaf Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover
  cechComplexNatFunctor
  Stacks.Cohomology.CechDerived.cechComplexIntFunctor ComplexShape.Embedding.extendFunctor
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {Z Z' : RingedSpace.{u, u}} (h : Z' ⟶ Z) {I : Type u} (U : I → Opens Z.carrier)
  (hU : (⊤ : Opens Z.carrier) = ⨆ i, U i)
  (hU' : (⊤ : Opens Z'.carrier) = ⨆ i, (Opens.map h.hom.base).obj (U i))

/-- The direct image `h_*𝒦'` of a bounded below complex, as a bounded below complex. -/
abbrev pushforwardPlus
    (K' : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))) :
    CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf)) :=
  (StacksDraft.KFlat.modulePushforward h).mapCochainComplexPlus.obj K'

/-- `cechPullbackHomology_homologyπ` for the cycles of the complex of global sections
`Γ(Z, h_*𝒦')`. -/
theorem cechPullbackHomology_homologyMap_homologyπ
    (K' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) ℤ) (n : ℤ)
    (s : (Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
      ((pushforwardComplex h).obj K')).cycles n) :
    (cechPullbackHomology h U hU hU' K' n).hom ((HomologicalComplex.homologyMap
        ((Cech.Linear.sectionsToTotalCech Z.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U
          hU).app ((pushforwardComplex h).obj K')) n).hom
        (((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
          ((pushforwardComplex h).obj K')).homologyπ n).hom s)) =
      (HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z'.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf) ⊤ (fun i =>
            (Opens.map h.hom.base).obj (U i)) hU').app
            K') n).hom
        (((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z' K').homologyπ n).hom
          (((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
            K').sc n).mapCyclesIso (restrictGlobal h)).hom.hom s)) :=
  cechPullbackHomology_homologyπ h U hU hU' K' n s

/-- **The pullback of the Čech class of a global cocycle.** For a global cocycle `s` of
`Γ(Z, h_*𝒦') = Γ(Z', 𝒦')`, both sides are the class of `s` on `Z'`. -/
theorem cohomologyPullback_cechBaseClass_homologyMap_sectionsToTotalCech
    (J' : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))) (n : ℤ)
    (s : (Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
      ((pushforwardComplex h).obj J'.obj)).cycles n) :
    (cohomologyPullback h (𝟙 _) n).hom ((cechBaseClass Z U hU (pushforwardPlus h J') n).hom
        ((HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).app
            ((pushforwardComplex h).obj J'.obj)) n).hom
          (((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
            ((pushforwardComplex h).obj J'.obj)).homologyπ n).hom s))) =
      (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' J' n).hom
        ((cechPullbackHomology h U hU hU' J'.obj n).hom
          ((HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z.carrier
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).app
              ((pushforwardComplex h).obj J'.obj)) n).hom
            (((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
              ((pushforwardComplex h).obj J'.obj)).homologyπ n).hom s))) := by
  let s' : (Cohomology.DerivedGlobalCupProduct.sectionsComplex Z' J'.obj).cycles n :=
    ((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
      J'.obj).sc n).mapCyclesIso (restrictGlobal h)).hom.hom s
  have hL := cechBaseClass_homologyMap_sectionsToTotalCech Z U hU (pushforwardPlus h J') n s
  have hR := cechBaseClass_homologyMap_sectionsToTotalCech Z'
    (fun i => (Opens.map h.hom.base).obj (U i)) hU' J' n s'
  have hi := ConcreteCategory.congr_hom
    ((((Cech.Linear.sectionsComplexFunctor Z'.carrier (ringCatSheaf Z') ⊤).obj
      J'.obj).sc n).mapCyclesIso_hom_iCycles (restrictGlobal h)) s
  have hφ : ((Cohomology.DerivedGlobalCupProduct.globalSections Z).mapHomologicalComplex
      (up ℤ)).map (𝟙 ((pushforwardComplex h).obj J'.obj)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have hs : ((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
        ((pushforwardComplex h).obj J'.obj)).iCycles n).hom
        ((HomologicalComplex.cyclesMap
          (((Cohomology.DerivedGlobalCupProduct.globalSections Z).mapHomologicalComplex
            (up ℤ)).map (𝟙 ((pushforwardComplex h).obj J'.obj))) n).hom s) =
      ((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z' J'.obj).iCycles n).hom
        s' := by
    refine (congrArg (fun (k : Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
        ((pushforwardComplex h).obj J'.obj) ⟶ Cohomology.DerivedGlobalCupProduct.sectionsComplex
          Z ((pushforwardComplex h).obj J'.obj)) =>
      ((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
      ((pushforwardComplex h).obj J'.obj)).iCycles n).hom
        ((HomologicalComplex.cyclesMap k n).hom s)) hφ).trans ?_
    refine (congrArg (fun (k : HomologicalComplex.cycles
        (Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
          ((pushforwardComplex h).obj J'.obj)) n ⟶ HomologicalComplex.cycles
        (Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
          ((pushforwardComplex h).obj J'.obj)) n) =>
      ((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
      ((pushforwardComplex h).obj J'.obj)).iCycles n).hom (k.hom s))
        (HomologicalComplex.cyclesMap_id _ n)).trans ?_
    exact hi.symm
  have hG := cohomologyPullback_globalClass h (𝟙 ((pushforwardComplex h).obj J'.obj)) n s s' hs
  have hπ := cechPullbackHomology_homologyMap_homologyπ h U hU hU' J'.obj n s
  refine (congrArg (cohomologyPullback h (𝟙 _) n).hom hL).trans (hG.trans (hR.symm.trans ?_))
  exact congrArg (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' J' n).hom
    hπ.symm

/-- **The pullback of a Čech class, for a bounded below complex of injectives** and the
identity `h_*𝓘' ⟶ h_*𝓘'`. Both the augmentation `Γ(Z', 𝓘') ⟶ Tot(Č(h⁻¹𝒰, 𝓘'))` and, `h_*𝓘'`
being flasque, the augmentation `Γ(Z, h_*𝓘') ⟶ Tot(Č(𝒰, h_*𝓘'))` are quasi-isomorphisms, so every
class is the class of a global cocycle, on which both sides are the class of that cocycle. -/
theorem cohomologyPullback_cechBaseClass_of_injective
    (J' : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)))
    (hJ : ∀ n : ℤ, Injective (J'.obj.X n)) (n : ℤ)
    (y : ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤
      U hU).obj ((pushforwardComplex h).obj J'.obj)).homology n) :
    (cohomologyPullback h (𝟙 _) n).hom ((cechBaseClass Z U hU (pushforwardPlus h J') n).hom y) =
      (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' J' n).hom
        ((cechPullbackHomology h U hU hU' J'.obj n).hom y) := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ J'.1).mp J'.2
  have hP : CochainComplex.IsStrictlyGE ((pushforwardComplex h).obj J'.obj) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (StacksDraft.KFlat.modulePushforward h).map_isZero (J'.obj.isZero_of_isStrictlyGE a i hi)
  have hfl : ∀ m : ℤ, (Stacks.Cohomology.CechSheaf.abSheaf
      (((pushforwardComplex h).obj J'.obj).X m)).IsFlasque := fun m =>
    @Stacks.Cohomology.PushforwardAcyclic.modulePushforward_underlying_isFlasque _ _ h
      (J'.obj.X m) (hJ m)
  have hq : QuasiIso ((Cech.Linear.sectionsToTotalCech Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).app
        ((pushforwardComplex h).obj J'.obj)) :=
    Stacks.Cech.Linear.quasiIso_sectionsToTotalCech_of_isFlasque _ _ _ _ _ _ a hfl
  obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
    ((Cech.Linear.sectionsToTotalCech Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).app
      ((pushforwardComplex h).obj J'.obj)) n)).2 y
  obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective
    ((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
      ((pushforwardComplex h).obj J'.obj)).homologyπ n)).1 inferInstance t
  have e : (HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).app
        ((pushforwardComplex h).obj J'.obj)) n).hom
        (((Cohomology.DerivedGlobalCupProduct.sectionsComplex Z
          ((pushforwardComplex h).obj J'.obj)).homologyπ n).hom s) = y :=
    (congrArg (HomologicalComplex.homologyMap ((Cech.Linear.sectionsToTotalCech Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).app
        ((pushforwardComplex h).obj J'.obj)) n).hom
        hs).trans ht
  exact e ▸ cohomologyPullback_cechBaseClass_homologyMap_sectionsToTotalCech h U hU hU' J' n s

/-- `cechPullbackHomology_naturality` on elements. -/
theorem cechPullbackHomology_homologyMap
    {K' L' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) ℤ} (a : K' ⟶ L')
    (n : ℤ)
    (y : ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤
      U hU).obj ((pushforwardComplex h).obj K')).homology n) :
    (cechPullbackHomology h U hU hU' L' n).hom ((HomologicalComplex.homologyMap
        ((Cech.Linear.totalCechComplexFunctor Z.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U
          hU).map ((pushforwardComplex h).map a)) n).hom y) =
      (HomologicalComplex.homologyMap
        ((Cech.Linear.totalCechComplexFunctor Z'.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf) ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').map a) n).hom
        ((cechPullbackHomology h U hU hU' K' n).hom y) :=
  ConcreteCategory.congr_hom (cechPullbackHomology_naturality h U hU hU' a n) y

/-- **The pullback of a Čech class along the identity of `h_*𝒦'`**, for a bounded below complex
`𝒦'`: both sides are natural in `𝒦'` and the pullback on `Z'` along a quasi-isomorphism is
invertible, so it suffices to treat the functorial injective resolution of `𝒦'`, which is
`cohomologyPullback_cechBaseClass_of_injective`. -/
theorem cohomologyPullback_id_cechBaseClass
    (K' : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))) (n : ℤ)
    (y : ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤
      U hU).obj ((pushforwardComplex h).obj K'.obj)).homology n) :
    (cohomologyPullback h (𝟙 _) n).hom ((cechBaseClass Z U hU (pushforwardPlus h K') n).hom y) =
      (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' K' n).hom
        ((cechPullbackHomology h U hU hU' K'.obj n).hom y) := by
  let J' := (Stacks.Cech.injectiveResolutionFunctor Z'.carrier
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)).obj K'
  let a : K' ⟶ J' := (Stacks.Cech.injectiveResolutionUnit Z'.carrier
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)).app K'
  have hJ : ∀ m : ℤ, Injective (J'.obj.X m) := fun m => by
    show Injective ((InjectiveObject.ι (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))).obj _)
    infer_instance
  have hqa0 : IsIso (DerivedCategory.Q.map a.hom) :=
    Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))
        (c := ComplexShape.up ℤ)) _ (Stacks.Cech.injectiveResolution_quasiIso _ _ K')
  have hqa : IsIso ((Cohomology.GlobalKunneth.baseSections Z').map
      (DerivedCategory.Q.map a.hom)) :=
    Iso.isIso_hom ((Cohomology.GlobalKunneth.baseSections Z').mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map a.hom) hqa0))
  have hinj := (ConcreteCategory.bijective_of_isIso ((DerivedCategory.homologyFunctor
    (ModuleCat.{u} (Cohomology.GlobalKunneth.baseRing Z')) n).map
      ((Cohomology.GlobalKunneth.baseSections Z').map (DerivedCategory.Q.map a.hom)))).1
  have n1 := cohomologyPullback_naturality h (𝟙 ((pushforwardComplex h).obj K'.obj))
    (𝟙 ((pushforwardComplex h).obj J'.obj)) ((pushforwardComplex h).map a.hom) a.hom
    ((Category.id_comp _).trans (Category.comp_id _).symm) n
    ((cechBaseClass Z U hU (pushforwardPlus h K') n).hom y)
  have n2 := ConcreteCategory.congr_hom (cechBaseClass_naturality Z U hU
    (K := pushforwardPlus h K') (L := pushforwardPlus h J')
    (ObjectProperty.homMk ((pushforwardComplex h).map a.hom)) n) y
  have n3 := cohomologyPullback_cechBaseClass_of_injective h U hU hU' J' hJ n
    ((HomologicalComplex.homologyMap ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).map
        ((pushforwardComplex h).map a.hom)) n).hom y)
  have n4 := cechPullbackHomology_homologyMap h U hU hU' a.hom n y
  have n5 := ConcreteCategory.congr_hom (cechBaseClass_naturality Z'
    (fun i => (Opens.map h.hom.base).obj (U i)) hU' a n)
    ((cechPullbackHomology h U hU hU' K'.obj n).hom y)
  exact hinj (n1.symm.trans ((congrArg (cohomologyPullback h (𝟙 _) n).hom n2).trans
    (n3.trans ((congrArg (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' J'
      n).hom n4).trans n5.symm))))

/-- **The pullback of a Čech class is the Čech class of the pulled back cochain.** For a
morphism of ringed spaces `h : Z' ⟶ Z`, bounded below complexes `𝒦` on `Z` and `𝒦'` on `Z'`, a
morphism of complexes `φ : 𝒦 ⟶ h_*𝒦'`, an open covering `𝒰` of `Z` and a class
`x ∈ Hⁿ(Tot(Č(𝒰, 𝒦)))`, the pullback `Hⁿ(Z, 𝒦) ⟶ Hⁿ(Z', 𝒦')` along `φ` sends the class of `x`
in `Hⁿ(Z, 𝒦)` ([Stacks, Tag 08BN]) to the class in `Hⁿ(Z', 𝒦')` of the image of `x` under
`Tot(Č(𝒰, 𝒦)) ⟶ Tot(Č(𝒰, h_*𝒦')) ⟶ Tot(Č(h⁻¹𝒰, 𝒦'))`. -/
theorem cohomologyPullback_cechBaseClass
    (K : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf)))
    (K' : CochainComplex.Plus (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)))
    (φ : K.obj ⟶ (pushforwardComplex h).obj K'.obj) (n : ℤ)
    (x : ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤
      U hU).obj K.obj).homology n) :
    (cohomologyPullback h φ n).hom ((cechBaseClass Z U hU K n).hom x) =
      (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' K' n).hom
        ((cechPullbackHomology h U hU hU' K'.obj n).hom
          ((HomologicalComplex.homologyMap ((Cech.Linear.totalCechComplexFunctor Z.carrier
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).map φ) n).hom
              x)) := by
  have m1 := cohomologyPullback_naturality h φ (𝟙 ((pushforwardComplex h).obj K'.obj)) φ
    (𝟙 K'.obj) ((congrArg (φ ≫ ·) ((pushforwardComplex h).map_id _)).trans
      ((Category.comp_id _).trans (Category.comp_id _).symm)) n
    ((cechBaseClass Z U hU K n).hom x)
  have m2 := ConcreteCategory.congr_hom (cechBaseClass_naturality Z U hU
    (K := K) (L := pushforwardPlus h K') (ObjectProperty.homMk φ) n) x
  have m3 := cohomologyPullback_id_cechBaseClass h U hU hU' K' n
    ((HomologicalComplex.homologyMap ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U hU).map φ) n).hom x)
  have hid := (congrArg (fun t => (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Cohomology.GlobalKunneth.baseRing Z')) n).map
        ((Cohomology.GlobalKunneth.baseSections Z').map t))
      ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Z'))).map_id K'.obj)).trans
    ((congrArg (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Cohomology.GlobalKunneth.baseRing Z')) n).map
        ((Cohomology.GlobalKunneth.baseSections Z').map_id _)).trans
      ((DerivedCategory.homologyFunctor _ n).map_id _))
  exact (ConcreteCategory.congr_hom hid _).symm.trans (m1.symm.trans
    ((congrArg (cohomologyPullback h (𝟙 _) n).hom m2).trans m3))

/-- **The pullback of the class of a Čech cocycle of a sheaf of modules.** For sheaves of modules
`ℱ` on `Z` and `ℱ'` on `Z'`, a morphism `φ : ℱ[0] ⟶ h_*(ℱ'[0])` and Čech `q`-cocycles `c` of `ℱ`
on `𝒰` and `c'` of `ℱ'` on `h⁻¹𝒰` such that `c'` is the image of `c` in the total Čech complex
of `ℱ'[0]`, the pullback along `φ` of the class of `c` is the class of `c'`. -/
theorem cohomologyPullback_cechSheafClass
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf))
    (F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))
    (φ : (singlePlus Z.sheaf F 0).obj ⟶
      (pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj)
    {q : ℕ} (c : CechCochains.Cochain U (abSections F) q)
    (hc : CechCochains.cechD U (abSections F) q c = 0)
    (c' : CechCochains.Cochain (fun i => (Opens.map h.hom.base).obj (U i))
      (abSections F') q)
    (hc' : CechCochains.cechD (fun i => (Opens.map h.hom.base).obj (U i))
      (abSections F') q c' = 0)
    (hcc : (cochainOfAt U hU F 0 c ≫
        ((Cech.Linear.totalCechComplexFunctor Z.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U
          hU).map φ).f ((q : ℤ) + 0) ≫
        (cechPullbackTotalMap h U hU hU'
          (singlePlus Z'.sheaf F' 0).obj).f ((q : ℤ) + 0)).hom 1 =
      (cochainOfAt (fun i => (Opens.map h.hom.base).obj (U i)) hU'
        F' 0 c').hom 1) :
    (cohomologyPullback h φ ((q : ℤ) + 0)).hom (cechSheafClass Z U hU F c hc) =
      cechSheafClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' F' c' hc' := by
  refine (cohomologyPullback_cechBaseClass h U hU hU' _ _ φ _ _).trans ?_
  refine congrArg (cechBaseClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' _ _).hom ?_
  have e1 := ConcreteCategory.congr_hom (Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap
    ((Cech.Linear.totalCechComplexFunctor Z.carrier
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U
      hU).map φ) ((q : ℤ) + 0) (cochainOfAt U hU F 0 c)
    (Stacks.Cech.Hypercohomology.cochainOfAt_d_eq_zero U hU F 0 c hc)) 1
  refine (congrArg (cechPullbackHomology h U hU hU'
    (singlePlus Z'.sheaf F' 0).obj ((q : ℤ) + 0)).hom e1).trans ?_
  exact cechPullbackHomology_cocycleClass h U hU hU' _ _ _ _ _
    (Stacks.Cech.Hypercohomology.cochainOfAt_d_eq_zero _ hU' F' 0 c' hc') hcc

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- The inclusion of a homogeneous summand of the total Čech complex, with its extension by
zero unfolded. -/
theorem ιTotalCechTo_eq_extendXIso_inv_comp_ιTotal
    (K' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) ℤ) {q : ℕ} (a n : ℤ)
    (hqa : (q : ℤ) + a = n) :
    ιTotalCechTo
        (coverObject (fun i => (Opens.map h.hom.base).obj (U i)) hU')
        (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf) ⊤)
        ((Cech.Refinement.sectionsComplex Z'.sheaf).obj K') q a n hqa =
      (((cechComplexNatFunctor (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj (K'.X a)).extendXIso
            ComplexShape.embeddingUpNat (i := q) (i' := (q : ℤ)) rfl).inv ≫
        (cechBicomplex (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
          K').flip.ιTotal (up ℤ) q a n hqa :=
  rfl

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- The inclusion of a homogeneous summand of the total Čech complex of `h_*𝒦'`, with its
extension by zero unfolded. -/
theorem cechPullbackTotalMap_ιTotalCechTo_pushforward_apply
    (K' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) ℤ) {q : ℕ} (a n : ℤ)
    (hqa : (q : ℤ) + a = n)
    (y : ToType (((CategoryTheory.cechComplexFunctor
      (coverObject U hU)).obj
        (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤
          (((pushforwardComplex h).obj K').X a))).X q)) :
    ((cechPullbackTotalMap h U hU hU' K').f n).hom
        ((ιTotalCechTo (coverObject U hU)
          (SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤)
          ((Cech.Refinement.sectionsComplex Z.sheaf).obj ((pushforwardComplex h).obj K')) q a
          n hqa).hom y) =
      ((((cechComplexNatFunctor (ringCatSheaf Z) ⊤ U hU).obj
        ((modulePushforward h).obj (K'.X a))).extendXIso ComplexShape.embeddingUpNat
          (i := q) (i' := (q : ℤ)) rfl).inv ≫
        (cechBicomplex (ringCatSheaf Z) ⊤ U hU
          (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).flip.ιTotal (up ℤ) q a n
          hqa ≫ (cechPullbackTotalMap h U hU hU' K').f n).hom y :=
  rfl

/-- **The map of total Čech complexes on the cochain of an explicit Čech cochain**: the cochain
of `Tot(Č(𝒰, h_*𝒦'))` attached to a Čech `q`-cochain `d` of `h_*𝒦'^a` goes to the cochain of
`Tot(Č(h⁻¹𝒰, 𝒦'))` attached to `d` read on `h⁻¹𝒰`. -/
theorem cechPullbackTotalMap_sliceCochain
    (K' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf)) ℤ) {q : ℕ} (a n : ℤ)
    (hqa : (q : ℤ) + a = n)
    (d : CechCochains.Cochain U (abSections
      ((StacksDraft.KFlat.modulePushforward h).obj (K'.X a))) q) :
    ((((cechComplexNatFunctor (ringCatSheaf Z) ⊤ U hU).obj
        ((modulePushforward h).obj (K'.X a))).extendXIso ComplexShape.embeddingUpNat
          (i := q) (i' := (q : ℤ)) rfl).inv ≫
      (cechBicomplex (ringCatSheaf Z) ⊤ U hU
        (((modulePushforward h).mapHomologicalComplex (up ℤ)).obj K')).flip.ιTotal (up ℤ) q a n
        hqa ≫ (cechPullbackTotalMap h U hU hU' K').f n).hom
        (sliceCochain (O := Z.sheaf) U hU
          ((StacksDraft.KFlat.modulePushforward h).obj (K'.X a)) d) =
      ((restrictGlobalScalars h).map
        ((((cechComplexNatFunctor (ringCatSheaf Z') ⊤
          (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj (K'.X a)).extendXIso
            ComplexShape.embeddingUpNat (i := q) (i' := (q : ℤ)) rfl).inv ≫
          (cechBicomplex (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
            K').flip.ιTotal (up ℤ) q a n hqa)).hom
        (sliceCochain (O := Z'.sheaf)
          (fun i => (Opens.map h.hom.base).obj (U i)) hU' (K'.X a)
          (preimageCochain h U (K'.X a) d)) :=
  (ConcreteCategory.congr_hom
    (extendXIso_inv_ιTotal_comp_cechPullbackTotalMap h U hU hU' K' q a n hqa) _).trans
    (congrArg ((restrictGlobalScalars h).map
      ((((cechComplexNatFunctor (ringCatSheaf Z') ⊤
        (fun i => (Opens.map h.hom.base).obj (U i)) hU').obj (K'.X a)).extendXIso
          ComplexShape.embeddingUpNat (i := q) (i' := (q : ℤ)) rfl).inv ≫
        (cechBicomplex (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
          K').flip.ιTotal (up ℤ) q a n hqa)).hom
      (cechComplexRefinementMap_sliceCochain h U hU hU' (K'.X a) d))

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- The image of the cochain attached to `c` in `Tot(Č(𝒰, h_*𝒦'))`, on the generator. -/
theorem cochainOfAt_comp_cech_map_comp_cechPullbackTotalMap_apply_one
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf))
    (F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))
    (φ : (singlePlus Z.sheaf F 0).obj ⟶ (pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj)
    {q : ℕ} (c : CechCochains.Cochain U (abSections F) q) :
    (cochainOfAt U hU F 0 c ≫
        ((Cech.Linear.totalCechComplexFunctor Z.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤ U
          hU).map φ).f ((q : ℤ) + 0) ≫
        (cechPullbackTotalMap h U hU hU' (singlePlus Z'.sheaf F' 0).obj).f ((q : ℤ) + 0)).hom 1 =
      ((cechPullbackTotalMap h U hU hU' (singlePlus Z'.sheaf F' 0).obj).f ((q : ℤ) + 0)).hom
        ((ιTotalCechTo (coverObject U hU) (SectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤)
          ((Cech.Refinement.sectionsComplex Z.sheaf).obj
            ((pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj)) q 0 ((q : ℤ) + 0)
              rfl).hom
          (sliceCochain (O := Z.sheaf) U hU
            (((pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj).X 0)
            (Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map
              ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c))) :=
  cochainOfAt_comp_cech_map_comp_apply_one U hU F φ
    ((cechPullbackTotalMap h U hU hU' (singlePlus Z'.sheaf F' 0).obj).f ((q : ℤ) + 0)) c

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- `cechPullbackTotalMap` on the cochain attached to the image of `c`. -/
theorem cechPullbackTotalMap_ιTotalCechTo_sliceCochain
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf))
    (F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))
    (φ : (singlePlus Z.sheaf F 0).obj ⟶ (pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj)
    {q : ℕ} (c : CechCochains.Cochain U (abSections F) q) :
    ((cechPullbackTotalMap h U hU hU' (singlePlus Z'.sheaf F' 0).obj).f ((q : ℤ) + 0)).hom
        ((ιTotalCechTo (coverObject U hU) (SectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf) ⊤)
          ((Cech.Refinement.sectionsComplex Z.sheaf).obj
            ((pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj)) q 0 ((q : ℤ) + 0)
              rfl).hom
          (sliceCochain (O := Z.sheaf) U hU
            (((pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj).X 0)
            (Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map
              ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c))) =
      ((restrictGlobalScalars h).map
        ((((cechComplexNatFunctor (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i))
          hU').obj ((singlePlus Z'.sheaf F' 0).obj.X 0)).extendXIso ComplexShape.embeddingUpNat
            (i := q) (i' := (q : ℤ)) rfl).inv ≫
          (cechBicomplex (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
            (singlePlus Z'.sheaf F' 0).obj).flip.ιTotal (up ℤ) q 0 ((q : ℤ) + 0) rfl)).hom
        (sliceCochain (O := Z'.sheaf) (fun i => (Opens.map h.hom.base).obj (U i)) hU'
          ((singlePlus Z'.sheaf F' 0).obj.X 0)
          (preimageCochain h U ((singlePlus Z'.sheaf F' 0).obj.X 0)
            (Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map
              ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c))) :=
  (cechPullbackTotalMap_ιTotalCechTo_pushforward_apply h U hU hU' (singlePlus Z'.sheaf F' 0).obj
    (q := q) 0 ((q : ℤ) + 0) rfl _).trans
    (cechPullbackTotalMap_sliceCochain h U hU hU' (singlePlus Z'.sheaf F' 0).obj 0 ((q : ℤ) + 0)
      rfl _)

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- The cochain attached to a Čech cochain `c'` of `ℱ'` on `h⁻¹𝒰`, on the generator. -/
theorem cochainOfAt_preimage_apply_one (F' : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))
    {q : ℕ} (c' : CechCochains.Cochain (fun i => (Opens.map h.hom.base).obj (U i))
      (abSections F') q) :
    (cochainOfAt (fun i => (Opens.map h.hom.base).obj (U i)) hU' F' 0 c').hom 1 =
      ((((cechComplexNatFunctor (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i))
        hU').obj ((singlePlus Z'.sheaf F' 0).obj.X 0)).extendXIso ComplexShape.embeddingUpNat
          (i := q) (i' := (q : ℤ)) rfl).inv ≫
        (cechBicomplex (ringCatSheaf Z') ⊤ (fun i => (Opens.map h.hom.base).obj (U i)) hU'
          (singlePlus Z'.sheaf F' 0).obj).flip.ιTotal (up ℤ) q 0 ((q : ℤ) + 0) rfl).hom
        (sliceCochain (O := Z'.sheaf) (fun i => (Opens.map h.hom.base).obj (U i)) hU'
          ((singlePlus Z'.sheaf F' 0).obj.X 0)
          (Cohomology.CechOne.push (fun i => (Opens.map h.hom.base).obj (U i))
            ((SheafOfModules.toSheaf _).map
              (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F' 0 rfl).inv).hom q c')) :=
  (cochainOfAt_apply_one (fun i => (Opens.map h.hom.base).obj (U i)) hU' F' c').trans
    (ConcreteCategory.congr_hom (ιTotalCechTo_eq_extendXIso_inv_comp_ιTotal h U hU'
      (singlePlus Z'.sheaf F' 0).obj (q := q) 0 ((q : ℤ) + 0) rfl) _)

/-- **The pullback of the class of a Čech cocycle of a sheaf of modules, explicitly.** If the
Čech cocycle `c'` of `ℱ'` on `h⁻¹𝒰` is the image of the cocycle `c` of `ℱ` on `𝒰` under the
degree-`0` component of `φ : ℱ[0] ⟶ h_*(ℱ'[0])`, read on `h⁻¹𝒰`, the pullback along `φ` of the
class of `c` is the class of `c'`. -/
theorem cohomologyPullback_cechSheafClass_of_preimageCochain
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf))
    (F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z'.sheaf))
    (φ : (singlePlus Z.sheaf F 0).obj ⟶ (pushforwardComplex h).obj (singlePlus Z'.sheaf F' 0).obj)
    {q : ℕ} (c : CechCochains.Cochain U (abSections F) q)
    (hc : CechCochains.cechD U (abSections F) q c = 0)
    (c' : CechCochains.Cochain (fun i => (Opens.map h.hom.base).obj (U i)) (abSections F') q)
    (hc' : CechCochains.cechD (fun i => (Opens.map h.hom.base).obj (U i)) (abSections F') q c' = 0)
    (hcc : preimageCochain h U ((singlePlus Z'.sheaf F' 0).obj.X 0)
        (Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map
          ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F 0 rfl).inv ≫ φ.f 0)).hom q c) =
      Cohomology.CechOne.push (fun i => (Opens.map h.hom.base).obj (U i))
        ((SheafOfModules.toSheaf _).map
          (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 F' 0 rfl).inv).hom q c') :
    (cohomologyPullback h φ ((q : ℤ) + 0)).hom (cechSheafClass Z U hU F c hc) =
      cechSheafClass Z' (fun i => (Opens.map h.hom.base).obj (U i)) hU' F' c' hc' :=
  cohomologyPullback_cechSheafClass h U hU hU' F F' φ c hc c' hc'
    ((cochainOfAt_comp_cech_map_comp_cechPullbackTotalMap_apply_one h U hU hU' F F' φ c).trans
      ((cechPullbackTotalMap_ιTotalCechTo_sliceCochain h U hU hU' F F' φ c).trans
        ((congrArg _ (congrArg (sliceCochain (O := Z'.sheaf)
          (fun i => (Opens.map h.hom.base).obj (U i)) hU' ((singlePlus Z'.sheaf F' 0).obj.X 0))
            hcc)).trans (cochainOfAt_preimage_apply_one h U hU' F' c').symm)))

end Pullback

section Hodge

open Stacks.Cohomology.CechSheaf (abSections)
open AlgebraicGeometry.SheafOfModules (deRhamTerm)

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g) {I : Type u} (U : I → X.Opens)

/-- **The pullback of a Čech cochain of differential forms** along a commutative square
`g' ≫ f = f' ≫ g`: on the tuple `s` it is the pullback along `g'` of the form `c s` on
`⋂ⱼ U_{s j}`, a form on `g'⁻¹(⋂ⱼ U_{s j})`, restricted to `⋂ⱼ g'⁻¹U_{s j}`. -/
def pullbackCochain (p : ℕ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q) :
    CechCochains.Cochain (fun i => g' ⁻¹ᵁ U i) (abSections (deRhamTerm (formsAlgebras f') p)) q :=
  fun s => CechCochains.restr _ (cechInter_map_le g'.base U s)
    (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) (CechCochains.inter U s)
      (c s))

/-- The pullback of differential forms of degree `p` on an open, as an additive map. -/
def formsPullbackAddHom (p : ℕ) (V : X.Opens) :
    Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) →+
      Γ(Scheme.Hom.relativeDifferentialForms f' (p : ℤ), g' ⁻¹ᵁ V) :=
  AddMonoidHom.mk' (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) V)
    (Scheme.Hom.relativeDifferentialFormsPullback_add g' f f' g w (p : ℤ) V)

/-- **The pullback of Čech cochains of differential forms commutes with the Čech
differential.** -/
theorem pullbackCochain_cechD (p : ℕ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q) :
    pullbackCochain g' f' f g w U p (CechCochains.cechD U _ q c) =
      CechCochains.cechD (fun i => g' ⁻¹ᵁ U i) _ q (pullbackCochain g' f' f g w U p c) := by
  funext s
  let ℱ := abSections (deRhamTerm (formsAlgebras f) p)
  let ℱ' := abSections (deRhamTerm (formsAlgebras f') p)
  show CechCochains.restr ℱ' (cechInter_map_le g'.base U s)
      (formsPullbackAddHom g' f' f g w p (CechCochains.inter U s)
        (∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          CechCochains.restr ℱ (CechCochains.inter_le_omit U s j) (c (s ∘ j.succAbove)))) =
    ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr ℱ' (CechCochains.inter_le_omit (fun i => g' ⁻¹ᵁ U i) s j)
        (CechCochains.restr ℱ' (cechInter_map_le g'.base U (s ∘ j.succAbove))
          (formsPullbackAddHom g' f' f g w p (CechCochains.inter U (s ∘ j.succAbove))
            (c (s ∘ j.succAbove))))
  refine (congrArg (CechCochains.restr ℱ' (cechInter_map_le g'.base U s))
    (map_sum (formsPullbackAddHom g' f' f g w p (CechCochains.inter U s)) _ _)).trans ?_
  refine (map_sum (CechCochains.restr ℱ' (cechInter_map_le g'.base U s)) _ _).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (congrArg (CechCochains.restr ℱ' (cechInter_map_le g'.base U s))
    (map_zsmul (formsPullbackAddHom g' f' f g w p (CechCochains.inter U s)) _ _)).trans
    ((map_zsmul (CechCochains.restr ℱ' (cechInter_map_le g'.base U s)) _ _).trans ?_)
  refine congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) ?_
  have hm := Scheme.Hom.relativeDifferentialFormsPullback_map g' f f' g w (p : ℤ)
    (CechCochains.inter_le_omit U s j) (c (s ∘ j.succAbove))
  refine (congrArg (CechCochains.restr ℱ' (cechInter_map_le g'.base U s)) hm).trans ?_
  exact (CechCochains.restr_restr ℱ' _ _ _).trans (CechCochains.restr_restr ℱ' _ _ _).symm

/-- **The pullback of a Čech cocycle of differential forms is a Čech cocycle.** -/
theorem cechD_pullbackCochain_eq_zero (p : ℕ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0) :
    CechCochains.cechD (fun i => g' ⁻¹ᵁ U i) (abSections (deRhamTerm (formsAlgebras f') p)) q
      (pullbackCochain g' f' f g w U p c) = 0 := by
  refine (pullbackCochain_cechD g' f' f g w U p c).symm.trans ?_
  rw [hc]
  funext s
  exact (congrArg (CechCochains.restr (abSections (deRhamTerm (formsAlgebras f') p))
    (cechInter_map_le g'.base U s)) (map_zero (formsPullbackAddHom g' f' f g w p
      (CechCochains.inter U s)))).trans (map_zero _)

variable (hU : (⊤ : X.Opens) = ⨆ i, U i) (hU' : (⊤ : X'.Opens) = ⨆ i, g' ⁻¹ᵁ U i)

/-- **The pullback of Čech cochains of differential forms is the canonical map of forms followed
by the passage to the inverse image covering**: `pullbackCochain c` is `c` pushed along the
degree-`0` component of `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])` and read on `g'⁻¹𝒰`. -/
theorem preimageCochain_push_formsSinglePushforward (p : ℕ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q) :
    preimageCochain (DeRhamBaseChange.inverseImageBaseMap g' f' f g w) U
        ((singlePlus (DeRhamDirectImage.inverseImageBase f').sheaf
          (deRhamTerm (X := X'.toRingedSpace) (formsAlgebras f') p) 0).obj.X 0)
        (Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map
          ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0
            (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p) 0 rfl).inv ≫
            (formsSinglePushforward g' f' f g w p).f 0)).hom q c) =
      Cohomology.CechOne.push (fun i => g' ⁻¹ᵁ U i) ((SheafOfModules.toSheaf _).map
        (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0
          (deRhamTerm (X := X'.toRingedSpace) (formsAlgebras f') p) 0 rfl).inv).hom q
        (pullbackCochain g' f' f g w U p c) := by
  funext s
  exact congrArg (CechCochains.restr (abSections
    ((singlePlus (DeRhamDirectImage.inverseImageBase f').sheaf
      (deRhamTerm (X := X'.toRingedSpace) (formsAlgebras f') p) 0).obj.X 0))
    (cechInter_map_le (DeRhamBaseChange.inverseImageBaseMap g' f' f g w).hom.base U s))
    (formsSinglePushforward_f_zero_val_app g' f' f g w p (op (CechCochains.inter U s)) (c s))

/-- **The Hodge pullback of the class of a Čech cocycle is the class of the pulled back
cocycle**: for a commutative square `g' ≫ f = f' ≫ g`, an open covering `𝒰` of `X` and a Čech
`q`-cocycle `c` of `Ω^p_{X/S}` on `𝒰`, the pullback `g'^* : H^q(X, Ω^p_{X/S}) ⟶
H^q(X', Ω^p_{X'/S'})` sends the class of `c` to the class of the cocycle `pullbackCochain` of
`Ω^p_{X'/S'}` on the covering `g'⁻¹𝒰` of `X'`. -/
theorem hodgePullback_hodgeCechClass (p : ℕ) {q : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0) :
    hodgePullback g' f' f g w p q (hodgeCechClass f U hU p c hc) =
      hodgeCechClass f' (fun i => g' ⁻¹ᵁ U i) hU' p (pullbackCochain g' f' f g w U p c)
        (cechD_pullbackCochain_eq_zero g' f' f g w U p c hc) :=
  cohomologyPullback_cechSheafClass_of_preimageCochain
    (DeRhamBaseChange.inverseImageBaseMap g' f' f g w) U hU hU'
    (deRhamTerm (X := X.toRingedSpace) (formsAlgebras f) p)
    (deRhamTerm (X := X'.toRingedSpace) (formsAlgebras f') p)
    (formsSinglePushforward g' f' f g w p) c hc (pullbackCochain g' f' f g w U p c)
    (cechD_pullbackCochain_eq_zero g' f' f g w U p c hc)
    (preimageCochain_push_formsSinglePushforward g' f' f g w U p c)

end Hodge

end Stacks.HodgeWeil

end
