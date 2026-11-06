module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.AbelianPullbackUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.HomologyPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationUnboundedGlobalClass
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.InverseImageBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# The pullback from a direct image across the realization comparison

Let `V` be a ringed space. The comparison of [Stacks, Tag 01F1] between the hypercohomology of the
underlying complex of abelian sheaves of a bounded below complex of `𝒪_V`-modules and its
hypercohomology in `𝒪_V`-modules, read in the unbounded model of derived global sections, is
`Stacks.Cech.Hypercohomology.realizationUnbounded`; it sends the class of a global cocycle to the
class of the same section (`Stacks.Cech.Hypercohomology.realizationUnbounded_abelianGlobalClass`).

For a commutative square of schemes `g' ≫ f = f' ≫ g` and the induced morphism
`h : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` (`Stacks.DeRhamBaseChange.inverseImageBaseMap`), whose
underlying continuous map is that of `g'`, the abelian direct image along `g'` of the underlying
complex of `M` is the underlying complex of the module direct image `h_*M`. The pullback from the
direct image in abelian sheaves (`AlgebraicGeometry.Scheme.Hom.pushforwardPullback`) is then
carried by the realization comparisons to the comparison `h_*M ⟶ Rh_*M` followed by the Leray
identification `Hⁿ(X, Rh_*M) = Hⁿ(X', M)` (`realizationUnbounded_pushforwardPullback`). This is
the comparison of the two pullbacks that the proof of [Stacks, Tag 0FMP] passes through.

The proof replaces `M` by a quasi-isomorphic bounded below complex of injective modules. There
the underlying abelian sheaves are acyclic for global sections and for the direct image, so every
class is the class of a global cocycle, on which both sides are computed directly.

## Main results

* `Stacks.Cech.Hypercohomology.abelianGlobalClass_pushforwardPullback`: classes of global cocycles
  across the pullback from a direct image.
* `Stacks.Cech.Hypercohomology.exists_abelianGlobalClass`: on a complex computing its derived
  global sections every class is the class of a global cocycle.
* `Stacks.DeRhamBaseChange.realizationUnbounded_pushforwardPullback`: **the edge identity**.
* `Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback`:
  the edge identity for the de Rham pullback.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology_eq`: the comparison
  of the two realizations of relative de Rham cohomology is `realizationUnbounded`.

## Implementation notes

The identification of the abelian direct image of the underlying complex with the underlying
complex of the module direct image holds by definition, but checking it unfolds the inverse-image
ring sheaves and is expensive; the proofs cross it only a bounded number of times per declaration,
through `toSheafPushforwardIso` (the identity, at the two spellings).

The derived categories are `HasDerivedCategory.standard`, the model in which the realization
comparison and the global cocycle classes are stated; it is given priority over the locally small
models that some imported files register as instances.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 0FMP](https://stacks.math.columbia.edu/tag/0FMP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HomologyPullback (map_map_comp_apply)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- A commutative square of morphisms of abelian groups, evaluated on an element, at variables. -/
private theorem square_apply {C : Type*} [Category* C] (H : C ⥤ AddCommGrpCat.{u}) {a b c d : C}
    (x : a ⟶ b) (y : b ⟶ c) (x' : a ⟶ d) (y' : d ⟶ c) (h : x ≫ y = x' ≫ y') (z : H.obj a) :
    (H.map y).hom ((H.map x).hom z) = (H.map y').hom ((H.map x').hom z) := by
  simpa only [Functor.map_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply] using congrArg (fun t => (H.map t).hom z) h

open Stacks.Cohomology.LerayLowDegree (abelianPushforward) in
/-- **Classes of global cocycles across the pullback from a direct image**: for a morphism of
schemes `φ : X' ⟶ X` and a global cocycle `s` of `Γ(X, φ_*K) = Γ(X', K)`, the pullback
`Hⁿ(X, φ_*K) ⟶ Hⁿ(X', K)` sends the class of `s` on `X` to its class on `X'`. -/
theorem abelianGlobalClass_pushforwardPullback {Y' Y : Scheme.{u}} (φ : Y' ⟶ Y)
    (K : CochainComplex.Plus (AbelianSheaf Y'.toRingedSpace.carrier)) (n : ℤ)
    (s : ((sectionsFunctor Y'.toRingedSpace.carrier ⊤).mapCochainComplexPlus.obj K).obj.cycles n) :
    ((DerivedCategory.Plus.homologyFunctor _ n).map (φ.pushforwardPullback K)).hom
        (abelianGlobalClass ((abelianPushforward.{u, u} φ.base).mapCochainComplexPlus.obj K) n s) =
      abelianGlobalClass K n s := by
  have e := congrArg (fun z =>
    (((sectionsFunctor Y'.toRingedSpace.carrier ⊤).mapCochainComplexPlus.obj K).obj.homologyπ n ≫
      (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
    (DerivedCategory.Plus.homologyFunctor _ n).map z).hom s)
    (Scheme.Hom.sectionsUnit_comp_pushforwardPullback φ K)
  simp only [Functor.map_comp] at e
  exact e

/-- **Every class of a complex computing its derived global sections is the class of a global
cocycle**: if the unit `Γ(Y, L) ⟶ R⁺Γ(Y, L)` is invertible, `abelianGlobalClass` is surjective. -/
theorem exists_abelianGlobalClass {Y : TopCat.{u}} (L : CochainComplex.Plus (AbelianSheaf Y))
    (n : ℤ) (hL : IsIso ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L))
    (y : abelianHypercohomology L n) :
    ∃ s, abelianGlobalClass L n s = y := by
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L)) :=
    Functor.map_isIso _ _
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective
    (((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj.homologyπ n)).1 inferInstance
    ((inv ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L)) ≫
      (DerivedCategory.homologyFunctorFactors _ n).hom.app _).hom y)
  refine ⟨s, ?_⟩
  show ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L)).hom
    (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).inv.app
      ((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj).hom
      ((((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj.homologyπ n).hom s)) = y
  rw [hs]
  have e : inv ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L)) ≫
      (DerivedCategory.homologyFunctorFactors _ n).hom.app _ ≫
      (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L) = 𝟙 _ :=
    (congrArg (_ ≫ ·) ((DerivedCategory.homologyFunctorFactors _ n).hom_inv_id_app_assoc
      _ _)).trans (IsIso.inv_hom_id ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L)))
  exact ConcreteCategory.congr_hom e y

/-- The derived unit of an additive functor is invertible on a bounded below complex of objects
right acyclic for it (Leray's acyclicity lemma, [Stacks, Tag 015E]). -/
private theorem isIso_derivedUnit_app_of_rightAcyclic {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (T : A ⥤ B) [T.Additive] (K : CochainComplex.Plus A) (hK : ∀ n, T.rightAcyclic (K.obj.X n)) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit T).app K) := by
  have hu := T.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
    ((HomotopyCategory.Plus.quotient A).obj K) hK
  rw [Functor.mapCochainComplexPlusDerivedUnit_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ hu
    inferInstance)

/-- The underlying complex of a bounded below complex of injective modules computes its derived
global sections in abelian sheaves. -/
theorem isIso_sectionsUnit_toSheaf_of_injective (V : RingedSpace.{u, u})
    (I : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V)))
    (hI : ∀ k, Injective (I.obj.X k)) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor V.carrier ⊤)).app
      ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj I)) := by
  exact isIso_derivedUnit_app_of_rightAcyclic (sectionsFunctor V.carrier ⊤) _ fun k =>
    Stacks.Cohomology.ModulePushforwardComparison.rightAcyclic_sections_toSheaf_obj_of_injective
      ⊤ (I.obj.X k) (hI k)

end Stacks.Cech.Hypercohomology

namespace Stacks.DeRhamBaseChange

open Stacks.Cech.Hypercohomology Stacks.DeRhamDirectImage
open Stacks.Cohomology.LerayLowDegree (abelianPushforward)

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

open Stacks.Cohomology.ModulePushforwardComparison
  (rightAcyclic_abelianPushforward_toSheaf_obj_of_injective) in
include f g w in
/-- For a bounded below complex `I` of injective `f'^{-1}𝒪_{S'}`-modules, the pullback from the
direct image of its underlying complex along `g'` is an isomorphism. -/
theorem isIso_pushforwardPullback_toSheaf_of_injective
    (I : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (hI : ∀ k, Injective (I.obj.X k)) :
    IsIso (g'.pushforwardPullback
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        I)) := by
  have hu := isIso_derivedUnit_app_of_rightAcyclic (abelianPushforward.{u, u} g'.base)
    ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
      I) fun k => rightAcyclic_abelianPushforward_toSheaf_obj_of_injective
      (inverseImageBaseMap g' f' f g w) (I.obj.X k) (hI k)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) inferInstance

open Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

/-- **The edge comparison on classes of global cocycles.** For a global cocycle `s` of
`Γ(X', M) = Γ(X, g'_*M)`, both sides of the edge identity send the class of `s` on `X` to the
class of `s` in `Hⁿ(X', M)`. -/
theorem realizationUnbounded_pushforwardPullback_abelianGlobalClass
    (M : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (n : ℤ)
    (s : ((sectionsFunctor X'.toRingedSpace.carrier ⊤).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        M)).obj.cycles n) :
    (realizationUnbounded (inverseImageBase f') M n).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M))).hom
          (abelianGlobalClass ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
            ((SheafOfModules.toSheaf
              (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M)) n s)) =
      (lerayCohomologyIso (inverseImageBaseMap g' f' f g w) (DerivedCategory.Q.obj M.obj) n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
          (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) M.obj))).hom
          ((realizationUnbounded (inverseImageBase f)
            ((StacksDraft.KFlat.modulePushforward
              (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) n).hom.hom
            (abelianGlobalClass ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
              ((SheafOfModules.toSheaf
                (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M)) n
              s))) := by
  have hs' := (ConcreteCategory.congr_hom
    (((sectionsComplex (inverseImageBase f') M.obj).sc n).mapCyclesIso_hom_iCycles
      (forget₂ (ModuleCat.{u} (baseRing (inverseImageBase f'))) AddCommGrpCat.{u})) s).symm
  have hs'' := (ConcreteCategory.congr_hom
    (((sectionsComplex (inverseImageBase f) ((StacksDraft.KFlat.modulePushforward
      (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M).obj).sc
        n).mapCyclesIso_hom_iCycles
      (forget₂ (ModuleCat.{u} (baseRing (inverseImageBase f))) AddCommGrpCat.{u})) s).symm
  refine (congrArg (realizationUnbounded (inverseImageBase f') M n).hom.hom
    (abelianGlobalClass_pushforwardPullback g' _ n s)).trans ?_
  refine (realizationUnbounded_abelianGlobalClass M n s _ hs').trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
      (DerivedCategory.Q.obj M.obj) n).hom
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
      (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) M.obj))).hom z))
    (realizationUnbounded_abelianGlobalClass ((StacksDraft.KFlat.modulePushforward
      (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) n s _ hs'')).symm
  exact (lerayCohomologyIso_globalClass (inverseImageBaseMap g' f' f g w) M.obj n _ _
    (hs''.symm.trans hs')).symm

/-- **The edge comparison on a complex of injectives.** For a bounded below complex `I` of
injective `f'^{-1}𝒪_{S'}`-modules, every class `x` of the abelian hypercohomology of the direct
image along `g'` of its underlying complex satisfies the edge identity
`realizationUnbounded_pushforwardPullback`. -/
theorem realizationUnbounded_pushforwardPullback_of_injective
    (I : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (hI : ∀ k, Injective (I.obj.X k)) (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        I)) n) :
    (realizationUnbounded (inverseImageBase f') I n).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj I))).hom x) =
      (lerayCohomologyIso (inverseImageBaseMap g' f' f g w) (DerivedCategory.Q.obj I.obj) n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
          (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) I.obj))).hom
          ((realizationUnbounded (inverseImageBase f)
            ((StacksDraft.KFlat.modulePushforward
              (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj I) n).hom.hom x)) := by
  have hu := isIso_sectionsUnit_toSheaf_of_injective (inverseImageBase f') I hI
  have hp := isIso_pushforwardPullback_toSheaf_of_injective g' f' f g w I hI
  obtain ⟨s, hs⟩ := exists_abelianGlobalClass _ n hu
    (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
      ((SheafOfModules.toSheaf
        (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj I))).hom x)
  have hx : x = abelianGlobalClass ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        I)) n s := by
    have hinj := (AddCommGrpCat.mono_iff_injective ((DerivedCategory.Plus.homologyFunctor _ n).map
      (g'.pushforwardPullback ((SheafOfModules.toSheaf
        (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj I)))).1
      (by haveI := hp; exact IsSplitMono.mono _)
    exact hinj (hs.symm.trans (abelianGlobalClass_pushforwardPullback g' _ n s).symm)
  subst hx
  exact realizationUnbounded_pushforwardPullback_abelianGlobalClass g' f' f g w I n s

/-- The left side of the edge identity is natural in the complex. -/
private theorem edge_lhs_naturality
    {M M' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f')))}
    (a : M ⟶ M') (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        M)) n) :
    (realizationUnbounded (inverseImageBase f') M' n).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M'))).hom
          (((DerivedCategory.Plus.homologyFunctor _ n).map
            ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
              (DerivedCategory.Plus.Q.map
                ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.map
                ((SheafOfModules.toSheaf
                  (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.map a))))).hom
            x)) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f')).map
          (DerivedCategory.Q.map a.hom))).hom
        ((realizationUnbounded (inverseImageBase f') M n).hom.hom
          (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
            ((SheafOfModules.toSheaf
              (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M))).hom
            x)) := by
  have h₁ := ConcreteCategory.congr_hom (congrArg (DerivedCategory.Plus.homologyFunctor _ n).map
    (Scheme.Hom.pushforwardPullback_naturality g'
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.map
        a))) x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h₁
  have h₂ := ConcreteCategory.congr_hom (realizationUnbounded_naturality (inverseImageBase f') a n)
    (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
      ((SheafOfModules.toSheaf
        (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M))).hom x)
  exact (congrArg (realizationUnbounded (inverseImageBase f') M' n).hom.hom h₁).trans h₂

/-- The right side of the edge identity, at a class of the abelian hypercohomology of the
underlying complex of `h_*M`: `realizationUnbounded` on `X`, the comparison `h_* ⟶ Rh_*` and
the Leray identification. -/
private def edgeRight
    (M : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (n : ℤ)
    (y : abelianHypercohomology ((SheafOfModules.toSheaf
      (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.obj
        ((StacksDraft.KFlat.modulePushforward
          (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M)) n) :
    (restrictGlobal (inverseImageBaseMap g' f' f g w)).obj
      (cohomologyModule (DerivedCategory.Q.obj M.obj) n) :=
  (lerayCohomologyIso (inverseImageBaseMap g' f' f g w) (DerivedCategory.Q.obj M.obj) n).hom
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
      (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) M.obj))).hom
      ((realizationUnbounded (inverseImageBase f)
        ((StacksDraft.KFlat.modulePushforward
          (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) n).hom.hom y))

/-- The right side of the edge identity is natural in the complex. -/
private theorem edgeRight_naturality
    {M M' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f')))}
    (a : M ⟶ M') (n : ℤ)
    (y : abelianHypercohomology ((SheafOfModules.toSheaf
      (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.obj
        ((StacksDraft.KFlat.modulePushforward
          (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M)) n) :
    edgeRight g' f' f g w M' n (((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((SheafOfModules.toSheaf
              (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.map
              ((StacksDraft.KFlat.modulePushforward
                (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.map a))))).hom y) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f')).map
          (DerivedCategory.Q.map a.hom))).hom (edgeRight g' f' f g w M n y) := by
  have h₁ := ConcreteCategory.congr_hom (realizationUnbounded_naturality (inverseImageBase f)
    ((StacksDraft.KFlat.modulePushforward
      (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.map a) n) y
  have h₂ := (map_map_comp_apply (baseSections (inverseImageBase f))
      (DerivedCategory.homologyFunctor _ n) _ _ _).symm.trans
    ((congrArg (fun z => ((DerivedCategory.homologyFunctor _ n).map
      ((baseSections (inverseImageBase f)).map z)).hom
        ((realizationUnbounded (inverseImageBase f) ((StacksDraft.KFlat.modulePushforward
          (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) n).hom.hom y))
      (pushforwardComparisonQ_naturality (inverseImageBaseMap g' f' f g w) a.hom)).trans
      (map_map_comp_apply (baseSections (inverseImageBase f))
        (DerivedCategory.homologyFunctor _ n) _ _ _))
  have h₃ := lerayCohomologyIso_naturality_apply (inverseImageBaseMap g' f' f g w)
    (DerivedCategory.Q.map a.hom) n
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
      (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) M.obj))).hom
      ((realizationUnbounded (inverseImageBase f) ((StacksDraft.KFlat.modulePushforward
        (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) n).hom.hom y))
  exact (congrArg (fun z => (lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
      (DerivedCategory.Q.obj M'.obj) n).hom
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
      (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) M'.obj))).hom z)) h₁).trans
    ((congrArg _ h₂).trans h₃)

/-- The underlying complex of the module direct image `h_*M` along `inverseImageBaseMap` is the
abelian direct image along `g'` of the underlying complex of `M`; the two are equal by definition,
and this is the identity, recorded once so that later statements need not unfold it. -/
private def toSheafPushforwardIso
    (M : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f')))) :
    (SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.obj
        ((StacksDraft.KFlat.modulePushforward
          (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) ≅
      (abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
        ((SheafOfModules.toSheaf
          (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M) :=
  Iso.refl _

/-- `toSheafPushforwardIso` is natural. -/
private theorem toSheafPushforwardIso_inv_naturality
    {M M' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f')))}
    (a : M ⟶ M') :
    (abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.map
        ((SheafOfModules.toSheaf
          (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.map a) ≫
        (toSheafPushforwardIso g' f' f g w M').inv =
      (toSheafPushforwardIso g' f' f g w M).inv ≫
        (SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.map
          ((StacksDraft.KFlat.modulePushforward
            (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.map a) :=
  ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun _ =>
    Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl)))

/-- `toSheafPushforwardIso` induces the identity on abelian hypercohomology. -/
private theorem homologyFunctor_map_toSheafPushforwardIso_inv
    (M : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        M)) n) :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (toSheafPushforwardIso g' f' f g w M).inv))).hom x = x := by
  have h : (DerivedCategory.Plus.homologyFunctor _ n).map
      ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (toSheafPushforwardIso g' f' f g w M).inv)) = 𝟙 _ := by
    show (DerivedCategory.Plus.homologyFunctor _ n).map
      ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (𝟙 _))) = 𝟙 _
    exact (congrArg (DerivedCategory.Plus.homologyFunctor _ n).map
      ((congrArg (sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map_id _)).trans (CategoryTheory.Functor.map_id _ _))).trans
      (CategoryTheory.Functor.map_id _ _)
  exact ConcreteCategory.congr_hom h x

/-- The edge identity on a complex of injectives, with the right side written through
`edgeRight` and `toSheafPushforwardIso`. -/
private theorem edge_of_injective
    (I : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (hI : ∀ k, Injective (I.obj.X k)) (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        I)) n) :
    (realizationUnbounded (inverseImageBase f') I n).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj I))).hom x) =
      edgeRight g' f' f g w I n (((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (toSheafPushforwardIso g' f' f g w I).inv))).hom x) :=
  (realizationUnbounded_pushforwardPullback_of_injective g' f' f g w I hI n x).trans
    (congrArg (edgeRight g' f' f g w I n)
      (homologyFunctor_map_toSheafPushforwardIso_inv g' f' f g w I n x)).symm

/-- `toSheafPushforwardIso` is natural, on abelian hypercohomology and on elements. -/
private theorem toSheafPushforwardIso_inv_naturality_apply
    {M M' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f')))}
    (a : M ⟶ M') (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        M)) n) :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (toSheafPushforwardIso g' f' f g w M').inv))).hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map
          ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.map
              ((SheafOfModules.toSheaf
                (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.map a))))).hom
          x) =
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((SheafOfModules.toSheaf
              (structureSheafRing (inverseImageBase f))).mapCochainComplexPlus.map
              ((StacksDraft.KFlat.modulePushforward
                (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.map a))))).hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map
          ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (toSheafPushforwardIso g' f' f g w M).inv))).hom x) :=
  square_apply (DerivedCategory.Plus.Q ⋙
      (sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n) _ _ _ _
    (toSheafPushforwardIso_inv_naturality g' f' f g w a) x

/-- The edge identity, with the right side written through `edgeRight` and
`toSheafPushforwardIso`: the reduction to a complex of injectives. -/
private theorem edge_toSheafPushforwardIso
    (M : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        M)) n) :
    (realizationUnbounded (inverseImageBase f') M n).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M))).hom x) =
      edgeRight g' f' f g w M n (((DerivedCategory.Plus.homologyFunctor _ n).map
        ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (toSheafPushforwardIso g' f' f g w M).inv))).hom x) := by
  obtain ⟨k, hk⟩ := M.2
  obtain ⟨J, -, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective M k
  have hJ : ∀ m, Injective (((InjectiveObject.ι _).mapCochainComplexPlus.obj J).obj.X m) :=
    fun m => (J.obj.X m).2
  have hQ : IsIso (DerivedCategory.Q.map i.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := SheafOfModules.{u}
      (structureSheafRing (inverseImageBase f'))) i.hom).2 hi
  have hH : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f')))
      n).map ((baseSections (inverseImageBase f')).map (DerivedCategory.Q.map i.hom))) :=
    Functor.map_isIso _ _
  have hinj := (ModuleCat.mono_iff_injective
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f'))) n).map
      ((baseSections (inverseImageBase f')).map (DerivedCategory.Q.map i.hom)))).1
    (IsIso.mono_of_iso _)
  apply hinj
  refine (edge_lhs_naturality g' f' i n x).symm.trans ?_
  refine (edge_of_injective g' f' f g w _ hJ n _).trans ?_
  refine (congrArg (edgeRight g' f' f g w _ n)
    (toSheafPushforwardIso_inv_naturality_apply g' f' f g w i n x)).trans ?_
  exact edgeRight_naturality g' f' f g w i n _

/-- **The edge identity of the Leray–Hirsch argument** ([Stacks, Tag 0FMP]), comparing the
pullback from a direct image in abelian sheaves with the one in modules through the realization
comparison of [Stacks, Tag 01F1]. For a commutative square `g' ≫ f = f' ≫ g` of schemes, the
induced morphism `h : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` and a bounded below complex `M` of
`f'^{-1}𝒪_{S'}`-modules, every class `x` of `Hⁿ(X, g'_*M)` (abelian sheaves) satisfies

`ρ_{X'}(g'^*x) = Leray_h(Hⁿ(RΓ(h_*M ⟶ Rh_*M))(ρ_X(x)))`,

where `g'^*` is the abelian pullback from the direct image and `ρ` is `realizationUnbounded`; the
abelian direct image `g'_*M` is, by definition, the underlying complex of the module direct image
`h_*M`. -/
theorem realizationUnbounded_pushforwardPullback
    (M : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing (inverseImageBase f'))))
    (n : ℤ)
    (x : abelianHypercohomology ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
        M)) n) :
    (realizationUnbounded (inverseImageBase f') M n).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ n).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj M))).hom x) =
      (lerayCohomologyIso (inverseImageBaseMap g' f' f g w) (DerivedCategory.Q.obj M.obj) n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections (inverseImageBase f)).map
          (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) M.obj))).hom
          ((realizationUnbounded (inverseImageBase f)
            ((StacksDraft.KFlat.modulePushforward
              (inverseImageBaseMap g' f' f g w)).mapCochainComplexPlus.obj M) n).hom.hom x)) :=
  (edge_toSheafPushforwardIso g' f' f g w M n x).trans
    (congrArg (edgeRight g' f' f g w M n)
      (homologyFunctor_map_toSheafPushforwardIso_inv g' f' f g w M n x))

end Stacks.DeRhamBaseChange

namespace AlgebraicGeometry.SheafOfModules

open Stacks.Cech.Hypercohomology

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The comparison of the two realizations of relative de Rham cohomology is
`realizationUnbounded`**, read through the identification `deRhamAbelianComplexPlusIso` of the de
Rham complex of abelian sheaves with the underlying complex of the de Rham complex of sheaves of
`A`-modules. -/
theorem deRhamCohomologyAbelianIsoDeRhamCohomology_eq (n : ℤ) :
    deRhamCohomologyAbelianIsoDeRhamCohomology B D n =
      (DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
          (deRhamAbelianComplexPlusIso B D) ≪≫
        realizationUnbounded (baseRingedSpace A) (deRhamComplexPlus (X := X) B D) n :=
  Iso.trans_assoc _ _ _

end AlgebraicGeometry.SheafOfModules

namespace Stacks.DeRhamBaseChange

/-! ### The de Rham specialization -/

section DeRham

open Stacks.Cech.Hypercohomology Stacks.DeRhamDirectImage
open Stacks.Cohomology.LerayLowDegree (abelianPushforward)
open Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The comparison of the two realizations of de Rham cohomology on `X'` is `realizationUnbounded`
on `(X', f'^{-1}𝒪_{S'})`, after the identification of the de Rham complexes. -/
private theorem deRhamCohomologyAbelianIsoDeRhamCohomology_apply (m : ℤ)
    (y : Scheme.Hom.deRhamCohomology f' m) :
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
        m).hom.hom y =
      (realizationUnbounded (inverseImageBase f')
        (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (X := X'.toRingedSpace)
          (Scheme.Hom.deRhamAlgebras f')
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')))
        m).hom.hom
        (((DerivedCategory.Plus.homologyFunctor _ m).map
          ((sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
                (Scheme.Hom.deRhamAlgebras f')
                (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                  (Scheme.Hom.deRhamAlgebras f'))).hom))).hom y) :=
  rfl

/-- The identification of the de Rham complexes on `X'`, carried across the abelian pullback from
the direct image along `g'`. -/
private theorem deRham_pushforwardPullback_naturality (m : ℤ)
    (z : abelianHypercohomology (Scheme.Hom.deRhamPushforwardPlus g' f') m) :
    ((DerivedCategory.Plus.homologyFunctor _ m).map
        ((sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
              (Scheme.Hom.deRhamAlgebras f')
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras f'))).hom))).hom
        (((DerivedCategory.Plus.homologyFunctor _ m).map (g'.pushforwardPullback
          (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras f')
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras f'))))).hom z) =
      ((DerivedCategory.Plus.homologyFunctor _ m).map (g'.pushforwardPullback
          ((SheafOfModules.toSheaf
            (structureSheafRing (inverseImageBase f'))).mapCochainComplexPlus.obj
            (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (X := X'.toRingedSpace)
              (Scheme.Hom.deRhamAlgebras f')
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras f')))))).hom
        (((DerivedCategory.Plus.homologyFunctor _ m).map
          ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.map
              (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
                (Scheme.Hom.deRhamAlgebras f')
                (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                  (Scheme.Hom.deRhamAlgebras f'))).hom)))).hom z) :=
  (square_apply (DerivedCategory.Plus.homologyFunctor _ m) _ _ _ _
    (Scheme.Hom.pushforwardPullback_naturality g'
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras f'))).hom) z).symm

/-- A composite of morphisms of abelian groups, evaluated on an element, at variables. -/
private theorem comp_apply_of_eq {C : Type*} [Category* C] (H : C ⥤ AddCommGrpCat.{u})
    {a b c : C} (x : a ⟶ b) (y : b ⟶ c) (t : a ⟶ c) (h : x ≫ y = t) (z : H.obj a) :
    (H.map y).hom ((H.map x).hom z) = (H.map t).hom z := by
  rw [← h, Functor.map_comp]
  rfl

/-- The abelian direct image of the identification of the de Rham complexes on `X'`, followed by
`toSheafPushforwardIso`, is `deRhamPushforwardPlusIso`. -/
private theorem abelianPushforward_map_deRhamAbelianComplexPlusIso_comp :
    (abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.map
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
          (Scheme.Hom.deRhamAlgebras f')
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras f'))).hom ≫
        (toSheafPushforwardIso g' f' f g w
          (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (X := X'.toRingedSpace)
            (Scheme.Hom.deRhamAlgebras f')
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras f')))).inv =
      (deRhamPushforwardPlusIso g' f' f g w).hom :=
  ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun _ =>
    Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl)))

/-- **The edge identity for relative de Rham cohomology** ([Stacks, Tag 0FMP]). For a commutative
square `g' ≫ f = f' ≫ g` of schemes and `g₀ = inverseImageBaseMap g' f' f g w`, the de Rham
pullback `H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of [Stacks, Tag 0FL6], read in derived global sections
of modules through the comparison of the two realizations ([Stacks, Tag 01F1]), is the canonical
map `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}`, the comparison `(g₀)_* ⟶ Rg₀_*` and the Leray identification
`H^m(X, Rg₀_* -) = H^m(X', -)`. -/
theorem deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback (m : ℤ)
    (ξ : Scheme.Hom.deRhamCohomology f m) :
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
        m).hom.hom ((Scheme.Hom.deRhamCohomologyPullback g' f f' g w m).hom ξ) =
      (lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
        (DerivedCategory.Q.obj (deRhamCochainComplex f')) m).hom
        (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase f)).map
          (DerivedCategory.Q.map (deRhamPushforwardInt g' f' f g w) ≫
            pushforwardComparisonQ (inverseImageBaseMap g' f' f g w)
              (AlgebraicGeometry.ProperSmoothDeRham.deRhamComplexInt f')))).hom
          ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
            (Scheme.Hom.deRhamAlgebras f)
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
            m).hom.hom ξ)) := by
  have hD1 := (deRhamCohomologyAbelianIsoDeRhamCohomology_apply f' m
      ((Scheme.Hom.deRhamCohomologyPullback g' f f' g w m).hom ξ)).trans
    (congrArg (realizationUnbounded (inverseImageBase f')
        (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (X := X'.toRingedSpace)
          (Scheme.Hom.deRhamAlgebras f')
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')))
        m).hom.hom
      ((congrArg ((DerivedCategory.Plus.homologyFunctor _ m).map
          ((sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
                (Scheme.Hom.deRhamAlgebras f')
                (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                  (Scheme.Hom.deRhamAlgebras f'))).hom))).hom
        (Scheme.Hom.deRhamCohomologyPullback_apply g' f f' g w m ξ)).trans
        (deRham_pushforwardPullback_naturality g' f' m _)))
  have hD2 := edge_toSheafPushforwardIso g' f' f g w
    (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (X := X'.toRingedSpace)
      (Scheme.Hom.deRhamAlgebras f')
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))) m
    (((DerivedCategory.Plus.homologyFunctor _ m).map
      ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((abelianPushforward.{u, u} g'.base).mapCochainComplexPlus.map
          (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
            (Scheme.Hom.deRhamAlgebras f')
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras f'))).hom)))).hom
      (((DerivedCategory.Plus.homologyFunctor _ m).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (Scheme.Hom.deRhamAbelianPushforwardMapPlus g' f f' g w)))).hom ξ))
  refine hD1.trans (hD2.trans ?_)
  refine (congrArg (edgeRight g' f' f g w
      (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus (X := X'.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))) m)
    ((comp_apply_of_eq (DerivedCategory.Plus.Q ⋙
        (sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m) _ _ _
      (abelianPushforward_map_deRhamAbelianComplexPlusIso_comp g' f' f g w) _).trans
      (square_apply (DerivedCategory.Plus.Q ⋙
        (sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m) _ _ _ _
        (deRhamAbelianPushforwardMapPlus_comp_iso g' f' f g w) ξ))).trans ?_
  have hN := ConcreteCategory.congr_hom (realizationUnbounded_naturality (inverseImageBase f)
    (deRhamPushforwardIntPlusHom g' f' f g w) m)
    (((DerivedCategory.Plus.homologyFunctor _ m).map
      ((sectionsFunctor (inverseImageBase f).carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
            (Scheme.Hom.deRhamAlgebras f)
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras f))).hom))).hom ξ)
  have hF := deRhamCohomologyAbelianIsoDeRhamCohomology_apply f m ξ
  exact (congrArg (fun z => (lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
      (DerivedCategory.Q.obj (deRhamCochainComplex f')) m).hom
    (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase f)).map
      (pushforwardComparisonQ (inverseImageBaseMap g' f' f g w)
        (AlgebraicGeometry.ProperSmoothDeRham.deRhamComplexInt f')))).hom z))
    (hN.trans (congrArg (fun z => ((DerivedCategory.homologyFunctor _ m).map
      ((baseSections (inverseImageBase f)).map
        (DerivedCategory.Q.map (deRhamPushforwardInt g' f' f g w)))).hom z) hF.symm))).trans
    (congrArg (lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
      (DerivedCategory.Q.obj (deRhamCochainComplex f')) m).hom
      (map_map_comp_apply (baseSections (inverseImageBase f))
        (DerivedCategory.homologyFunctor _ m) _ _ _).symm)

end DeRham

end Stacks.DeRhamBaseChange

end
