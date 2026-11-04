module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueSequenceBase
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationBoundary
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ShiftedBoundaryHomology

/-!
# The value at the unit of the boundary map of the residue sequence

Let `D` be a line-bundle situation (`f : X ⟶ S`, `L` invertible) and
`δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` the boundary map of the shifted residue sequence
`0 → Ω^•[1] → Ω^•_{L^⋆/S,0}[1] → Ω^• → 0` of [Stacks, Tag 0FUF]. The value `δ(1)` of Remark 0FU7
lives in de Rham cohomology computed in sheaves of `f^{-1}𝒪_S`-modules, while the first Chern
class of [Stacks, Tag 0FLE] is constructed in the abelian-sheaf realization. This file reduces the
computation of `δ(1)` to the abelian-sheaf realization: the realization comparison of
[Stacks, Tag 01F1] intertwines the two boundary maps
(`Stacks.Cohomology.RealizationBoundary.shortExactBoundary_comp_realizationIsoAt`) and the two
shift identifications (`Stacks.Cohomology.RealizationShift.realizationIsoAt_shift`), so `δ(1) = c`
as soon as the abelian boundary of the sequence carries the abelian class of `1` to `c`.

## Main definitions

* `Stacks.LineBundle.Situation.residuePlusSequence`: the shifted residue sequence as a short
  complex of bounded below complexes.

## Main results

* `Stacks.LineBundle.Situation.deRhamEvalOne_residueBoundary_eq_of`: the reduction.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.LineBundle

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

variable (D : Situation.{u})

/-- The translate of a bounded below complex is bounded below. -/
theorem plus_shift_prop {C : Type*} [Category* C] [Abelian C] (K : CochainComplex.Plus C) (n : ℤ) :
    CochainComplex.plus C (K.obj⟦n⟧) :=
  (CochainComplex.plus C).prop_of_iso (((CochainComplex.Plus.ι C).commShiftIso n).app K)
    (K⟦n⟧).property

/-- The base `f^{-1}𝒪_S` of the relative de Rham complex of a situation, as a sheaf of rings. -/
abbrev Situation.baseSheaf : TopCat.Sheaf CommRingCat.{u} D.X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} D.f.base).obj D.S.sheaf

/-- The ringed space `(X, f^{-1}𝒪_S)`. -/
abbrev Situation.baseSpace : RingedSpace.{u, u} :=
  AlgebraicGeometry.SheafOfModules.baseRingedSpace D.baseSheaf

/-- The relative de Rham complex `Ω^•_{X/S}` of a situation, as a bounded below complex of sheaves
of `f^{-1}𝒪_S`-modules. -/
abbrev Situation.deRhamPlus :
    CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing D.baseSpace)) :=
  AlgebraicGeometry.SheafOfModules.deRhamComplexPlus.{u} (X := D.X.toRingedSpace)
    (Scheme.Hom.deRhamAlgebras D.f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))

/-- **The shifted residue sequence `0 → Ω^•[1] → Ω^•_{L^⋆/S,0}[1] → Ω^• → 0` as a short complex of
bounded below complexes.** -/
def Situation.residuePlusSequence :
    ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing D.baseSpace))) where
  X₁ := ⟨_, plus_shift_prop (Situation.deRhamPlus D) 1⟩
  X₂ := ⟨_, plus_shift_prop (⟨D.weightZeroBaseComplex.extend ComplexShape.embeddingUpNat, 0,
    inferInstance⟩ : CochainComplex.Plus (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f))) 1⟩
  X₃ := Situation.deRhamPlus D
  f := ObjectProperty.homMk D.residueShiftedSequence.incl
  g := ObjectProperty.homMk D.residueShiftedSequence.res
  zero := ObjectProperty.hom_ext _ D.residueShiftedSequence.incl_comp_res

/-- The shifted residue sequence of bounded below complexes is short exact. -/
theorem Situation.residuePlusSequence_shortExact :
    (Stacks.Cohomology.RightDerivedBoundary.toSC D.residuePlusSequence).ShortExact :=
  D.residueShiftedSequence.shortExact

open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.RealizationShift (realizationIsoAt shiftHomologyIso shiftHomologyIsoU)
open Stacks.Cohomology.DerivedSectionsLeray (derivedSectionsOverOpen)

/-- Derived global sections of the underlying complex of abelian sheaves, on bounded below
complexes of `f^{-1}𝒪_S`-modules. -/
abbrev Situation.abelianSections :
    CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing D.baseSpace)) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q ⋙ (sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus

/-- The identification of the first term of the residue sequence with the translate of the de Rham
complex, in bounded below complexes. -/
def Situation.residuePlusShiftHom :
    D.residuePlusSequence.X₁ ⟶ D.deRhamPlus⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk (((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).inv.app D.deRhamPlus)

/-- The algebra of `residuePlusShiftHom_comp_shiftHomologyIsoU`, with every object and morphism a
variable. -/
private theorem shift_book {C D' : Type*} [Category* C] [Category* D'] (H : C ⥤ D')
    {p q r : C} {u : D'} (e : p ⟶ q) (c : q ⟶ r) (c' : p ⟶ r) (k : H.obj r ⟶ u)
    (sl : H.obj q ⟶ u) (sr : H.obj r ⟶ u) (hsl : sl = H.map c ≫ k) (hsr : sr = k)
    (hc : e ≫ c = c') : H.map e ≫ sl = H.map c' ≫ sr := by
  rw [hsl, hsr, ← hc, H.map_comp, Category.assoc]

/-- The identification of the first term of the residue sequence with the translate of the de Rham
complex, followed by the commutation of `Q` with the shift on bounded below complexes, is the
commutation of `Q` with the shift on complexes. -/
theorem Situation.Q_map_residuePlusShiftHom_comp :
    (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing D.baseSpace))).map
        D.residuePlusShiftHom.hom ≫
      ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing D.baseSpace)) ⋙
        DerivedCategory.Q).commShiftIso (1 : ℤ)).hom.app D.deRhamPlus =
      ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing D.baseSpace))).commShiftIso
        (1 : ℤ)).hom.app D.deRhamPlus.obj := by
  rw [Functor.commShiftIso_comp_hom_app, ← Category.assoc, ← Functor.map_comp]
  change DerivedCategory.Q.map (((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).inv.app
    D.deRhamPlus ≫ ((CochainComplex.Plus.ι _).commShiftIso (1 : ℤ)).hom.app D.deRhamPlus) ≫ _ = _
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- **The module side of the shift bookkeeping**: the identification of the first term of the
residue sequence with the translate of the de Rham complex, followed by
`H¹(X, Ω^•[1]) = H²(X, Ω^•)` for bounded below complexes, is the commutation of the localization
with the shift followed by `H¹(X, Ω^•[1]) = H²(X, Ω^•)` in the derived category. -/
theorem Situation.residuePlusShiftHom_comp_shiftHomologyIsoU :
    (DerivedCategory.homologyFunctor _ 1).map ((derivedSectionsOverOpen D.baseSpace ⊤).map
        ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing D.baseSpace))).map
          D.residuePlusShiftHom.hom)) ≫
      (shiftHomologyIsoU
        ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing D.baseSpace)) ⋙
          DerivedCategory.Q) ⋙
        derivedSectionsOverOpen D.baseSpace ⊤) D.deRhamPlus 1 1 2 (by omega)).hom =
    (DerivedCategory.homologyFunctor _ 1).map ((derivedSectionsOverOpen D.baseSpace ⊤).map
        (((DerivedCategory.Q
          (C := SheafOfModules.{u} (structureSheafRing D.baseSpace))).commShiftIso (1 : ℤ)).hom.app
            D.deRhamPlus.obj)) ≫
      (shiftHomologyIsoU (derivedSectionsOverOpen D.baseSpace ⊤)
        ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing D.baseSpace))).obj
          D.deRhamPlus.obj) 1 1 2 (by omega)).hom :=
  shift_book (derivedSectionsOverOpen D.baseSpace ⊤ ⋙ DerivedCategory.homologyFunctor _ 1)
    _ _ _ _ _ _ (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_comp_hom _ _ _ _ _ _ _) rfl
    D.Q_map_residuePlusShiftHom_comp

open Stacks.Cohomology.RightDerivedBoundary (shortExactBoundary)
open Stacks.Cohomology.RealizationBoundary (mapPlus toSC_mapPlus_shortExact)

/-- The algebra of `deRhamEvalOne_residueBoundary_eq_of`, with every object and morphism a
variable. -/
private theorem eval_paste {C D' : Type*} [Category* C] [Category* D'] (G : D' ⥤ C)
    {m₀ m₁ m₁' m₁'' m₂ : D'} {a₀ b₁ b₁' b₂ : C}
    (b : m₀ ⟶ m₂) (sm : m₀ ⟶ m₁) (cq : m₁ ⟶ m₁'') (shU : m₁'' ⟶ m₂) (te : m₁ ⟶ m₁')
    (shM : m₁' ⟶ m₂) (R₀ : a₀ ⟶ G.obj m₀) (δ : a₀ ⟶ b₁) (R₁ : b₁ ⟶ G.obj m₁) (fe : b₁ ⟶ b₁')
    (R₁' : b₁' ⟶ G.obj m₁') (shA : b₁' ⟶ b₂) (R₂ : b₂ ⟶ G.obj m₂)
    (hM : b = sm ≫ cq ≫ shU) (hE : te ≫ shM = cq ≫ shU) (hB : δ ≫ R₁ = R₀ ≫ G.map sm)
    (hN : fe ≫ R₁' = R₁ ≫ G.map te) (hS : R₁' ≫ G.map shM = shA ≫ R₂) :
    R₀ ≫ G.map b = δ ≫ fe ≫ shA ≫ R₂ := by
  rw [hM, ← hE, G.map_comp, G.map_comp, ← reassoc_of% hB, ← hS, reassoc_of% hN]

/-- **The value at the unit of the boundary map of the residue sequence, from the abelian-sheaf
realization.** If the class `1_{ab}` of `H⁰` of the abelian de Rham complex is carried to the unit
`1 ∈ H⁰_{dR}` by the realization comparison of Stacks 01F1, and the abelian boundary of the
residue sequence carries `1_{ab}` to `c` under `H¹(X, Ω^•[1]) = H²(X, Ω^•)`, then the boundary map
of the residue sequence takes the value `c` at the unit. -/
theorem Situation.deRhamEvalOne_residueBoundary_eq_of
    (oneAb : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 0).obj
      (D.abelianSections.obj D.deRhamPlus))
    (hU1 : (realizationIsoAt D.baseSpace D.deRhamPlus 0).hom oneAb =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))
    (c : AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) 2)
    (hAB : (shiftHomologyIso D.abelianSections D.deRhamPlus 1 1 2 (by omega)).hom
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 1).map
          (D.abelianSections.map D.residuePlusShiftHom)
          (shortExactBoundary (sectionsFunctor D.baseSpace.carrier ⊤)
            (mapPlus (SheafOfModules.toSheaf (structureSheafRing D.baseSpace))
              D.residuePlusSequence)
            (toSC_mapPlus_shortExact _ _ D.residuePlusSequence_shortExact) 0 1 rfl oneAb)) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        ((sectionsFunctor D.baseSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso
              (Scheme.Hom.deRhamAlgebras D.f)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras D.f))).hom)) c) :
    AlgebraicGeometry.SheafOfModules.deRhamEvalOne (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) 2
        D.residueShiftedSequence.boundary =
      (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))
          2).hom.hom c := by
  have hM := Stacks.ShiftedBoundary.Sequence.homology_boundary_comp_shiftHomologyIsoU
    (derivedSectionsOverOpen D.baseSpace ⊤) D.residueShiftedSequence
  have hE := D.residuePlusShiftHom_comp_shiftHomologyIsoU
  have hB := Stacks.Cohomology.RealizationBoundary.shortExactBoundary_comp_realizationIsoAt
    D.baseSpace D.residuePlusSequence D.residuePlusSequence_shortExact 0 1 rfl
  have hN := Stacks.Cohomology.RealizationShift.realizationIsoAt_naturality D.baseSpace
    D.residuePlusShiftHom 1
  have hS := Stacks.Cohomology.RealizationShift.realizationIsoAt_shift D.baseSpace D.deRhamPlus
    1 1 2 (by omega)
  have key := eval_paste (forget₂ (ModuleCat.{u} ((structureSheafRing D.baseSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}) _ _ _ _ _ _ _ _ _ _ _ _ _ hM hE hB hN hS
  have hRE :=
    Stacks.Cohomology.RealizationAgreement.realizationIso_hom_comp_derivedSectionsFunctorIso
      D.baseSpace D.deRhamPlus 2
  have h₁ := ConcreteCategory.congr_hom key oneAb
  have hU1' : (realizationIsoAt D.baseSpace D.residuePlusSequence.X₃ 0).hom oneAb =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) := hU1
  refine Eq.trans ?_ (h₁.trans ?_)
  · exact congrArg (fun z => ConcreteCategory.hom ((forget₂ (ModuleCat.{u}
      ((structureSheafRing D.baseSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ 0).map
          ((derivedSectionsOverOpen D.baseSpace ⊤).map D.residueShiftedSequence.boundary) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
          (derivedSectionsOverOpen D.baseSpace ⊤)
          _ 2 0 2 (by omega)).hom)) z) hU1'.symm
  · exact (congrArg (realizationIsoAt D.baseSpace D.deRhamPlus 2).hom hAB).trans
      (ConcreteCategory.congr_hom hRE _).symm

end Stacks.LineBundle
