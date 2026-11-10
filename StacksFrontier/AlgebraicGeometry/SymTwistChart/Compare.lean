module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeScaling
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwist
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart
public import StacksFrontier.AlgebraicGeometry.RelativeProjGlue.Basic
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.DegreeOne

/-!
# The chart isomorphism of `𝐏(E ⊗ ℒ) ≅ 𝐏(E)` is canonical and natural

For an affine open `U` of a scheme `X` and a trivialization `e` of an `𝒪_X`-module `L` over `U`,
`Stacks.SymTwistChart.chartProjIso` is an isomorphism `Proj Γ(U, Sym(E ⊗ L)) ≅ Proj Γ(U, Sym E)`
over the base. This file proves two compatibilities of these chart isomorphisms:

* the chart isomorphism does not depend on the trivialization (`chartProjIso_eq`);
* the chart isomorphisms commute with the transition morphisms of the charts
  (`chartProjIso_naturality`).

## Main results

* `Stacks.SymTwistChart.exists_unit_generator`: two trivializations of `L` over `U` have
  generators differing by a unit of `𝒪_X(U)`.
* `Stacks.SymTwistChart.chartGradedHom_eq_degreeScale_comp`: the comparison homomorphisms of two
  trivializations differ by rescaling the degree-`d` part of the target by `u ^ d`, where `u` is
  the unit relating their generators.
* `Stacks.SymTwistChart.chartProjIso_eq`: **the chart isomorphism does not depend on the
  trivialization.**
* `Stacks.SymTwistChart.res_comp_chartGradedHom`: the restriction square of graded ring
  homomorphisms commutes on the nose, for the restricted trivialization.
* `Stacks.SymTwistChart.chartProjIso_naturality`: **the chart isomorphisms commute with the
  transition morphisms of the charts**, for arbitrary trivializations over the two opens.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification
open Stacks.AlgebraicGeometry.RelativeProjGlue (chartFunctor irrelevant_le_map_res_of_le
  mapDomain_res_eq_top_of_le)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain mapDomain_eq_top_of_irrelevant_le_map)
open Stacks.AlgebraicGeometry.ProjBundleSurjection (mapHomOfTop_comp)
open Stacks.AlgebraicGeometry.ProjPolynomialSections (mapHomOfTop_congr)
open Stacks.AlgebraicGeometry.TwistGenerator (res_generator)
open Stacks.AlgebraicGeometry.GradedAlgebraTwist (tensorSectionsAt_smul_right
  tensorSectionsAt_naturality)

universe u

namespace Stacks.SymTwistChart

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {X : Scheme.{u}} (E L : X.Modules)
  [E.IsQuasicoherent] [(tensorObj E L).IsQuasicoherent]
  (hqcE : Stacks.SymGraded.IsQuasicoherentPieces E)
  (hqcEL : Stacks.SymGraded.IsQuasicoherentPieces (tensorObj E L))

/-! ### Independence of the trivialization -/

section Independence

variable {U : X.Opens}
  (e e' : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))

/-- **Two trivializations of `L` over `U` have generators differing by a unit of `𝒪_X(U)`.** -/
public theorem exists_unit_generator :
    ∃ u : Γ(X, U)ˣ, generator L e' = (u : Γ(X, U)) • generator L e :=
  Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton
    (bijective_toSpanSingleton_generator L e) (bijective_toSpanSingleton_generator L e')

variable (hUaff : IsAffineOpen U)

include hUaff in
/-- **The two comparisons differ by rescaling the degree-`d` part of the target by `u ^ d`**,
where the generators of the two trivializations differ by the unit `u`. -/
public theorem chartGradedHom_eq_degreeScale_comp (u : Γ(X, U)ˣ)
    (hu : generator L e' = (u : Γ(X, U)) • generator L e) :
    chartGradedHom E L hqcE hqcEL e' hUaff =
      (Stacks.GradedRing.degreeScale
          ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U)
          ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
            (u : Γ(X, U)))).comp
        (chartGradedHom E L hqcE hqcEL e hUaff) := by
  refine gradedRingHom_ext_degree_one E hqcE hUaff (fun r => ?_) (fun m => ?_)
  · refine Eq.trans (chartRingEquiv_strHom E L hqcE hqcEL e' hUaff r) ?_
    refine Eq.trans ?_ (congrArg
      (Stacks.GradedRing.degreeScale
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U)
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
          (u : Γ(X, U))))
      (chartRingEquiv_strHom E L hqcE hqcEL e hUaff r)).symm
    refine Eq.trans ?_ (Stacks.GradedRing.degreeScale_apply_of_mem
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U) _
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U r)).symm
    rw [pow_zero, one_mul]
  · refine Eq.trans (chartRingEquiv_of_symOne E L hqcE hqcEL e' hUaff m) ?_
    have hsec : sectionsEquiv E L e' m = (u : Γ(X, U)) • sectionsEquiv E L e m := by
      rw [sectionsEquiv_apply, sectionsEquiv_apply, hu]
      exact Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_smul_right
        X.sheaf.obj (isSheafStr (X := X)) (op U) E L (u : Γ(X, U)) m (generator L e)
    refine Eq.trans (congrArg (fun y => DirectSum.of
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).sectionPieces U) 1
      (symOne (tensorObj E L) hqcEL y)) hsec) ?_
    refine Eq.trans (congrArg (DirectSum.of
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).sectionPieces U) 1)
      (symOne_smul (tensorObj E L) hqcEL (u : Γ(X, U)) (sectionsEquiv E L e m))) ?_
    refine Eq.trans ((Stacks.SymGraded.schemeSheafGradedAlgebra
      (tensorObj E L) hqcEL).strHom_mul_of U (u : Γ(X, U))
      (symOne (tensorObj E L) hqcEL (sectionsEquiv E L e m))).symm ?_
    refine Eq.trans ?_ (congrArg
      (Stacks.GradedRing.degreeScale
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U)
        ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
          (u : Γ(X, U))))
      (chartRingEquiv_of_symOne E L hqcE hqcEL e hUaff m)).symm
    refine Eq.trans ?_ (Stacks.GradedRing.degreeScale_apply_of_mem
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
        (u : Γ(X, U)))
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).of_mem_grading U
        (n := 1) (symOne (tensorObj E L) hqcEL (sectionsEquiv E L e m)))).symm
    rw [pow_one]

include hUaff in
/-- **The chart isomorphism does not depend on the chosen trivialization of `L`.** -/
public theorem chartProjIso_eq :
    chartProjIso E L hqcE hqcEL e hUaff = chartProjIso E L hqcE hqcEL e' hUaff := by
  obtain ⟨u, hu⟩ := exists_unit_generator L e e'
  have hcomp := chartGradedHom_eq_degreeScale_comp E L hqcE hqcEL e e' hUaff u hu
  refine Iso.ext (Eq.trans (chartProjIso_hom_eq_map E L hqcE hqcEL e hUaff) ?_)
  refine Eq.trans ?_ (chartProjIso_hom_eq_map E L hqcE hqcEL e' hUaff).symm
  refine (Stacks.GradedRing.Proj_map_eq_of_target_degreeScale
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
      (u : Γ(X, U)))
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
      ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)))
    ?_ (chartGradedHom E L hqcE hqcEL e hUaff) (chartGradedHom E L hqcE hqcEL e' hUaff)
    (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e hUaff)
    (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e' hUaff) ?_).symm
  · exact (map_mul ((Stacks.SymGraded.schemeSheafGradedAlgebra
      (tensorObj E L) hqcEL).strHom U) _ _).symm.trans
      ((congrArg ((Stacks.SymGraded.schemeSheafGradedAlgebra
          (tensorObj E L) hqcEL).strHom U) u.mul_inv).trans
        (map_one ((Stacks.SymGraded.schemeSheafGradedAlgebra
          (tensorObj E L) hqcEL).strHom U)))
  · intro i a ha
    refine Eq.trans (congrArg (fun φ => φ a) hcomp) ?_
    exact Stacks.GradedRing.degreeScale_apply_of_mem
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).strHom_mem U
        (u : Γ(X, U)))
      (GradedRingHom.map_mem (chartGradedHom E L hqcE hqcEL e hUaff) ha)

end Independence

/-! ### Naturality in the open -/

section Naturality

variable {U U' : X.Opens} (h : U' ≤ U)
  (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))

omit [E.IsQuasicoherent] [(tensorObj E L).IsQuasicoherent] in
/-- **Restricting `x ⊗ g` gives `res x ⊗ res g`, and `res g` is the generator of the restricted
trivialization.** -/
public theorem res_sectionsEquiv (m : Γ(E, U)) :
    (tensorObj E L).val.map (homOfLE h).op (sectionsEquiv E L e m) =
      sectionsEquiv E L (isoUnitOverOfHom L (homOfLE h) e) (E.val.map (homOfLE h).op m) := by
  refine Eq.trans (congrArg (fun y => (tensorObj E L).val.map (homOfLE h).op y)
    (sectionsEquiv_apply E L e m)) ?_
  refine Eq.trans (tensorSectionsAt_naturality X.sheaf.obj (isSheafStr (X := X)) E L
    (homOfLE h).op m (generator L e)) ?_
  refine Eq.trans (congrArg (fun g => tensorSectionsAt X.sheaf.obj (isSheafStr (X := X))
    (op U') E L (E.val.map (homOfLE h).op m) g) (res_generator h e)) ?_
  exact (sectionsEquiv_apply E L (isoUnitOverOfHom L (homOfLE h) e)
    (E.val.map (homOfLE h).op m)).symm

variable (hUaff : IsAffineOpen U) (hU'aff : IsAffineOpen U')

include hUaff hU'aff in
/-- **The ring-level square commutes on the nose for the restricted trivialization**: the
comparison over `U` followed by restriction to `U'` is restriction to `U'` followed by the
comparison over `U'` for the restricted trivialization. -/
public theorem res_comp_chartGradedHom :
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).res h).comp
        (chartGradedHom E L hqcE hqcEL e hUaff) =
      (chartGradedHom E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) hU'aff).comp
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).res h) := by
  refine gradedRingHom_ext_degree_one E hqcE hUaff (fun r => ?_) (fun m => ?_)
  · change (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).resRingHom h
        (chartRingEquiv E L hqcE hqcEL e hUaff
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).strHom U r)) =
      chartRingEquiv E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) hU'aff
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).resRingHom h
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).strHom U r))
    rw [chartRingEquiv_strHom, SheafGradedAlgebra.resRingHom_strHom,
      SheafGradedAlgebra.resRingHom_strHom, chartRingEquiv_strHom]
  · change (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).resRingHom h
        (chartRingEquiv E L hqcE hqcEL e hUaff
          (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionPieces U) 1
            (symOne E hqcE m))) =
      chartRingEquiv E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) hU'aff
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).resRingHom h
          (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionPieces U) 1
            (symOne E hqcE m)))
    rw [chartRingEquiv_of_symOne, SheafGradedAlgebra.resRingHom_of,
      SheafGradedAlgebra.resRingHom_of, resPiece_symOne, resPiece_symOne]
    refine Eq.trans (congrArg (fun y => DirectSum.of
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).sectionPieces U') 1
      (symOne (tensorObj E L) hqcEL y)) (res_sectionsEquiv E L h e m)) ?_
    exact (chartRingEquiv_of_symOne E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) hU'aff
      (E.val.map (homOfLE h).op m)).symm

end Naturality

section NaturalitySite

variable (U U' : X.AffineZariskiSite) (φ : U' ⟶ U)
  (e : L.over U.toOpens ≅ SheafOfModules.unit (X.ringCatSheaf.over U.toOpens))
  (e' : L.over U'.toOpens ≅ SheafOfModules.unit (X.ringCatSheaf.over U'.toOpens))

/-- **The chart isomorphisms are natural in the affine open.** For an inclusion `U' ⊆ U` of
affine opens of the base, both carrying trivializations of `L`, the chart isomorphism over `U'`
followed by the transition morphism of the charts of `Sym(E)` is the transition morphism of the
charts of `Sym(E ⊗ L)` followed by the chart isomorphism over `U`. -/
public theorem chartProjIso_naturality :
    (chartProjIso E L hqcE hqcEL e' U'.2).hom ≫
        (chartFunctor
          (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra).map φ =
      (chartFunctor (Stacks.SymGraded.schemeSheafGradedAlgebra
          (tensorObj E L) hqcEL).toGradedAlgebra).map φ ≫
        (chartProjIso E L hqcE hqcEL e U.2).hom := by
  have h : U'.toOpens ≤ U.toOpens := Scheme.AffineZariskiSite.toOpens_mono φ.le
  have hresA := irrelevant_le_map_res_of_le
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra φ.le h
  have hresB := irrelevant_le_map_res_of_le
    (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).toGradedAlgebra φ.le h
  have hcomp := res_comp_chartGradedHom E L hqcE hqcEL h e U.2 U'.2
  have hd1 : mapDomain ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U.toOpens)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U'.toOpens)
      ((chartGradedHom E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) U'.2).comp
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).res h)) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (HomogeneousIdeal.irrelevant_le_map_comp hresA
        (irrelevant_le_map_chartGradedHom E L hqcE hqcEL
          (isoUnitOverOfHom L (homOfLE h) e) U'.2))
  have hd2 : mapDomain ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U.toOpens)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U'.toOpens)
      (((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).res h).comp
        (chartGradedHom E L hqcE hqcEL e U.2)) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (HomogeneousIdeal.irrelevant_le_map_comp
        (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e U.2) hresB)
  have hdomA := mapDomain_res_eq_top_of_le
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).toGradedAlgebra φ.le h
  have hdomB := mapDomain_res_eq_top_of_le
    (Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).toGradedAlgebra φ.le h
  have hdome : mapDomain ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U.toOpens)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U.toOpens)
      (chartGradedHom E L hqcE hqcEL e U.2) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e U.2)
  have hdome' : mapDomain ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U'.toOpens)
      ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U'.toOpens)
      (chartGradedHom E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) U'.2) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_chartGradedHom E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) U'.2)
  rw [chartProjIso_eq E L hqcE hqcEL e' (isoUnitOverOfHom L (homOfLE h) e) U'.2]
  refine Eq.trans (mapHomOfTop_comp
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U.toOpens)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U'.toOpens)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U'.toOpens)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).res h)
    (chartGradedHom E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) U'.2) hresA
    (irrelevant_le_map_chartGradedHom E L hqcE hqcEL (isoUnitOverOfHom L (homOfLE h) e) U'.2)
    hdomA hdome' hd1).symm ?_
  refine Eq.trans (mapHomOfTop_congr _ _ hcomp.symm hd1 hd2) ?_
  exact mapHomOfTop_comp
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).grading U.toOpens)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U.toOpens)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).grading U'.toOpens)
    (chartGradedHom E L hqcE hqcEL e U.2)
    ((Stacks.SymGraded.schemeSheafGradedAlgebra (tensorObj E L) hqcEL).res h)
    (irrelevant_le_map_chartGradedHom E L hqcE hqcEL e U.2) hresB hdome hdomB hd2

end NaturalitySite

end Stacks.SymTwistChart

end
