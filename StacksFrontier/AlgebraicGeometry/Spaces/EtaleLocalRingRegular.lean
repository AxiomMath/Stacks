module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# Regularity of a locally Noetherian algebraic space and its étale local rings

A locally Noetherian algebraic space is regular exactly when all of its étale local rings at
geometric points are regular local rings. Regularity of the space is the étale-local scheme
property `AlgebraicGeometry.IsRegular` asked of a surjective étale scheme atlas, and the étale
local ring at a geometric point is the strict henselization of the ordinary local ring of any
scheme chart through that point; regularity is unchanged on passing to a strict henselization,
so the two conditions are two readings of regularity of the local rings of a chart.

## Main results

* `AlgebraicGeometry.Space.isRegularLocalRing_etaleLocalRing_iff_chart`: the étale local ring
  at a geometric point of a locally Noetherian algebraic space is regular exactly when the
  local ring of a given small étale chart is regular at the point the chart selects.
* `AlgebraicGeometry.Space.isRegular_iff_etaleLocalRings_regular`: a locally Noetherian
  algebraic space is regular exactly when all of its étale local rings are regular.

## References

* [Stacks Project, Tag 06LQ](https://stacks.math.columbia.edu/tag/06LQ)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The spectrum of an algebraic closure of the residue field at a point of a scheme of the
chosen big fppf site lies in that site again: an algebraic extension does not increase
cardinality past the cutoff. -/
private theorem contains_specAlgebraicClosure_residueField {X : Scheme.{u}}
    (hX : B.Contains X) (y : X) :
    B.Contains (Spec (.of (AlgebraicClosure (X.residueField y)))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (B.residueField_spec_contains hX y)
    ((Algebra.IsAlgebraic.cardinalMk_le_max _ _).trans_eq (max_comm _ _))

/-- The scheme underlying an étale chart of an algebraic space over a big fppf site lies in the
big étale site attached to that site: the two have the same size cutoff. -/
private theorem bigEtaleSiteOfFppfSite_contains_chartScheme (U : SmallEtale B S hS F) :
    (bigEtaleSiteOfFppfSite B).Contains (chartScheme U) := by
  change ((BigFppfOver.toScheme B S hS).obj U.obj.left).size < B.cutoff
  exact U.obj.left.left.property

/-- The étale local ring of an algebraic space at a geometric point is a regular local ring exactly
when the local ring of a small étale chart through that point is regular at the point the chart
selects, provided that chart is locally Noetherian. -/
theorem isRegularLocalRing_etaleLocalRing_iff_chart (hF : IsAlgebraicSpace B S hS F)
    {x : GeometricPoint B S hS F} (V : SmallEtaleNeighborhood x)
    (hV : IsLocallyNoetherian (chartScheme V.chart)) :
    IsRegularLocalRing (etaleLocalRing B S hS F x) ↔
      IsRegularLocalRing ((chartScheme V.chart).presheaf.stalk
        ((chartGeometricPoint V).hom
          (closedPoint (chartGeometricPoint V).residueField))) := by
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let κ := separableClosure (ResidueField R) (chartGeometricPoint V).residueField
  let T := henselizationTower R κ
  let e := strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B)
    (bigEtaleSiteOfFppfSite_contains_chartScheme V.chart) T
  have : IsNoetherianRing R := inferInstance
  have hhens : IsRegularLocalRing R ↔ IsRegularLocalRing T.strictHenselization :=
    (isRegularLocalRing_iff_henselizations R T.henselization T.strictHenselization κ).2
  exact ⟨fun _ ↦ hhens.mpr (.of_ringEquiv e.symm), fun h ↦ have := hhens.mp h; .of_ringEquiv e⟩

/-- A locally Noetherian algebraic space is regular exactly when its étale local rings at all
geometric points are regular local rings. -/
@[stacks 06LQ]
theorem isRegular_iff_etaleLocalRings_regular (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (hnoeth : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsLocallyNoetherian X)) :
    HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsRegular X) ↔
      ∀ x : GeometricPoint B S hS F, IsRegularLocalRing (etaleLocalRing B S hS F x) := by
  have hnoethAll := (exists_atlas_iff_forall_etale B S hS F
    (fun X : Scheme.{u} ↦ IsLocallyNoetherian X) hF).mp hnoeth
  have hiff := exists_atlas_iff_forall_etale B S hS F (fun X : Scheme.{u} ↦ IsRegular X) hF
  constructor
  · intro hregular x
    obtain ⟨U, f, hSurj, hEtale⟩ := hF.exists_atlas
    obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF x f hSurj hEtale
    have hVreg := hiff.mp hregular
      ((SmallEtale.toOver B S hS F).obj V.chart) V.chart.obj.hom V.chart.property
    exact (isRegularLocalRing_etaleLocalRing_iff_chart hF V
      (hnoethAll ((SmallEtale.toOver B S hS F).obj V.chart) V.chart.obj.hom V.chart.property)).mpr
      ((((isRegular_tfae (chartScheme V.chart)).out 1 2 rfl rfl).mp hVreg).2 _)
  · intro hall
    refine hiff.mpr fun U f hf ↦ ?_
    have hXnoeth := hnoethAll U f hf
    refine ((isRegular_tfae ((BigFppfOver.toScheme B S hS).obj U)).out 2 1 rfl rfl).mp
      ⟨hXnoeth, fun y ↦ ?_⟩
    let s := GeometricPoint.ofPoint ((BigFppfOver.toScheme B S hS).obj U) y
    have hΩ : B.Contains (Spec (.of s.residueField)) :=
      contains_specAlgebraicClosure_residueField U.left.property y
    let a : B.obj hΩ ⟶ U.left := B.inclusion.preimage s.hom
    let p : FieldValuedPoint B S hS (yoneda.obj U) :=
      { carrier := s.residueField
        contained := hΩ
        toBase := B.inclusion.map (a ≫ U.hom)
        value := Over.homMk a }
    let x : GeometricPoint B S hS F :=
      ⟨FieldValuedPoint.map B S hS (yoneda.obj U) f p, s.isAlgClosed_residueField⟩
    let V : SmallEtaleNeighborhood x :=
      { chart := ⟨CostructuredArrow.mk f, hf⟩
        point := Over.homMk a
        point_comp := rfl }
    have hVlocal :=
      (isRegularLocalRing_etaleLocalRing_iff_chart hF V hXnoeth).mp (hall x)
    have hpoint : (chartGeometricPoint V).hom
        (closedPoint (chartGeometricPoint V).residueField) = y := by
      change (B.inclusion.map a) (closedPoint s.residueField) = y
      rw [B.inclusion.map_preimage,
        Subsingleton.elim (closedPoint s.residueField) (default : s.source)]
      exact GeometricPoint.ofPoint_liesOver ((BigFppfOver.toScheme B S hS).obj U) y
    rwa [hpoint] at hVlocal

end AlgebraicGeometry.Space

end
