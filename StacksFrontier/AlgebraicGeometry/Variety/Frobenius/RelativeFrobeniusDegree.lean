module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FunctionFieldDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.GenericDegreeEquality
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedGenericPoints
public import StacksFrontier.RingTheory.FormallySmooth.Field

/-!
# The degree of the relative Frobenius of a variety

Let `X` be a variety of dimension `d` over a field `k` of characteristic `p > 0` whose Frobenius
twist is reduced. Then the relative Frobenius `F_{X/k} : X ⟶ X^{(p)}` has degree `p ^ d`.

## Main results

* `AlgebraicGeometry.residueDegree_relativeFrobenius_genericPoint` — the residue degree of the
  relative Frobenius at the generic point is `p ^ d`.
* `AlgebraicGeometry.degreeOver_relativeFrobenius` — the degree of `X` over its Frobenius twist,
  in the sense of Stacks Tag 02NY, is `p ^ d`.

## References

* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The residue field at a point of a scheme locally of finite type over a field is essentially
of finite type over that field. -/
private theorem essFiniteType_residueField {k : Type u} [Field k] {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.EssFiniteType k (X.residueField x) := by
  let _ : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let φ₁ : k →+* (Spec (.of k)).residueField (pX x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (pX x)).hom
  let φ₂ : (Spec (.of k)).residueField (pX x) →+* X.residueField x :=
    (pX.residueFieldMap x).hom
  have h₁ : φ₁.EssFiniteType :=
    (RingHom.FiniteType.of_surjective φ₁ (spec_field_evaluation_surjective (pX x))).essFiniteType
  have h₂ : φ₂.EssFiniteType :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap pX x)
  have he : ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (pX x)) ≫
      pX.residueFieldMap x = (Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x := by
    rw [Category.assoc, Scheme.Γevaluation_naturality]
  have hcomp : φ₂.comp φ₁ = algebraMap k (X.residueField x) := congrArg CommRingCat.Hom.hom he
  exact RingHom.essFiniteType_algebraMap.mp (hcomp ▸ RingHom.EssFiniteType.comp h₁ h₂)

/-- For a geometrically reduced integral scheme over a field, the residue field at the generic
point is formally smooth over the base field. -/
@[ega "0 21.5.1" "more general", ega "IV 4.6.12" "(a), special case"]
private theorem formallySmooth_residueField_genericPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [IsIntegral X] (hgeom : GeometricallyReduced pX) :
    letI : Algebra k (X.residueField (genericPoint X)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫
        X.Γevaluation (genericPoint X)).hom.toAlgebra
    Algebra.FormallySmooth k (X.residueField (genericPoint X)) := by
  let _ : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let _ : Algebra k X.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.germToFunctionField ⊤).hom.toAlgebra
  have _ : Algebra.FormallySmooth k X.functionField :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k X.functionField).mpr
      ((geometricallyReduced_iff_isSeparableExtension_functionField pX).mp hgeom)
  exact Algebra.FormallySmooth.of_equiv
    (AlgEquiv.ofRingEquiv (f := genericResidueEquiv X) (fun _ => rfl))

/-- **Stacks Project, Tag 0CCF.** For a geometrically reduced integral scheme of dimension `d`,
locally of finite type over a field `k` of characteristic `p`, the residue degree of the
relative Frobenius at the generic point is `p ^ d`. -/
@[stacks 0CCF "frobenius_degree, as the residue degree at the generic point"]
theorem residueDegree_relativeFrobenius_genericPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsIntegral X] [LocallyOfFiniteType pX]
    (hS : IsInCharacteristic (Spec (.of k)) p) (hgeom : GeometricallyReduced pX)
    (d : ℕ) (hd : topologicalKrullDim X = d) :
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left.residueDegree (genericPoint X) =
      p ^ d := by
  classical
  let η := genericPoint X
  let _ : Algebra k (X.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom.toAlgebra
  have _ : CharP (X.residueField η) p := charP_residueField_of_over p pX η
  have _ : Algebra.EssFiniteType k (X.residueField η) := essFiniteType_residueField pX η
  have _ : Algebra.FormallySmooth k (X.residueField η) :=
    formallySmooth_residueField_genericPoint pX hgeom
  have htr : Cardinal.toNat (Algebra.trdeg k (X.residueField η)) = d := by
    have hdim := topologicalKrullDim_eq_trdeg_residueField k X pX η (genericPoint_spec X)
    rw [hd] at hdim
    have hdim' : (d : ℕ∞) = Cardinal.toENat (Algebra.trdeg k (X.residueField η)) := by
      exact_mod_cast hdim
    simpa only [ENat.toNat_natCast, Cardinal.toNat_toENat] using (congrArg ENat.toNat hdim').symm
  have hcomp : Module.finrank (compositumFrobenius k (X.residueField η) p) (X.residueField η) =
      p ^ d := by
    rw [finrank_compositumFrobenius_eq_pow_trdeg p, htr]
  rw [residueDegree_eq_finrank_fieldRange, fieldRange_residueFieldMap_relativeFrobenius]
  exact hcomp

/-- The residue degree of a dominant morphism of integral schemes at the generic point is its
degree in the sense of Stacks Tag 02NY, the degree of the extension of function fields. -/
theorem residueDegree_genericPoint_eq_degreeOver {Z T : Scheme.{u}} (h : Z ⟶ T)
    [IsIntegral Z] [IsIntegral T] [LocallyOfFiniteType h] [IsDominant h] :
    h.residueDegree (genericPoint Z) = degreeOver h := by
  have hff : functionFieldMap h = dominantFunctionFieldMap h :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target h (genericPoint Z) (map_genericPoint_of_isDominant h))).symm
  let _ : Algebra T.functionField Z.functionField := (functionFieldMap h).toAlgebra
  let _ : Algebra (T.residueField (h.base (genericPoint Z))) (Z.residueField (genericPoint Z)) :=
    (h.residueFieldMap (genericPoint Z)).hom.toAlgebra
  rw [degreeOver_eq_finrank h hff]
  exact (Algebra.finrank_eq_of_equiv_equiv (genericResidueEquivOfDominant h)
    (genericResidueEquiv Z) (residueFieldMap_comp_genericResidueEquivOfDominant h).symm).symm

/-- **Stacks Project, Tag 0CCF.** For a variety `X` of dimension `d` over a field `k` of
characteristic `p` whose Frobenius twist is reduced, the relative Frobenius of `X` has degree
`p ^ d` over the twist. -/
@[stacks 0CCF "frobenius_degree"]
theorem degreeOver_relativeFrobenius
    {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsVariety k pX]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p)
    (hred : IsReduced (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left))
    (d : ℕ) (hd : topologicalKrullDim X = d) :
    letI : LocallyOfFiniteType (Over.mk pX).hom := inferInstanceAs (LocallyOfFiniteType pX)
    letI : IsVariety k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
      isVariety_frobeniusTwist_of_isReduced pX p hred
    degreeOver (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left = p ^ d := by
  let : LocallyOfFiniteType (Over.mk pX).hom := inferInstanceAs (LocallyOfFiniteType pX)
  let : IsVariety k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    isVariety_frobeniusTwist_of_isReduced pX p hred
  rw [← residueDegree_genericPoint_eq_degreeOver]
  exact residueDegree_relativeFrobenius_genericPoint pX p hS
    ((geometricallyReduced_iff_isReduced_frobeniusTwist p pX).mpr hred) d hd

end AlgebraicGeometry

end
