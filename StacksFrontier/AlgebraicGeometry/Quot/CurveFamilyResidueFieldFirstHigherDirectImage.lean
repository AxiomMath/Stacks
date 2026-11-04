module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstHigherDirectImageFieldFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldBaseChangeGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGeometricFibresGlobalFunctions

/-!
# Parts (2) and (3) of Stacks 0E1J under `κ(s) = H⁰(X_s, 𝒪_{X_s})`

Let `f : X → S` be a family of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s` of
`S`. A morphism `Spec k → S` from the spectrum of a field factors as
`Spec k → Spec κ(s) → S` for a field extension `k/κ(s)`, and `X_k` is the base change of `X_s`
along it; so `k = H⁰(X_k, 𝒪_{X_k})` by flat base change
(`AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_fieldBaseChange`). Hence
`R¹f_*𝒪_X` is finite locally free and its formation commutes with arbitrary base change, by
the results of `Quot/CurveFamilyFirstHigherDirectImageFieldFibres.lean`.

## Main results

In namespace `AlgebraicGeometry.CurveFamily`:

* `hasBijectiveFieldFibreGlobalFunctions_of_hasResidueFieldGlobalFunctions`: from the residue
  fields to all fields.
* `hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions`: part (2).
* `firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions`: part (3).

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- Two field-valued points of a represented presheaf with the same field are equal once their
underlying morphisms to the representing object agree: the structure map to the base is then
determined. -/
theorem fieldValuedPoint_yoneda_ext {S : Scheme.{u}} {hS : B.Contains S} {U : BigFppfOver B S hS}
    {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} (t₁ t₂ : Spec (.of k) ⟶ S)
    (v₁ : Over.mk (⟨t₁⟩ : B.obj hk ⟶ B.obj hS) ⟶ U) (v₂ : Over.mk (⟨t₂⟩ : B.obj hk ⟶ B.obj hS) ⟶ U)
    (h : v₁.left = v₂.left) :
    (⟨k, hk, t₁, v₁⟩ : Space.FieldValuedPoint B S hS (yoneda.obj U)) = ⟨k, hk, t₂, v₂⟩ := by
  have ht : (⟨t₁⟩ : B.obj hk ⟶ B.obj hS) = ⟨t₂⟩ :=
    calc (⟨t₁⟩ : B.obj hk ⟶ B.obj hS) = v₁.left ≫ U.hom := (Over.w v₁).symm
      _ = v₂.left ≫ U.hom := by rw [h]
      _ = ⟨t₂⟩ := Over.w v₂
  obtain rfl : t₁ = t₂ := congrArg (fun g => g.hom) ht
  obtain rfl : v₁ = v₂ := Over.OverMorphism.ext h
  rfl

/-- **`k = H⁰(X_k, 𝒪)` on every fibre over a field from the residue fields.** If
`κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s` of the base, then `k = H⁰(X_k, 𝒪_{X_k})` for
every morphism `Spec k → S` from the spectrum of a field: it factors through `Spec κ(s)`, and
`X_k` is the base change of `X_s` along the field extension `k/κ(s)`. -/
theorem hasBijectiveFieldFibreGlobalFunctions_of_hasResidueFieldGlobalFunctions
    {X : CurveFamily B hZ} (hX : X.HasResidueFieldGlobalFunctions) :
    Space.HasBijectiveFieldFibreGlobalFunctions B integerBase hZ X.toBase := by
  intro p
  obtain ⟨k, hk, toBase, value⟩ := p
  let T := X.base.left.1
  let φ : Spec (.of k) ⟶ T := value.left.hom
  let s : T := φ.base (IsLocalRing.closedPoint k)
  let σ : T.residueField s ⟶ CommRingCat.of k := T.descResidueField (Scheme.stalkClosedPointTo φ)
  let : Algebra (T.residueField s) k := σ.hom.toAlgebra
  have hs : B.Contains (Spec (.of (T.residueField s))) :=
    B.residueField_spec_contains X.base.left.property s
  let r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).1 :=
    { carrier := T.residueField s
      contained := hs
      toBase := T.fromSpecResidueField s ≫ X.base.hom.1
      value := Space.residueFieldMap B integerBase hZ X.base s hs }
  -- the residue-field point
  have hr : Function.Bijective (algebraMap r.carrier (Space.globalFunctions B
      (Spec (.of r.carrier)) r.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom r))) :=
    Space.bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective B integerBase hZ
      X.toBase.hom r X.total.2 (schemeSpace X.base).2 (hX s)
  -- the given point is the extension of the residue-field point along `k/κ(s)`
  have hp : (⟨k, hk, toBase, value⟩ : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace X.base).1) = r.extend B integerBase hZ k hk :=
    fieldValuedPoint_yoneda_ext _ _ _ _ (ObjectProperty.hom_ext _
      (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k T φ).symm)
  rw [hp]
  have hF := Space.isAlgebraicSpace_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom
    X.total.2 (schemeSpace X.base).2 r
  refine (Space.bijective_algebraMap_globalFunctions_congr B
    (Space.isAlgebraicSpace_fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom
      X.total.2 (schemeSpace X.base).2 _)
    (isAlgebraicSpace_relocalizeRestrict B _ _ hk r.contained _ _ hF)
    (Space.fibreOverFieldValuedPointExtendIso B integerBase hZ X.toBase.hom r k hk)).mpr ?_
  exact Space.bijective_algebraMap_globalFunctions_fieldBaseChange B hF _
    (Space.isProper_restrictedFibre B integerBase hZ X.toBase.hom r.contained _ _ X.total.2
      (schemeSpace X.base).2 X.proper).1
    (Space.isFlat_restrictedFibre B integerBase hZ X.toBase.hom r.contained _ _ X.total.2
      (schemeSpace X.base).2 X.flat)
    (Space.isFinitePresentation_restrictedFibre B integerBase hZ X.toBase.hom r.contained _ _
      X.total.2 (schemeSpace X.base).2 X.finitePresentation) hr k hk

/-- **Part (2) of Stacks 0E1J.** For a family of curves `f : X → S` with
`κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s ∈ S`, `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module. -/
theorem hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions
    {X : CurveFamily B hZ} (hX : X.HasResidueFieldGlobalFunctions) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage :=
  Space.isFiniteLocallyFree_rightDerived_one_structureSheafModule B integerBase hZ X.toBase
    X.proper X.flat X.finitePresentation
    (hasBijectiveFieldFibreGlobalFunctions_of_hasResidueFieldGlobalFunctions hX)
    X.hasVanishingFieldFibreCohomologyAboveOne

/-- **Part (3) of Stacks 0E1J.** For a family of curves `f : X → S` with
`κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s ∈ S`, the formation of `R¹f_*𝒪_X` commutes with arbitrary
base change. -/
theorem firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions
    {X : CurveFamily B hZ} (hX : X.HasResidueFieldGlobalFunctions) :
    X.FirstHigherDirectImageCommutesWithBaseChange := fun F a =>
  Space.nonempty_modulePullback_rightDerived_one_iso B integerBase hZ X.toBase X.proper X.flat
    X.finitePresentation
    (hasBijectiveFieldFibreGlobalFunctions_of_hasResidueFieldGlobalFunctions hX)
    X.hasVanishingFieldFibreCohomologyAboveOne (schemeSpaceMap a.baseMap) F.toBase a.totalMap
    a.cartesian

end CurveFamily

end AlgebraicGeometry

end
