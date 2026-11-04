module

public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel

/-!
# Uniqueness of the nonsingular projective model, and its genus

Over a field `F`, a regular proper curve is determined up to isomorphism over `F` by its function
field: two regular proper curves over `F` with `F`-isomorphic function fields are isomorphic over
`F`. This is the uniqueness half of [Stacks, Tag 0BY1], read off the equivalences of categories
that tag supplies: the function-field functor of [Stacks, Tag 0BXN] is fully faithful, so the
isomorphism of function fields is an isomorphism of curves in the category of curves and dominant
rational maps, and the functor from normal projective curves and nonconstant morphisms to that
category is fully faithful ([Stacks, Tag 0BXZ]), so it comes from an isomorphism of schemes over
`F`. A regular curve is normal, and a proper curve is projective.

Consequently the genus of a nonsingular projective model of a curve does not depend on the model.

## Main results

* `AlgebraicGeometry.exists_iso_of_functionFieldEquiv`: regular proper curves over `F` with
  `F`-isomorphic function fields are isomorphic over `F`.
* `AlgebraicGeometry.genus_eq_of_functionFieldEquiv`: such curves have the same genus.
* `AlgebraicGeometry.NonsingularProjectiveModel.genus_eq`: any two nonsingular projective models
  of a curve have the same genus.

## References

* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Uniqueness of the nonsingular projective model.** Two regular proper curves over a field
`F` whose function fields are `F`-isomorphic are isomorphic over `F`. -/
theorem exists_iso_of_functionFieldEquiv (F : Type u) [Field F] {Y Y' : Scheme.{u}}
    (s : Y ⟶ Spec (.of F)) (s' : Y' ⟶ Spec (.of F)) [IsCurve F s] [IsCurve F s']
    [IsProper s] [IsProper s'] (hY : IsRegular Y) (hY' : IsRegular Y')
    (e : letI := functionFieldAlgebra F s; letI := functionFieldAlgebra F s'
      Y.functionField ≃ₐ[F] Y'.functionField) :
    ∃ φ : Y ≅ Y', φ.hom ≫ s' = s := by
  let C : NormalProjectiveCurve F := ⟨⟨Over.mk s⟩,
    isRegularProjectiveCurve_le_isNormalProjectiveCurve F _
      ⟨inferInstanceAs (IsCurve F s), isProjectiveMorphism_of_isProper_of_isCurve F s, hY⟩⟩
  let C' : NormalProjectiveCurve F := ⟨⟨Over.mk s'⟩,
    isRegularProjectiveCurve_le_isNormalProjectiveCurve F _
      ⟨inferInstanceAs (IsCurve F s'), isProjectiveMorphism_of_isProper_of_isCurve F s',
        hY'⟩⟩
  let V := ((normalProjectiveCurveToCurve F).obj C).obj
  let V' := ((normalProjectiveCurveToCurve F).obj C').obj
  have hV : varietyFunctionFieldAlgebra V = functionFieldAlgebra F s :=
    varietyFunctionFieldAlgebra_eq_germToFunctionField V
  have hV' : varietyFunctionFieldAlgebra V' = functionFieldAlgebra F s' :=
    varietyFunctionFieldAlgebra_eq_germToFunctionField V'
  let e' : V.toScheme.functionField ≃ₐ[F] V'.toScheme.functionField := by
    let := functionFieldAlgebra F s
    let := functionFieldAlgebra F s'
    refine AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun a => ?_
    have h1 : (varietyFunctionFieldAlgebra V).algebraMap a =
        (functionFieldAlgebra F s).algebraMap a := by rw [hV]; rfl
    have h2 : (varietyFunctionFieldAlgebra V').algebraMap a =
        (functionFieldAlgebra F s').algebraMap a := by rw [hV']; rfl
    exact (congrArg e h1).trans ((e.commutes a).trans h2.symm)
  let α : functionFieldObject V' ≅ functionFieldObject V :=
    ObjectProperty.isoMk _ (CommAlgCat.isoMk e'.symm)
  let β : V ≅ V' := (functionFieldFunctor F).preimageIso α.op
  let γ : (normalProjectiveCurveToCurve F).obj C ≅ (normalProjectiveCurveToCurve F).obj C' :=
    (ObjectProperty.fullyFaithfulι _).preimageIso β
  let δ : C ≅ C' := (normalProjectiveCurveToCurveFullyFaithful F).preimageIso γ
  let φ : Y ≅ Y' := (ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _ ⋙ Over.forget _).mapIso δ
  exact ⟨φ, Over.w δ.hom.hom.hom⟩

/-- Two regular proper curves over a field `F` whose function fields are `F`-isomorphic have the
same genus. -/
theorem genus_eq_of_functionFieldEquiv (F : Type u) [Field F] {Y Y' : Scheme.{u}}
    (s : Y ⟶ Spec (.of F)) (s' : Y' ⟶ Spec (.of F)) [IsCurve F s] [IsCurve F s']
    [IsProper s] [IsProper s'] (hY : IsRegular Y) (hY' : IsRegular Y')
    (e : letI := functionFieldAlgebra F s; letI := functionFieldAlgebra F s'
      Y.functionField ≃ₐ[F] Y'.functionField) :
    genus s = genus s' := by
  obtain ⟨φ, hφ⟩ := exists_iso_of_functionFieldEquiv F s s' hY hY' e
  rw [← hφ, genus_comp_iso_eq]

/-- The structure morphism of a nonsingular projective model is proper. -/
theorem NonsingularProjectiveModel.isProper_structureMap {F : Type u} [Field F]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of F)} [IsCurve F sX]
    (M : NonsingularProjectiveModel F X sX) : IsProper M.structureMap :=
  isProper_of_isProjectiveMorphism _ M.isProjectiveVariety.isProjective

/-- **The genus of a nonsingular projective model does not depend on the model.** Any two
nonsingular projective models of a curve over a field `F` have the same genus: their function
fields are both `F`-isomorphic to that of the curve. -/
theorem NonsingularProjectiveModel.genus_eq {F : Type u} [Field F] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of F)} [IsCurve F sX] (M M' : NonsingularProjectiveModel F X sX) :
    genus M.structureMap = genus M'.structureMap := by
  let := M.isCurve
  let := M'.isCurve
  let := M.isProper_structureMap
  let := M'.isProper_structureMap
  let := functionFieldAlgebra F sX
  let := functionFieldAlgebra F M.structureMap
  let := functionFieldAlgebra F M'.structureMap
  exact genus_eq_of_functionFieldEquiv F _ _ M.isRegular M'.isRegular
    (M.functionFieldEquiv.symm.trans M'.functionFieldEquiv)

end AlgebraicGeometry

end
