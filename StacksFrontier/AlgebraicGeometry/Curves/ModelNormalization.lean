module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ModelGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.HProjective
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField

/-!
# The nonsingular projective model of a proper curve is its normalization

Let `K` be a field and let `Z` be a proper curve over `K`. Its normalization is a regular
projective curve over `K` with the same function field, hence a nonsingular projective model of
`Z`. Applied to the reduction `(X_K)_red` of the base change of a curve `X` over a smaller field
`k`, this identifies a nonsingular projective model of `(X_K)_red` with the normalization of
`X_K`.

## Main definitions

* `AlgebraicGeometry.normalizationModel` is the nonsingular projective model of a proper curve
  given by its normalization.
* `AlgebraicGeometry.normalizationModel'` is the same model, with projectivity proved by another
  route.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_normalizationSchemeOverField`: the normalization of a
  variety over a field has the same dimension as the variety.
* `AlgebraicGeometry.exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange`: a
  nonsingular projective model of `(X_K)_red` whose underlying scheme is the normalization of
  `X_K` over `K`.
* `AlgebraicGeometry.exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange'`:
  Tag 0BY4(1), the same statement with nothing carried.

## Implementation notes

The unprimed declarations obtain the source's step "a proper curve is projective" from
`AlgebraicGeometry.isProjectiveMorphism_of_topologicalKrullDim_le_one`, which assumes nothing.

The primed declarations — `normalizationModel'` and
`exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange'`, which is where Tag
0BY4(1) is registered — assume nothing. The source's step "a proper curve is projective" is
applied to a *normalization*, which is an integral scheme of dimension one, and in that
generality [Stacks, Tag 0A25] holds outright from [Stacks, Tag 09ND], as
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`; properness then upgrades
H-quasi-projectivity to H-projectivity, which is [Stacks, Tag 0BCL],
`AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`. The library's
general Tag 0A26 does not assume [Stacks, Tag 09NZ] either; it is
`Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one`
in `StacksFrontier/AlgebraicGeometry/HQuasiProjectiveDimensionOne/Basic.lean`.

That the normalization is one-dimensional is read off the dimension formula for a dominant
morphism of integral schemes, `topologicalKrullDim_eq_add_trdeg_of_isClosedMap` (Tag 02JX): the
normalization morphism is finite, hence closed, and birational (Tag 0BXC), so the induced
extension of function fields is an isomorphism and contributes transcendence degree zero. The
same isomorphism of function fields, which is a `K`-algebra isomorphism because the germ
description of `AlgebraicGeometry.Scheme.Hom.functionFieldMap` is compatible with the structure
morphisms, is the comparison datum of the model.

The normalization of `X_K` and the normalization of `(X_K)_red` are identified by
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction` (Tag 035O), so the model
built from the latter is the normalization of the former; that identification is part of the
conclusion of Tag 0BY4(1).

## References

* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
* [Stacks Project, Tag 02JX](https://stacks.math.columbia.edu/tag/02JX)
* [Stacks Project, Tag 0BX2](https://stacks.math.columbia.edu/tag/0BX2)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Normalization

variable (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsVariety K sZ]

/-- The normalization morphism of a variety over a field induces an isomorphism of function
fields: it is birational, so its stalk map at the generic point is an isomorphism. -/
public theorem isIso_functionFieldMap_normalizationOverField
    [IsVariety K (normalizationOverField K sZ ≫ sZ)]
    [IsDominant (normalizationOverField K sZ)] :
    IsIso (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)) := by
  have hbir : IsBirational (normalizationOverField K sZ) :=
    Scheme.isBirational_normalization Z (finite_irreducibleComponents_of_locallyOfFiniteType K sZ)
  have hgen : genericPoint (normalizationSchemeOverField K sZ) ∈
      genericPoints (normalizationSchemeOverField K sZ) := by
    rw [genericPoints_eq_singleton]
    rfl
  have : IsIso ((normalizationOverField K sZ).stalkMap
      (genericPoint (normalizationSchemeOverField K sZ))) :=
    hbir.isIso_stalkMap _ hgen
  have hspec : Z.presheaf.stalkSpecializes
      (specializes_genericPoint_of_isDominant (normalizationOverField K sZ)) =
      (Z.presheaf.stalkCongr (Inseparable.of_eq
        (genericPoint_eq_of_isDominant (normalizationOverField K sZ)).symm)).hom := rfl
  rw [Scheme.Hom.functionFieldMap, hspec]
  infer_instance

/-- The normalization of a variety over a field has the same dimension as the variety: the
normalization morphism is finite, hence closed, and induces an isomorphism of function fields, so
the dimension formula for a dominant morphism contributes no transcendence degree. -/
public theorem topologicalKrullDim_normalizationSchemeOverField :
    topologicalKrullDim (normalizationSchemeOverField K sZ) = topologicalKrullDim Z := by
  have hV : IsVariety K (normalizationOverField K sZ ≫ sZ) :=
    isVariety_normalizationOverField K sZ
  have : IsIntegral (normalizationSchemeOverField K sZ) := hV.toIsIntegral
  have : IsDominant (normalizationOverField K sZ) := isDominant_normalizationOverField K sZ
  have : IsFinite (normalizationOverField K sZ) := isFinite_normalizationOverField K sZ
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let _ : Algebra Z.functionField (normalizationSchemeOverField K sZ).functionField :=
    (functionFieldMap (normalizationOverField K sZ)).toAlgebra
  have : IsIso (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)) :=
    isIso_functionFieldMap_normalizationOverField K sZ
  have hbij : Function.Bijective
      (algebraMap Z.functionField (normalizationSchemeOverField K sZ).functionField) :=
    ConcreteCategory.bijective_of_isIso
      (Scheme.Hom.functionFieldMap (normalizationOverField K sZ))
  have : Algebra.IsAlgebraic Z.functionField
      (normalizationSchemeOverField K sZ).functionField := ⟨fun a => by
    obtain ⟨r, rfl⟩ := hbij.surjective a
    exact isAlgebraic_algebraMap r⟩
  rw [topologicalKrullDim_eq_add_trdeg_of_isClosedMap (normalizationOverField K sZ)
    (Scheme.Hom.isClosedMap (normalizationOverField K sZ)), trdeg_eq_zero]
  simp

end Normalization

/-- The isomorphism of function fields induced by the normalization morphism of a curve over a
field is one of `K`-algebras: the germ description of the map of function fields is compatible
with the structure morphisms. -/
public theorem functionFieldMap_normalizationOverField_algebraMap
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsCurve K (normalizationOverField K sZ ≫ sZ)]
    [IsDominant (normalizationOverField K sZ)] (a : K) :
    letI : Algebra K Z.functionField := functionFieldAlgebra K sZ
    letI : Algebra K (normalizationSchemeOverField K sZ).functionField :=
      functionFieldAlgebra K (normalizationOverField K sZ ≫ sZ)
    (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)).hom
        (algebraMap K Z.functionField a) =
      algebraMap K (normalizationSchemeOverField K sZ).functionField a := by
  let _ : Algebra K Z.functionField := functionFieldAlgebra K sZ
  let _ : Algebra K (normalizationSchemeOverField K sZ).functionField :=
    functionFieldAlgebra K (normalizationOverField K sZ ≫ sZ)
  let _ : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  let _ : Nonempty (⊤ : (normalizationSchemeOverField K sZ).Opens) :=
    ⟨⟨genericPoint (normalizationSchemeOverField K sZ), trivial⟩⟩
  have hle : (⊤ : (normalizationSchemeOverField K sZ).Opens) ≤
      normalizationOverField K sZ ⁻¹ᵁ (⊤ : Z.Opens) := by simp
  change (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)).hom
      ((Z.germToFunctionField ⊤).hom
        ((sZ.appTop).hom (((Scheme.ΓSpecIso (.of K)).inv).hom a))) = _
  rw [Scheme.Hom.functionFieldMap_germToFunctionField (normalizationOverField K sZ) hle]
  change _ = ((normalizationSchemeOverField K sZ).germToFunctionField ⊤).hom
      (((normalizationOverField K sZ ≫ sZ).appTop).hom
        (((Scheme.ΓSpecIso (.of K)).inv).hom a))
  have happ : (normalizationOverField K sZ).appLE ⊤ ⊤ hle =
      (normalizationOverField K sZ).appTop := by
    rw [Scheme.Hom.appLE,
      show (homOfLE hle) = 𝟙 (⊤ : (normalizationSchemeOverField K sZ).Opens) from
        Subsingleton.elim _ _]
    simp only [Opens.map_top, op_id, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [Scheme.Hom.comp_appTop]
  exact congrArg _ (congrFun (congrArg _ (congrArg CommRingCat.Hom.hom happ)) _)

/-- **The nonsingular projective model of a proper curve, as its normalization.** The
normalization of a proper curve `Z` over a field `K` is normal and proper over `K`, of the same
dimension, hence a regular projective curve with the same function field as `Z`, that is a
nonsingular projective model of `Z`. -/
public def normalizationModel
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsProper sZ] :
    NonsingularProjectiveModel K Z sZ := by
  let hV : IsVariety K (normalizationOverField K sZ ≫ sZ) :=
    isVariety_normalizationOverField K sZ
  let _ : IsIntegral (normalizationSchemeOverField K sZ) := hV.toIsIntegral
  let _ : LocallyOfFiniteType (normalizationOverField K sZ ≫ sZ) := hV.toLocallyOfFiniteType
  let _ : IsDominant (normalizationOverField K sZ) := isDominant_normalizationOverField K sZ
  let _ : IsProper (normalizationOverField K sZ ≫ sZ) :=
    isProper_normalizationOverField_comp K sZ
  let _ : IsNormal (normalizationSchemeOverField K sZ) :=
    Scheme.isNormal_normalizationScheme Z
      (finite_irreducibleComponents_of_locallyOfFiniteType K sZ)
  have hdim : topologicalKrullDim (normalizationSchemeOverField K sZ) = 1 :=
    (topologicalKrullDim_normalizationSchemeOverField K sZ).trans
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := sZ))
  let hC : IsCurve K (normalizationOverField K sZ ≫ sZ) :=
    { topologicalKrullDim_eq_one := hdim }
  let _ : IsLocallyNoetherian (normalizationSchemeOverField K sZ) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField K sZ ≫ sZ)
  let _ : IsProjectiveVariety K (normalizationOverField K sZ ≫ sZ) :=
    { isProjective := isProjectiveMorphism_of_topologicalKrullDim_le_one
        (normalizationOverField K sZ ≫ sZ) (le_of_eq hdim) }
  let _ : Algebra K Z.functionField := functionFieldAlgebra K sZ
  let _ : Algebra K (normalizationSchemeOverField K sZ).functionField :=
    functionFieldAlgebra K (normalizationOverField K sZ ≫ sZ)
  let _ : IsIso (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)) :=
    isIso_functionFieldMap_normalizationOverField K sZ
  exact
    { Y := normalizationSchemeOverField K sZ
      structureMap := normalizationOverField K sZ ≫ sZ
      isCurve := hC
      isProjectiveVariety := inferInstance
      isRegular := isRegular_of_isNormal_of_topologicalKrullDim_le_one
        (normalizationSchemeOverField K sZ) (le_of_eq hdim)
      functionFieldEquiv :=
        { RingEquiv.ofBijective
            (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)).hom
            (ConcreteCategory.bijective_of_isIso
              (Scheme.Hom.functionFieldMap (normalizationOverField K sZ))) with
          commutes' := functionFieldMap_normalizationOverField_algebraMap K sZ } }

/-- **The nonsingular projective model of a proper curve, as its normalization, with nothing
carried.** This is `AlgebraicGeometry.normalizationModel`, built another way.

The step "a proper curve is projective" is applied to the normalization, which is integral of
dimension one, and there [Stacks, Tag 0A25] is
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`; properness upgrades
H-quasi-projectivity to H-projectivity by [Stacks, Tag 0BCL],
`AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`. So
[Stacks, Tag 09NZ] is not needed. -/
public def normalizationModel'
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsProper sZ] :
    NonsingularProjectiveModel K Z sZ := by
  let hV : IsVariety K (normalizationOverField K sZ ≫ sZ) :=
    isVariety_normalizationOverField K sZ
  let _ : IsIntegral (normalizationSchemeOverField K sZ) := hV.toIsIntegral
  let _ : LocallyOfFiniteType (normalizationOverField K sZ ≫ sZ) := hV.toLocallyOfFiniteType
  let _ : IsDominant (normalizationOverField K sZ) := isDominant_normalizationOverField K sZ
  let _ : IsProper (normalizationOverField K sZ ≫ sZ) :=
    isProper_normalizationOverField_comp K sZ
  let _ : IsNormal (normalizationSchemeOverField K sZ) :=
    Scheme.isNormal_normalizationScheme Z
      (finite_irreducibleComponents_of_locallyOfFiniteType K sZ)
  have hdim : topologicalKrullDim (normalizationSchemeOverField K sZ) = 1 :=
    (topologicalKrullDim_normalizationSchemeOverField K sZ).trans
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := sZ))
  let hC : IsCurve K (normalizationOverField K sZ ≫ sZ) :=
    { topologicalKrullDim_eq_one := hdim }
  let _ : IsLocallyNoetherian (normalizationSchemeOverField K sZ) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField K sZ ≫ sZ)
  let _ : IsProjectiveVariety K (normalizationOverField K sZ ≫ sZ) :=
    { isProjective := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper
        (f := normalizationOverField K sZ ≫ sZ)).mpr
        ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral
          (normalizationOverField K sZ ≫ sZ) hdim, inferInstance⟩ }
  let _ : Algebra K Z.functionField := functionFieldAlgebra K sZ
  let _ : Algebra K (normalizationSchemeOverField K sZ).functionField :=
    functionFieldAlgebra K (normalizationOverField K sZ ≫ sZ)
  let _ : IsIso (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)) :=
    isIso_functionFieldMap_normalizationOverField K sZ
  exact
    { Y := normalizationSchemeOverField K sZ
      structureMap := normalizationOverField K sZ ≫ sZ
      isCurve := hC
      isProjectiveVariety := inferInstance
      isRegular := isRegular_of_isNormal_of_topologicalKrullDim_le_one
        (normalizationSchemeOverField K sZ) (le_of_eq hdim)
      functionFieldEquiv :=
        { RingEquiv.ofBijective
            (Scheme.Hom.functionFieldMap (normalizationOverField K sZ)).hom
            (ConcreteCategory.bijective_of_isIso
              (Scheme.Hom.functionFieldMap (normalizationOverField K sZ))) with
          commutes' := functionFieldMap_normalizationOverField_algebraMap K sZ } }

/-- The scheme underlying `AlgebraicGeometry.normalizationModel` is the normalization. -/
@[simp]
public theorem normalizationModel_Y
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsProper sZ] :
    (normalizationModel K sZ).Y = normalizationSchemeOverField K sZ := rfl

/-- The scheme underlying `AlgebraicGeometry.normalizationModel'` is the normalization. -/
@[simp]
public theorem normalizationModel'_Y
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsProper sZ] :
    (normalizationModel' K sZ).Y = normalizationSchemeOverField K sZ := rfl

/-- The structure morphism of `AlgebraicGeometry.normalizationModel` is the normalization
morphism followed by the structure morphism. -/
@[simp]
public theorem normalizationModel_structureMap
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsProper sZ] :
    (normalizationModel K sZ).structureMap = normalizationOverField K sZ ≫ sZ := rfl

/-- The structure morphism of `AlgebraicGeometry.normalizationModel'` is the normalization
morphism followed by the structure morphism. -/
@[simp]
public theorem normalizationModel'_structureMap
    (K : Type u) [Field K] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ]
    [IsProper sZ] :
    (normalizationModel' K sZ).structureMap = normalizationOverField K sZ ≫ sZ := rfl

/-- The reduction of the base change of a proper geometrically irreducible curve along a field
extension is a curve over the larger field: it is reduced by construction, irreducible because
the base change is geometrically irreducible over a one-point base, and of dimension one because
extension of the ground field of a proper scheme preserves dimension. -/
public instance isCurve_reducedBaseChangeStructureMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX] [IsProper sX] :
    IsCurve K (reducedBaseChangeStructureMap k K sX) := by
  have hPi : IsProper
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι := inferInstance
  have hPp : IsProper
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hP : IsProper (reducedBaseChangeStructureMap k K sX) := inferInstance
  have hL : LocallyOfFiniteType (reducedBaseChangeStructureMap k K sX) :=
    IsProper.toLocallyOfFiniteType
  have hQi : QuasiCompact
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι := inferInstance
  have hQp : QuasiCompact
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hQ : QuasiCompact (reducedBaseChangeStructureMap k K sX) := inferInstance
  have hS : IsSeparated (reducedBaseChangeStructureMap k K sX) := IsProper.toIsSeparated
  let _ : IrreducibleSpace (reducedBaseChange k K sX) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (reducedBaseChangeStructureMap k K sX)
  let _ : IsIntegral (reducedBaseChange k K sX) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hhomeo : IsHomeomorph
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    (inferInstance : UniversalHomeomorphism
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι)
      |>.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hdim : topologicalKrullDim (reducedBaseChange k K sX) = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hhomeo,
      topologicalKrullDim_baseChange k K
        (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) sX
        (IsPullback.of_hasPullback _ _)]
    exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := sX)
  exact { topologicalKrullDim_eq_one := hdim }

/-- The reduction of the base change of a geometrically irreducible curve along a field
extension is a curve over the larger field: it is reduced by construction, irreducible because
the base change is geometrically irreducible over a one-point base, and of dimension one because
extension of the ground field of a scheme locally of finite type preserves dimension.

This is `AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap` with properness of `sX` not
assumed. Separatedness, finite type and quasi-compactness of the structure morphism come from
the two factors it is composed of: the reduction morphism is a closed immersion, hence proper,
and the projection is the base change of `sX`. -/
public instance isCurve_reducedBaseChangeStructureMap'
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX] :
    IsCurve K (reducedBaseChangeStructureMap k K sX) := by
  have hPi : IsProper
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι := inferInstance
  have hLi : LocallyOfFiniteType
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    IsProper.toLocallyOfFiniteType
  have hSi : IsSeparated
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    IsProper.toIsSeparated
  have hLp : LocallyOfFiniteType
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hSp : IsSeparated
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hL : LocallyOfFiniteType (reducedBaseChangeStructureMap k K sX) := inferInstance
  have hQi : QuasiCompact
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι := inferInstance
  have hQp : QuasiCompact
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hQ : QuasiCompact (reducedBaseChangeStructureMap k K sX) := inferInstance
  have hS : IsSeparated (reducedBaseChangeStructureMap k K sX) := inferInstance
  have : IrreducibleSpace (reducedBaseChange k K sX) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (reducedBaseChangeStructureMap k K sX)
  have : IsIntegral (reducedBaseChange k K sX) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have hhomeo : IsHomeomorph
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    (inferInstance : UniversalHomeomorphism
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι)
      |>.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hdim : topologicalKrullDim (reducedBaseChange k K sX) = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hhomeo,
      topologicalKrullDim_baseChange k K
        (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) sX
        (IsPullback.of_hasPullback _ _)]
    exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := sX)
  exact { topologicalKrullDim_eq_one := hdim }

/-- The normalization of the base change `X_K` is isomorphic to that of `(X_K)_red`, compatibly
with the maps to `X_K`. -/
private theorem exists_iso_normalization_reducedBaseChange_aux
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX] [IsProper sX]
    [LocallyOfFiniteType (reducedBaseChangeStructureMap k K sX)] :
    ∃ e : normalizationSchemeOverField K
        (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≅
          normalizationSchemeOverField K (reducedBaseChangeStructureMap k K sX),
      normalizationOverField K
          (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
        pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          e.hom ≫ normalizationOverField K (reducedBaseChangeStructureMap k K sX) ≫
            reducedBaseChangeStructureMap k K sX := by
  obtain ⟨e, he⟩ := Scheme.exists_normalizationScheme_iso_reduction
    (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (finite_irreducibleComponents_of_locallyOfFiniteType K
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  refine ⟨e, ?_⟩
  have h1 : normalizationOverField K
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      e.hom ≫ normalizationOverField K (reducedBaseChangeStructureMap k K sX) ≫
        (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    he.symm
  rw [h1]
  simp only [reducedBaseChangeStructureMap]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun φ => e.hom ≫ φ) (Category.assoc _ _ _))

/-- **Stacks Project, Tag 0BY4, part (1).** Let `k` be a field, let `X` be a proper
geometrically irreducible curve over `k` and let `K/k` be a field extension. Then `(X_K)_red` has
a nonsingular projective model whose underlying scheme is the normalization of `X_K` over `K`. -/
public theorem exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX] [IsProper sX] :
    ∃ M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
        (reducedBaseChangeStructureMap k K sX),
      ∃ e : normalizationSchemeOverField K
          (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≅ M.Y,
        normalizationOverField K
            (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
          pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
            e.hom ≫ M.structureMap := by
  have hPi : IsProper
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι := inferInstance
  have hPp : IsProper
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hP : IsProper (reducedBaseChangeStructureMap k K sX) := inferInstance
  have hL : LocallyOfFiniteType (reducedBaseChangeStructureMap k K sX) :=
    IsProper.toLocallyOfFiniteType
  refine ⟨normalizationModel K (reducedBaseChangeStructureMap k K sX), ?_⟩
  rw [normalizationModel_structureMap]
  exact exists_iso_normalization_reducedBaseChange_aux k K sX

/-- **Stacks Project, Tag 0BY4, part (1).** Let `k` be a field, let `X` be a proper
geometrically irreducible curve over `k` and let `K/k` be a field extension. Then `(X_K)_red` has
a nonsingular projective model whose underlying scheme is the normalization of `X_K` over `K`.

Nothing is carried: the model is `AlgebraicGeometry.normalizationModel'`, whose projectivity is
the step "a proper curve is projective" applied to a normalization. This is
`AlgebraicGeometry.exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange`, proved
another way. -/
@[stacks 0BY4 "part (1), with nothing carried: the source's step `a proper curve is projective` \
is applied to a normalization, which is integral of dimension one, so Tag 0A25 holds outright as \
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral` and Tag 09NZ is not \
needed"]
public theorem exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange'
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX] [IsProper sX] :
    ∃ M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
        (reducedBaseChangeStructureMap k K sX),
      ∃ e : normalizationSchemeOverField K
          (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≅ M.Y,
        normalizationOverField K
            (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
          pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
            e.hom ≫ M.structureMap := by
  have hPi : IsProper
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι := inferInstance
  have hPp : IsProper
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  have hP : IsProper (reducedBaseChangeStructureMap k K sX) := inferInstance
  have hL : LocallyOfFiniteType (reducedBaseChangeStructureMap k K sX) :=
    IsProper.toLocallyOfFiniteType
  refine ⟨normalizationModel' K (reducedBaseChangeStructureMap k K sX), ?_⟩
  rw [normalizationModel'_structureMap]
  exact exists_iso_normalization_reducedBaseChange_aux k K sX

end AlgebraicGeometry

end
