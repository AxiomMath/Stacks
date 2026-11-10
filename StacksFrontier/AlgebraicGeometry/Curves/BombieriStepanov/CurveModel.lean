module

public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.FieldToResidue

/-!
# A proper model of a function field of one variable

Let `L` be a finitely generated field extension of transcendence degree one of a field `F`. Then
`L` is the function field of a normal projective curve `M` over `F`, by an isomorphism of
`F`-algebras: this is the composite of the anti-equivalence of Stacks 0BXN (`L` is the function
field of a variety `V`, which is a curve because `L` has transcendence degree one) and of the
essential surjectivity of normal projective curves onto curves in Stacks 0BY1. The local rings
of `M` at its places are discrete valuation rings (Stacks 0BX2).

## Main results

* `Stacks.BombieriStepanov.exists_curve_model`: the model, with the comparison of constants
  `e (c) = (k → 𝒪_{M,η}) (c)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

/-- The structure map of the function field of a variety is the germ of the constants at the
generic point. -/
theorem functionFieldAlgebraMap_eq_fieldToStalk {F : Type u} [Field F] (V : Variety F) (c : F) :
    functionFieldAlgebraMap V c =
      (fieldToStalk V.structureMap (genericPoint V.toScheme)).hom c := by
  rw [DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField V) c]
  rfl

/-- **The proper model of a function field of one variable.** A finitely generated extension
`L/F` of transcendence degree one is, as an `F`-algebra, the function field of a normal proper
curve over `F` whose local rings at its places are discrete valuation rings. -/
theorem exists_curve_model (F : Type u) [Field F] (L : Type u) [Field L] [Algebra F L]
    [Algebra.EssFiniteType F L] (htr : Algebra.trdeg F L = 1) :
    ∃ (M : Scheme.{u}) (p : M ⟶ Spec (.of F)) (_ : IsIntegral M) (_ : IsProper p)
      (_ : IsCurve F p) (_ : IsLocallyNoetherian M)
      (_ : ∀ x : M, coheight x = 1 → IsDiscreteValuationRing (M.presheaf.stalk x))
      (e : L ≃+* M.functionField),
      ∀ c : F, e (algebraMap F L c) = (fieldToStalk p (genericPoint M)).hom c := by
  -- `L` is the function field of a variety `V`
  let K₀ : FinitelyGeneratedFieldExtension F :=
    ⟨CommAlgCat.of F L, ⟨Field.toIsField L, inferInstance⟩⟩
  let V := (functionFieldFunctor F).objPreimage (Opposite.op K₀)
  let i₁ : (functionFieldFunctor F).obj V ≅ Opposite.op K₀ :=
    (functionFieldFunctor F).objObjPreimageIso _
  let e₁ : L ≃ₐ[F] V.toScheme.functionField :=
    CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso i₁.unop)
  have hV : IsCurve F V.structureMap := by
    rw [isCurve_iff_trdeg_functionField_eq_one]
    exact e₁.trdeg_eq ▸ htr
  -- `V` is isomorphic to a normal projective curve `N`
  let C : Curve F := ⟨V, hV⟩
  let N := (normalProjectiveCurveToCurve F).objPreimage C
  let i₂ : (normalProjectiveCurveToCurve F).obj N ≅ C :=
    (normalProjectiveCurveToCurve F).objObjPreimageIso C
  let i₃ := (functionFieldFunctor F).mapIso ((ObjectProperty.ι _).mapIso i₂)
  let e₂ : V.toScheme.functionField ≃ₐ[F]
      ((normalProjectiveCurveToCurve F).obj N).obj.toScheme.functionField :=
    CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso i₃.unop)
  let NV := ((normalProjectiveCurveToCurve F).obj N).obj
  have : IsCurve F NV.structureMap := N.property.1
  have : IsProper NV.structureMap :=
    isProper_of_isProjectiveMorphism NV.structureMap N.property.2.1
  have : IsNormal NV.toScheme := N.property.2.2
  have : IsLocallyNoetherian NV.toScheme := LocallyOfFiniteType.isLocallyNoetherian NV.structureMap
  refine ⟨NV.toScheme, NV.structureMap, inferInstance, inferInstance, inferInstance,
    inferInstance, fun x hx => ?_, (e₁.trans e₂).toRingEquiv, fun c => ?_⟩
  · have hdim := IsCurve.topologicalKrullDim_eq_one (k := F) (f := NV.structureMap)
    have hxg : x ≠ genericPoint NV.toScheme := by
      intro h
      have hmax : IsMax (genericPoint NV.toScheme) := fun y _ => genericPoint_specializes y
      rw [h, Order.coheight_eq_zero.mpr hmax] at hx
      exact zero_ne_one hx
    have hcl := Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
      NV.toScheme hdim hxg
    have hreg := isRegular_of_isNormal_of_topologicalKrullDim_le_one NV.toScheme hdim.le
    have hx' : IsRegularLocalRing (NV.toScheme.presheaf.stalk x) :=
      (((isRegular_tfae NV.toScheme).out 1 2 rfl rfl).mp hreg).2 x
    exact ((isDiscreteValuationRing_stalk_tfae_of_isCurve F NV.structureMap hcl).out 1 3).mp hx'
  · change e₂ (e₁ (algebraMap F L c)) = _
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
    exact functionFieldAlgebraMap_eq_fieldToStalk NV c

end Stacks.BombieriStepanov

end
