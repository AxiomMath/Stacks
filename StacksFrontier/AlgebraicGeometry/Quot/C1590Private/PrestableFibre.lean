module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.GlobalFunctionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.NodalOverField
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties

/-!
# The fibres of a prestable family of curves

Let `X ⟶ S` be a prestable family of curves (Stacks 0E6T) and `P : Spec K ⟶ S` a field-valued
point. A scheme `V` presenting the fibre of `X` at `P` is a proper curve over `K`: it has dimension
one, at-worst-nodal singularities and `H⁰(V, 𝒪_V) = K`. These are the hypotheses of Stacks 0E7Q
on the fibre, apart from the genus.

## Main results

* `AlgebraicGeometry.C1590Private.isPullback_homMk_of_isPullback`: a presentation of a fibre as a
  cartesian square of algebraic spaces.
* `AlgebraicGeometry.C1590Private.yonedaEquiv_symm_value`: the presheaf map of a field-valued
  point.
* `AlgebraicGeometry.C1590Private.fibre_properties_of_isPrestableCurveFamily`.

## Implementation notes

The fibre is the family of curves `AlgebraicGeometry.C1590Private.curveFamilyOfIsPullback` over the
point, whose structure morphism is the morphism of schemes `V ⟶ Spec K` read as a morphism of
algebraic spaces. It is prestable, being a base change of `X`. Nodality is read on the identity
chart (Stacks 0C59 over a field,
`AlgebraicGeometry.C1590Private.isAtWorstNodalOfRelativeDimensionOne_iff_of_field`) and
`H⁰(V, 𝒪_V) = K` is the universal bijectivity of global functions at the identity of the point.

## References

* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A presentation of the fibre of a family of curves along a morphism of schemes, as a cartesian
square of algebraic spaces. -/
theorem isPullback_homMk_of_isPullback {X : CurveFamily B hZ} {K V : BigFppfOver B integerBase hZ}
    (t : K ⟶ X.base) (v : V ⟶ K) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map t)) :
    IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v) X.toBase
      (schemeSpaceMap t) :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hV.w) hV

/-- The presheaf map of a field-valued point is the Yoneda image of its morphism of schemes. -/
theorem yonedaEquiv_symm_value {Y : BigFppfOver B integerBase hZ}
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y).obj) :
    yonedaEquiv.symm P.value = yoneda.map (show P.siteObject ⟶ Y from P.value) := by
  ext W f
  rfl

/-- **The fibres of a prestable family of curves.** If `X` is prestable and `V` presents the fibre
of `X` at a field-valued point with field `K`, then `V ⟶ Spec K` is proper, `V` has dimension
one, `H⁰(V, 𝒪_V) = K` and `V` has at-worst-nodal singularities. -/
theorem fibre_properties_of_isPrestableCurveFamily {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value)) :
    let fV : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ Spec (.of P.carrier) :=
      (BigFppfOver.toScheme B integerBase hZ).map v
    IsProper fV ∧ topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫ fV.appTop) ∧
      (letI : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over (Spec (.of P.carrier)) := ⟨fV⟩;
        Stacks.Curves.HasAtWorstNodalSingularities P.carrier
          ((BigFppfOver.toScheme B integerBase hZ).obj V)) := by
  intro fV
  rw [yonedaEquiv_symm_value] at hV
  have h := isPullback_homMk_of_isPullback _ v q hV
  have hXP := CurveFamily.isPrestableCurveFamily_of_hom
    (curveFamilyOfIsPullbackHom X _ _ _ h) hX
  have : IsProper fV := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap h
  have : LocallyOfFinitePresentation fV :=
    X.locallyOfFinitePresentation_toScheme_map_of_isPullback h
  have h1 := HasUniversallyBijectiveGlobalFunctions.bijective_globalFunctionsMap B hZ hXP.2
  rw [curveFamilyOfIsPullback_toBase] at h1
  have hb := bijective_appTop_of_bijective_globalFunctionsMap v h1
  have : IsIso fV.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hb
  have : IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫ fV.appTop) := inferInstance
  have : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj V) :=
    (connectedSpace_of_isIso_globalSections P.carrier fV).toNonempty
  have hn := hXP.1
  rw [curveFamilyOfIsPullback_toBase] at hn
  have hnod : IsAtWorstNodalOfRelativeDimensionOne fV :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget v).1 hn
  obtain ⟨-, hdim, hnodal⟩ :=
    (isAtWorstNodalOfRelativeDimensionOne_iff_of_field P.carrier fV).1 hnod
  exact ⟨inferInstance, hdim, inferInstance, hnodal⟩

end AlgebraicGeometry.C1590Private

end
