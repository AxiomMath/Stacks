module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelSpecialFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber

/-!
# The fibres of a prestable family of curves

Let `f : X ⟶ S` be a prestable family of curves and `p : Spec k ⟶ S` a field-valued point of its
base. A scheme `V` presenting the fibre `X_p` is a proper scheme over `k` of dimension one with
`H⁰(V, 𝒪_V) = k` and at-worst-nodal singularities: properness and `H⁰ = k` are inherited from the
family, and nodality of `V ⟶ Spec k` is Stacks 0DSF, read on the fibre over the unique point of
`Spec k`. These are the standing hypotheses of Algebraic Curves, Lemma 0E7Q, which Stacks 0E8A
applies to every fibre.

## Main results

* `AlgebraicGeometry.CurveFamily.isPullback_schemeSpace_of_isPullback_yoneda`: a presentation of
  a fibre by a cartesian square of presheaves is a cartesian square of algebraic spaces.
* `AlgebraicGeometry.CurveFamily.fibre_standing_of_isPrestableCurveFamily`: the four standing
  hypotheses of Stacks 0E7Q on a presentation of a fibre of a prestable family.

## References

* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0DSF](https://stacks.math.columbia.edu/tag/0DSF)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A presentation of the fibre of a family of curves over a field-valued point by a cartesian
square of presheaves is a cartesian square of algebraic spaces. -/
theorem isPullback_schemeSpace_of_isPullback_yoneda {X : CurveFamily B hZ}
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value)) :
    IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v) X.toBase
      (schemeSpaceMap p.value) := by
  have hp : yonedaEquiv.symm p.value = yoneda.map p.value :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map p.value).symm
  rw [hp] at hsq
  exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq

/-- **The standing hypotheses of Stacks 0E7Q on the fibres of a prestable family.** If `X ⟶ S`
is a prestable family of curves and `V` presents the fibre of `X` over a field-valued point `p`
of `S`, then `V` is proper over the field `k` of `p`, `H⁰(V, 𝒪_V) = k`, `V` has dimension one and
`V` has at-worst-nodal singularities over `k`. -/
theorem fibre_standing_of_isPrestableCurveFamily {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value)) :
    IsProper ((𝒯).map v) ∧
      IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ ((𝒯).map v).appTop) ∧
      topologicalKrullDim ((𝒯).obj V) = 1 ∧
      (letI : ((𝒯).obj V).Over (Spec (.of p.carrier)) := ⟨(𝒯).map v⟩;
        Stacks.Curves.HasAtWorstNodalSingularities p.carrier ((𝒯).obj V)) := by
  have hsq' := isPullback_schemeSpace_of_isPullback_yoneda hsq
  have hprop : IsProper ((𝒯).map v) := isProper_of_isPullback_fieldValuedPoint hsq'
  have hH0 : IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ ((𝒯).map v).appTop) :=
    isIso_appTop_of_isPullback_fieldValuedPoint hX.2 hsq'
  -- nodality of the fibre, as a morphism of schemes to `Spec k`
  have hnod : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne ((𝒯).map v) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget v).1
      ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase
        hZ).of_isPullback hsq' hX.1)
  -- read on the fibre over the unique point of `Spec k`
  set k := p.carrier
  set f : (𝒯).obj V ⟶ Spec (.of k) := (𝒯).map v
  set s : Spec (.of k) := IsLocalRing.closedPoint k
  have : IsIso ((Spec (.of k)).fromSpecResidueField s) := isIso_fromSpecResidueField_of_field k s
  have : Nonempty ((𝒯).obj V) := Stacks.Models.nonempty_of_isIso_globalSections f
  let g : (𝒯).obj V ⟶ Spec (.of ((Spec (.of k)).residueField s)) :=
    f ≫ inv ((Spec (.of k)).fromSpecResidueField s)
  have hfg : g ≫ (Spec (.of k)).fromSpecResidueField s = f := by simp [g]
  have sq : IsPullback (𝟙 _) g f ((Spec (.of k)).fromSpecResidueField s) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hfg]⟩
  obtain ⟨hdim, hnodal⟩ := Stacks.Models.hasAtWorstNodalSingularities_of_isPullback_fiber hnod s sq
  refine ⟨hprop, hH0, hdim, ?_⟩
  -- transport from the residue field of `s` to `k`
  let φ : CommRingCat.of k ⟶ CommRingCat.of ((Spec (.of k)).residueField s) :=
    Spec.preimage ((Spec (.of k)).fromSpecResidueField s)
  have hφ : Spec.map φ = (Spec (.of k)).fromSpecResidueField s := Spec.map_preimage _
  have : IsIso (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : IsIso (Scheme.Spec.map φ.op) := inferInstanceAs (IsIso (Spec.map φ))
  have : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  have : IsIso φ := isIso_of_op φ
  have : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType f := inferInstance
    dsimp only [g]
    infer_instance
  exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso g f hdim (𝟙 _) φ
    (by rw [Category.id_comp, hφ, hfg]) hnodal

end CurveFamily

end AlgebraicGeometry

end
