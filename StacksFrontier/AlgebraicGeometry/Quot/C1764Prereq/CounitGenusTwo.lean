module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.CounitFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.C1764Prereq.OnePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.C1764Prereq.RepresentedHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension

/-!
# Base change of `f_*𝓛` to a fibre with vanishing `H¹`

Let `f : X → S` be a family of curves (flat, proper, of finite presentation, of relative
dimension at most one), `𝓛` an invertible module on the total space, `s ∈ S` a point and `V` a
scheme presenting the fibre `X_s`. If `H¹(V, 𝓛|_V) = 0`, then the base change map
`s^*f_*𝓛 ⟶ f_{V,*}(𝓛|_V)` is an isomorphism.

## Main results

* `AlgebraicGeometry.C1764Prereq.isIso_moduleBaseChangeMap_fibre_of_isZero_cohomology_one`: the
  base change map is an isomorphism.
* `AlgebraicGeometry.C1764Prereq.epi_moduleBaseChangeMap_fibre_of_isZero_cohomology_one`: it is
  in particular an epimorphism.
* `AlgebraicGeometry.C1764Prereq.topologicalKrullDim_le_one_of_isFibrePresentation`: a
  presentation of a fibre of a family of curves has dimension at most one.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0D20](https://stacks.math.columbia.edu/tag/0D20)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace C1764Prereq

/-- A scheme `V` presenting a fibre `X_s` of a family of curves has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_isFibrePresentation {X : CurveFamily B hZ}
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q) :
    topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1 := by
  let C := C1590Private.curveFamilyOfIsPullback X (CurveFamily.residuePointMap B hZ X s)
    (ObjectProperty.homMk q) (schemeSpaceMap v) (isPullback_fibre hq)
  let p : Space.FieldValuedPoint B integerBase hZ
      (yoneda.obj (CurveFamily.residuePoint B hZ X s)) :=
    ⟨_, B.residueField_spec_contains X.base.left.property s, _, 𝟙 _⟩
  rw [← Space.dimension_yoneda_eq_topologicalKrullDim B integerBase hZ]
  refine iSup_le fun x => ?_
  obtain ⟨e, he, hx⟩ := C.relativeDimensionLE x
  have h := (Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B integerBase hZ
    (isAlgebraicSpace_yoneda B integerBase hZ V) p (yoneda.map v) x e).1 hx
  rw [h]
  exact_mod_cast he

/-- The Zariski cohomology `Hⁿ(V, 𝓛|_V)`, `n ≥ 1`, of the pullback of a module to a presentation
`V` of a fibre of a family of curves vanishes, given that `H¹(V, 𝓛|_V)` vanishes and that `V` has
dimension at most one. -/
theorem isZero_cohomology_baseChangeModule {X : CurveFamily B hZ}
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (h1 : haveI := hq.isProper
      IsZero (cohomologyOverField
        (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
        (CurveFamily.fibreMap B hZ X s v) (Space.baseChangeModule B integerBase hZ L V q) 1))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation
      ((BigFppfOver.toScheme B integerBase hZ).obj V).ringCatSheaf (Opposite.op ⊤)).rightDerived
        n).obj (Space.baseChangeModule B integerBase hZ L V q)) := by
  have := hq.isProper
  have hn' : IsZero (cohomologyOverField
      (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
      (CurveFamily.fibreMap B hZ X s v) (Space.baseChangeModule B integerBase hZ L V q) n) := by
    rcases Nat.lt_or_ge 1 n with hn₁ | hn₁
    · exact isZero_cohomologyOverField_of_topologicalKrullDim_le _ _ _ (d := 1)
        (by exact_mod_cast hdim) hn₁
    · obtain rfl : n = 1 := by lia
      exact h1
  rwa [ModuleCat.isZero_iff_subsingleton] at hn' ⊢

/-- **Cohomology and base change in degree zero at a fibre with vanishing `H¹`**: for an
invertible module `𝓛` on the total space of a family of curves and a presentation `V` of the fibre
`X_s` with `H¹(V, 𝓛|_V) = 0`, the base change map `s^*f_*𝓛 ⟶ f_{V,*}(𝓛|_V)` is an
isomorphism. -/
theorem isIso_moduleBaseChangeMap_fibre_of_isZero_cohomology_one (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property L)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q)
    (h1 : haveI := hq.isProper
      IsZero (cohomologyOverField
        (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
        (CurveFamily.fibreMap B hZ X s v) (Space.baseChangeModule B integerBase hZ L V q) 1)) :
    IsIso ((Space.moduleBaseChangeMap X.toBase
      (schemeSpaceMap (CurveFamily.residuePointMap B hZ X s)) (schemeSpaceMap v)
      (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (isPullback_fibre hq).w).app L) := by
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := hq.isProper
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj
      (CurveFamily.residuePoint B hZ X s)) :=
    inferInstanceAs (IsAffine (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj
      X.base).residueField s))))
  have hLfp : L.IsFinitePresentation := Space.isFinitePresentation_of_isInvertibleModule L hL
  have hqc := Space.isQuasicoherentOnSite_modulePullback_of_isFinitePresentation B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) L hLfp
  exact isIso_moduleBaseChangeMap_app_of_isZero_rightDerived X.toBase _ _ _ X.proper
    X.finitePresentation L hLfp (Space.isFlatOver_of_isInvertibleModule X.toBase L X.flat hL)
    (isPullback_fibre hq)
    (Space.subsingleton_points_yoneda_siteObject B integerBase hZ (X.residueFieldPoint s))
    (fun n hn => isZero_rightDerived_modulePushforward_representedSpaceMap_of_isZero v _ hqc n
      (isZero_cohomology_baseChangeModule hq L h1
        (topologicalKrullDim_le_one_of_isFibrePresentation hq) n hn)) _

/-- Cohomology and base change in degree zero at a fibre with vanishing `H¹`: for an
invertible module `𝓛` on the total space of a family of curves and a presentation `V` of the fibre
`X_s` with `H¹(V, 𝓛|_V) = 0`, the base change map `s^*f_*𝓛 ⟶ f_{V,*}(𝓛|_V)` is an
epimorphism. -/
theorem epi_moduleBaseChangeMap_fibre_of_isZero_cohomology_one (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property L)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q)
    (h1 : haveI := hq.isProper
      IsZero (cohomologyOverField
        (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
        (CurveFamily.fibreMap B hZ X s v) (Space.baseChangeModule B integerBase hZ L V q) 1)) :
    Epi ((Space.moduleBaseChangeMap X.toBase
      (schemeSpaceMap (CurveFamily.residuePointMap B hZ X s)) (schemeSpaceMap v)
      (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (isPullback_fibre hq).w).app L) :=
  have := isIso_moduleBaseChangeMap_fibre_of_isZero_cohomology_one X L hL s hq h1
  inferInstance

end C1764Prereq

end AlgebraicGeometry
