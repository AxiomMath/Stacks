module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafShape
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree

/-!
# The relative dualizing sheaf of a prestable family restricted to a fibre

Let `f : X ⟶ S` be a prestable family of curves with relative dualizing complex
`(ω^•_{X/S}, τ)` (Stacks 0E5X) and relative dualizing sheaf `ω_{X/S} = H^{-1}(ω^•_{X/S})`
(Stacks 0E6Q). For a presentation `q : V ⟶ X` of the fibre `X_s` by a scheme `V` over
`Spec κ(s)`, the restriction of `ω_{X/S}` to `V` is the dualizing sheaf `ω_V` of Stacks 0BS2.

The base `Spec κ(s)` of the fibre square is affine, so the defining property of a relative
dualizing complex identifies `Lq^*ω^•_{X/S}` with the right adjoint `a(𝒪_{Spec κ(s)})` of the
represented morphism `V ⟶ Spec κ(s)`, which corresponds to the dualizing complex `ω_V^•` of the
scheme `V` (Stacks 0E6E). As `ω^•_{X/S}` lies in `D^{≤ -1}` (Stacks 0E6P), the degree `-1`
cohomology of `Lq^*ω^•_{X/S}` is `q^*ω_{X/S}`, and reading it on the scheme `V` gives
`H^{-1}(ω_V^•) = ω_V`.

## Main results

* `AlgebraicGeometry.C1764Prereq.nonempty_baseChangeModule_dualizingSheafOfComplex_iso`: the
  restriction of `ω_{X/S}` to a presentation of a fibre is the dualizing sheaf of the fibre.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.C1764Prereq

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective SheafOfModules.instAbelian

/-- **The relative dualizing sheaf restricts to the dualizing sheaf on the fibres.** For a
prestable family of curves, a relative dualizing complex `ω^•_{X/S}` and a presentation
`q : V ⟶ X` of the fibre `X_s` over `Spec κ(s)`, the restriction of `ω_{X/S} = H^{-1}(ω^•_{X/S})`
to `V` is the dualizing sheaf of `V ⟶ Spec κ(s)` of Stacks 0BS2. -/
theorem nonempty_baseChangeModule_dualizingSheafOfComplex_iso {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (h : CurveFamily.IsFibrePresentation B hZ X s v q) :
    haveI := h.isProper
    Nonempty (Space.baseChangeModule B integerBase hZ (X.dualizingSheafOfComplex D) V q ≅
      Stacks.Duality.dualizingSheafOverField (CurveFamily.fibreMap B hZ X s v)) := by
  have := h.isProper
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := h.isProper
  have sq := C1764Prereq.isPullback_fibre h
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj
      (CurveFamily.residuePoint B hZ X s)) :=
    inferInstanceAs (IsAffine (Spec (.of
      (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))))
  have hLE : @DerivedCategory.IsLE _ _ _ (HasDerivedCategory.standard _) D.ω (-1) :=
    (@DerivedCategory.isLE_iff _ _ _ (HasDerivedCategory.standard _) _ _).2 fun i hi =>
      C1764Prereq.isZero_homology_relDualizing_of_ne hX D i (by omega)
  obtain ⟨e₁⟩ := Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE
    (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) D.ω (-1) hLE
  let M := (DerivedCategory.homologyFunctor
    ((BigFppfOver.toScheme B integerBase hZ).obj V).Modules (-1)).obj
      (C1590Private.relativeDualizingComplex ((BigFppfOver.toScheme B integerBase hZ).map v)).obj
  have hM : SheafOfModules.IsQuasicoherent M :=
    (C1590Private.relativeDualizingComplex ((BigFppfOver.toScheme B integerBase hZ).map v)).property
      (-1)
  let e₂ := e₁.symm ≪≫ homologyChartIso D sq (-1) ≪≫
    (Space.representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
      B integerBase hZ V).app M
  exact ⟨(Space.restrictToChartSchemeFunctor B integerBase hZ (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase hZ V) (Space.idEtaleChart B integerBase hZ V)).mapIso
      e₂ ≪≫ Space.restrictToChartSchemeRepresentedAssociatedModuleIso B integerBase hZ V M hM ≪≫
    eqToIso (C1590Private.relativeDualizingSheaf_eq_dualizingSheafOverField
      (CurveFamily.fibreMap B hZ X s v))⟩

end AlgebraicGeometry.C1764Prereq

end
