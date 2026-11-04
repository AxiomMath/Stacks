module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.RelativeOpenCover
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeFunctor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSource
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart

/-!
# The kernels attached to the affine opens of `X`, and their comparison on the overlaps

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` of affine diagonal,
and let `F : QCoh(O_X) ⥤ QCoh(O_Y)` be `R`-linear, right exact and commuting with arbitrary
direct sums.  `AlgebraicGeometry.affineSourceKernel` attaches to every morphism with affine
source a quasi-coherent kernel; this file specialises that to the inclusions of the *affine
opens* of `X`, which is the family the gluing of [Stacks, Tag 0GPA] is formed from, and produces
the comparison of two such kernels over an open of `X ×_R Y` lying in both charts, in exactly
the shape `AlgebraicGeometry.RestrictIsoGlueData.iso` asks for.

The comparison is assembled from three ingredients, all of them already available:

* the source-change comparison `AlgebraicGeometry.affineSourceKernelSourceChangeIso` of
  [Stacks, Tag 0FZF], at the inclusion of the intersection into each of the two opens --
  legitimate because the intersection of two affine opens of a scheme with affine diagonal is
  affine (`AlgebraicGeometry.IsAffineOpen.inf`);
* uniqueness of the factorisation of an open through a chart
  (`AlgebraicGeometry.openLift_comp_eq`), which identifies the factorisation through the chart of
  `U` with the factorisation through the chart of `U ⊓ V` followed by the chart map -- so the
  comparison over the open is the *restriction* of the comparison on the intersection chart;
* the chart comparison `AlgebraicGeometry.restrictPushforwardIsoOfRestrictIso`, which turns an
  isomorphism of the restrictions along the two factorisations into an isomorphism of the
  restrictions of the two direct images.

The comparison of the two charts is in particular of the shape
`AlgebraicGeometry.restrictMiddleIso` -- a comparison taken through a third chart contained in
both -- and the `iso_restrict` field of the glueing data is exactly the statement that such a
comparison, shrunk, is the comparison through that chart over the smaller open.

## Main definitions

* `AlgebraicGeometry.openSubInclusionOver` and `AlgebraicGeometry.openSubChartMap`: the inclusion
  of a smaller open of `X`, and the map it induces on the charts of `X ×_R Y`.
* `AlgebraicGeometry.openKernel`: **the kernel attached to an affine open of `X`.**
* `AlgebraicGeometry.openKernelRestrictIso`: **the kernel of a smaller affine open is the inverse
  image of the kernel of a larger one** -- Tag 0FZF read on the charts.
* `AlgebraicGeometry.openKernelRestrictSigma`: the same, read as an identification of the
  *restriction* of the kernel of the larger open along the chart map.
* `AlgebraicGeometry.openKernelMiddleIso`: **the comparison, over an open contained in both
  charts, of the restrictions of the kernels of two affine opens**, taken through the chart of
  the intersection.
* `AlgebraicGeometry.openKernelChartIso`: **the comparison of the two charts over an open
  contained in both**, in the shape the glueing data asks for.

## Main results

* `AlgebraicGeometry.openSubChartMap_comp` and `AlgebraicGeometry.openSubChartMap_trans`: the
  chart maps compose to the chart map, and compose with each other.
* `AlgebraicGeometry.openLift_baseChangeOpenTargetMap_comp`: the factorisation of an open through
  the chart of `U` is the factorisation through the chart of a smaller open followed by the chart
  map.
* `AlgebraicGeometry.restrictLocal_openKernelChartIso`: **the `iso_restrict` field of
  `AlgebraicGeometry.RestrictIsoGlueData`** for the family of charts of the affine opens of `X`.

## Implementation notes

### Where the glueing is completed

`AlgebraicGeometry.openKernelChartIso` is the `iso` field of
`AlgebraicGeometry.RestrictIsoGlueData` for the family of charts of the affine opens of `X`, and
`AlgebraicGeometry.restrictLocal_openKernelChartIso` is its `iso_restrict` field.  The remaining
field, the cocycle condition `iso_trans` on a triple overlap, and the single quasi-coherent
module on `X ×_R Y` that construction (1) of [Stacks, Tag 0GPA] asks for, are
`AlgebraicGeometry.gluedKernel` and its glueing data.

The cocycle condition is obtained by rewriting all three pairwise comparisons through the chart
of the triple intersection `U ⊓ V ⊓ W` using `AlgebraicGeometry.restrictMiddleIso_refine`, whose
hypothesis is the pseudo-functoriality of `AlgebraicGeometry.openKernelRestrictSigma` along a
composite of two inclusions; that splits into the coherence of restriction with inverse image
along a composite (`AlgebraicGeometry.restrictFunctorIsoPullback_comp`) and the
pseudo-functoriality of `AlgebraicGeometry.affineSourceKernelSourceChangeIso`, i.e.
`AlgebraicGeometry.affineSourceKernelSourceChangeIso_comp`.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] isOpenImmersion_over_comp_left

section Charts

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- The inclusion of a smaller open subscheme of `X` into a larger one, as a morphism of schemes
over `R`. -/
def openSubInclusionOver {U U' : X.left.Opens} (h : U' ≤ U) :
    openSubOver R X U' ⟶ openSubOver R X U :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ U.ι ≫ X.hom = U'.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The underlying morphism of schemes of `AlgebraicGeometry.openSubInclusionOver` is the
inclusion `X.left.homOfLE h`. -/
@[simp] theorem openSubInclusionOver_left {U U' : X.left.Opens} (h : U' ≤ U) :
    (openSubInclusionOver R X h).left = X.left.homOfLE h := rfl

/-- The inclusion of a smaller open subscheme of `X` into a larger one is an open immersion. -/
instance isOpenImmersion_openSubInclusionOver_left {U U' : X.left.Opens} (h : U' ≤ U) :
    IsOpenImmersion (openSubInclusionOver R X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

/-- The inclusion of an open subscheme, as a morphism of schemes over `R`, is an open
immersion. -/
theorem isOpenImmersion_openSubOverHom_left (U : X.left.Opens) :
    IsOpenImmersion (openSubOverHom R X U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The inclusion of a smaller open, followed by the inclusion of the larger one, is the
inclusion of the smaller one. -/
theorem openSubInclusionOver_comp {U U' : X.left.Opens} (h : U' ≤ U) :
    openSubInclusionOver R X h ≫ openSubOverHom R X U = openSubOverHom R X U' :=
  Over.OverMorphism.ext (by
    show X.left.homOfLE h ≫ U.ι = U'.ι
    rw [Scheme.homOfLE_ι])

/-- The inclusions of the opens of `X` compose. -/
theorem openSubInclusionOver_trans {U U' U'' : X.left.Opens} (h : U' ≤ U) (h' : U'' ≤ U') :
    openSubInclusionOver R X h' ≫ openSubInclusionOver R X h =
      openSubInclusionOver R X (h'.trans h) :=
  Over.OverMorphism.ext (by
    show X.left.homOfLE h' ≫ X.left.homOfLE h = X.left.homOfLE (h'.trans h)
    rw [Scheme.homOfLE_homOfLE])

/-- The map of charts of `X ×_R Y` induced by the inclusion of a smaller open subscheme of
`X`. -/
abbrev openSubChartMap {U U' : X.left.Opens} (h : U' ≤ U) :
    pullback (openSubOver R X U').hom Y.hom ⟶ pullback (openSubOver R X U).hom Y.hom :=
  sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y (openSubInclusionOver R X h)

/-- The morphisms `f × id_Y` of Tag 0FZF compose, for a composite given up to equality. -/
private theorem sourceChangeMap_comp_of_eq {R : Type u} [CommRing R]
    {X X' X'' : Over (Spec (.of R))} (Y : Over (Spec (.of R))) (f : X' ⟶ X) (g : X'' ⟶ X')
    {k : X'' ⟶ X} (h : g ≫ f = k) :
    sourceChangeMap R X' X'' Y g ≫ sourceChangeMap R X X' Y f = sourceChangeMap R X X'' Y k :=
  h ▸ sourceChangeMap_comp R X X' X'' Y f g

/-- **The chart map of a smaller open, followed by the chart of the larger one, is the chart of
the smaller one.** -/
theorem openSubChartMap_comp {U U' : X.left.Opens} (h : U' ≤ U) :
    openSubChartMap R X Y h ≫ baseChangeOpenTargetMap R X Y U =
      baseChangeOpenTargetMap R X Y U' :=
  sourceChangeMap_comp_of_eq Y _ _ (openSubInclusionOver_comp R X h)

/-- **The chart maps of the opens of `X` compose.** -/
theorem openSubChartMap_trans {U U' U'' : X.left.Opens} (h : U' ≤ U) (h' : U'' ≤ U') :
    openSubChartMap R X Y h' ≫ openSubChartMap R X Y h = openSubChartMap R X Y (h'.trans h) :=
  sourceChangeMap_comp_of_eq Y _ _ (openSubInclusionOver_trans R X h h')

/-- **The factorisation of an open through the chart of `U` is the factorisation through the chart
of a smaller open followed by the chart map.**  This is `AlgebraicGeometry.openLift_comp_eq` at
the chart maps, and it is what lets a comparison living on the chart of `U ⊓ V` produce the
comparison of the charts of `U` and of `V`. -/
theorem openLift_baseChangeOpenTargetMap_comp {U U' : X.left.Opens} (h : U' ≤ U)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZ : Z ≤ (baseChangeOpenTargetMap R X Y U').opensRange)
    (hU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange) :
    openLift (baseChangeOpenTargetMap R X Y U') hZ ≫ openSubChartMap R X Y h =
      openLift (baseChangeOpenTargetMap R X Y U) hU :=
  eq_openLift _ _ _ (by rw [Category.assoc, openSubChartMap_comp, openLift_comp])

end Charts

/-! ### The kernels of the affine opens -/

section Kernel

attribute [local instance] isOpenImmersion_openSubOverHom_left

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- **The kernel attached to an affine open of `X`:** the quasi-coherent module on `U ×_R Y`
whose integral transform is `F ∘ j_{U,*}`. -/
def openKernel {U : X.left.Opens} (hU : IsAffineOpen U) :
    Scheme.QuasicoherentModules (pullback (openSubOver R X U).hom Y.hom) :=
  letI : IsAffine (openSubOver R X U).left := hU
  affineSourceKernel R X Y F hF (openSubOverHom R X U)

/-- **The kernel of a smaller affine open is the inverse image of the kernel of a larger one.**
This is `AlgebraicGeometry.affineSourceKernelSourceChangeIso`, i.e. Tag 0FZF, read on the charts
of `X ×_R Y`. -/
def openKernelRestrictIso {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (h : U' ≤ U) :
    (sourceChangeKernel R (openSubOver R X U) (openSubOver R X U') Y
        (openSubInclusionOver R X h) (openKernel R X Y F hF hU) ≅
      openKernel R X Y F hF hU') :=
  letI : IsAffine (openSubOver R X U).left := hU
  letI : IsAffine (openSubOver R X U').left := hU'
  affineSourceKernelSourceChangeIso R X Y F hF (openSubOverHom R X U)
      (openSubInclusionOver R X h) ≪≫
    eqToIso (affineSourceKernel_congr R X Y F hF (openSubInclusionOver_comp R X h))

/-- The inverse image of the kernel of `U` along the chart map, read as the inverse image of its
underlying sheaf of modules. -/
theorem sourceChangeKernel_openKernel_obj {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (h : U' ≤ U) :
    (sourceChangeKernel R (openSubOver R X U) (openSubOver R X U') Y
        (openSubInclusionOver R X h) (openKernel R X Y F hF hU)).obj =
      (Scheme.Modules.pullback (openSubChartMap R X Y h)).obj
        (openKernel R X Y F hF hU).obj := rfl

/-- **The kernel of a smaller affine open is the restriction, along the chart map, of the kernel
of a larger one.**  This is `AlgebraicGeometry.openKernelRestrictIso` read through the comparison
of the restriction along an open immersion with the inverse image. -/
def openKernelRestrictSigma {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (h : U' ≤ U) :
    Scheme.Modules.restrict (openKernel R X Y F hF hU).obj (openSubChartMap R X Y h) ≅
      (openKernel R X Y F hF hU').obj :=
  (Scheme.Modules.restrictFunctorIsoPullback (openSubChartMap R X Y h)).app
      (openKernel R X Y F hF hU).obj ≪≫
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback (openSubOver R X U').hom Y.hom).ringCatSheaf)).mapIso
        (openKernelRestrictIso R X Y F hF hU hU' h)

/-- **The comparison, over an open contained in both charts, of the restrictions of the kernels
of two affine opens**, taken through the chart of the intersection.  The intersection is an
affine open because `X` has affine diagonal, so it carries a kernel, and both kernels restrict to
it. -/
def openKernelMiddleIso {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    Scheme.Modules.restrict (openKernel R X Y F hF hU).obj
        (openLift (baseChangeOpenTargetMap R X Y U) hZU) ≅
      Scheme.Modules.restrict (openKernel R X Y F hF hV).obj
        (openLift (baseChangeOpenTargetMap R X Y V) hZV) :=
  restrictMiddleIso (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
    (baseChangeOpenTargetMap R X Y (U ⊓ V))
    (openSubChartMap_comp R X Y (inf_le_left : U ⊓ V ≤ U))
    (openSubChartMap_comp R X Y (inf_le_right : U ⊓ V ≤ V))
    (openKernelRestrictSigma R X Y F hF hU
      ((hU.inf hV)) inf_le_left)
    (openKernelRestrictSigma R X Y F hF hV
      ((hU.inf hV)) inf_le_right)
    ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV)) hZU hZV

/-- **The comparison of the two charts over an open contained in both**, in the shape the `iso`
field of `AlgebraicGeometry.RestrictIsoGlueData` asks for. -/
def openKernelChartIso {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    (Scheme.Modules.restrict ((Scheme.Modules.pushforward
          (baseChangeOpenTargetMap R X Y U)).obj (openKernel R X Y F hF hU).obj) Z.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward
          (baseChangeOpenTargetMap R X Y V)).obj (openKernel R X Y F hF hV).obj) Z.ι) :=
  restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (openKernel R X Y F hF hU).obj
    (openKernel R X Y F hF hV).obj hZU hZV (openKernelMiddleIso R X Y F hF hU hV hZU hZV)

/-- **The `iso_restrict` field of `AlgebraicGeometry.RestrictIsoGlueData`** for the family of
charts of the affine opens of `X`:  the comparison of two charts over an open is compatible with
shrinking the open.  Both comparisons are taken through the chart of the intersection, and
`AlgebraicGeometry.openLiftShrinkIso_restrictMiddleIso` says that the comparison through a middle
chart, shrunk, is the comparison through that chart over the smaller open. -/
theorem restrictLocal_openKernelChartIso {U V : X.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) {Z Z' : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) (hZ' : Z' ≤ Z) :
    restrictLocal (openKernelChartIso R X Y F hF hU hV hZU hZV).hom hZ' =
      (openKernelChartIso R X Y F hF hU hV (hZ'.trans hZU) (hZ'.trans hZV)).hom := by
  refine (restrictLocal_restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (openKernel R X Y F hF hU).obj
    (openKernel R X Y F hF hV).obj hZU hZV hZ'
    (openKernelMiddleIso R X Y F hF hU hV hZU hZV)).trans ?_
  exact congrArg (fun e ↦ (restrictPushforwardIsoOfRestrictIso
      (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
      (openKernel R X Y F hF hU).obj (openKernel R X Y F hF hV).obj
      (hZ'.trans hZU) (hZ'.trans hZV) e).hom)
    (openLiftShrinkIso_restrictMiddleIso (baseChangeOpenTargetMap R X Y U)
      (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y (U ⊓ V))
      (openSubChartMap_comp R X Y (inf_le_left : U ⊓ V ≤ U))
      (openSubChartMap_comp R X Y (inf_le_right : U ⊓ V ≤ V))
      (openKernelRestrictSigma R X Y F hF hU
        ((hU.inf hV)) inf_le_left)
      (openKernelRestrictSigma R X Y F hF hV
        ((hU.inf hV)) inf_le_right)
      ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV))
      hZU hZV hZ')

end Kernel

end AlgebraicGeometry

end
