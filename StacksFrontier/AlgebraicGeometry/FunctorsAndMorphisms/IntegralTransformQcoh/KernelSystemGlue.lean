module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineOpenKernelCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso

/-!
# Gluing a compatible system of kernels on the charts of the affine opens

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R`, the diagonal of `X` being
affine.  An affine open `U` of `X` gives the chart `U ×_R Y ⟶ X ×_R Y`.  This file glues a family
of quasi-coherent modules `K_U` on the charts `U ×_R Y`, one for every affine open `U`, given
identifications `(U' ×_R Y ⟶ U ×_R Y)^* K_U ≅ K_{U'}` for `U' ≤ U` satisfying the cocycle
condition along chains `U'' ≤ U' ≤ U`, into one quasi-coherent module on `X ×_R Y`.

The comparison of two charts `U`, `V` is taken through the chart of `U ⊓ V`, which is affine
since the diagonal of `X` is.  The glueing datum is
`AlgebraicGeometry.AffineChartKernels.glueData`; its cocycle condition is reduced to the
cocycle condition of the system by passing all three comparisons of a triple overlap through the
chart of the triple intersection.

## Main definitions

* `AlgebraicGeometry.AffineChartKernels`: a compatible system of kernels on the charts.
* `AlgebraicGeometry.AffineChartKernels.glueData`: its glueing datum.
* `AlgebraicGeometry.AffineChartKernels.glued`: **the glued quasi-coherent module.**
* `AlgebraicGeometry.AffineChartKernels.chartIso`: its restriction to each chart.

## Main results

* `AlgebraicGeometry.AffineChartKernels.sigma_trans`: the identifications of restrictions are
  pseudo-functorial along chains of affine opens.
* `AlgebraicGeometry.AffineChartKernels.chartIsoOver_trans`: the cocycle condition of the
  glueing datum.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- **A compatible system of quasi-coherent kernels on the charts of the affine opens.**  For
every affine open `U` of `X` a quasi-coherent module on `U ×_R Y`, for every inclusion `U' ≤ U`
of affine opens an identification of the inverse image of the kernel of `U` along the chart map
with the kernel of `U'`, and the cocycle condition along chains of three affine opens. -/
structure AffineChartKernels where
  /-- The kernel on the chart of an affine open. -/
  kern : ∀ {U : X.left.Opens}, IsAffineOpen U →
    Scheme.QuasicoherentModules (pullback (openSubOver R X U).hom Y.hom)
  /-- The inverse image of the kernel of `U` along the chart map of `U' ≤ U` is the kernel of
  `U'`. -/
  restrictIso : ∀ {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (h : U' ≤ U),
    sourceChangeKernel R (openSubOver R X U) (openSubOver R X U') Y
        (openSubInclusionOver R X h) (kern hU) ≅ kern hU'
  /-- The cocycle condition along a chain `U'' ≤ U' ≤ U`. -/
  restrictIso_trans : ∀ {U U' U'' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'') (hle : U' ≤ U) (hle' : U'' ≤ U'),
    eqToHom (congrArg (fun n : openSubOver R X U'' ⟶ openSubOver R X U ↦
          sourceChangeKernel R (openSubOver R X U) (openSubOver R X U'') Y n
            (kern hU)) (openSubInclusionOver_trans R X hle hle').symm) ≫
        (sourceChangeKernelCompIso R (openSubOver R X U) (openSubOver R X U')
            (openSubOver R X U'') Y (openSubInclusionOver R X hle)
            (openSubInclusionOver R X hle') (kern hU)).hom ≫
          sourceChangeKernelMap R (openSubOver R X U') (openSubOver R X U'') Y
              (openSubInclusionOver R X hle') (restrictIso hU hU' hle).hom ≫
            (restrictIso hU' hU'' hle').hom =
      (restrictIso hU hU'' (hle'.trans hle)).hom

namespace AffineChartKernels

variable {R X Y} (S : AffineChartKernels R X Y)

/-- The identification of the system, read on the inverse image of the underlying sheaf of
modules. -/
def rho {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U) :
    (Scheme.Modules.pullback (openSubChartMap R X Y h)).obj (S.kern hU).obj ≅
      (S.kern hU').obj :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback (openSubOver R X U').hom Y.hom).ringCatSheaf)).mapIso (S.restrictIso hU hU' h)

/-- The identification of the system, read on the restriction along the chart map. -/
def sigma {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U) :
    Scheme.Modules.restrict (S.kern hU).obj (openSubChartMap R X Y h) ≅ (S.kern hU').obj :=
  (Scheme.Modules.restrictFunctorIsoPullback (openSubChartMap R X Y h)).app (S.kern hU).obj ≪≫
    S.rho hU hU' h

/-- The chart maps of the opens of `X` compose, written with `AlgebraicGeometry.sourceChangeMap`
spelled out. -/
theorem sourceChangeMap_openSubInclusionOver_trans {U U' U'' : X.left.Opens} (h : U' ≤ U)
    (h' : U'' ≤ U') :
    sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y (openSubInclusionOver R X h') ≫
        sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y (openSubInclusionOver R X h) =
      sourceChangeMap R (openSubOver R X U) (openSubOver R X U'') Y
        (openSubInclusionOver R X (h'.trans h)) :=
  openSubChartMap_trans R X Y h h'

/-- The cocycle condition of the system, read on the inverse images of the underlying sheaves of
modules. -/
theorem rho_trans {U U' U'' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') (h : U' ≤ U) (h' : U'' ≤ U') :
    (pullbackCompIsoOfEq
        (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
          (openSubInclusionOver R X h'))
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X h))
        (sourceChangeMap_openSubInclusionOver_trans h h') (S.kern hU).obj).hom ≫
        (S.rho hU hU'' (h'.trans h)).hom =
      (Scheme.Modules.pullback (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
          (openSubInclusionOver R X h'))).map (S.rho hU hU' h).hom ≫
        (S.rho hU' hU'' h').hom :=
  pullbackCompIsoOfEq_sourceChangeKernel R Y (openSubInclusionOver R X h)
      (openSubInclusionOver R X h') (openSubInclusionOver_trans R X h h')
      (S.restrictIso hU hU' h) (S.restrictIso hU' hU'' h') (S.restrictIso hU hU'' (h'.trans h))
      (S.rho hU hU' h) (S.rho hU' hU'' h') (S.rho hU hU'' (h'.trans h)) rfl rfl rfl
      (sourceChangeMap_openSubInclusionOver_trans h h') (S.restrictIso_trans hU hU' hU'' h h')

/-- **The identifications of restrictions are pseudo-functorial** along a chain of affine opens
`U'' ≤ U' ≤ U`. -/
theorem sigma_trans {U U' U'' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') (h : U' ≤ U) (h' : U'' ≤ U') :
    restrictChartIso
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y (openSubInclusionOver R X h))
        (S.sigma hU hU' h)
        (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
          (openSubInclusionOver R X h'))
        (sourceChangeMap_openSubInclusionOver_trans h h') ≪≫ S.sigma hU' hU'' h' =
      S.sigma hU hU'' (h'.trans h) :=
  restrictChartIso_pullback_trans
    (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y (openSubInclusionOver R X h))
    (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y (openSubInclusionOver R X h'))
    (sourceChangeMap_openSubInclusionOver_trans h h') (S.rho hU hU' h) (S.rho hU' hU'' h')
    (S.rho hU hU'' (h'.trans h)) (S.rho_trans hU hU' hU'' h h')

variable [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- **The comparison, over an open contained in the charts of two affine opens, of the
restrictions of their kernels**, taken through the chart of the intersection. -/
def middleIso {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    Scheme.Modules.restrict (S.kern hU).obj (openLift (baseChangeOpenTargetMap R X Y U) hZU) ≅
      Scheme.Modules.restrict (S.kern hV).obj (openLift (baseChangeOpenTargetMap R X Y V) hZV) :=
  restrictMiddleIso (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
    (baseChangeOpenTargetMap R X Y (U ⊓ V))
    (openSubChartMap_comp R X Y (inf_le_left : U ⊓ V ≤ U))
    (openSubChartMap_comp R X Y (inf_le_right : U ⊓ V ≤ V))
    (S.sigma hU (hU.inf hV) inf_le_left) (S.sigma hV (hU.inf hV) inf_le_right)
    ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV)) hZU hZV

/-- **The comparison of two charts over an open contained in both.** -/
def chartIsoOver {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    (Scheme.Modules.restrict ((Scheme.Modules.pushforward
          (baseChangeOpenTargetMap R X Y U)).obj (S.kern hU).obj) Z.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward
          (baseChangeOpenTargetMap R X Y V)).obj (S.kern hV).obj) Z.ι) :=
  restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (S.kern hU).obj (S.kern hV).obj hZU hZV
    (S.middleIso hU hV hZU hZV)

/-- The comparison of two charts is compatible with shrinking the open. -/
theorem restrictLocal_chartIsoOver {U V : X.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) {Z Z' : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) (hZ' : Z' ≤ Z) :
    restrictLocal (S.chartIsoOver hU hV hZU hZV).hom hZ' =
      (S.chartIsoOver hU hV (hZ'.trans hZU) (hZ'.trans hZV)).hom := by
  refine (restrictLocal_restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (S.kern hU).obj (S.kern hV).obj hZU hZV hZ'
    (S.middleIso hU hV hZU hZV)).trans ?_
  congr 2
  exact (openLiftShrinkIso_restrictMiddleIso (baseChangeOpenTargetMap R X Y U)
      (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y (U ⊓ V))
      (openSubChartMap_comp R X Y (inf_le_left : U ⊓ V ≤ U))
      (openSubChartMap_comp R X Y (inf_le_right : U ⊓ V ≤ V))
      (S.sigma hU (hU.inf hV) inf_le_left) (S.sigma hV (hU.inf hV) inf_le_right)
      ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV))
      hZU hZV hZ')

/-- The comparison of two charts through the chart of their intersection is the comparison
through the chart of any smaller affine open containing the open. -/
theorem middleIso_refine {U V T : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hT : IsAffineOpen T) (hTU : T ≤ U) (hTV : T ≤ V) {Z : (pullback X.hom Y.hom).Opens}
    (hZT : Z ≤ (baseChangeOpenTargetMap R X Y T).opensRange)
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    S.middleIso hU hV hZU hZV =
      restrictMiddleIso (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
        (baseChangeOpenTargetMap R X Y T) (openSubChartMap_comp R X Y hTU)
        (openSubChartMap_comp R X Y hTV) (S.sigma hU hT hTU) (S.sigma hV hT hTV) hZT hZU hZV :=
  (restrictMiddleIso_refine (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
    (baseChangeOpenTargetMap R X Y (U ⊓ V)) (baseChangeOpenTargetMap R X Y T)
    (openSubChartMap_comp R X Y (inf_le_left : U ⊓ V ≤ U))
    (openSubChartMap_comp R X Y (inf_le_right : U ⊓ V ≤ V))
    (openSubChartMap_comp R X Y (le_inf hTU hTV))
    (openSubChartMap_trans R X Y inf_le_left (le_inf hTU hTV))
    (openSubChartMap_trans R X Y inf_le_right (le_inf hTU hTV))
    (S.sigma hU (hU.inf hV) inf_le_left) (S.sigma hV (hU.inf hV) inf_le_right)
    (S.sigma (hU.inf hV) hT (le_inf hTU hTV)) (S.sigma hU hT hTU) (S.sigma hV hT hTV)
    (S.sigma_trans hU (hU.inf hV) hT inf_le_left (le_inf hTU hTV))
    (S.sigma_trans hV (hU.inf hV) hT inf_le_right (le_inf hTU hTV)) hZT hZU hZV).symm

/-- **The cocycle condition of the comparisons of the charts.** -/
theorem chartIsoOver_trans {U V W : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange)
    (hZW : Z ≤ (baseChangeOpenTargetMap R X Y W).opensRange) :
    (S.chartIsoOver hU hV hZU hZV).hom ≫ (S.chartIsoOver hV hW hZV hZW).hom =
      (S.chartIsoOver hU hW hZU hZW).hom := by
  have hT : IsAffineOpen (U ⊓ V ⊓ W) := (hU.inf hV).inf hW
  have hZT : Z ≤ (baseChangeOpenTargetMap R X Y (U ⊓ V ⊓ W)).opensRange := by
    rw [← opensRange_baseChangeOpenTargetMap_inf, ← opensRange_baseChangeOpenTargetMap_inf]
    exact le_inf (le_inf hZU hZV) hZW
  have hTU : U ⊓ V ⊓ W ≤ U := inf_le_left.trans inf_le_left
  have hTV : U ⊓ V ⊓ W ≤ V := inf_le_left.trans inf_le_right
  have hTW : U ⊓ V ⊓ W ≤ W := inf_le_right
  refine (restrictPushforwardIsoOfRestrictIso_trans (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y W) (S.kern hU).obj
    (S.kern hV).obj (S.kern hW).obj hZU hZV hZW (S.middleIso hU hV hZU hZV)
    (S.middleIso hV hW hZV hZW)).trans ?_
  congr 2
  rw [S.middleIso_refine hU hV hT hTU hTV hZT hZU hZV,
    S.middleIso_refine hV hW hT hTV hTW hZT hZV hZW,
    S.middleIso_refine hU hW hT hTU hTW hZT hZU hZW]
  exact (restrictMiddleIso_trans (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y W)
    (baseChangeOpenTargetMap R X Y (U ⊓ V ⊓ W)) (openSubChartMap_comp R X Y hTU)
    (openSubChartMap_comp R X Y hTV) (openSubChartMap_comp R X Y hTW) (S.sigma hU hT hTU)
    (S.sigma hV hT hTV) (S.sigma hW hT hTW) hZT hZU hZV hZW)

/-- **The glueing datum of the system** on the charts of all affine opens of `X`. -/
def glueData : RestrictIsoGlueData (pullback X.hom Y.hom)
    (fun U : X.left.affineOpens ↦ baseChangeOpenTargetMap R X Y (U : X.left.Opens)) where
  mod U := (S.kern U.2).obj
  iso U V {_Z} hU hV := S.chartIsoOver U.2 V.2 hU hV
  iso_restrict U V {_Z _Z'} hU hV hV' := S.restrictLocal_chartIsoOver U.2 V.2 hU hV hV'
  iso_trans U V W {_Z} hU hV hW := S.chartIsoOver_trans U.2 V.2 W.2 hU hV hW

/-- **The quasi-coherent module on `X ×_R Y` glued from the system.** -/
def glued : Scheme.QuasicoherentModules (pullback X.hom Y.hom) :=
  ⟨S.glueData.glued,
    S.glueData.isQuasicoherent_glued (iSup_opensRange_baseChangeOpenTargetMap R X Y)
      fun U ↦ (S.kern U.2).property⟩

/-- **The glued module restricts on the chart of an affine open to the kernel of that open.** -/
def chartIso {U : X.left.Opens} (hU : IsAffineOpen U) :
    Scheme.Modules.restrict S.glued.obj (baseChangeOpenTargetMap R X Y U) ≅ (S.kern hU).obj :=
  S.glueData.chartIso ⟨U, hU⟩

end AffineChartKernels

end AlgebraicGeometry

end
