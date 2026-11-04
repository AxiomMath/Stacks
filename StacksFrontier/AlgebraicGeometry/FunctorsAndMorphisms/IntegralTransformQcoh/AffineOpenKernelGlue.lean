module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineOpenKernelCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso

/-!
# The kernel on `X ×_R Y` glued from the kernels of the affine opens of `X`

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with the diagonal of `X` over
`R` affine, and let `F : QCoh(O_X) ⥤ QCoh(O_Y)` be `R`-linear, right exact and commuting with
arbitrary direct sums.  The affine opens `U` of `X` carry kernels
`AlgebraicGeometry.openKernel` on the charts `U ×_R Y` of `X ×_R Y`, and those charts cover
`X ×_R Y` (`AlgebraicGeometry.iSup_opensRange_baseChangeOpenTargetMap`).  This file assembles
them into a single quasi-coherent module on `X ×_R Y`, which is construction (1) of
[Stacks, Tag 0GPA].

## Main definitions

* `AlgebraicGeometry.AffineOpenKernelFamily`: **a kernel for each affine open of `X`, with
  pseudo-functorial comparisons of the inverse images.**
* `AlgebraicGeometry.AffineOpenKernelFamily.glueData`: **the glueing datum it determines**;
  `AlgebraicGeometry.AffineOpenKernelFamily.gluedKernel` the quasi-coherent module on `X ×_R Y`
  glued from it, and `AlgebraicGeometry.AffineOpenKernelFamily.gluedChartIso` the identification
  of its restriction along the chart of `U` with the kernel of `U`.
* `AlgebraicGeometry.openKernelFamily`: **the family of the kernels of the affine opens of `X`.**
* `AlgebraicGeometry.gluedKernel`: **the quasi-coherent module on `X ×_R Y` of construction (1)
  of [Stacks, Tag 0GPA]**, and `AlgebraicGeometry.gluedKernelChartIso` its identification on the
  chart of an affine open.

## Main results

* `AlgebraicGeometry.restrictChartIso_trans_of_eq`: `restrictChartIso` is pseudo-functorial for
  comparisons of restrictions *presented* as comparisons of inverse images.
* `AlgebraicGeometry.AffineOpenKernelFamily.sigma_trans`: **the comparisons of the restrictions
  along the chart maps are pseudo-functorial** along a chain `U'' ≤ U' ≤ U`.
* `AlgebraicGeometry.AffineOpenKernelFamily.middleIso_trans` and
  `AlgebraicGeometry.AffineOpenKernelFamily.chartComparison_trans`: **the cocycle condition on a
  triple overlap.**

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **`AlgebraicGeometry.restrictChartIso` is pseudo-functorial for comparisons of restrictions
*presented* as comparisons of inverse images.**  If the comparisons of restrictions `σ`, `σ'`,
`σ''` are the comparisons of inverse images `ρ`, `ρ'`, `ρ''` composed with
`Scheme.Modules.restrictFunctorIsoPullback`, and `ρ`, `ρ'`, `ρ''` are compatible, then
`restrictChartIso a σ b hk ≪≫ σ' = σ''`. -/
theorem restrictChartIso_trans_of_eq {Q P P' : Scheme.{u}} (a : P ⟶ Q) (b : P' ⟶ P)
    [IsOpenImmersion a] [IsOpenImmersion b] {k : P' ⟶ Q} (hk : b ≫ a = k) [IsOpenImmersion k]
    {M : Q.Modules} {M' : P.Modules} {M'' : P'.Modules}
    (σ : Scheme.Modules.restrict M a ≅ M') (σ' : Scheme.Modules.restrict M' b ≅ M'')
    (σ'' : Scheme.Modules.restrict M k ≅ M'')
    (ρ : (Scheme.Modules.pullback a).obj M ≅ M')
    (ρ' : (Scheme.Modules.pullback b).obj M' ≅ M'')
    (ρ'' : (Scheme.Modules.pullback k).obj M ≅ M'')
    (hσ : σ = (Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ρ)
    (hσ' : σ' = (Scheme.Modules.restrictFunctorIsoPullback b).app M' ≪≫ ρ')
    (hσ'' : σ'' = (Scheme.Modules.restrictFunctorIsoPullback k).app M ≪≫ ρ'')
    (hρ : (pullbackCompIsoOfEq b a hk M).hom ≫ ρ''.hom =
      (Scheme.Modules.pullback b).map ρ.hom ≫ ρ'.hom) :
    restrictChartIso a σ b hk ≪≫ σ' = σ'' := by
  subst hσ hσ' hσ''
  exact restrictChartIso_pullback_trans a b hk ρ ρ' ρ'' hρ

/-! ### The composition laws of the chart maps, written out -/

section ChartSpelling

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- For opens `U' ≤ U` of `X`, the chart map `U' ×_R Y ⟶ U ×_R Y`, written as a
`AlgebraicGeometry.sourceChangeMap`, followed by the chart of `U` is the chart of `U'`. -/
theorem sourceChangeMap_openSubInclusionOver_comp {U U' : X.left.Opens} (hle : U' ≤ U) :
    sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle) ≫ baseChangeOpenTargetMap R X Y U =
      baseChangeOpenTargetMap R X Y U' :=
  openSubChartMap_comp R X Y hle

/-- For opens `U'' ≤ U' ≤ U` of `X`, the chart maps `U'' ×_R Y ⟶ U' ×_R Y ⟶ U ×_R Y`, written as
`AlgebraicGeometry.sourceChangeMap`s, compose to the chart map `U'' ×_R Y ⟶ U ×_R Y`. -/
theorem sourceChangeMap_openSubInclusionOver_trans {U U' U'' : X.left.Opens} (hle : U' ≤ U)
    (hle' : U'' ≤ U') :
    sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
          (openSubInclusionOver R X hle') ≫
        sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle) =
      sourceChangeMap R (openSubOver R X U) (openSubOver R X U'') Y
        (openSubInclusionOver R X (hle'.trans hle)) :=
  (sourceChangeMap_comp R (openSubOver R X U) (openSubOver R X U') (openSubOver R X U'') Y
      (openSubInclusionOver R X hle) (openSubInclusionOver R X hle')).trans
    (congrArg (fun g : openSubOver R X U'' ⟶ openSubOver R X U ↦
      sourceChangeMap R (openSubOver R X U) (openSubOver R X U'') Y g)
      (openSubInclusionOver_trans R X hle hle'))

end ChartSpelling

/-! ### A family of kernels on the charts of the affine opens -/

/-- **A kernel for each affine open of `X`, with pseudo-functorial comparisons of the inverse
images.**  For each affine open `U` of `X` a quasi-coherent module on the chart `U ×_R Y`, for
each inclusion `U' ≤ U` of affine opens an identification of the inverse image of the kernel of
`U` along the chart map with the kernel of `U'`, and the compatibility of those identifications
along a chain `U'' ≤ U' ≤ U`. -/
structure AffineOpenKernelFamily (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) where
  /-- The kernel attached to an affine open `U` of `X`, on the chart `U ×_R Y`. -/
  ker : ∀ {U : X.left.Opens}, IsAffineOpen U →
    Scheme.QuasicoherentModules (pullback (openSubOver R X U).hom Y.hom)
  /-- The inverse image of the kernel of `U` along the chart map of a smaller affine open `U'`
  is the kernel of `U'`. -/
  iso : ∀ {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U),
    sourceChangeKernel R (openSubOver R X U) (openSubOver R X U') Y
      (openSubInclusionOver R X hle) (ker hU) ≅ ker hU'
  /-- The identifications are compatible along a chain `U'' ≤ U' ≤ U`. -/
  iso_trans : ∀ {U U' U'' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
      (hU'' : IsAffineOpen U'') (hle : U' ≤ U) (hle' : U'' ≤ U'),
    eqToHom (congrArg (fun n : openSubOver R X U'' ⟶ openSubOver R X U ↦
          sourceChangeKernel R (openSubOver R X U) (openSubOver R X U'') Y n (ker hU))
        (openSubInclusionOver_trans R X hle hle').symm) ≫
      (sourceChangeKernelCompIso R (openSubOver R X U) (openSubOver R X U')
          (openSubOver R X U'') Y (openSubInclusionOver R X hle)
          (openSubInclusionOver R X hle') (ker hU)).hom ≫
        sourceChangeKernelMap R (openSubOver R X U') (openSubOver R X U'') Y
            (openSubInclusionOver R X hle') (iso hU hU' hle).hom ≫
          (iso hU' hU'' hle').hom =
      (iso hU hU'' (hle'.trans hle)).hom

namespace AffineOpenKernelFamily

section Basic

variable {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))}
  (D : AffineOpenKernelFamily R X Y)

/-- The identification of the inverse images, read on the underlying sheaves of modules. -/
def rho {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    (Scheme.Modules.pullback (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
        (openSubInclusionOver R X hle))).obj (D.ker hU).obj ≅ (D.ker hU').obj :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent
    (pullback (openSubOver R X U').hom Y.hom).ringCatSheaf)).mapIso (D.iso hU hU' hle)

/-- The hom of `rho` is the underlying morphism of sheaves of modules of the hom of `iso`. -/
theorem rho_hom {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hle : U' ≤ U) :
    (D.rho hU hU' hle).hom =
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent
        (pullback (openSubOver R X U').hom Y.hom).ringCatSheaf)).map
          (D.iso hU hU' hle).hom := rfl

/-- **The cocycle condition of the family, read on the inverse images of the underlying sheaves
of modules.** -/
theorem rho_trans {U U' U'' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') (hle : U' ≤ U) (hle' : U'' ≤ U') :
    (pullbackCompIsoOfEq
          (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
            (openSubInclusionOver R X hle'))
          (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
            (openSubInclusionOver R X hle))
          (sourceChangeMap_openSubInclusionOver_trans R X Y hle hle')
          (D.ker hU).obj).hom ≫ (D.rho hU hU'' (hle'.trans hle)).hom =
      (Scheme.Modules.pullback (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
          (openSubInclusionOver R X hle'))).map
          (D.rho hU hU' hle).hom ≫ (D.rho hU' hU'' hle').hom :=
  pullbackCompIsoOfEq_sourceChangeKernel R Y (openSubInclusionOver R X hle)
    (openSubInclusionOver R X hle') (openSubInclusionOver_trans R X hle hle')
    (D.iso hU hU' hle) (D.iso hU' hU'' hle') (D.iso hU hU'' (hle'.trans hle))
    (D.rho hU hU' hle) (D.rho hU' hU'' hle') (D.rho hU hU'' (hle'.trans hle))
    (D.rho_hom hU hU' hle) (D.rho_hom hU' hU'' hle')
    (D.rho_hom hU hU'' (hle'.trans hle))
    (sourceChangeMap_openSubInclusionOver_trans R X Y hle hle')
    (D.iso_trans hU hU' hU'' hle hle')

/-- The identification of the *restriction* of the kernel of `U` along the chart map of a
smaller affine open `U'` with the kernel of `U'`. -/
def sigma {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    Scheme.Modules.restrict (D.ker hU).obj
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle)) ≅ (D.ker hU').obj :=
  (Scheme.Modules.restrictFunctorIsoPullback (sourceChangeMap R (openSubOver R X U)
      (openSubOver R X U') Y (openSubInclusionOver R X hle))).app (D.ker hU).obj ≪≫
    D.rho hU hU' hle

/-- `sigma` is `Scheme.Modules.restrictFunctorIsoPullback` followed by `rho`. -/
theorem sigma_eq {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hle : U' ≤ U) :
    D.sigma hU hU' hle =
      (Scheme.Modules.restrictFunctorIsoPullback (sourceChangeMap R (openSubOver R X U)
        (openSubOver R X U') Y (openSubInclusionOver R X hle))).app (D.ker hU).obj ≪≫
          D.rho hU hU' hle := rfl

/-- **The comparisons of the restrictions along the chart maps are pseudo-functorial.** -/
theorem sigma_trans {U U' U'' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') (hle : U' ≤ U) (hle' : U'' ≤ U') :
    restrictChartIso (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
            (openSubInclusionOver R X hle)) (D.sigma hU hU' hle)
          (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
            (openSubInclusionOver R X hle'))
          (sourceChangeMap_openSubInclusionOver_trans R X Y hle hle') ≪≫
        D.sigma hU' hU'' hle' =
      D.sigma hU hU'' (hle'.trans hle) :=
  restrictChartIso_trans_of_eq
    (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
      (openSubInclusionOver R X hle))
    (sourceChangeMap R (openSubOver R X U') (openSubOver R X U'') Y
      (openSubInclusionOver R X hle'))
    (sourceChangeMap_openSubInclusionOver_trans R X Y hle hle')
    (D.sigma hU hU' hle) (D.sigma hU' hU'' hle') (D.sigma hU hU'' (hle'.trans hle))
    (D.rho hU hU' hle) (D.rho hU' hU'' hle') (D.rho hU hU'' (hle'.trans hle))
    (D.sigma_eq hU hU' hle) (D.sigma_eq hU' hU'' hle')
    (D.sigma_eq hU hU'' (hle'.trans hle)) (D.rho_trans hU hU' hU'' hle hle')

end Basic

/-! ### The comparison of two charts -/

section Charts

variable {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))}
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (D : AffineOpenKernelFamily R X Y)

/-- **The comparison, over an open contained in both charts, of the restrictions of the kernels
of two affine opens `U` and `V`**, taken through the chart of the affine open `U ⊓ V`. -/
def middleIso {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    Scheme.Modules.restrict (D.ker hU).obj
        (openLift (baseChangeOpenTargetMap R X Y U) hZU) ≅
      Scheme.Modules.restrict (D.ker hV).obj
        (openLift (baseChangeOpenTargetMap R X Y V) hZV) :=
  restrictMiddleIso (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
    (baseChangeOpenTargetMap R X Y (U ⊓ V))
    (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_left : U ⊓ V ≤ U))
    (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_right : U ⊓ V ≤ V))
    (D.sigma hU (hU.inf hV) inf_le_left) (D.sigma hV (hU.inf hV) inf_le_right)
    ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV)) hZU hZV

/-- **The cocycle condition of the comparisons of the restrictions along the factorisations:**
over an open `Z` contained in the charts of `U`, `V` and `W`, the comparison for `(U, V)`
followed by the comparison for `(V, W)` is the comparison for `(U, W)`. -/
theorem middleIso_trans {U V W : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange)
    (hZW : Z ≤ (baseChangeOpenTargetMap R X Y W).opensRange) :
    D.middleIso hU hV hZU hZV ≪≫ D.middleIso hV hW hZV hZW = D.middleIso hU hW hZU hZW := by
  have hUVW : IsAffineOpen (U ⊓ V ⊓ W) := (hU.inf hV).inf hW
  have hZT : Z ≤ (baseChangeOpenTargetMap R X Y (U ⊓ V ⊓ W)).opensRange :=
    (opensRange_baseChangeOpenTargetMap_inf R X Y (U ⊓ V) W).le.trans'
      (le_inf ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV)) hZW)
  have hTU : U ⊓ V ⊓ W ≤ U := le_trans inf_le_left inf_le_left
  have hTV : U ⊓ V ⊓ W ≤ V := le_trans inf_le_left inf_le_right
  have hTW : U ⊓ V ⊓ W ≤ W := inf_le_right
  have key : ∀ {P Q : X.left.Opens} (hP : IsAffineOpen P) (hQ : IsAffineOpen Q)
      (hZP : Z ≤ (baseChangeOpenTargetMap R X Y P).opensRange)
      (hZQ : Z ≤ (baseChangeOpenTargetMap R X Y Q).opensRange)
      (hTP : U ⊓ V ⊓ W ≤ P) (hTQ : U ⊓ V ⊓ W ≤ Q),
      D.middleIso hP hQ hZP hZQ =
        restrictMiddleIso (baseChangeOpenTargetMap R X Y P) (baseChangeOpenTargetMap R X Y Q)
          (baseChangeOpenTargetMap R X Y (U ⊓ V ⊓ W))
          (sourceChangeMap_openSubInclusionOver_comp R X Y hTP)
          (sourceChangeMap_openSubInclusionOver_comp R X Y hTQ)
          (D.sigma hP hUVW hTP) (D.sigma hQ hUVW hTQ) hZT hZP hZQ := by
    intro P Q hP hQ hZP hZQ hTP hTQ
    exact (restrictMiddleIso_refine (baseChangeOpenTargetMap R X Y P)
      (baseChangeOpenTargetMap R X Y Q) (baseChangeOpenTargetMap R X Y (P ⊓ Q))
      (baseChangeOpenTargetMap R X Y (U ⊓ V ⊓ W))
      (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_left : P ⊓ Q ≤ P))
      (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_right : P ⊓ Q ≤ Q))
      (sourceChangeMap_openSubInclusionOver_comp R X Y (le_inf hTP hTQ))
      (sourceChangeMap_openSubInclusionOver_trans R X Y inf_le_left (le_inf hTP hTQ))
      (sourceChangeMap_openSubInclusionOver_trans R X Y inf_le_right (le_inf hTP hTQ))
      (D.sigma hP (hP.inf hQ) inf_le_left) (D.sigma hQ (hP.inf hQ) inf_le_right)
      (D.sigma (hP.inf hQ) hUVW (le_inf hTP hTQ)) (D.sigma hP hUVW hTP) (D.sigma hQ hUVW hTQ)
      (D.sigma_trans hP (hP.inf hQ) hUVW inf_le_left (le_inf hTP hTQ))
      (D.sigma_trans hQ (hP.inf hQ) hUVW inf_le_right (le_inf hTP hTQ)) hZT hZP hZQ).symm
  rw [key hU hV hZU hZV hTU hTV, key hV hW hZV hZW hTV hTW, key hU hW hZU hZW hTU hTW]
  exact restrictMiddleIso_trans (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y W)
    (baseChangeOpenTargetMap R X Y (U ⊓ V ⊓ W))
    (sourceChangeMap_openSubInclusionOver_comp R X Y hTU)
    (sourceChangeMap_openSubInclusionOver_comp R X Y hTV)
    (sourceChangeMap_openSubInclusionOver_comp R X Y hTW)
    (D.sigma hU hUVW hTU) (D.sigma hV hUVW hTV) (D.sigma hW hUVW hTW) hZT hZU hZV hZW

/-- **The comparison of the two charts over an open contained in both:** the identification of
the restrictions to `Z` of the pushforwards of the kernels of `U` and `V` along their charts. -/
def chartComparison {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    (Scheme.Modules.restrict ((Scheme.Modules.pushforward
          (baseChangeOpenTargetMap R X Y U)).obj (D.ker hU).obj) Z.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward
          (baseChangeOpenTargetMap R X Y V)).obj (D.ker hV).obj) Z.ι) :=
  restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (D.ker hU).obj (D.ker hV).obj hZU hZV
    (D.middleIso hU hV hZU hZV)

/-- The comparison of two charts over an open is compatible with shrinking the open. -/
theorem restrictLocal_chartComparison {U V : X.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) {Z Z' : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) (hZ' : Z' ≤ Z) :
    restrictLocal (D.chartComparison hU hV hZU hZV).hom hZ' =
      (D.chartComparison hU hV (hZ'.trans hZU) (hZ'.trans hZV)).hom := by
  refine (restrictLocal_restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y V) (D.ker hU).obj (D.ker hV).obj hZU hZV hZ'
    (D.middleIso hU hV hZU hZV)).trans ?_
  exact congrArg (fun e ↦ (restrictPushforwardIsoOfRestrictIso
      (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y V)
      (D.ker hU).obj (D.ker hV).obj (hZ'.trans hZU) (hZ'.trans hZV) e).hom)
    (openLiftShrinkIso_restrictMiddleIso (baseChangeOpenTargetMap R X Y U)
      (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y (U ⊓ V))
      (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_left : U ⊓ V ≤ U))
      (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_right : U ⊓ V ≤ V))
      (D.sigma hU (hU.inf hV) inf_le_left) (D.sigma hV (hU.inf hV) inf_le_right)
      ((opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV))
      hZU hZV hZ')

/-- The comparisons of the charts over an open contained in three of them compose. -/
theorem chartComparison_trans {U V W : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange)
    (hZW : Z ≤ (baseChangeOpenTargetMap R X Y W).opensRange) :
    (D.chartComparison hU hV hZU hZV).hom ≫ (D.chartComparison hV hW hZV hZW).hom =
      (D.chartComparison hU hW hZU hZW).hom :=
  (restrictPushforwardIsoOfRestrictIso_trans (baseChangeOpenTargetMap R X Y U)
      (baseChangeOpenTargetMap R X Y V) (baseChangeOpenTargetMap R X Y W) (D.ker hU).obj
      (D.ker hV).obj (D.ker hW).obj hZU hZV hZW (D.middleIso hU hV hZU hZV)
      (D.middleIso hV hW hZV hZW)).trans
    (congrArg (fun e ↦ (restrictPushforwardIsoOfRestrictIso (baseChangeOpenTargetMap R X Y U)
        (baseChangeOpenTargetMap R X Y W) (D.ker hU).obj (D.ker hW).obj hZU hZW e).hom)
      (D.middleIso_trans hU hV hW hZU hZV hZW))

/-! ### The glued kernel -/

/-- **The glueing datum of a family of kernels on the charts of the affine opens of `X`.**  The
charts are the open immersions `U ×_R Y ⟶ X ×_R Y` for `U` an affine open of `X`, the module on
the `U`-th chart is the kernel of `U`, and the comparison over an open contained in two charts is
`AlgebraicGeometry.AffineOpenKernelFamily.chartComparison`. -/
def glueData :
    RestrictIsoGlueData (pullback X.hom Y.hom)
      (fun U : X.left.affineOpens ↦ baseChangeOpenTargetMap R X Y (U : X.left.Opens)) where
  mod U := (D.ker U.2).obj
  iso U V {_Z} hZU hZV := D.chartComparison U.2 V.2 hZU hZV
  iso_restrict U V {_Z _Z'} hZU hZV hZ' := D.restrictLocal_chartComparison U.2 V.2 hZU hZV hZ'
  iso_trans U V W {_Z} hZU hZV hZW := D.chartComparison_trans U.2 V.2 W.2 hZU hZV hZW

/-- **The quasi-coherent module on `X ×_R Y` glued from a family of kernels on the charts of the
affine opens of `X`.** -/
def gluedKernel : Scheme.QuasicoherentModules (pullback X.hom Y.hom) :=
  ⟨D.glueData.glued,
    D.glueData.isQuasicoherent_glued (iSup_opensRange_baseChangeOpenTargetMap R X Y)
      fun U ↦ (D.ker U.2).property⟩

/-- **The glued kernel restricts along the chart of an affine open `U` of `X` to the kernel
of `U`.** -/
def gluedChartIso (U : X.left.affineOpens) :
    Scheme.Modules.restrict D.gluedKernel.obj
        (baseChangeOpenTargetMap R X Y (U : X.left.Opens)) ≅ (D.ker U.2).obj :=
  D.glueData.chartIso U

end Charts

end AffineOpenKernelFamily

/-! ### The family of the kernels of the affine opens, and the glued kernel of Tag 0GPA -/

section Glued

attribute [local instance] isOpenImmersion_openSubOverHom_left

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- **The family of the kernels of the affine opens of `X`.**  Its three fields are
`AlgebraicGeometry.openKernel`, `AlgebraicGeometry.openKernelRestrictIso` and the cocycle
condition `AlgebraicGeometry.openKernelRestrictIso_trans`. -/
def openKernelFamily : AffineOpenKernelFamily R X Y where
  ker {_U} hU := openKernel R X Y F hF hU
  iso {_U _U'} hU hU' hle := openKernelRestrictIso R X Y F hF hU hU' hle
  iso_trans {_U _U' _U''} hU hU' hU'' hle hle' :=
    openKernelRestrictIso_trans R X Y F hF hU hU' hU'' hle hle'

/-- The kernel of `U` in `AlgebraicGeometry.openKernelFamily` is `AlgebraicGeometry.openKernel`. -/
@[simp] theorem openKernelFamily_ker {U : X.left.Opens} (hU : IsAffineOpen U) :
    (openKernelFamily R X Y F hF).ker hU = openKernel R X Y F hF hU := rfl

/-- **The quasi-coherent module on `X ×_R Y` glued from the kernels of the affine opens of
`X`:** construction (1) of [Stacks, Tag 0GPA]. -/
def gluedKernel : Scheme.QuasicoherentModules (pullback X.hom Y.hom) :=
  (openKernelFamily R X Y F hF).gluedKernel

/-- **The glued kernel of [Stacks, Tag 0GPA] restricts along the chart of an affine open `U` of
`X` to the kernel attached to `U`.** -/
def gluedKernelChartIso (U : X.left.affineOpens) :
    Scheme.Modules.restrict (gluedKernel R X Y F hF).obj
        (baseChangeOpenTargetMap R X Y (U : X.left.Opens)) ≅
      (openKernel R X Y F hF U.2).obj :=
  (openKernelFamily R X Y F hF).gluedChartIso U

end Glued

end AlgebraicGeometry

end
