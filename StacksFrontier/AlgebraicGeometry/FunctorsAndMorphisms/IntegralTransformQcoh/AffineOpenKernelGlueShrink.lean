module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartShrink
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineOpenKernelGlue

/-!
# The glued kernel compared on two nested affine opens of `X`

`AlgebraicGeometry.AffineOpenKernelFamily.gluedChartIso` identifies the restriction of the glued
kernel along the chart of an affine open `U` of `X` with the kernel the family attached to `U`.
This file proves that those identifications are compatible with shrinking `U`:  for affine opens
`U' ≤ U`, restricting the identification at `U` further along the chart map of `U' ≤ U` and
following it with the family's own comparison `AffineOpenKernelFamily.sigma` gives the
identification at `U'`.

## Main definitions

* `AlgebraicGeometry.AffineOpenKernelFamily.gluedRho` and
  `AlgebraicGeometry.AffineOpenKernelFamily.gluedSourceChangeIso`: the inverse image of the glued
  kernel along the chart of an affine open of `X` is the kernel of that open, on the underlying
  sheaves of modules and on the kernels.

## Main results

* `AlgebraicGeometry.restrictChartIso_eq_id_of_trans`: a unital identification of the restriction
  along a self-map with the module itself induces the identity on a chart.
* `AlgebraicGeometry.AffineOpenKernelFamily.sigma_self_chart_hom`: the family's comparison at
  `U ≤ U`, read on the chart of `U`, is the identity.
* `AlgebraicGeometry.AffineOpenKernelFamily.middleIso_le`: for `U' ≤ U` the comparison of the two
  charts over the range of the chart of `U'` is the family's own comparison, read on that range.
* `AlgebraicGeometry.AffineOpenKernelFamily.gluedChartIso_shrink`: the identifications of the glued
  kernel on two nested affine opens of `X` agree.
* `AlgebraicGeometry.sourceChangeKernel_cocycle_of_pullbackCompIsoOfEq`: the cocycle condition of
  a family of identifications of inverse images of quasi-coherent kernels, from the same
  condition on the underlying sheaves of modules.
* `AlgebraicGeometry.AffineOpenKernelFamily.pullbackCompIsoOfEq_gluedRho`: the cocycle condition of
  the identifications `gluedRho`, read on the inverse images.
* `AlgebraicGeometry.AffineOpenKernelFamily.gluedSourceChangeIso_trans`: the cocycle condition of
  the identifications `gluedSourceChangeIso`, on the kernels themselves.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A unital identification of the restriction along a self-map with the module itself induces the
identity on a chart. Let `p : T ⟶ T` be an open immersion with `p ≫ p = p` and let `s : N|_p ≅ N`
satisfy the unit law `restrictChartIso p s p ≪≫ s = s`. Then for any chart `c : W ⟶ T` fixed by `p`
the induced comparison of `N|_c` with itself is the identity. -/
theorem restrictChartIso_eq_id_of_trans {T W : Scheme.{u}} {p : T ⟶ T} [IsOpenImmersion p]
    (hp : p ≫ p = p) {N : T.Modules} (s : Scheme.Modules.restrict N p ≅ N)
    (hs : restrictChartIso p s p hp ≪≫ s = s)
    (c : W ⟶ T) [IsOpenImmersion c] (hc : c ≫ p = c) :
    (restrictChartIso p s c hc).hom = 𝟙 (Scheme.Modules.restrict N c) := by
  have h := restrictChartIso_trans p p hp s s c hc hc
  rw [hs] at h
  have h' : 𝟙 (Scheme.Modules.restrict N c) ≫ (restrictChartIso p s c hc).hom =
      (restrictChartIso p s c hc).hom ≫ (restrictChartIso p s c hc).hom :=
    (Category.id_comp _).trans (congrArg Iso.hom h)
  exact ((cancel_mono (restrictChartIso p s c hc).hom).mp h').symm

/-- The cocycle condition of a family of identifications of inverse images of quasi-coherent
kernels follows from the same condition on the underlying sheaves of modules. -/
theorem sourceChangeKernel_cocycle_of_pullbackCompIsoOfEq (R : Type u) [CommRing R]
    (Y : Over (Spec (.of R))) {W V V' : Over (Spec (.of R))} (j : V ⟶ W) (j' : V' ⟶ V)
    {m : V' ⟶ W} (hm : j' ≫ j = m)
    {K : Scheme.QuasicoherentModules (pullback W.hom Y.hom)}
    {L : Scheme.QuasicoherentModules (pullback V.hom Y.hom)}
    {N : Scheme.QuasicoherentModules (pullback V'.hom Y.hom)}
    (ρ : sourceChangeKernel R W V Y j K ≅ L) (ρ' : sourceChangeKernel R V V' Y j' L ≅ N)
    (ρ'' : sourceChangeKernel R W V' Y m K ≅ N)
    (σ : (Scheme.Modules.pullback (sourceChangeMap R W V Y j)).obj K.obj ≅ L.obj)
    (σ' : (Scheme.Modules.pullback (sourceChangeMap R V V' Y j')).obj L.obj ≅ N.obj)
    (σ'' : (Scheme.Modules.pullback (sourceChangeMap R W V' Y m)).obj K.obj ≅ N.obj)
    (hσ : σ.hom = (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback V.hom Y.hom).ringCatSheaf)).map ρ.hom)
    (hσ' : σ'.hom = (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback V'.hom Y.hom).ringCatSheaf)).map ρ'.hom)
    (hσ'' : σ''.hom = (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback V'.hom Y.hom).ringCatSheaf)).map ρ''.hom)
    (hk : sourceChangeMap R V V' Y j' ≫ sourceChangeMap R W V Y j =
      sourceChangeMap R W V' Y m)
    (h : (pullbackCompIsoOfEq (sourceChangeMap R V V' Y j')
            (sourceChangeMap R W V Y j) hk K.obj).hom ≫ σ''.hom =
      (Scheme.Modules.pullback (sourceChangeMap R V V' Y j')).map σ.hom ≫ σ'.hom) :
    eqToHom (congrArg (fun q : V' ⟶ W ↦ sourceChangeKernel R W V' Y q K) hm.symm) ≫
        (sourceChangeKernelCompIso R W V V' Y j j' K).hom ≫
          sourceChangeKernelMap R V V' Y j' ρ.hom ≫ ρ'.hom = ρ''.hom := by
  subst hm
  have key : (pullbackCompIsoOfEq (sourceChangeMap R V V' Y j')
          (sourceChangeMap R W V Y j) (sourceChangeMap_comp R W V V' Y j j') K.obj).inv ≫
        (Scheme.Modules.pullback (sourceChangeMap R V V' Y j')).map σ.hom ≫ σ'.hom =
      σ''.hom :=
    (congrArg ((pullbackCompIsoOfEq (sourceChangeMap R V V' Y j')
        (sourceChangeMap R W V Y j) (sourceChangeMap_comp R W V V' Y j j') K.obj).inv ≫ ·)
      h.symm).trans (Iso.inv_hom_id_assoc _ _)
  rw [hσ, hσ', hσ''] at key
  rw [eqToHom_refl, Category.id_comp]
  refine (ObjectProperty.ι (SheafOfModules.isQuasicoherent
    (pullback V'.hom Y.hom).ringCatSheaf)).map_injective (Eq.trans ?_ key)
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- `AlgebraicGeometry.sourceChangeMap_openSubInclusionOver_comp` with the chart of the larger
open written out as a `AlgebraicGeometry.sourceChangeMap` on both sides, rather than through the
abbreviation `AlgebraicGeometry.baseChangeOpenTargetMap`. -/
theorem sourceChangeMap_openSubOverHom_comp (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) {U U' : X.left.Opens} (hle : U' ≤ U) :
    sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle) ≫
        sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U) =
      sourceChangeMap R X (openSubOver R X U') Y (openSubOverHom R X U') :=
  sourceChangeMap_openSubInclusionOver_comp R X Y hle

namespace AffineOpenKernelFamily

section Shrink

variable {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))}
  (D : AffineOpenKernelFamily R X Y)

/-- The chart map of `U ≤ U` is idempotent. -/
theorem sourceChangeMap_openSubInclusionOver_self_comp (U : X.left.Opens) :
    sourceChangeMap R (openSubOver R X U) (openSubOver R X U) Y
          (openSubInclusionOver R X (le_refl U)) ≫
        sourceChangeMap R (openSubOver R X U) (openSubOver R X U) Y
          (openSubInclusionOver R X (le_refl U)) =
      sourceChangeMap R (openSubOver R X U) (openSubOver R X U) Y
        (openSubInclusionOver R X (le_refl U)) :=
  sourceChangeMap_openSubInclusionOver_trans R X Y (le_refl U) (le_refl U)

/-- The chart of `U` is fixed by the chart map of `U ≤ U`, read on the factorisation of the range
of that chart. -/
theorem openLift_comp_sourceChangeMap_self (U : X.left.Opens) :
    openLift (baseChangeOpenTargetMap R X Y U)
          (le_refl (baseChangeOpenTargetMap R X Y U).opensRange) ≫
        sourceChangeMap R (openSubOver R X U) (openSubOver R X U) Y
          (openSubInclusionOver R X (le_refl U)) =
      openLift (baseChangeOpenTargetMap R X Y U)
        (le_refl (baseChangeOpenTargetMap R X Y U).opensRange) :=
  eq_openLift (baseChangeOpenTargetMap R X Y U) _ _ (by
    rw [Category.assoc, sourceChangeMap_openSubInclusionOver_comp R X Y (le_refl U),
      openLift_comp])

/-- The family's comparison at `U ≤ U`, read on the chart of `U`, is the identity. -/
theorem sigma_self_chart_hom {U : X.left.Opens} (hU : IsAffineOpen U) :
    (restrictChartIso
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U) Y
          (openSubInclusionOver R X (le_refl U)))
        (D.sigma hU hU (le_refl U))
        (openLift (baseChangeOpenTargetMap R X Y U)
          (le_refl (baseChangeOpenTargetMap R X Y U).opensRange))
        (openLift_comp_sourceChangeMap_self (R := R) (Y := Y) U)).hom = 𝟙 _ :=
  restrictChartIso_eq_id_of_trans
    (sourceChangeMap_openSubInclusionOver_self_comp (R := R) (Y := Y) U)
    (D.sigma hU hU (le_refl U)) (D.sigma_trans hU hU hU (le_refl U) (le_refl U)) _
    (openLift_comp_sourceChangeMap_self (R := R) (Y := Y) U)

variable [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- For `U' ≤ U` the comparison `AlgebraicGeometry.AffineOpenKernelFamily.middleIso` of the two
charts over the range of the chart of `U'` is the family's own comparison, read on that range. -/
theorem middleIso_le {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hle : U' ≤ U) :
    D.middleIso hU hU'
        (opensRange_le_of_comp (baseChangeOpenTargetMap R X Y U)
          (sourceChangeMap_openSubInclusionOver_comp R X Y hle))
        (le_refl (baseChangeOpenTargetMap R X Y U').opensRange) =
      restrictChartIso
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle))
        (D.sigma hU hU' hle)
        (openLift (baseChangeOpenTargetMap R X Y U')
          (le_refl (baseChangeOpenTargetMap R X Y U').opensRange))
        (openLift_comp_eq (baseChangeOpenTargetMap R X Y U)
          (sourceChangeMap_openSubInclusionOver_comp R X Y hle)
          (le_refl (baseChangeOpenTargetMap R X Y U').opensRange)) := by
  have hT : U' ≤ U ⊓ U' := le_inf hle le_rfl
  have hij : (baseChangeOpenTargetMap R X Y U').opensRange ≤
      (baseChangeOpenTargetMap R X Y U).opensRange :=
    opensRange_le_of_comp (baseChangeOpenTargetMap R X Y U)
      (sourceChangeMap_openSubInclusionOver_comp R X Y hle)
  have hrefine := restrictMiddleIso_refine (baseChangeOpenTargetMap R X Y U)
    (baseChangeOpenTargetMap R X Y U') (baseChangeOpenTargetMap R X Y (U ⊓ U'))
    (baseChangeOpenTargetMap R X Y U')
    (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_left : U ⊓ U' ≤ U))
    (sourceChangeMap_openSubInclusionOver_comp R X Y (inf_le_right : U ⊓ U' ≤ U'))
    (sourceChangeMap_openSubInclusionOver_comp R X Y hT)
    (sourceChangeMap_openSubInclusionOver_trans R X Y (inf_le_left : U ⊓ U' ≤ U) hT)
    (sourceChangeMap_openSubInclusionOver_trans R X Y (inf_le_right : U ⊓ U' ≤ U') hT)
    (D.sigma hU (hU.inf hU') inf_le_left) (D.sigma hU' (hU.inf hU') inf_le_right)
    (D.sigma (hU.inf hU') hU' hT) (D.sigma hU hU' hle) (D.sigma hU' hU' (le_refl U'))
    (D.sigma_trans hU (hU.inf hU') hU' inf_le_left hT)
    (D.sigma_trans hU' (hU.inf hU') hU' inf_le_right hT)
    (le_refl (baseChangeOpenTargetMap R X Y U').opensRange) hij
    (le_refl (baseChangeOpenTargetMap R X Y U').opensRange)
  refine Iso.ext ((congrArg Iso.hom hrefine).symm.trans ?_)
  rw [← Category.comp_id (restrictChartIso _ (D.sigma hU hU' hle) _ _).hom]
  exact congrArg (CategoryStruct.comp _)
    (Iso.inv_ext' ((Category.comp_id _).trans (D.sigma_self_chart_hom hU'))).symm

/-- The identifications of the glued kernel on two nested affine opens of `X` agree. For affine
opens `U' ≤ U` of `X`, restricting the identification of the glued kernel with the kernel of `U`
further along the chart map of `U' ≤ U`, and following it with the family's comparison
`AlgebraicGeometry.AffineOpenKernelFamily.sigma`, gives the identification of the glued kernel with
the kernel of `U'`. -/
theorem gluedChartIso_shrink {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hle : U' ≤ U) :
    restrictChartIso (baseChangeOpenTargetMap R X Y U) (D.gluedChartIso ⟨U, hU⟩)
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle))
        (sourceChangeMap_openSubInclusionOver_comp R X Y hle) ≪≫
      D.sigma hU hU' hle = D.gluedChartIso ⟨U', hU'⟩ :=
  D.glueData.restrictChartIso_chartIso ⟨U, hU⟩ ⟨U', hU'⟩
    (sourceChangeMap_openSubInclusionOver_comp R X Y hle) (D.sigma hU hU' hle)
    (congrArg (fun e ↦ restrictPushforwardIsoOfRestrictIso
        (baseChangeOpenTargetMap R X Y U) (baseChangeOpenTargetMap R X Y U')
        (D.ker hU).obj (D.ker hU').obj
        (opensRange_le_of_comp (baseChangeOpenTargetMap R X Y U)
          (sourceChangeMap_openSubInclusionOver_comp R X Y hle))
        (le_refl (baseChangeOpenTargetMap R X Y U').opensRange) e)
      (D.middleIso_le hU hU' hle))

/-- The identification of the inverse image of the glued kernel along the chart of an affine open
`U` of `X` with the kernel of `U`, read on the underlying sheaves of modules.  This is the
underlying module isomorphism of `AlgebraicGeometry.gluedKernelSourceChangeIso`. -/
def gluedRho {U : X.left.Opens} (hU : IsAffineOpen U) :
    (Scheme.Modules.pullback (sourceChangeMap R X (openSubOver R X U) Y
        (openSubOverHom R X U))).obj D.gluedKernel.obj ≅ (D.ker hU).obj :=
  ((Scheme.Modules.restrictFunctorIsoPullback (baseChangeOpenTargetMap R X Y U)).app
      D.gluedKernel.obj).symm ≪≫ D.gluedChartIso ⟨U, hU⟩

/-- The identification of the restriction along the chart of `U` with the inverse image, followed
by `gluedRho`, is `gluedChartIso`. -/
theorem restrictFunctorIsoPullback_trans_gluedRho {U : X.left.Opens} (hU : IsAffineOpen U) :
    (Scheme.Modules.restrictFunctorIsoPullback (sourceChangeMap R X (openSubOver R X U) Y
          (openSubOverHom R X U))).app D.gluedKernel.obj ≪≫ D.gluedRho hU =
      D.gluedChartIso ⟨U, hU⟩ :=
  Iso.ext (((Scheme.Modules.restrictFunctorIsoPullback
    (sourceChangeMap R X (openSubOver R X U) Y
      (openSubOverHom R X U))).app D.gluedKernel.obj).hom_inv_id_assoc
      (D.gluedChartIso ⟨U, hU⟩).hom)

/-- The cocycle condition of the glued kernel's chart identifications, read on the inverse images.
For affine opens `U' ≤ U` of `X`, the comparison of the two iterated inverse images of the glued
kernel carries the identification at `U'` to the inverse image along the chart map of the
identification at `U`, followed by the family's own comparison. -/
theorem pullbackCompIsoOfEq_gluedRho {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    (pullbackCompIsoOfEq
          (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
            (openSubInclusionOver R X hle))
          (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))
          (sourceChangeMap_openSubInclusionOver_comp R X Y hle)
          D.gluedKernel.obj).hom ≫ (D.gluedRho hU').hom =
      (Scheme.Modules.pullback (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
            (openSubInclusionOver R X hle))).map (D.gluedRho hU).hom ≫
        (D.rho hU hU' hle).hom :=
  pullbackCompIsoOfEq_hom_comp_of_restrictChartIso
    (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))
    (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
      (openSubInclusionOver R X hle))
    (sourceChangeMap_openSubInclusionOver_comp R X Y hle)
    (D.gluedRho hU) (D.rho hU hU' hle) (D.gluedRho hU')
    (by
      rw [D.restrictFunctorIsoPullback_trans_gluedRho hU,
        D.restrictFunctorIsoPullback_trans_gluedRho hU', ← D.sigma_eq hU hU' hle]
      exact D.gluedChartIso_shrink hU hU' hle)

/-- The inverse image of the glued kernel along the chart of an affine open `U` of `X` is the
kernel of `U`. This is `AlgebraicGeometry.gluedKernelSourceChangeIso` for an arbitrary family of
kernels on the charts. -/
def gluedSourceChangeIso {U : X.left.Opens} (hU : IsAffineOpen U) :
    sourceChangeKernel R X (openSubOver R X U) Y (openSubOverHom R X U) D.gluedKernel ≅
      D.ker hU :=
  ObjectProperty.isoMk _ (D.gluedRho hU)

/-- `gluedRho` is the morphism of underlying sheaves of modules of `gluedSourceChangeIso`. -/
theorem map_gluedSourceChangeIso_hom {U : X.left.Opens} (hU : IsAffineOpen U) :
    (D.gluedRho hU).hom =
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent
        (pullback (openSubOver R X U).hom Y.hom).ringCatSheaf)).map
          (D.gluedSourceChangeIso hU).hom := rfl

/-- `AlgebraicGeometry.AffineOpenKernelFamily.gluedChartIso_shrink` with the chart of the larger
open written out as a `AlgebraicGeometry.sourceChangeMap` rather than through the abbreviation
`AlgebraicGeometry.baseChangeOpenTargetMap`. -/
theorem gluedChartIso_shrink' {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    restrictChartIso (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))
        (D.gluedChartIso ⟨U, hU⟩)
        (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
          (openSubInclusionOver R X hle))
        (sourceChangeMap_openSubOverHom_comp R X Y hle) ≪≫
      D.sigma hU hU' hle = D.gluedChartIso ⟨U', hU'⟩ :=
  D.gluedChartIso_shrink hU hU' hle

/-- `AlgebraicGeometry.AffineOpenKernelFamily.pullbackCompIsoOfEq_gluedRho` with the chart of the
larger open written out as a `AlgebraicGeometry.sourceChangeMap`. -/
theorem pullbackCompIsoOfEq_gluedRho' {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    (pullbackCompIsoOfEq
          (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
            (openSubInclusionOver R X hle))
          (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))
          (sourceChangeMap_openSubOverHom_comp R X Y hle)
          D.gluedKernel.obj).hom ≫ (D.gluedRho hU').hom =
      (Scheme.Modules.pullback (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
            (openSubInclusionOver R X hle))).map (D.gluedRho hU).hom ≫
        (D.rho hU hU' hle).hom :=
  pullbackCompIsoOfEq_hom_comp_of_restrictChartIso
    (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))
    (sourceChangeMap R (openSubOver R X U) (openSubOver R X U') Y
      (openSubInclusionOver R X hle))
    (sourceChangeMap_openSubOverHom_comp R X Y hle)
    (D.gluedRho hU) (D.rho hU hU' hle) (D.gluedRho hU')
    (by
      rw [D.restrictFunctorIsoPullback_trans_gluedRho hU,
        D.restrictFunctorIsoPullback_trans_gluedRho hU', ← D.sigma_eq hU hU' hle]
      exact D.gluedChartIso_shrink' hU hU' hle)

/-- The cocycle condition of the identifications of the inverse images of the glued kernel, on the
kernels themselves. For affine opens `U' ≤ U` of `X`, the comparison of the two iterated inverse
images of the glued kernel carries the identification at `U'` to the inverse image along the chart
map of the identification at `U`, followed by the family's own comparison. -/
theorem gluedSourceChangeIso_trans {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    eqToHom (congrArg (fun q : openSubOver R X U' ⟶ X ↦
          sourceChangeKernel R X (openSubOver R X U') Y q D.gluedKernel)
        (openSubInclusionOver_comp R X hle).symm) ≫
        (sourceChangeKernelCompIso R X (openSubOver R X U) (openSubOver R X U') Y
            (openSubOverHom R X U) (openSubInclusionOver R X hle) D.gluedKernel).hom ≫
          sourceChangeKernelMap R (openSubOver R X U) (openSubOver R X U') Y
              (openSubInclusionOver R X hle) (D.gluedSourceChangeIso hU).hom ≫
            (D.iso hU hU' hle).hom =
      (D.gluedSourceChangeIso hU').hom :=
  sourceChangeKernel_cocycle_of_pullbackCompIsoOfEq R Y (openSubOverHom R X U)
    (openSubInclusionOver R X hle) (openSubInclusionOver_comp R X hle)
    (D.gluedSourceChangeIso hU) (D.iso hU hU' hle) (D.gluedSourceChangeIso hU')
    (D.gluedRho hU) (D.rho hU hU' hle) (D.gluedRho hU')
    (D.map_gluedSourceChangeIso_hom hU) (D.rho_hom hU hU' hle)
    (D.map_gluedSourceChangeIso_hom hU')
    (sourceChangeMap_openSubOverHom_comp R X Y hle)
    (D.pullbackCompIsoOfEq_gluedRho' hU hU' hle)

end Shrink

end AffineOpenKernelFamily

end AlgebraicGeometry

end
