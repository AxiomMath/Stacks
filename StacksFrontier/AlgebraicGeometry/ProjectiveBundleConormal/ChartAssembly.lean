module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartSourceGenerator
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.RestrictTensorSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartConormalTarget
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatioSplit
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTrivialisationPairing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.TildePullbackHomExt
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic

/-!
# Clause (b) of Tag 0B3V: the conormal sheaf of a section of a projective bundle

For a quasi-coherent module `ℰ` on a scheme `X` with an invertible quotient `q : ℰ → 𝓛`, and the
section `σ : X ⟶ 𝐏(ℰ)` that quotient names, the canonical map
`Ker(q) ⊗ 𝓛^{⊗ -1} ⟶ 𝒞_σ` of [Stacks, Tag 0B3V] is an isomorphism. This file assembles the two
halves of the chart computation — whose inventory is the "What is not done here" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting` — and closes the clause.

## Main results

* `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap`: **clause (b)**, as an
  `IsIso` statement. The tag is registered once, on
  `Stacks.RelativeProj.projectiveBundle_sections_classification` in
  `StacksFrontier/AlgebraicGeometry/ProjectiveBundleConormal/SectionsClause.lean`, stated on
  `Stacks.RelativeProj.projectiveBundle`.
* `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_restrict_eq_taut`: **the chart equation**,
  i.e. the hypothesis `h` of
  `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq_taut`.
* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections_hom_apply`: **the
  identification of `specModule F hU` with the sections of `F` over `U` is a restriction map of
  the presheaf of `F`.** Both sides of that identification are sections of `F` over opens between
  `U` and `U.ι ''ᵁ (hU.isoSpec.inv ''ᵁ ⊤)`, and every factor of the identification is a
  restriction map along an equality of opens, so the composite is the one restriction map from the
  larger open to `U`.
* `Stacks.ProjectiveBundleConormal.map_ι_image_top_specModuleChartKerIso_inv`: **the section of
  `ker(q)` over `W` that the source generator formula of clause (b) produces at `k` is the section
  `k` is.** This is what lets the chart coordinate the target half asks for be `k` itself.
* `Stacks.ProjectiveBundleConormal.idealSheafIsoOfIsoSource_inv_restrictIdealSheafIso'_app_ι`: the
  hypothesis `hy'` of the target generator formula at the tautological chart.
* `Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio`:
  **the source half with its section of `ℐ(σ)` pinned to the ratio itself**, through the pinned
  `w₀`.
* `Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι_appLE` and
  `Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso_hom_toOpen_app_ι`: the two sides of
  the coordinate equation, compared in
  `Stacks.ProjectiveBundleConormal.chartIdealSection_idealSheafIsoOfIsoSource_hom_eq_toOpen`.

## Implementation notes

Nothing is rewritten: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio` for why no `rw` occurs on
this layer.

**The target generator formula is applied, never restated.** Supplying its first eleven arguments
and leaving the remaining telescope as binders costs a fraction of a second; restating it at the
chart is a kernel timeout. The same discipline governs
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections`: the identity
`inv ≫ hom = 𝟙` is used at the level of *morphisms*, because
`CategoryTheory.Iso.inv_hom_id_apply` at that isomorphism — the same identity read on a section —
is a deterministic timeout at `whnf`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.SheafOfModules (tensorSectionsAt)

universe u

/-- Two successive restriction maps of a presheaf of modules on opens compose to the one. -/
private theorem map_map_homOfLE_apply {T : TopCat.{u}} {R : (TopologicalSpace.Opens T)ᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules R) {U V W : TopologicalSpace.Opens T} (hUV : U ≤ V) (hVW : V ≤ W)
    (hUW : U ≤ W) (m : M.obj (op W)) :
    M.map (homOfLE hUV).op (M.map (homOfLE hVW).op m) = M.map (homOfLE hUW).op m :=
  (PresheafOfModules.map_comp_apply M (homOfLE hVW).op (homOfLE hUV).op m).symm.trans
    (PresheafOfModules.congr_map_apply M (Subsingleton.elim _ _) m)

namespace Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

/-- **`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections` is a restriction
map of the presheaf.** A section of `specModule F hU` *is*, definitionally, a section of `F` over
`U.ι ''ᵁ (hU.isoSpec.inv ''ᵁ ⊤)`, and each of the three factors of the identification —
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`,
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictSectionsEquiv` and
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.sectionsCongrSelf` — is a restriction map along
an inclusion of opens. Since the hom-sets of `TopologicalSpace.Opens` are subsingletons, the
composite is the restriction map down to `U`.

This is the normalisation that the chart computation of [Stacks, Tag 0B3V] clause 3 needs in order
to recognise the section of `ker(q)` that its source generator formula
`Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde_inv_unit_toOpen` produces; the inclusion
is a parameter, in the discipline of that statement. -/
theorem specModuleIsoSections_hom_apply {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    (hA : U ≤ U.ι ''ᵁ (hU.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)))
    (m : specModule F hU) :
    (specModuleIsoSections F ⟨U, hU⟩).hom m = F.val.map (homOfLE hA).op m := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hTop : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  have hiso : hU.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) =
      (⊤ : (↑U : Scheme.{u}).Opens) := by simp
  have hDEq : U.ι ''ᵁ (hU.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) = U :=
    (congrArg (fun V : (↑U : Scheme.{u}).Opens => U.ι ''ᵁ V) hiso).trans U.ι_image_top
  have hB : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) ≤
      U.ι ''ᵁ (hU.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) :=
    le_of_eq (hTop.trans hDEq.symm)
  have h1 : (specModuleIsoSections F ⟨U, hU⟩).hom m =
      F.val.map (eqToHom hTop.symm).op
        (((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F).inv.val.app (op ⊤) m) :=
    rfl
  have h2 : ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F).inv.val.app (op ⊤) m =
      F.val.map (homOfLE hB).op m := rfl
  refine Eq.trans h1 (Eq.trans (congrArg
    (fun z : Γ(F, hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) =>
      F.val.map (eqToHom hTop.symm).op z) h2) ?_)
  exact map_map_homOfLE_apply F.val hTop.symm.le hB hA m

end Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

/-! ### The source generator formula names the section it should -/

section SourceGenerator

variable {X : Scheme.{u}} {E : X.Modules} [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E) {W : X.Opens} (hW : IsAffineOpen W)
  (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))

/-- **The section of `ker(q)` over `W` that the source generator formula of clause 3 produces at
`k` is the section `k` is.**
`Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde_inv_unit_toOpen` returns the section of
`ker(q)|_W` over `⊤` obtained from
`Stacks.ProjectiveBundleConormal.specModuleChartKerIso`; read over `W` rather than over
`W.ι ''ᵁ ⊤`, it is `Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv` backwards at `k`.

This is `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections_hom_apply` after
the two restriction maps between `W` and `W.ι ''ᵁ (hW.isoSpec.inv ''ᵁ ⊤)` have been collapsed into
one; the second factor of `specModuleChartKerIso` is `kernelSectionsKerEquiv` and changes nothing
but the type, and the identity `specModuleIsoSections.inv ≫ specModuleIsoSections.hom = 𝟙` is
used at the level of morphisms — read on a section it is a kernel timeout. -/
theorem map_ι_image_top_specModuleChartKerIso_inv
    (h : (⊤ : (↑W : Scheme.{u}).Opens) ≤ hW.isoSpec.inv ''ᵁ ⊤) (k : chartKerModule Q W eL) :
    (kernel Q.q).val.map (homOfLE W.ι_image_top.ge).op
        (((kernel Q.q).restrict W.ι).val.map (homOfLE h).op
          ((specModuleChartKerIso Q W eL hW).inv k)) =
      (kernelSectionsKerEquiv Q W eL).symm k := by
  have hC : W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens) ≤
      W.ι ''ᵁ (hW.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, W)).Opens)) := Scheme.Hom.image_mono W.ι h
  have hA : W ≤ W.ι ''ᵁ (hW.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, W)).Opens)) :=
    W.ι_image_top.ge.trans hC
  have htr : (specModuleChartKerIso Q W eL hW).inv =
      (sectionsChartKerIso Q W eL).inv ≫
        (specModuleIsoSections (kernel Q.q) ⟨W, hW⟩).inv := rfl
  have hmor : (specModuleChartKerIso Q W eL hW).inv ≫
        (specModuleIsoSections (kernel Q.q) ⟨W, hW⟩).hom =
      (sectionsChartKerIso Q W eL).inv :=
    Eq.trans (congrArg (fun φ => φ ≫ (specModuleIsoSections (kernel Q.q) ⟨W, hW⟩).hom) htr)
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg (fun φ => (sectionsChartKerIso Q W eL).inv ≫ φ)
            (specModuleIsoSections (kernel Q.q) ⟨W, hW⟩).inv_hom_id)
          (Category.comp_id _)))
  have happ : (specModuleIsoSections (kernel Q.q) ⟨W, hW⟩).hom
        ((specModuleChartKerIso Q W eL hW).inv k) =
      (kernelSectionsKerEquiv Q W eL).symm k :=
    (ConcreteCategory.congr_hom hmor k : _)
  have hstep : ((kernel Q.q).restrict W.ι).val.map (homOfLE h).op
        ((specModuleChartKerIso Q W eL hW).inv k) =
      (kernel Q.q).val.map (homOfLE hC).op ((specModuleChartKerIso Q W eL hW).inv k) := rfl
  refine Eq.trans (congrArg
    (fun z : Γ(kernel Q.q, W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens)) =>
      (kernel Q.q).val.map (homOfLE W.ι_image_top.ge).op z) hstep) ?_
  refine Eq.trans (map_map_homOfLE_apply (kernel Q.q).val W.ι_image_top.ge hC hA _) ?_
  exact Eq.trans
    (specModuleIsoSections_hom_apply (kernel Q.q) hW hA
      ((specModuleChartKerIso Q W eL hW).inv k)).symm happ

end SourceGenerator

/-! ### The transported section of the ideal sheaf, pinned -/

section Transport

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

variable {W : X.Opens} (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
  (t : Γ(E, W)) (ht : chartLinearForm Q W eL t = 1)

include hσ e hqe in
omit [IsImmersion σ] in
/-- **The image in the structure sheaf of the transported section of the ideal sheaf that
`Stacks.ProjectiveBundleConormal.chartIdealSection` is built from.** This is the hypothesis `hy'`
of `Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_
toOpen` at `V := tautologicalChart E W t`, the section `y'` being the one
`Stacks.ProjectiveBundleConormal.chartIdealSection_eq` names.

It is the last two steps of the proof of
`Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι` — the source transport past the
inclusion
(`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_inv_comp_ι`) and the
restriction isomorphism (`Stacks.Tag01R3PartTwo.image_restrictIso'`) — with the inclusion of the
ideal sheaf moved back across the one restriction map by naturality. -/
theorem idealSheafIsoOfIsoSource_inv_restrictIdealSheafIso'_app_ι
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t))) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom
            ((Scheme.isoOfEq X
                  (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫
              σ ∣_ tautologicalChart E W t).toLRSHom.toShHom))).val.app
        (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
        ((Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
              (Scheme.isoOfEq X
                (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm)
              (σ ∣_ tautologicalChart E W t)).inv.val.app
          (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
          ((Stacks.Conormal.Restriction.restrictIdealSheafIso' σ
                (tautologicalChart E W t)).hom.val.app
            (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
            ((Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.map
              (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
                (tautologicalChart E W t))).op y))) =
      ((tautologicalChart E W t).ι.appIso
            ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)).hom
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom σ.toLRSHom.toShHom))).val.app
            (op ((tautologicalChart E W t).ι ''ᵁ
              ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)))
          ((Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.map
            (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
              (tautologicalChart E W t))).op y)) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
        (Scheme.isoOfEq X
          (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm)
        (σ ∣_ tautologicalChart E W t)).inv
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom
        ((Scheme.isoOfEq X
              (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫
          σ ∣_ tautologicalChart E W t).toLRSHom.toShHom)))
    (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)) _).symm ?_
  refine Eq.trans (congrArg
    (fun φ : Stacks.ClosedImmersion.idealSheaf
          (σ ∣_ tautologicalChart E W t).toLRSHom.toShHom ⟶
        Stacks.IdealSheafRestrict.unitModule (tautologicalChart E W t).toScheme =>
      φ.val.app (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)) _)
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_inv_comp_ι
      (Scheme.isoOfEq X
        (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm)
      (σ ∣_ tautologicalChart E W t))) ?_
  refine Eq.trans (Stacks.Tag01R3PartTwo.image_restrictIso' σ (tautologicalChart E W t)
    ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)
    ((tautologicalChart E W t).ι.image_preimage_le (tautologicalChart E W t)) y) ?_
  refine congrArg ((tautologicalChart E W t).ι.appIso
    ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)).hom ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom σ.toLRSHom.toShHom))).val
    (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
      (tautologicalChart E W t))).op y).symm
  exact (Stacks.Conormal.Locality.unitModule_val_map
    ((tautologicalChart E W t).ι.image_preimage_le (tautologicalChart E W t)) _).symm

include hσ e hqe in
/-- **The source half of clause 3 on a chart, with the section of `ℐ(σ)` it produces pinned to the
ratio.** For chart data `(W, hW, eL, t, ht)`, a section `κ` of `ker(q)` over `W`, and the
generator `w` of `𝓛^{⊗ -1}` whose pairing against the frame section `q t` is `1`, the clause's map
carries the product section `κ ⊗ w` to the conormal generator named by a section `y` of `ℐ(σ)` over
the tautological chart **whose image in `𝒪_{𝐏(ℰ)}` is the ratio `g` itself** — not the ratio times
an unknown unit.

This is `Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt`
fed with the `w₀` of
`Stacks.ProjectiveBundleConormal`
`.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned`, whose pin is the value
`1` of the product of `w₀` with the degree-one section of the frame. The three steps that turn
the pin into the ratio are
`Stacks.ProjectiveBundleConormal.kernelTautologicalMap_res_unitSection`, the hypothesis `hg`, and
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_smul_left_eq_mul`.

The ratio `g` is a variable named by `hg`, so that a consumer instantiates it from
`Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι` rather than
unfolding anything. -/
theorem exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio
    (κ : Γ(kernel Q.q, W))
    (w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), W))
    (hpair : Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) W (Q.q.app W t) w =
      Stacks.SheafOfModules.unitSection X.toRingedSpace W)
    (g : Γ((bundle E).scheme, tautologicalChart E W t))
    (hg : (tautologicalTwist E (symPieces E)).presheaf.map
          (homOfLE (tautologicalChart_le E W t)).op
          (tautologicalSectionOver E W ((kernel.ι Q.q).val.app (op W) κ)) =
        ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
          ((tautologicalTwist E (symPieces E)).presheaf.map
            (homOfLE (tautologicalChart_le E W t)).op (tautologicalSectionOver E W t))) :
    ∃ y : Γ(kernel (structureSheafUnit σ), tautologicalChart E W t),
      (kernel.ι (structureSheafUnit σ)).val.app (op (tautologicalChart E W t)) y = g ∧
        (conormalCanonicalMap E Q hσ e hqe).val.app (op W)
            (tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
              (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
                Q.L (-1)) κ w) =
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
            (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ))
              (tautologicalChart E W t) W
              (le_preimage_tautologicalChart E Q hσ e hqe W t hW eL ht) y) := by
  obtain ⟨w₀, hw, hpin⟩ :=
    exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned E Q hσ e hqe W t hW eL ht
      w hpair
  obtain ⟨y, hy, hmap⟩ := exists_conormalCanonicalMap_val_app_tensorSectionsAt E Q hσ e hqe W
    (tautologicalChart E W t) (tautologicalChart_le E W t)
    (le_preimage_tautologicalChart E Q hσ e hqe W t hW eL ht) κ w w₀ hw
  refine ⟨y, ?_, hmap⟩
  refine Eq.trans hy ?_
  refine Eq.trans (congrArg
    (fun a : Γ(tautologicalTwist E (symPieces E), tautologicalChart E W t) =>
      Stacks.SheafOfModules.Invertible.sectionMulNegOne (bundle E).scheme.presheaf
        (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E))
        (op (tautologicalChart E W t)) a w₀)
    ((kernelTautologicalMap_res_unitSection E Q W (tautologicalChart E W t)
      (tautologicalChart_le E W t) κ).trans hg)) ?_
  refine Eq.trans (sectionMulNegOne_smul_left_eq_mul (tautologicalTwist E (symPieces E))
    (tautologicalChart E W t) g 1
    ((tautologicalTwist E (symPieces E)).presheaf.map
      (homOfLE (tautologicalChart_le E W t)).op (tautologicalSectionOver E W t)) w₀ hpin) ?_
  exact mul_one g

end Transport

/-! ### The two sides of the coordinate equation `hxκ` -/

section Coordinate

open SymmetricAlgebra
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

variable (A K : Type u) [CommRing A] [AddCommGroup K] [Module A K]

/-- **The target side of `hxκ`: the image in `Sym_A(K)` of the section of the ideal sheaf of the
zero section named by an element of the augmentation ideal is that element.**

`Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso_hom_comp_idealSheafι` carries the
inclusion of the ideal sheaf to the sheafification of the inclusion `I ⟶ Sym_A(K)`, so the
computation is `AlgebraicGeometry.tilde.toOpen_map_app` and nothing else;
`AlgebraicGeometry.tilde.tildeSelf` is the identity and
`AlgebraicGeometry.tilde.toOpen` at `M = Sym_A(K)` is `(AlgebraicGeometry.Scheme.ΓSpecIso _).inv`
by `rfl`, so no vocabulary bridge is owed against the ratio lemma, which states its value in that
spelling. -/
theorem zeroSectionIdealSheafIso_hom_toOpen_app_ι (κ : augIdealOf A K) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (zeroSection A K).toLRSHom.toShHom))).val.app (op ⊤)
        ((zeroSectionIdealSheafIso A K).hom.val.app (op ⊤)
          (tilde.toOpen (augIdealModule A K) ⊤ κ)) =
      (Scheme.ΓSpecIso (symRing A K)).inv.hom (κ : SymmetricAlgebra A K) := by
  have hι : kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (zeroSection A K).toLRSHom.toShHom)) =
      idealSheafι (zeroSection A K).toLRSHom.toShHom := rfl
  refine Eq.trans (congrArg
    (fun φ : idealSheaf (zeroSection A K).toLRSHom.toShHom ⟶
        Stacks.IdealSheafRestrict.unitModule (Spec (symRing A K)) =>
      φ.val.app (op ⊤)
        ((zeroSectionIdealSheafIso A K).hom.val.app (op ⊤)
          (tilde.toOpen (augIdealModule A K) ⊤ κ))) hι) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply (zeroSectionIdealSheafIso A K).hom
    (idealSheafι (zeroSection A K).toLRSHom.toShHom) (op ⊤) _).symm ?_
  refine Eq.trans (congrArg
    (fun φ : tilde (augIdealModule A K) ⟶
        Stacks.IdealSheafRestrict.unitModule (Spec (symRing A K)) =>
      φ.val.app (op ⊤) (tilde.toOpen (augIdealModule A K) ⊤ κ))
    (zeroSectionIdealSheafIso_hom_comp_idealSheafι A K)) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (tilde.map (ModuleCat.ofHom (augIdealOf A K).subtype)) tildeSelf.hom (op ⊤) _) ?_
  exact congrArg (fun z => tildeSelf.hom.val.app (op ⊤) z)
    (AlgebraicGeometry.TildeTensor.toOpen_map_app_apply
      (ModuleCat.ofHom (augIdealOf A K).subtype) ⊤ κ)

end Coordinate

/-! ### The source side of the coordinate equation -/

section SourceCoordinate

open SymmetricAlgebra

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

variable {W : X.Opens} (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
  (t : Γ(E, W)) (ht : chartLinearForm Q W eL t = 1)

include hσ e hqe in
omit [IsImmersion σ] in
/-- **The source side of `hxκ`: the image of
`Stacks.ProjectiveBundleConormal.chartIdealSection` in `Sym_A(ker p)` is the image of `y`,
pulled back along the two charts.** `Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι`
reads that image as `(tautologicalChartLift)^♯` of `(ι_V)^♯` of the image of `y`, and
`Stacks.ProjectiveBundleConormal.tautologicalChartLift_comp_ι` turns the composite into
`(splitChartMap ≫ chartMap)^♯`, which is the spelling
`Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι` is stated at.

The two `♯`s are read as `AlgebraicGeometry.Scheme.Hom.appLE` of the two morphisms and composed by
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`; the open immersion of the chart contributes
`AlgebraicGeometry.Scheme.Opens.ι_appLE` and `AlgebraicGeometry.Scheme.Opens.ι_appIso`, and the
structure-sheaf unit is `AlgebraicGeometry.Scheme.Hom.app` on the nose. The image `g` of `y` is a
variable named by `hg`, so that a consumer instantiates it from
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio`. -/
theorem chartIdealSection_app_ι_appLE
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t)))
    (g : Γ((bundle E).scheme, tautologicalChart E W t))
    (hg : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom σ.toLRSHom.toShHom))).val.app
        (op (tautologicalChart E W t)) y = g) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom
            (hW.isoSpec.hom ≫
              zeroSection Γ(X, W)
                (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom))).val.app (op ⊤)
        (chartIdealSection E Q hσ e hqe hW eL t ht y) =
      ((splitChartMap (chartLinearForm Q W eL) t ht ≫
            chartMap E (symPieces E) hW).appLE (tautologicalChart E W t) ⊤
          (top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart
            E Q hW eL t ht)).hom g := by
  have hj : (⊤ : (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).Opens) ≤
      tautologicalChartLift E Q hW eL t ht ⁻¹ᵁ
        ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) :=
    le_of_eq (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)
  have hα : (tautologicalChart E W t).ι.appLE (tautologicalChart E W t)
        ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) le_rfl =
      (bundle E).scheme.presheaf.map
        (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
          (tautologicalChart E W t))).op := by
    rw [Scheme.Opens.ι_appLE]
  have hαi : ∀ z : Γ((bundle E).scheme,
      (tautologicalChart E W t).ι ''ᵁ ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)),
      ((tautologicalChart E W t).ι.appIso
          ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)).hom z = z := by
    rw [Scheme.Opens.ι_appIso]
    exact fun _ => rfl
  have hβ : ∀ b : Γ((tautologicalChart E W t).toScheme,
        (tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t),
      (Stacks.IdealSheafRestrict.unitModule
            (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL))))).val.map
          (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)).op
          ((SheafOfModules.unitToPushforwardObjUnit
                (structureSheafHom
                  (tautologicalChartLift E Q hW eL t ht).toLRSHom.toShHom)).val.app
              (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)) b) =
        ((tautologicalChartLift E Q hW eL t ht).appLE
            ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) ⊤ hj).hom b := fun b =>
    congrArg
      (fun φ : (op (tautologicalChartLift E Q hW eL t ht ⁻¹ᵁ
            ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)) :
          (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).Opensᵒᵖ) ⟶
          op (⊤ : (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).Opens) =>
        (((Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).presheaf.map
            φ)).hom
          (((tautologicalChartLift E Q hW eL t ht).app
            ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)).hom b))
      (congrArg Quiver.Hom.op
        (Subsingleton.elim
          (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht))
          (homOfLE hj)))
  have hring : (tautologicalChart E W t).ι.appLE (tautologicalChart E W t)
          ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) le_rfl ≫
        (tautologicalChartLift E Q hW eL t ht).appLE
          ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) ⊤ hj =
      (splitChartMap (chartLinearForm Q W eL) t ht ≫
          chartMap E (symPieces E) hW).appLE (tautologicalChart E W t) ⊤
        (top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart E Q hW eL t ht) :=
    (Scheme.Hom.appLE_comp_appLE (tautologicalChartLift E Q hW eL t ht)
          (tautologicalChart E W t).ι (tautologicalChart E W t)
          ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) ⊤ le_rfl hj).trans
      (Stacks.DiagonalConormal.appLE_congr
        (tautologicalChartLift_comp_ι E Q hW eL t ht) (tautologicalChart E W t) ⊤ _ _)
  refine Eq.trans (chartIdealSection_app_ι E Q hσ e hqe hW eL t ht y) ?_
  refine Eq.trans (congrArg
    (fun z : Γ((bundle E).scheme, tautologicalChart E W t) =>
      (Stacks.IdealSheafRestrict.unitModule
            (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL))))).val.map
          (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)).op
          ((SheafOfModules.unitToPushforwardObjUnit
                (structureSheafHom
                  (tautologicalChartLift E Q hW eL t ht).toLRSHom.toShHom)).val.app
              (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
            (((tautologicalChart E W t).ι.appIso
                  ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)).hom
              (((bundle E).scheme.presheaf.map
                    (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
                      (tautologicalChart E W t))).op).hom z)))) hg) ?_
  refine Eq.trans (hβ _) ?_
  refine Eq.trans (congrArg
    (fun z : Γ((tautologicalChart E W t).toScheme,
        (tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) =>
      ((tautologicalChartLift E Q hW eL t ht).appLE
        ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t) ⊤ hj).hom z)
    ((hαi _).trans (congrArg (fun φ => CommRingCat.Hom.hom φ g) hα).symm)) ?_
  exact congrArg (fun φ => CommRingCat.Hom.hom φ g) hring

include hσ e hqe in
omit [IsImmersion σ] in
/-- **The coordinate equation `hxκ` of the target generator formula, discharged on the tautological
chart.** The element of the augmentation ideal of `Sym_A(ker p)` that the section `y` of `ℐ(σ)`
cuts out on the chart is `ι k`, where `k` is the coordinate of the ratio.

`Stacks.Conormal.Locality.idealSheaf_section_injective` reduces the equation between sections of
the ideal sheaf of the affine chart to one in `Γ(𝒪, ⊤) = Sym_A(ker p)`; the two sides are
`Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι_appLE` (after
`Stacks.AlgebraicGeometry.ConormalSourceTransport.idealSheafIsoOfIsoSource_hom_comp_ι` has moved
the source transport past the inclusion) and
`Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso_hom_toOpen_app_ι`, and both are
`(AlgebraicGeometry.Scheme.ΓSpecIso _).inv` of an element of `Sym_A(ker p)`. -/
theorem chartIdealSection_idealSheafIsoOfIsoSource_hom_eq_toOpen
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t)))
    (k : chartKerModule Q W eL)
    (g : Γ((bundle E).scheme, tautologicalChart E W t))
    (hg : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom σ.toLRSHom.toShHom))).val.app
        (op (tautologicalChart E W t)) y = g)
    (happ : ((splitChartMap (chartLinearForm Q W eL) t ht ≫
            chartMap E (symPieces E) hW).appLE (tautologicalChart E W t) ⊤
          (top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart
            E Q hW eL t ht)).hom g =
      (Scheme.ΓSpecIso
            (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).inv.hom
        (SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) k)) :
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
          hW.isoSpec (zeroSection Γ(X, W)
            (LinearMap.ker (chartLinearForm Q W eL)))).hom.val.app (op ⊤)
        (chartIdealSection E Q hσ e hqe hW eL t ht y) =
      (zeroSectionIdealSheafIso Γ(X, W)
            ↥(LinearMap.ker (chartLinearForm Q W eL))).hom.val.app (op ⊤)
        (tilde.toOpen (augIdealModule Γ(X, W)
            ↥(LinearMap.ker (chartLinearForm Q W eL))) ⊤
          ⟨SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) k,
            SymmetricAlgebra.ι_mem_augIdeal k⟩) := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL))) ⊤ ?_
  refine Eq.trans ?_ (zeroSectionIdealSheafIso_hom_toOpen_app_ι Γ(X, W)
    ↥(LinearMap.ker (chartLinearForm Q W eL))
    ⟨SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) k,
      SymmetricAlgebra.ι_mem_augIdeal k⟩).symm
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
      hW.isoSpec (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))).hom
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom (zeroSection Γ(X, W)
        (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom))) (op ⊤) _).symm ?_
  refine Eq.trans (congrArg
    (fun φ : Stacks.ClosedImmersion.idealSheaf
          (hW.isoSpec.hom ≫ zeroSection Γ(X, W)
            (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom ⟶
        Stacks.IdealSheafRestrict.unitModule
          (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))) =>
      φ.val.app (op ⊤) (chartIdealSection E Q hσ e hqe hW eL t ht y))
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_hom_comp_ι
      hW.isoSpec (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL))))) ?_
  exact (chartIdealSection_app_ι_appLE E Q hσ e hqe hW eL t ht y g hg).trans happ

include hσ e hqe in
/-- **The target identification at the tautological chart, read on the canonical global section
named by `k`.** It is the conormal generator at a section `y` of `ℐ(σ)` over the chart, provided
`y` cuts out `ι k` there.

This is `Stacks.ProjectiveBundleConormal`
`.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen` *applied* at the chart — the
sixteen arguments being the
`isoSpec_comp_zeroSection_comp_tautologicalChartLift_*` family,
`Stacks.ProjectiveBundleConormal.top_eq_preimage_tautologicalChartLift_preimage_ι`,
`Stacks.ProjectiveBundleConormal.chartIdealSection` with its two pins, and `κ := ι k`, whose
derivative at the origin is `k` by `SymmetricAlgebra.augDeriv_ι` — turned around by
`Stacks.SheafOfModules.inv_val_app_hom_val_app`. The formula is never restated: restating it is a
kernel timeout and applying it costs a fraction of a second. -/
theorem restrictConormalTargetIsoTildeTaut_inv_unit_toOpen
    (ν : W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens) ⟶ σ ⁻¹ᵁ tautologicalChart E W t)
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t)))
    (k : chartKerModule Q W eL)
    (hxκ : (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
          hW.isoSpec (zeroSection Γ(X, W)
            (LinearMap.ker (chartLinearForm Q W eL)))).hom.val.app (op ⊤)
        (chartIdealSection E Q hσ e hqe hW eL t ht y) =
      (zeroSectionIdealSheafIso Γ(X, W)
            ↥(LinearMap.ker (chartLinearForm Q W eL))).hom.val.app (op ⊤)
        (tilde.toOpen (augIdealModule Γ(X, W)
            ↥(LinearMap.ker (chartLinearForm Q W eL))) ⊤
          ⟨SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) k,
            SymmetricAlgebra.ι_mem_augIdeal k⟩)) :
    (restrictConormalTargetIsoTildeTaut E Q hσ e hqe hW eL t ht).inv.val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction hW.isoSpec.hom).unit.app
            (tilde (chartKerModule Q W eL))).val.app (op ⊤)
          (tilde.toOpen (chartKerModule Q W eL) ⊤ k)) =
      (Stacks.Conormal.conormalSheaf σ).val.map ν.op
        ((Stacks.Immersion.canonicalConormalQuotientMap σ).val.app
          (op (tautologicalChart E W t)) y) := by
  have htgt := restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen
    σ (tautologicalChart E W t)
    (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm
    ↥Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL))
    hW.isoSpec (tautologicalChartLift E Q hW eL t ht)
    (isoSpec_comp_zeroSection_comp_tautologicalChartLift_comp_ι E Q hσ e hqe hW eL t ht)
    ((Scheme.isoOfEq X
          (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫
      σ ∣_ tautologicalChart E W t)
    (isoSpec_comp_zeroSection_comp_tautologicalChartLift_eq E Q hσ e hqe hW eL t ht)
    (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)
    ν y _
    (idealSheafIsoOfIsoSource_inv_restrictIdealSheafIso'_app_ι E Q hσ e hqe hW eL t ht y)
    (chartIdealSection E Q hσ e hqe hW eL t ht y)
    (chartIdealSection_eq E Q hσ e hqe hW eL t ht y)
    ⟨SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) k,
      SymmetricAlgebra.ι_mem_augIdeal k⟩
    hxκ
  have hUk : (restrictConormalTargetIsoTildeTaut E Q hσ e hqe hW eL t ht).hom.val.app (op ⊤)
        ((Stacks.Conormal.conormalSheaf σ).val.map ν.op
          ((Stacks.Immersion.canonicalConormalQuotientMap σ).val.app
            (op (tautologicalChart E W t)) y)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction hW.isoSpec.hom).unit.app
          (tilde (chartKerModule Q W eL))).val.app (op ⊤)
        (tilde.toOpen (chartKerModule Q W eL) ⊤ k) :=
    htgt.trans (congrArg
      (fun z : chartKerModule Q W eL =>
        ((Scheme.Modules.pullbackPushforwardAdjunction hW.isoSpec.hom).unit.app
            (tilde (chartKerModule Q W eL))).val.app (op ⊤)
          (tilde.toOpen (chartKerModule Q W eL) ⊤ z))
      (SymmetricAlgebra.augDeriv_ι k))
  exact Eq.trans (congrArg
      (fun z : ((Scheme.Modules.pullback hW.isoSpec.hom).obj
          (tilde (chartKerModule Q W eL))).val.obj (op ⊤) =>
        (restrictConormalTargetIsoTildeTaut E Q hσ e hqe hW eL t ht).inv.val.app (op ⊤) z)
      hUk.symm)
    (Stacks.SheafOfModules.inv_val_app_hom_val_app
      (restrictConormalTargetIsoTildeTaut E Q hσ e hqe hW eL t ht) (op ⊤) _)

include hσ e hqe in
/-- **The chart equation of [Stacks, Tag 0B3V] clause 3.** On an affine open `W` carrying a frame
`eL` for `𝓛` and a section `t` of `ℰ` at which the chart's linear form takes the value `1`, and for
the trivialisation that data induces, the restriction of the clause's map to `W` *is* the composite
of the two identifications of its source and target with `(ker p)^~`.

This is the hypothesis `h` of
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq_taut`.

`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_unit_toOpen` reduces it to one equation per
element `k` of `ker p`. The target side is
`Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTildeTaut_inv_unit_toOpen` and the
source side is `Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen`
followed by
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio`; the
two are stated over `W.ι ''ᵁ ⊤` and over `W` respectively, and
`Stacks.ProjectiveBundleConormal.val_app_ι_image_top_of_val_app` together with
`Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality` matches them. The
section of `ker(q)` the source formula produces is recognised by
`Stacks.ProjectiveBundleConormal.map_ι_image_top_specModuleChartKerIso_inv`, its ratio is computed
by `Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι`, and that ratio
is `ι k` because `Stacks.ProjectiveBundleConormal.kernelSectionsKerEquiv` and its inverse cancel.
The two spellings of a conormal generator are bridged by
`Stacks.Conormal.conormalSheafIsoPullbackSelf_inv_pullbackSection`. -/
theorem conormalCanonicalMap_restrict_eq_taut
    (τ : (Scheme.Modules.restrictFunctor W.ι).obj Q.L ≅ 𝟙_ (↑W : Scheme.{u}).Modules)
    (hτ : τ = chartTrivialisation Q hW eL t ht) :
    (restrictConormalSourceIsoTilde Q W eL hW τ).inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map (conormalCanonicalMap E Q hσ e hqe) =
      (restrictConormalTargetIsoTildeTaut E Q hσ e hqe hW eL t ht).inv := by
  subst hτ
  have hUW : W ≤ W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens) := W.ι_image_top.ge
  have hWU : W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens) ≤ W := W.ι_image_top.le
  have hisoeq : hW.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, W)).Opens) =
      (⊤ : (↑W : Scheme.{u}).Opens) := by simp
  have hiso : (⊤ : (↑W : Scheme.{u}).Opens) ≤ hW.isoSpec.inv ''ᵁ ⊤ := le_of_eq hisoeq.symm
  have hpre : (⊤ : (↑W : Scheme.{u}).Opens) ≤
      W.ι ⁻¹ᵁ (W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens)) := by simp
  have hWV : W ≤ σ ⁻¹ᵁ tautologicalChart E W t :=
    le_preimage_tautologicalChart E Q hσ e hqe W t hW eL ht
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_unit_toOpen hW.isoSpec.hom ?_
  intro k
  obtain ⟨w, hwdef⟩ : ∃ w : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
        X.ringCatSheaf.2 Q.L (-1), W),
      w = (show X.Modules from Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
            X.ringCatSheaf.2 Q.L (-1)).presheaf.map (homOfLE hUW).op
          ((restrictInverseTwistIso Q.L W (chartTrivialisation Q hW eL t ht)).inv.val.app
            (op (⊤ : (↑W : Scheme.{u}).Opens))
            (1 : Γ((↑W : Scheme.{u}), (⊤ : (↑W : Scheme.{u}).Opens)))) := ⟨_, rfl⟩
  have hpair := tensorPairing_chartTrivialisation_eq_unitSection Q hW eL t ht hUW hWU hpre w hwdef
  obtain ⟨g, hgsec, happ⟩ := exists_appLE_splitChartMap_comp_chartMap_eq_ι E Q hW eL t ht
    ((kernelSectionsKerEquiv Q W eL).symm k)
  have happ' : ((splitChartMap (chartLinearForm Q W eL) t ht ≫
          chartMap E (symPieces E) hW).appLE (tautologicalChart E W t) ⊤
        (top_le_splitChartMap_comp_chartMap_preimage_tautologicalChart E Q hW eL t ht)).hom g =
      (Scheme.ΓSpecIso
            (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).inv.hom
        (SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) k) :=
    happ.trans (congrArg
      (fun z : ↥(LinearMap.ker (chartLinearForm Q W eL)) =>
        (Scheme.ΓSpecIso
              (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))).inv.hom
          (SymmetricAlgebra.ι Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)) z))
      ((kernelSectionsKerEquiv Q W eL).apply_symm_apply k))
  obtain ⟨y, hyι, hmap⟩ := exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio
    E Q hσ e hqe hW eL t ht ((kernelSectionsKerEquiv Q W eL).symm k) w hpair g hgsec
  have hxκ := chartIdealSection_idealSheafIsoOfIsoSource_hom_eq_toOpen
    E Q hσ e hqe hW eL t ht y k g hyι happ'
  have htgt := restrictConormalTargetIsoTildeTaut_inv_unit_toOpen E Q hσ e hqe hW eL t ht
    (homOfLE (le_of_eq (W.ι_image_top.trans
      (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm))) y k hxκ
  refine Eq.trans ?_ htgt.symm
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (restrictConormalSourceIsoTilde Q W eL hW (chartTrivialisation Q hW eL t ht)).inv
    ((Scheme.Modules.restrictFunctor W.ι).map (conormalCanonicalMap E Q hσ e hqe)) (op ⊤) _) ?_
  refine Eq.trans (congrArg
    (fun z : ((Scheme.Modules.restrictFunctor W.ι).obj
        (kernel Q.q ⊗ Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
          X.ringCatSheaf.2 Q.L (-1))).val.obj (op ⊤) =>
      ((Scheme.Modules.restrictFunctor W.ι).map
        (conormalCanonicalMap E Q hσ e hqe)).val.app (op ⊤) z)
    (restrictConormalSourceIsoTilde_inv_unit_toOpen Q W eL hW
      (chartTrivialisation Q hW eL t ht) hiso hpre k)) ?_
  refine Eq.trans (Stacks.Conormal.Locality.restrictFunctor_map_val_app W
    (conormalCanonicalMap E Q hσ e hqe) ⊤ _) ?_
  refine Eq.trans (val_app_ι_image_top_of_val_app (conormalCanonicalMap E Q hσ e hqe) W _
    ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W)
      (Scheme.Modules.pullbackSection σ (kernel (structureSheafUnit σ))
        (tautologicalChart E W t) W hWV y)) ?_) ?_
  · refine Eq.trans (congrArg
      (fun z : Γ(kernel Q.q ⊗ Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
          X.ringCatSheaf.2 Q.L (-1), W) =>
        (conormalCanonicalMap E Q hσ e hqe).val.app (op W) z) ?_) hmap
    refine Eq.trans (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality
      X.presheaf X.ringCatSheaf.2 (kernel Q.q)
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
      (homOfLE hUW).op _ _) ?_
    exact congrArg₂
      (fun a (b : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
          X.ringCatSheaf.2 Q.L (-1), W)) =>
        tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op W) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) a b)
      (map_ι_image_top_specModuleChartKerIso_inv Q hW eL hiso k) hwdef.symm
  · refine Eq.trans (congrArg
      (fun z : Γ(Stacks.Conormal.conormalSheaf σ, W) =>
        (Stacks.Conormal.conormalSheaf σ).val.map (homOfLE W.ι_image_top.le).op z)
      (Stacks.Conormal.conormalSheafIsoPullbackSelf_inv_pullbackSection σ
        (tautologicalChart E W t) W hWV (homOfLE hWV) y)) ?_
    exact map_map_homOfLE_apply (Stacks.Conormal.conormalSheaf σ).val W.ι_image_top.le hWV _ _

end SourceCoordinate

/-! ### Clause (b) of Tag 0B3V -/

section Clause

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **Clause (b) of [Stacks, Tag 0B3V]: the canonical map
`Ker(ℰ → 𝓛) ⊗ 𝓛^{⊗ -1} ⟶ 𝒞_σ` is an isomorphism.** For a quasi-coherent module `ℰ` on a scheme
`X` with an invertible quotient `q : ℰ → 𝓛`, and the section `σ : X ⟶ 𝐏(ℰ)` it names, the conormal
sheaf of `σ` — which is an immersion by [Stacks, Tag 0B3V] clause (a) — is the kernel of `q`
twisted by the inverse of `𝓛`.

`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq_taut` reduces this to
the chart equation `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_restrict_eq_taut`, and
`Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` is the cover of charts it is
quantified over — a cover that returns the trivialisation the frame induces, which is what makes
the pairing of the chart computation `1` rather than an unknown unit. -/
theorem isIso_conormalCanonicalMap : IsIso (conormalCanonicalMap E Q hσ e hqe) :=
  isIso_conormalCanonicalMap_of_restrict_eq_taut E Q hσ e hqe
    fun _ hW eL t ht τ hτ => conormalCanonicalMap_restrict_eq_taut E Q hσ e hqe hW eL t ht τ hτ

end Clause

end Stacks.ProjectiveBundleConormal

end
