module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.SectionChain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every invertible quotient is classified by a section of `π`

* The degree-one dictionary at an arbitrary section of `π`
  (`Stacks.RelativeProj.classifyingTrivialisationOfSection`).
* The object comparison over a member of the cover, on the pulled-back tautological map.
* `Stacks.RelativeProj.exists_classifies_tautologicalDatum`.
* The nonvanishing open of a global section trivialised to a unit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks.RelativeProj

open Stacks.Divisors

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

variable {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-! ### The degree-one dictionary at an arbitrary section of `π` -/

section SectionClassify

open Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (V : X.Opens) (hV : IsAffineOpen V) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
  (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
  (α : (Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F) ≅ L)

/-- **The pulled-back tautological map of `𝐏(ℰ)`, inverse-imaged to an open of the base and read
on a pulled-back section — at an arbitrary section `σ` of `π`.** At `x : Γ(ℰ, V)` the value is the
twice pulled-back value of `Stacks.ProjectiveBundleSplitting.tautologicalMap` — which is exactly
the section `restrictChartFactorisationPullbackTwistIso_hom_pullbackSection` consumes.

`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality` moves the inverse image past the
map, `Stacks.ProjectiveBundleConormal.pullbackSection_preimage_self` identifies the pulled-back
section over the whole preimage with the adjunction unit, and
`pullbackQuotientMap_tautologicalDatum_val_app` — already stated at an arbitrary `σ` — evaluates
the map itself. -/
public theorem pullback_map_pullbackQuotientMap_unitSection (V : X.Opens)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) (x : Γ(F, V)) :
    ((Scheme.Modules.pullback V.ι).map
          ((tautologicalDatum F).pullbackQuotientMap σ hσ)).val.app
        (op (V.ι ⁻¹ᵁ V)) (unitSection V.ι F V x)
      = Scheme.Modules.pullbackSection V.ι
          ((Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F))
          V (V.ι ⁻¹ᵁ V) le_rfl
          (Scheme.Modules.pullbackSection σ (tautologicalDatumTwist F)
            (projectiveBundleToBase X F ⁻¹ᵁ V) V
            (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) σ hσ V).ge
            (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
                (isQuasicoherentPieces_of_isQuasicoherent F))
              ((symGradedBundle F).toBase ⁻¹ᵁ V)
              (projectiveBundleToBase X F ⁻¹ᵁ V)
              (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
              ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                  (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
                (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
                (unitSection (symGradedBundle F).toBase F V x)))) :=
  by
  have hb := (preimage_bundlePresentationIso_inv_preimage_toBase (F := F) V).ge
  have hinner := congrArg
    (fun y : Γ((Scheme.Modules.pullback (symGradedBundle F).toBase).obj F,
        (symGradedBundle F).toBase ⁻¹ᵁ V) =>
      Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
          (isQuasicoherentPieces_of_isQuasicoherent F))
        ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V) hb
        ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
            (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
          (op ((symGradedBundle F).toBase ⁻¹ᵁ V)) y))
    (Stacks.ProjectiveBundleConormal.pullbackSection_preimage_self
      (symGradedBundle F).toBase F V le_rfl x)
  refine Eq.trans (congrArg
    (fun y : Γ((Scheme.Modules.pullback V.ι).obj F, V.ι ⁻¹ᵁ V) =>
      ((Scheme.Modules.pullback V.ι).map
          ((tautologicalDatum F).pullbackQuotientMap σ hσ)).val.app (op (V.ι ⁻¹ᵁ V)) y)
    (Stacks.ProjectiveBundleConormal.pullbackSection_preimage_self V.ι F V le_rfl x).symm) ?_
  refine Eq.trans (Scheme.Modules.pullbackSection_naturality V.ι
    ((tautologicalDatum F).pullbackQuotientMap σ hσ) V (V.ι ⁻¹ᵁ V) le_rfl x) ?_
  exact congrArg
    (Scheme.Modules.pullbackSection V.ι
      ((Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F)) V (V.ι ⁻¹ᵁ V) le_rfl)
    ((pullbackQuotientMap_tautologicalDatum_val_app σ hσ V
        (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) σ hσ V).ge hb x).trans
      (congrArg
        (Scheme.Modules.pullbackSection σ (tautologicalDatumTwist F)
          (projectiveBundleToBase X F ⁻¹ᵁ V) V
          (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) σ hσ V).ge) hinner))

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The `ℒ` side of the classifying datum at an arbitrary section.** A `Classifies`
isomorphism `α` carries the pulled-back tautological map to `q`, so the inverse image of the
pulled-back tautological map followed by `α` and by the trivialisation of the inverse image of
`ℒ` sends the pullback of `x` to the trivialised quotient `e (q x)`.

This is `pullback_map_comp_pullbackIsoUnitOfOverIsoUnit_hom_unitSection` with the two inverse
images merged by `CategoryTheory.Functor.map_comp` and `α`'s compatibility substituted. -/
public theorem pullback_map_comp_classifyingIso_hom_unitSection
    (hα : (tautologicalDatum F).pullbackQuotientMap σ hσ ≫ α.hom = q) (x : Γ(F, V)) :
    ((Scheme.Modules.pullback V.ι).map ((tautologicalDatum F).pullbackQuotientMap σ hσ) ≫
          ((Scheme.Modules.pullback V.ι).mapIso α).hom ≫
            (pullbackIsoUnitOfOverIsoUnit V L e).hom).val.app
        (op (V.ι ⁻¹ᵁ V)) (unitSection V.ι F V x)
      = ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) x) :=
  have hmap : (Scheme.Modules.pullback V.ι).map
          ((tautologicalDatum F).pullbackQuotientMap σ hσ) ≫
        (Scheme.Modules.pullback V.ι).map α.hom =
      (Scheme.Modules.pullback V.ι).map q :=
    (CategoryTheory.Functor.map_comp (Scheme.Modules.pullback V.ι) _ _).symm.trans
      (congrArg (Scheme.Modules.pullback V.ι).map hα)
  (congrArg
      (fun z : (Scheme.Modules.pullback V.ι).obj F ⟶
          (Scheme.Modules.pullback V.ι).obj L =>
        (z ≫ (pullbackIsoUnitOfOverIsoUnit V L e).hom).val.app (op (V.ι ⁻¹ᵁ V))
          (unitSection V.ι F V x))
      hmap).trans
    (pullback_map_comp_pullbackIsoUnitOfOverIsoUnit_hom_unitSection V q e x)

/-- **The trivialisation of the pulled-back twisting sheaf attached to a classified section.**

Let `σ` be an arbitrary section of `π`, let `α` witness that `σ` classifies the invertible
quotient `q : ℰ ↠ ℒ`, and let `V` be an affine open on which `ℒ` is trivialised by `e`. Composing
the object comparison `Stacks.RelativeProj.restrictChartFactorisationTwistIso` backwards with
`α` and `e` gives an isomorphism of the twisting sheaf of `Γ(V, Sym ℰ)` pulled back along
`Stacks.RelativeProj.sectionChartMap` with the structure sheaf of `V`.

**What this is for**: `classifyingTrivialisationOfSection_hom_pullbackSection` says it carries
the pulled-back degree-one section of `x` to `e (q x)`, with no standard-open hypothesis of any
kind. At an `x` whose trivialised quotient is the unit — one exists over an affine open by
`Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` — the pulled-back degree-one
section is therefore carried to `1`, which is what
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq_nonvanishingOpen` needs
in order to produce `sectionChartMap ⁻¹ᵁ D₊(x) = ⊤`, which is
`preimage_basicOpen_sectionChartMap_eq_top` below. -/
public def classifyingTrivialisationOfSection :
    (Scheme.Modules.pullback (sectionChartMap V σ hσ hV)).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          1) ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
  (restrictChartFactorisationTwistIso V hV σ (V.ι ≫ σ) rfl (sectionChartMap V σ hσ hV)
      (sectionChartMap_comp_chart V σ hσ hV)).symm ≪≫
    (Scheme.Modules.pullback V.ι).mapIso α ≪≫ pullbackIsoUnitOfOverIsoUnit V L e

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The trivialisation carries the pulled-back degree-one section of `x` to `e (q x)`** — the
degree-one dictionary at an arbitrary classified section of `π`, over the open `V.ι ⁻¹ᵁ V`.

Both sides are read off the twice pulled-back value of
`Stacks.ProjectiveBundleSplitting.tautologicalMap`:
`restrictChartFactorisationTwistIso_hom_pullbackSection` says the object comparison carries that
section to the pulled-back degree-one section, and
`pullback_map_comp_classifyingIso_hom_unitSection` says `α` followed by the trivialisation
carries it to `e (q x)`. **No standard-open hypothesis and no choice of frame appears.** -/
public theorem classifyingTrivialisationOfSection_hom_pullbackSection
    (hα : (tautologicalDatum F).pullbackQuotientMap σ hσ ≫ α.hom = q)
    (hf : V.ι ⁻¹ᵁ V ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤) (x : Γ(F, V)) :
    (classifyingTrivialisationOfSection V hV e σ hσ α).hom.val.app (op (V.ι ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection (sectionChartMap V σ hσ hV)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ (V.ι ⁻¹ᵁ V) hf
          (Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
            (isQuasicoherentPieces_of_isQuasicoherent F) hV x))
      = ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) x) := by
  have hτ : V.ι ⁻¹ᵁ V ≤ (V.ι ≫ σ) ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V) :=
    (congrArg (fun U : X.Opens => V.ι ⁻¹ᵁ U)
      (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) σ hσ V)).ge
  have hobj := restrictChartFactorisationTwistIso_hom_pullbackSection V hV σ (V.ι ≫ σ) rfl
    (sectionChartMap V σ hσ hV) (sectionChartMap_comp_chart V σ hσ hV) (V.ι ⁻¹ᵁ V) le_rfl
    (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) σ hσ V).ge hτ hf x
  have hmor : (restrictChartFactorisationTwistIso V hV σ (V.ι ≫ σ) rfl
          (sectionChartMap V σ hσ hV) (sectionChartMap_comp_chart V σ hσ hV)).hom ≫
        (classifyingTrivialisationOfSection V hV e σ hσ α).hom =
      ((Scheme.Modules.pullback V.ι).mapIso α).hom ≫
        (pullbackIsoUnitOfOverIsoUnit V L e).hom :=
    Iso.hom_inv_id_assoc _ _
  have htriv := comp_val_app_apply_eq
    ((Scheme.Modules.pullback V.ι).map ((tautologicalDatum F).pullbackQuotientMap σ hσ))
    (((Scheme.Modules.pullback V.ι).mapIso α).hom ≫ (pullbackIsoUnitOfOverIsoUnit V L e).hom)
    (V.ι ⁻¹ᵁ V) (pullback_map_pullbackQuotientMap_unitSection V σ hσ x)
  exact (comp_val_app_apply_eq
      (restrictChartFactorisationTwistIso V hV σ (V.ι ≫ σ) rfl (sectionChartMap V σ hσ hV)
        (sectionChartMap_comp_chart V σ hσ hV)).hom
      (classifyingTrivialisationOfSection V hV e σ hσ α).hom (V.ι ⁻¹ᵁ V) hobj).symm.trans
    ((Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr hmor
        (op (V.ι ⁻¹ᵁ V)) _).trans
      (htriv.symm.trans
        (pullback_map_comp_classifyingIso_hom_unitSection V q e σ hσ α hα x)))

end SectionClassify

/-! ### The object comparison over a member of the cover, on the pulled-back tautological map -/

section CoverChain

open Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjTwistPinnedChart
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjGlobalSectionsAppTop (resTop)
open Stacks.ProjectiveFromSections (resT)
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (q : F ⟶ L) [Epi q] (Vt : TrivAffineOpens L)
  (et : L.over Vt.1.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over Vt.1.1))

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [Epi q] in
/-- **The glued section restricted to a member of the cover is a section of `π` over that
member**, as the inclusion of opens the pullback comparisons take as their hypothesis. -/
public theorem preimage_self_le_localSection_preimage
    (hq : Function.Surjective (q.val.app (op Vt.1.1))) :
    Vt.1.1.ι ⁻¹ᵁ Vt.1.1 ≤
      localSection Vt.1.1 q et Vt.1.2 hq ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ Vt.1.1) :=
  (congrArg (fun k : Vt.1.1.toScheme ⟶ X => k ⁻¹ᵁ Vt.1.1)
    (localSection_comp_projectiveBundleToBase Vt.1.1 q et Vt.1.2 hq)).ge

/-- **`Stacks.RelativeProj.globalSectionPullbackTwistIsoOnCover` is
`…RelativeProj.restrictChartFactorisationPullbackTwistIso` at the glued section and the chart
factorisation of `Stacks.RelativeProj.localSection`.** True by `rfl`, and a *morphism*-level
identity: this is the one definitional crossing of the specialisation below, which the consumer's
`Eq.trans` then takes for free. Read on a section instead, the same identity exhausts the
200000-heartbeat budget — see this file's implementation notes. -/
public theorem globalSectionPullbackTwistIsoOnCover_hom
    (hq : Function.Surjective (q.val.app (op Vt.1.1))) {m₀ : Γ(F, Vt.1.1)}
    (hg : localChartMap Vt.1.1 q et hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
        (localDegreeOne Vt.1.1 m₀).1 = ⊤) :
    (globalSectionPullbackTwistIsoOnCover q Vt et hq hg).hom =
      (restrictChartFactorisationPullbackTwistIso Vt.1.1 Vt.1.2 (globalSection q)
        (localSection Vt.1.1 q et Vt.1.2 hq) (ι_comp_globalSection_eq_localSection q Vt et hq)
        (localChartMap Vt.1.1 q et hq)
        (localSection_comp_bundlePresentationIso_inv Vt.1.1 q et Vt.1.2 hq) hg).hom :=
  rfl

/-- **The object comparison over a member of the cover, read on the section the pulled-back
tautological map produces.** This is
`restrictChartFactorisationPullbackTwistIso_hom_pullbackSection` at the glued section and the chart
factorisation of `Stacks.RelativeProj.localSection`, over the open `V.ι ⁻¹ᵁ V`. -/
public theorem globalSectionPullbackTwistIsoOnCover_hom_pullbackSection
    (hq : Function.Surjective (q.val.app (op Vt.1.1))) {m₀ : Γ(F, Vt.1.1)}
    (hg : localChartMap Vt.1.1 q et hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
        (localDegreeOne Vt.1.1 m₀).1 = ⊤) (x : Γ(F, Vt.1.1)) :
    (globalSectionPullbackTwistIsoOnCover q Vt et hq hg).hom.val.app
        (op (Vt.1.1.ι ⁻¹ᵁ Vt.1.1))
        (Scheme.Modules.pullbackSection Vt.1.1.ι
          ((Scheme.Modules.pullback (globalSection q)).obj (tautologicalDatumTwist F))
          Vt.1.1 (Vt.1.1.ι ⁻¹ᵁ Vt.1.1) le_rfl
          (Scheme.Modules.pullbackSection (globalSection q) (tautologicalDatumTwist F)
            (projectiveBundleToBase X F ⁻¹ᵁ Vt.1.1) Vt.1.1
            (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) (globalSection q)
              (globalSection_comp_projectiveBundleToBase q) Vt.1.1).ge
            (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
                (isQuasicoherentPieces_of_isQuasicoherent F))
              ((symGradedBundle F).toBase ⁻¹ᵁ Vt.1.1)
              (projectiveBundleToBase X F ⁻¹ᵁ Vt.1.1)
              (preimage_bundlePresentationIso_inv_preimage_toBase Vt.1.1).ge
              ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                  (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
                (op ((symGradedBundle F).toBase ⁻¹ᵁ Vt.1.1))
                (unitSection (symGradedBundle F).toBase F Vt.1.1 x)))))
      = resT (Vt.1.1.ι ⁻¹ᵁ Vt.1.1) (pullbackDegreeSection _
          (chartFactor _ (localDegreeOne Vt.1.1 m₀).2 (localChartMap Vt.1.1 q et hq) hg)
          (localDegreeOne Vt.1.1 x)) :=
  (Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr
      (globalSectionPullbackTwistIsoOnCover_hom q Vt et hq hg)
      (op (Vt.1.1.ι ⁻¹ᵁ Vt.1.1)) _).trans
    (restrictChartFactorisationPullbackTwistIso_hom_pullbackSection Vt.1.1 Vt.1.2 (globalSection q)
      (localSection Vt.1.1 q et Vt.1.2 hq) (ι_comp_globalSection_eq_localSection q Vt et hq)
      (localChartMap Vt.1.1 q et hq)
      (localSection_comp_bundlePresentationIso_inv Vt.1.1 q et Vt.1.2 hq) hg
      (Vt.1.1.ι ⁻¹ᵁ Vt.1.1) le_rfl
      (preimage_preimage_of_comp_eq_id (projectiveBundleToBase X F) (globalSection q)
        (globalSection_comp_projectiveBundleToBase q) Vt.1.1).ge
      (preimage_self_le_localSection_preimage q Vt et hq) x)

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [Epi q] in
/-- **The pinned frame inverted on the section the chain produces is the trivialised quotient.**

The pinning match `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` says the
restricted pulled-back degree-one section of `x` is `e (q x)` times the frame;
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.pinnedFrameIso_inv_smul_resT` reads the inverse of
the frame isomorphism on such a multiple, returning the scalar; and
`resTop_preimageSelfTopRingHom` cancels the two restrictions between `V` and `V.ι ⁻¹ᵁ V`, which
is what puts the scalar in the spelling the `ℒ` side of the datum produces. -/
public theorem pinnedFrameIso_inv_resT_pullbackDegreeSection
    (hq : Function.Surjective (q.val.app (op Vt.1.1))) {m₀ : Γ(F, Vt.1.1)}
    (hm₀ : ofPushforwardUnit Vt.1.1.ι
      ((trivializedQuotientHom Vt.1.1 q et).val.app (op Vt.1.1) m₀) = 1)
    (hg : localChartMap Vt.1.1 q et hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
        (localDegreeOne Vt.1.1 m₀).1 = ⊤) (x : Γ(F, Vt.1.1)) :
    (pinnedFrameIso
          ((schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
          (localDegreeOne Vt.1.1 m₀) (localChartMap Vt.1.1 q et hq) hg).inv.val.app
        (op (Vt.1.1.ι ⁻¹ᵁ Vt.1.1))
        (resT (Vt.1.1.ι ⁻¹ᵁ Vt.1.1) (pullbackDegreeSection _
          (chartFactor _ (localDegreeOne Vt.1.1 m₀).2 (localChartMap Vt.1.1 q et hq) hg)
          (localDegreeOne Vt.1.1 x)))
      = ofPushforwardUnit Vt.1.1.ι
          ((trivializedQuotientHom Vt.1.1 q et).val.app (op Vt.1.1) x) :=
  (congrArg
      (fun z => (pinnedFrameIso
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
            (localDegreeOne Vt.1.1 m₀) (localChartMap Vt.1.1 q et hq) hg).inv.val.app
          (op (Vt.1.1.ι ⁻¹ᵁ Vt.1.1)) z)
      (resT_pullbackDegreeSection_localChartMap Vt.1.1 q et hq hm₀ hg x
        (Vt.1.1.ι ⁻¹ᵁ Vt.1.1))).trans
    ((pinnedFrameIso_inv_smul_resT _ (localDegreeOne Vt.1.1 m₀)
          (localChartMap Vt.1.1 q et hq) hg (Vt.1.1.ι ⁻¹ᵁ Vt.1.1) _).trans
      (resTop_preimageSelfTopRingHom Vt.1.1 _))

/-- **The `𝒪(1)` side of the local classifying datum, on a pulled-back section** — and it lands
on the same trivialised quotient as the `ℒ` side.

This is the whole chain in one place: `pullback_map_pullbackQuotientMap_unitSection` evaluates
the inverse image of the pulled-back tautological map,
`globalSectionPullbackTwistIsoOnCover_hom_pullbackSection` carries the result across the object
comparison onto the section the pinning match is stated on, and
`pinnedFrameIso_inv_resT_pullbackDegreeSection` inverts the frame on it. -/
public theorem pullbackQuotientMap_comp_pinnedFrameIso_inv_unitSection
    (hq : Function.Surjective (q.val.app (op Vt.1.1))) {m₀ : Γ(F, Vt.1.1)}
    (hm₀ : ofPushforwardUnit Vt.1.1.ι
      ((trivializedQuotientHom Vt.1.1 q et).val.app (op Vt.1.1) m₀) = 1)
    (hg : localChartMap Vt.1.1 q et hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
        (localDegreeOne Vt.1.1 m₀).1 = ⊤) (x : Γ(F, Vt.1.1)) :
    ((Scheme.Modules.pullback Vt.1.1.ι).map
            ((tautologicalDatum F).pullbackQuotientMap (globalSection q)
              (globalSection_comp_projectiveBundleToBase q)) ≫
          (globalSectionPullbackTwistIsoOnCover q Vt et hq hg).hom ≫
            (pinnedFrameIso _ (localDegreeOne Vt.1.1 m₀)
              (localChartMap Vt.1.1 q et hq) hg).inv).val.app
        (op (Vt.1.1.ι ⁻¹ᵁ Vt.1.1)) (unitSection Vt.1.1.ι F Vt.1.1 x)
      = ofPushforwardUnit Vt.1.1.ι
          ((trivializedQuotientHom Vt.1.1 q et).val.app (op Vt.1.1) x) := by
  refine Eq.trans
    (comp_val_app_apply_eq _ _ _ (pullback_map_pullbackQuotientMap_unitSection Vt.1.1
      (globalSection q) (globalSection_comp_projectiveBundleToBase q) x)) ?_
  refine Eq.trans (comp_val_app_apply_eq _ _ _
    (globalSectionPullbackTwistIsoOnCover_hom_pullbackSection q Vt et hq hg x)) ?_
  exact pinnedFrameIso_inv_resT_pullbackDegreeSection q Vt et hq hm₀ hg x

/-- **The object comparison over a member of the cover carries the inverse image of the
pulled-back tautological map to the inverse image of `q`** — the compatibility that the local
classifying datum of
`Stacks.RelativeProj.TautologicalDatum.exists_classifies_of_pullback_cover` asks for, read as an
identity of morphisms rather than of sections.

`Stacks.Chow.GenuineChern.pullback_hom_ext_of_isAffineOpen` at `V.ι` turns the identity of
morphisms into the identity on pulled-back sections over `V`, which is exactly the
quantification the pinning match offers — and that is why the members of
`Stacks.RelativeProj.trivCover` are required to be affine. The two sides on a section are
`pullbackQuotientMap_comp_pinnedFrameIso_inv_unitSection` and
`pullback_map_comp_pullbackIsoUnitOfOverIsoUnit_hom_unitSection`, which land on the same
trivialised quotient. -/
public theorem pullbackQuotientMap_comp_pinnedFrameIso_inv
    (hq : Function.Surjective (q.val.app (op Vt.1.1))) {m₀ : Γ(F, Vt.1.1)}
    (hm₀ : ofPushforwardUnit Vt.1.1.ι
      ((trivializedQuotientHom Vt.1.1 q et).val.app (op Vt.1.1) m₀) = 1)
    (hg : localChartMap Vt.1.1 q et hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading Vt.1.1)
        (localDegreeOne Vt.1.1 m₀).1 = ⊤) :
    (Scheme.Modules.pullback Vt.1.1.ι).map
          ((tautologicalDatum F).pullbackQuotientMap (globalSection q)
            (globalSection_comp_projectiveBundleToBase q)) ≫
        (globalSectionPullbackTwistIsoOnCover q Vt et hq hg).hom ≫
          (pinnedFrameIso _ (localDegreeOne Vt.1.1 m₀)
            (localChartMap Vt.1.1 q et hq) hg).inv
      = (Scheme.Modules.pullback Vt.1.1.ι).map q ≫
          (pullbackIsoUnitOfOverIsoUnit Vt.1.1 L et).hom :=
  Stacks.Chow.GenuineChern.pullback_hom_ext_of_isAffineOpen Vt.1.1.ι Vt.1.2
    Vt.1.1.ι_preimage_self F fun x =>
      (pullbackQuotientMap_comp_pinnedFrameIso_inv_unitSection q Vt et hq hm₀ hg x).trans
        (pullback_map_comp_pullbackIsoUnitOfOverIsoUnit_hom_unitSection Vt.1.1 q et x).symm

/-- **The local classifying datum over a member of the cover, with nothing left for the
consumer.** Over a trivialising affine open the inverse image of the module the glued section
pulls back from `𝒪_{𝐏(ℰ)}(1)` is isomorphic to the inverse image of `ℒ`, by an isomorphism
carrying the inverse image of the pulled-back tautological map to the inverse image of `q`.

The isomorphism is the object comparison
`Stacks.RelativeProj.globalSectionPullbackTwistIsoOnCover`, then the pinned frame
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.pinnedFrameIso` inverted, then the trivialisation
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.pullbackIsoUnitOfOverIsoUnit` inverted; the
compatibility is `pullbackQuotientMap_comp_pinnedFrameIso_inv` cancelled against that last
trivialisation. Everything it needs of the member is produced here: the trivialisation from the
member's own `Nonempty`, the surjectivity on sections from
`Stacks.RelativeProj.surjective_app_of_isAffineOpen_of_epi`, the frame from
`Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` and the standard-open hypothesis
from `Stacks.RelativeProj.preimage_basicOpen_localDegreeOne_eq_top`. -/
public theorem exists_classifyingIso_onCover :
    ∃ α : (Scheme.Modules.pullback Vt.1.1.ι).obj
          ((Scheme.Modules.pullback (globalSection q)).obj (tautologicalDatum F).twist) ≅
        (Scheme.Modules.pullback Vt.1.1.ι).obj L,
      (Scheme.Modules.pullback Vt.1.1.ι).map
            ((tautologicalDatum F).pullbackQuotientMap (globalSection q)
              (globalSection_comp_projectiveBundleToBase q)) ≫ α.hom =
        (Scheme.Modules.pullback Vt.1.1.ι).map q := by
  have hq := surjective_app_of_isAffineOpen_of_epi q Vt.1.2
  obtain ⟨m₀, hm₀⟩ := exists_app_trivializedQuotientHom_eq_one Vt.1.1 q Vt.2.some hq
  have hg := preimage_basicOpen_localDegreeOne_eq_top Vt.1.1 q Vt.2.some hq hm₀
  refine ⟨(globalSectionPullbackTwistIsoOnCover q Vt Vt.2.some hq hg ≪≫
      (pinnedFrameIso _ (localDegreeOne Vt.1.1 m₀) (localChartMap Vt.1.1 q Vt.2.some hq)
        hg).symm) ≪≫
    (pullbackIsoUnitOfOverIsoUnit Vt.1.1 L Vt.2.some).symm, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.Iso.comp_inv_eq (pullbackIsoUnitOfOverIsoUnit Vt.1.1 L Vt.2.some)).mpr
      (pullbackQuotientMap_comp_pinnedFrameIso_inv q Vt Vt.2.some hq hm₀ hg))

/-- **`exists_classifies` for one invertible quotient, at the tautological datum of `𝐏(ℰ)`.**
Every epimorphism `q : ℰ ↠ ℒ` onto an invertible module is classified by a section of
`π : 𝐏(ℰ) ⟶ X`, namely the glued section `Stacks.RelativeProj.globalSection q`.

This is `Stacks.RelativeProj.TautologicalDatum.exists_classifies_of_pullback_cover` at the cover
of `X` by the trivialising affine opens — a cover by
`Stacks.RelativeProj.exists_trivAffineOpen_mem_le` — fed with the local classifying datum
`exists_classifyingIso_onCover`, which needs nothing of the consumer. -/
public theorem exists_classifies_globalSection
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    ∃ σ : X ⟶ projectiveBundle X F, ∃ hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X,
      (tautologicalDatum F).Classifies σ hσ ⟨L, hL, q, ‹Epi q›⟩ :=
  (tautologicalDatum F).exists_classifies_of_pullback_cover q hL
    (fun Vt : TrivAffineOpens L => Vt.1.1)
    (fun x => by
      obtain ⟨Vt, hxV, -⟩ := exists_trivAffineOpen_mem_le (L := L) (U := ⊤) (x := x) trivial
      exact ⟨Vt, hxV⟩)
    (fun Vt => exists_classifyingIso_onCover q Vt)

end CoverChain

/-! ### `exists_classifies` for the tautological datum of the projective bundle -/

section Universal

open Opposite

/-- **Every invertible quotient of `ℰ` is classified by a section of `π : 𝐏(ℰ) ⟶ X`.**

This is the first field of `Stacks.RelativeProj.TautologicalDatum.IsUniversal` for the
repository's own tautological datum `Stacks.RelativeProj.tautologicalDatum`, discharged. The
section is `Stacks.RelativeProj.globalSection` of the quotient map, and that it *classifies* the
quotient — the content that `Stacks.RelativeProj.exists_section_of_invertibleQuotient` stops
short of — is `exists_classifies_globalSection`.

The second field is `eq_of_classifies_tautologicalDatum` below; with both of them
`isUniversal_tautologicalDatum` is an instance and `projectiveBundleSectionsEquiv` is
[Stacks, Tag 0B3V]'s bijection, unconditionally. -/
@[ega "II 4.2.5" "special case"]
public theorem exists_classifies_tautologicalDatum
    (Q : Stacks.Divisors.InvertibleQuotient X F) :
    ∃ σ : X ⟶ projectiveBundle X F, ∃ hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X,
      (tautologicalDatum F).Classifies σ hσ Q := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Q.L :=
    Q.invertible
  have : Epi Q.q := Q.epi
  exact exists_classifies_globalSection Q.q Q.invertible

end Universal


/-! ### The nonvanishing open of a global section trivialised to a unit -/

section Nonvanishing

open Opposite
open Stacks.NonvanishingOpen (nonvanishingOpen)

/-- **The nonvanishing locus of a global section of the structure sheaf is its basic open**, in
the `Γ(M, ⊤)` spelling.

[Stacks, Tag 01CY]'s nonvanishing locus comes in two spellings in this repository — over a
restriction-compatible family (`Stacks.SheafOfModules.nonvanishingLocus`) and over a global
element (`Stacks.Ample.nonvanishingLocus`) — and the identification with the basic open is
proved only in the first, as `Stacks.SheafOfModules.nonvanishingLocus_unit_eq_basicOpen`. This
is the second, by the bridge `Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop`; the
`Stacks.NonvanishingOpen.nonvanishingOpen` of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq_nonvanishingOpen` is
built on the second, which is why the transport is needed at all. -/
@[ega "0 5.5.2" "special case"]
public theorem nonvanishingLocus_unit_eq_basicOpen {Y : Scheme.{u}}
    (r : Γ(SheafOfModules.unit Y.ringCatSheaf, (⊤ : Y.Opens))) :
    Stacks.Ample.nonvanishingLocus (SheafOfModules.unit Y.ringCatSheaf) r
      = (Y.basicOpen (U := ⊤) r : Set Y) :=
  (Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop _ r).symm.trans
    ((Stacks.SheafOfModules.nonvanishingLocus_unit_eq_basicOpen Y.toRingedSpace
      (Stacks.SheafOfModules.sectionsOfTop _ r)).trans
      (congrArg (fun z => (Y.basicOpen (U := ⊤) z : Set Y))
        (Stacks.SheafOfModules.sectionsOfTop_eval_top _ r)))

/-- **A global section that a trivialisation carries to a unit vanishes nowhere.** This is the
statement that the nonvanishing open of a section is carried along an isomorphism of
`𝒪_Y`-modules, in the only form the route needs: the isomorphism lands in the structure sheaf,
where nonvanishing is being a unit.

`Stacks.Ample.nonvanishingLocus_congr` moves the locus across the isomorphism and
`nonvanishingLocus_unit_eq_basicOpen` computes it on the other side. The section is given
up to an equation (`hss`) because the consumer meets it in a different spelling, and the
substitution is performed here, where the module is a variable — read at the projective bundle's
twist instead, the same `congrArg` exhausts the recursion budget. -/
@[ega "0 5.5.2" "special case"]
public theorem nonvanishingOpen_eq_top_of_isoUnit {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M]
    (ε : M ≅ SheafOfModules.unit Y.ringCatSheaf) {s s' : Γ(M, (⊤ : Y.Opens))} (hss : s = s')
    {r : Γ(Y, (⊤ : Y.Opens))}
    (hr : ε.hom.val.app (op (⊤ : Y.Opens)) s' = r) (hs : IsUnit r) :
    nonvanishingOpen Y M s = ⊤ :=
  (congrArg (nonvanishingOpen Y M) hss).trans (TopologicalSpace.Opens.ext
    (((Stacks.Ample.nonvanishingLocus_congr ε s').symm.trans
        (nonvanishingLocus_unit_eq_basicOpen (ε.hom.app ⊤ s'))).trans
      (congrArg (fun U : Y.Opens => (U : Set Y))
        ((congrArg (fun z : Γ(Y, (⊤ : Y.Opens)) => Y.basicOpen z)
            (show ε.hom.app ⊤ s' = r from hr)).trans
          (Y.basicOpen_of_isUnit hs)))))

/-- **The `hom` of a `pullbackCongr`-then-anything composite**, at an opaque pair of equal
morphisms and an opaque module. True by `rfl`, and split off for the heartbeat rule: it is the
one definitional crossing of `nonvanishingOpen_pullbackSection_eq_top`, which then reaches the
section level through `Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr`. -/
public theorem pullbackCongrApp_trans_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g)
    (M : Z.Modules) {N : Y.Modules} (ε : (Scheme.Modules.pullback g).obj M ≅ N) :
    ((Scheme.Modules.pullbackCongr h).app M ≪≫ ε).hom
      = ((Scheme.Modules.pullbackCongr h).hom.app M) ≫ ε.hom :=
  rfl

/-- **The nonvanishing open of a pulled-back global section is everything**, when the inverse
image along an *equal* morphism is trivialised so as to carry that section to a unit.

This is the step that turns the degree-one dictionary into the standard-open hypothesis, and
every piece of it is stated at opaque morphisms and an opaque module, so that the consumer
instantiates rather than unfolds: the two morphisms differ by
`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.toProj_factorThroughDegreeOpenOne`, the module
is the absolute twisting sheaf, and `ε` is
`Stacks.RelativeProj.classifyingTrivialisationOfSection`. The comparison of the two pullbacks is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr`, cancelled against `ε` by
`comp_val_app_apply_eq`. -/
public theorem nonvanishingOpen_pullbackSection_eq_top {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    (hfg : f = g) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback f).obj M)]
    (ε : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (hf : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : Z.Opens)) (hg : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (⊤ : Z.Opens))
    {a a' : Γ(M, (⊤ : Z.Opens))} (haa : a = a')
    {s : Γ((Scheme.Modules.pullback f).obj M, (⊤ : Y.Opens))}
    (hs : s = Scheme.Modules.pullbackSection f M ⊤ ⊤ hf a)
    {r : Γ(Y, (⊤ : Y.Opens))}
    (hr : ε.hom.val.app (op (⊤ : Y.Opens))
      (Scheme.Modules.pullbackSection g M ⊤ ⊤ hg a') = r) (hu : IsUnit r) :
    nonvanishingOpen Y ((Scheme.Modules.pullback f).obj M) s = ⊤ := by
  subst haa
  exact nonvanishingOpen_eq_top_of_isoUnit _ ((Scheme.Modules.pullbackCongr hfg).app M ≪≫ ε) hs
    ((Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr
          (pullbackCongrApp_trans_hom hfg M ε) (op ⊤) _).trans
      ((comp_val_app_apply_eq ((Scheme.Modules.pullbackCongr hfg).hom.app M) ε.hom ⊤
          (Scheme.Modules.pullbackSection_congr hfg M ⊤ ⊤ hf hg a)).trans hr))
    hu

end Nonvanishing

end Stacks.RelativeProj

end
