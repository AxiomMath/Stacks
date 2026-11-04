module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chain of sections, and the chart factorisation of a section of `π`

* The chain of sections joining the object comparison to the pinning match.
* The object comparison over an affine open, at an arbitrary section of `π`.
* `Stacks.RelativeProj.sectionChartMap`: the chart factorisation of an arbitrary section of `π`.
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

/-! ### The chain of sections joining the object comparison to the pinning match -/

section ChainOfSections

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

variable (V : X.Opens) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))

/-- **The two restrictions between `V` and `V.ι ⁻¹ᵁ V` cancel.** The inverse image of `V` along
its own inclusion is all of `V`, so `Stacks.RelativeProj.preimageSelfTopRingHom` and the
restriction of a global section of `𝒪_V` back to `V.ι ⁻¹ᵁ V` are mutually inverse restrictions
between two equal opens.

This is what turns the scalar the pinning match
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` produces — a global section of
`𝒪_V` restricted to the open the match is read over — into the scalar the `ℒ` side of the local
classifying datum produces, which
`pullbackIsoUnitOfOverIsoUnit_hom_pullback_map_unitSection` delivers over `V.ι ⁻¹ᵁ V`. -/
public theorem resTop_preimageSelfTopRingHom
    (z : V.toScheme.ringCatSheaf.obj.obj (op (V.ι ⁻¹ᵁ V))) :
    resTop (V.ι ⁻¹ᵁ V) (preimageSelfTopRingHom V z) = z := by
  have h : V.toScheme.presheaf.map (homOfLE V.ι_preimage_self.ge).op ≫
      V.toScheme.presheaf.map (homOfLE (le_top (a := V.ι ⁻¹ᵁ V))).op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp,
      show homOfLE (le_top (a := V.ι ⁻¹ᵁ V)) ≫ homOfLE V.ι_preimage_self.ge = 𝟙 _ from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  exact CategoryTheory.ConcreteCategory.congr_hom h z

/-- Evaluating `pullbackComp`, `pullbackCongr` and a trailing iso on a twice-pulled-back section. -/
private theorem pullbackSection_pullbackComp_pullbackCongr_trans {S P T : Scheme.{u}}
    (c : T ⟶ S) (σ : S ⟶ P) (τ : T ⟶ P) (hcs : c ≫ σ = τ) (M : P.Modules) {N : T.Modules}
    (ψ : (Scheme.Modules.pullback τ).obj M ≅ N)
    (U : P.Opens) (W : S.Opens) (V' : T.Opens) (hW : W ≤ σ ⁻¹ᵁ U) (hV : V' ≤ c ⁻¹ᵁ W)
    (hτ : V' ≤ τ ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp c σ).app M ≪≫
        (Scheme.Modules.pullbackCongr hcs).app M ≪≫ ψ).hom.val.app (op V')
        (Scheme.Modules.pullbackSection c ((Scheme.Modules.pullback σ).obj M) W V' hV
          (Scheme.Modules.pullbackSection σ M U W hW a))
      = ψ.hom.val.app (op V') (Scheme.Modules.pullbackSection τ M U V' hτ a) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op V') _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op V') _) ?_
  exact congrArg (fun z => ψ.hom.val.app (op V') z)
    ((SheafOfModules.comp_val_app_apply _ _ (op V') _).symm.trans
      (pullbackSection_compCongr_map c σ τ hcs M U W V' hW hV hτ a))

/-- **A factorisation `c ≫ b = cm ≫ ch` carried forwards across the four comparisons it
induces, on a twice-pulled-back section.** The composite
`pullbackComp`-`pullbackCongr`-`pullbackComp⁻¹`-`pullback cm`-of-`ti` sends the pullback along
`c` of the pullback along `b` of `a` to the pullback along `cm` of the value of `ti` at the
pullback of `a` along `ch`.

**This is the shape `Stacks.RelativeProj.localSectionTwistIso` is literally in**, so that
comparison's evaluation on sections is an instance of this one with the chart layer of the bundle
never unfolded: the four morphisms of schemes are *variables*. The legs are
`pullbackSection_compCongr_map` for the first two, `pullbackComp_inv_pullbackSection` for the
third and `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality` for the last. -/
public theorem pullbackSection_fourComparisons_map {Y P Q C : Scheme.{u}} (c : Y ⟶ P)
    (b : P ⟶ Q) (cm : Y ⟶ C) (ch : C ⟶ Q) (hcs : c ≫ b = cm ≫ ch) (M : Q.Modules)
    {N : C.Modules} (ti : (Scheme.Modules.pullback ch).obj M ≅ N)
    (U : Q.Opens) (T : P.Opens) (Tc : C.Opens) (W : Y.Opens)
    (hb : T ≤ b ⁻¹ᵁ U) (hτ : W ≤ c ⁻¹ᵁ T) (hc : Tc ≤ ch ⁻¹ᵁ U) (hf : W ≤ cm ⁻¹ᵁ Tc)
    (a : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp c b).app M ≪≫
        (Scheme.Modules.pullbackCongr hcs).app M ≪≫
          ((Scheme.Modules.pullbackComp cm ch).app M).symm ≪≫
            (Scheme.Modules.pullback cm).mapIso ti).hom.val.app (op W)
        (Scheme.Modules.pullbackSection c ((Scheme.Modules.pullback b).obj M) T W hτ
          (Scheme.Modules.pullbackSection b M U T hb a))
      = Scheme.Modules.pullbackSection cm N Tc W hf
          (ti.hom.val.app (op Tc) (Scheme.Modules.pullbackSection ch M U Tc hc a)) := by
  have hcc : W ≤ (cm ≫ ch) ⁻¹ᵁ U := hf.trans (cm.preimage_mono hc)
  refine (pullbackSection_pullbackComp_pullbackCongr_trans c b (cm ≫ ch) hcs M
    (((Scheme.Modules.pullbackComp cm ch).app M).symm ≪≫ (Scheme.Modules.pullback cm).mapIso ti)
    U T W hb hτ hcc a).trans ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ (op W) _) ?_
  refine Eq.trans (congrArg
    (fun z => ((Scheme.Modules.pullback cm).map ti.hom).val.app (op W) z)
    (pullbackComp_inv_pullbackSection cm ch M U Tc W hc hf hcc a)) ?_
  exact Scheme.Modules.pullbackSection_naturality cm ti.hom Tc W hf _

/-- **`Stacks.RelativeProj.chartFactorisationPullbackTwistIso` is
`…RelativeProj.chartFactorisationTwistIso` followed by the transport along
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.toProj_chartFactor`.** True by `rfl`, and **a
morphism-level identity on purpose**: the same statement read on a *section* costs the whole
200000-heartbeat budget, because `isDefEq` then whnfs the two sides as elements of a `ModuleCat`
carrier and unfolds the pullback construction itself. At the level of morphisms it is free, and a
consumer reaches the section form by one `congrArg`.

It also needs the `implicit_reducible` attributes of this section: the objects mention the
reducible abbreviations `Stacks.RelativeProj.projectiveBundle`,
`…RelativeProj.projectiveBundleToBase` and `…RelativeProj.tautologicalDatumTwist`, through which
the unifier otherwise unfolds the chart layer. -/
public theorem chartFactorisationPullbackTwistIso_hom {Y : Scheme.{u}} (hV : IsAffineOpen V)
    (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) :
    (chartFactorisationPullbackTwistIso V hV g h hgh hg).hom =
      (chartFactorisationTwistIso V hV g h hgh).hom ≫
        ((Scheme.Modules.pullbackCongr
            (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).app
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1)).hom :=
  rfl

/-- **`Stacks.RelativeProj.chartFactorisationTwistIso` written out as the composite of the four
`AlgebraicGeometry.Scheme.Modules.pullback` comparisons it is.** True by `rfl`; named for the
same reason, and split from `chartFactorisationPullbackTwistIso_hom` for the same reason — the two
identities together exceed one heartbeat budget, separately each is free. -/
public theorem chartFactorisationTwistIso_hom {Y : Scheme.{u}} (hV : IsAffineOpen V)
    (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV) :
    (chartFactorisationTwistIso V hV g h hgh).hom =
      ((Scheme.Modules.pullbackComp g (bundlePresentationIso F).inv).app
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F)) ≪≫
          (Scheme.Modules.pullbackCongr hgh).app _ ≪≫
          ((Scheme.Modules.pullbackComp h ((symGradedBundle F).chart V hV)).app _).symm ≪≫
          (Scheme.Modules.pullback h).mapIso
            (Stacks.ProjectiveBundle.chartTwistIso F
              (isQuasicoherentPieces_of_isQuasicoherent F) hV)).hom :=
  rfl

/-- **The twist comparison at the local chart, read on the pulled-back tautological section**,
over an arbitrary open `W` of `V`.

`Stacks.RelativeProj.chartFactorisationTwistIso` is four
`AlgebraicGeometry.Scheme.Modules.pullback` comparisons, and this evaluates all four on the
section that `Stacks.RelativeProj.pullbackQuotientMap_tautologicalDatum_val_app` produces: the
pullback along `bundlePresentationIso.inv` of the value of
`Stacks.ProjectiveBundleSplitting.tautologicalMap` at the pullback of `m`. The result is the
pullback along `h` of `Stacks.ProjectiveBundleConormal.chartDegreeOneSection`.

The content is `pullbackSection_fourComparisons_map` at the four morphisms, with
`Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection` evaluating
the chart comparison; `chartFactorisationTwistIso_hom` is what lets the generic statement be cited
without unfolding the chart layer. -/
@[ega "II 4.2.1" "partial"]
public theorem chartFactorisationTwistIso_hom_pullbackSection {Y : Scheme.{u}}
    (hV : IsAffineOpen V) (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)
    (W : Y.Opens) (hτ : W ≤ g ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V))
    (hf : W ≤ h ⁻¹ᵁ ⊤) (m : Γ(F, V)) :
    (chartFactorisationTwistIso V hV g h hgh).hom.val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F)))
          (projectiveBundleToBase X F ⁻¹ᵁ V) W hτ
          (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F))
            ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
            (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
              (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
              (unitSection (symGradedBundle F).toBase F V m))))
      = Scheme.Modules.pullbackSection h
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ W hf
          (Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
            (isQuasicoherentPieces_of_isQuasicoherent F) hV m) := by
  refine Eq.trans (Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr
    (chartFactorisationTwistIso_hom V hV g h hgh) (op W) _) ?_
  refine Eq.trans (pullbackSection_fourComparisons_map g
    (bundlePresentationIso F).inv h ((symGradedBundle F).chart V hV) hgh
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
      (isQuasicoherentPieces_of_isQuasicoherent F))
    (Stacks.ProjectiveBundle.chartTwistIso F
      (isQuasicoherentPieces_of_isQuasicoherent F) hV)
    ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V) ⊤ W
    (preimage_bundlePresentationIso_inv_preimage_toBase V).ge hτ
    (Stacks.ProjectiveBundleConormal.top_le_chart_preimage F
      (isQuasicoherentPieces_of_isQuasicoherent F) hV) hf
    ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
        (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
      (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
      (unitSection (symGradedBundle F).toBase F V m))) ?_
  exact congrArg
    (Scheme.Modules.pullbackSection h
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ W hf)
    (Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection F
      (isQuasicoherentPieces_of_isQuasicoherent F) hV m)

/-- **`Stacks.RelativeProj.chartFactorisationPullbackTwistIso` split into its first four
comparisons and its fifth, read on the pulled-back tautological section.** This is
`chartFactorisationPullbackTwistIso_hom` carried from morphisms to sections by
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr`.

It is a separate declaration, and it stops at the *composite* rather than at the nested
application, because interposing `SheafOfModules.comp_val_app_apply` here costs the whole
200000-heartbeat budget while the consumer's `Eq.trans` crosses the same step for free. -/
public theorem chartFactorisationPullbackTwistIso_hom_val_app {Y : Scheme.{u}}
    (hV : IsAffineOpen V) (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) (W : Y.Opens)
    (hτ : W ≤ g ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V)) (m : Γ(F, V)) :
    (chartFactorisationPullbackTwistIso V hV g h hgh hg).hom.val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F)))
          (projectiveBundleToBase X F ⁻¹ᵁ V) W hτ
          (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F))
            ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
            (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
              (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
              (unitSection (symGradedBundle F).toBase F V m))))
      = ((chartFactorisationTwistIso V hV g h hgh).hom ≫
          ((Scheme.Modules.pullbackCongr
              (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).app
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
              ((schemeSheafGradedAlgebra F
                (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1)).hom).val.app (op W)
        (
        (Scheme.Modules.pullbackSection g
          ((Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F)))
          (projectiveBundleToBase X F ⁻¹ᵁ V) W hτ
          (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F))
            ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
            (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
              (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
              (unitSection (symGradedBundle F).toBase F V m))))) :=
  Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr
    (chartFactorisationPullbackTwistIso_hom V hV g h hgh hg) (op W) _

/-- **The fifth comparison carries the chart's degree-one section to the section the pinning
match is stated on.** `Stacks.RelativeProj.pullbackCongr_hom_pullbackSection_chartDegreeOneSection`
over an arbitrary open, followed by `pullbackSection_top_eq_resT` and
`pullbackDegreeSection_eq_pullbackSection` — the dictionary from the
`AlgebraicGeometry.Scheme.Modules.pullbackSection` spelling the comparisons produce to the
`Stacks.ProjectiveFromSections.resT`-of-a-global-section spelling the pinning match uses. -/
public theorem pullbackCongr_hom_pullbackSection_chartDegreeOneSection_resT {Y : Scheme.{u}}
    (hV : IsAffineOpen V)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) (W : Y.Opens)
    (hf : W ≤ h ⁻¹ᵁ ⊤) (m : Γ(F, V)) :
    ((Scheme.Modules.pullbackCongr
          (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).app
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1)).hom.val.app (op W)
        (Scheme.Modules.pullbackSection h
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ W hf
          (Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
            (isQuasicoherentPieces_of_isQuasicoherent F) hV m))
      = resT W (pullbackDegreeSection _
          (chartFactor _ (localDegreeOne V m₀).2 h hg) (localDegreeOne V m)) :=
  have hW' : W ≤ toProj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
      (chartFactor _ (localDegreeOne V m₀).2 h hg) ⁻¹ᵁ ⊤ :=
    le_top.trans (Scheme.Hom.preimage_top _).ge
  have ht : (⊤ : Y.Opens) ≤ toProj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
      (chartFactor _ (localDegreeOne V m₀).2 h hg) ⁻¹ᵁ ⊤ :=
    (Scheme.Hom.preimage_top _).ge
  (pullbackCongr_hom_pullbackSection_chartDegreeOneSection V hV h hg m W hf hW').trans
    ((pullbackSection_top_eq_resT _ _ W hW' ht _).trans
      (congrArg (resT W)
        (pullbackDegreeSection_eq_pullbackSection _ _ (localDegreeOne V m) ht).symm))

/-- **The twist comparison at a chart factorisation, through all five of its comparisons, read on
the pulled-back tautological section** — over an arbitrary open `W` of the source. **The result is
the section the pinning match `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` is
stated on**, restricted to `W`.

The first four comparisons are `chartFactorisationTwistIso_hom_pullbackSection`; the fifth is
`chartFactorisationPullbackTwistIso_hom_val_app` together with
`pullbackCongr_hom_pullbackSection_chartDegreeOneSection_resT`, which is where
`Stacks.RelativeProj.pullbackCongr_hom_pullbackSection_chartDegreeOneSection` over an arbitrary
open is consumed. -/
public theorem chartFactorisationPullbackTwistIso_hom_pullbackSection {Y : Scheme.{u}}
    (hV : IsAffineOpen V) (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) (W : Y.Opens)
    (hτ : W ≤ g ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V)) (m : Γ(F, V)) :
    (chartFactorisationPullbackTwistIso V hV g h hgh hg).hom.val.app (op W)
        (Scheme.Modules.pullbackSection g
          ((Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F)))
          (projectiveBundleToBase X F ⁻¹ᵁ V) W hτ
          (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F))
            ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
            (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
              (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
              (unitSection (symGradedBundle F).toBase F V m))))
      = resT W (pullbackDegreeSection _
          (chartFactor _ (localDegreeOne V m₀).2 h hg) (localDegreeOne V m)) :=
  have hf : W ≤ h ⁻¹ᵁ ⊤ := le_top.trans (Scheme.Hom.preimage_top h).ge
  (chartFactorisationPullbackTwistIso_hom_val_app V hV g h hgh hg W hτ m).trans
    ((congrArg
        (fun z => ((Scheme.Modules.pullbackCongr
              (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).app
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1)).hom.val.app (op W) z)
        (chartFactorisationTwistIso_hom_pullbackSection V hV g h hgh W hτ hf m)).trans
      (pullbackCongr_hom_pullbackSection_chartDegreeOneSection_resT V hV h hg W hf m))

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The twist comparison at the local chart, through all five of its comparisons, read on the
pulled-back tautological section.** This is
`chartFactorisationPullbackTwistIso_hom_pullbackSection` at the chart factorisation
`Stacks.RelativeProj.localSection_comp_bundlePresentationIso_inv`, which is the pair the descent
below consumes. -/
public theorem localSectionPullbackTwistIso_hom_pullbackSection (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) {m₀ : Γ(F, V)}
    (hg : localChartMap V q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) (W : V.toScheme.Opens)
    (hτ : W ≤ localSection V q e hV hq ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V)) (m : Γ(F, V)) :
    (localSectionPullbackTwistIso V q e hV hq hg).hom.val.app (op W)
        (Scheme.Modules.pullbackSection (localSection V q e hV hq)
          ((Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F)))
          (projectiveBundleToBase X F ⁻¹ᵁ V) W hτ
          (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
              (isQuasicoherentPieces_of_isQuasicoherent F))
            ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
            (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
            ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
              (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
              (unitSection (symGradedBundle F).toBase F V m))))
      = resT W (pullbackDegreeSection _
          (chartFactor _ (localDegreeOne V m₀).2 (localChartMap V q e hq) hg)
          (localDegreeOne V m)) :=
  chartFactorisationPullbackTwistIso_hom_pullbackSection V hV (localSection V q e hV hq)
    (localChartMap V q e hq) (localSection_comp_bundlePresentationIso_inv V q e hV hq) hg W hτ m

/-- **A composite read on a section whose first value is known.** `comp_val_app_apply` with the
value of the first morphism substituted in one step.

It exists because the substitution written as a `congrArg` over an explicit composite is matched
against the goal by `isDefEq` on two closed terms, and on this layer that costs the whole
200000-heartbeat budget; stated with the two morphisms as *variables* the same step is a
metavariable assignment. -/
public theorem comp_val_app_apply_eq {Y : Scheme.{u}} {A B C : Y.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (W : Y.Opens) {z : Γ(A, W)} {w : Γ(B, W)} (h : f.val.app (op W) z = w) :
    (f ≫ g).val.app (op W) z = g.val.app (op W) w :=
  (SheafOfModules.comp_val_app_apply f g (op W) z).trans
    (congrArg (fun y => g.val.app (op W) y) h)

/-- **A factorisation `c ≫ σ = τ` carried forwards across the two comparisons it induces and
then along an arbitrary morphism out of `τ^*M`, on a twice-pulled-back section.**

This is `pullbackSection_compCongr_map` with a trailing isomorphism `ψ`, which is the shape
`Stacks.RelativeProj.globalSectionPullbackTwistIsoOnCover` is literally in: its `hom` is the
`pullbackComp` of `(V.ι, globalSection q)`, then the `pullbackCongr` of
`Stacks.RelativeProj.ι_comp_globalSection_eq_localSection`, then
`Stacks.RelativeProj.localSectionPullbackTwistIso`. Stated at opaque morphisms so that the
specialisation unfolds nothing. -/
public theorem pullbackSection_compCongrTrans_map {S P T : Scheme.{u}} (c : T ⟶ S) (σ : S ⟶ P)
    (τ : T ⟶ P) (hcs : c ≫ σ = τ) (M : P.Modules) {N : T.Modules}
    (ψ : (Scheme.Modules.pullback τ).obj M ≅ N)
    (U : P.Opens) (W : S.Opens) (V' : T.Opens) (hW : W ≤ σ ⁻¹ᵁ U) (hV : V' ≤ c ⁻¹ᵁ W)
    (hτ : V' ≤ τ ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp c σ).app M ≪≫
        (Scheme.Modules.pullbackCongr hcs).app M ≪≫ ψ).hom.val.app (op V')
        (Scheme.Modules.pullbackSection c ((Scheme.Modules.pullback σ).obj M) W V' hV
          (Scheme.Modules.pullbackSection σ M U W hW a))
      = ψ.hom.val.app (op V') (Scheme.Modules.pullbackSection τ M U V' hτ a) :=
  pullbackSection_pullbackComp_pullbackCongr_trans c σ τ hcs M ψ U W V' hW hV hτ a

end ChainOfSections

/-! ### The object comparison over an affine open, at an arbitrary section of `π` -/

section RestrictChain

open Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjTwistPinnedChart
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjectiveFromSections (resT)
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (V : X.Opens) (hV : IsAffineOpen V) (σ : X ⟶ projectiveBundle X F)
  (τ : V.toScheme ⟶ projectiveBundle X F) (hcs : V.ι ≫ σ = τ)
  (h : V.toScheme ⟶ AlgebraicGeometry.Proj
    ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
  (hgh : τ ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)

/-- **`Stacks.RelativeProj.restrictChartFactorisationTwistIso` written out as the composite of
the three comparisons it is.** True by `rfl`, at the level of morphisms. -/
public theorem restrictChartFactorisationTwistIso_hom :
    (restrictChartFactorisationTwistIso V hV σ τ hcs h hgh).hom =
      ((Scheme.Modules.pullbackComp V.ι σ).app (tautologicalDatumTwist F) ≪≫
        (Scheme.Modules.pullbackCongr hcs).app (tautologicalDatumTwist F) ≪≫
        chartFactorisationTwistIso V hV τ h hgh).hom :=
  rfl

/-- **The object comparison over an affine open, read on the section the pulled-back tautological
map produces — at an arbitrary section `σ` of `π` and with no standard-open hypothesis.**

The value is the pullback along `h` of
`Stacks.ProjectiveBundleConormal.chartDegreeOneSection`, the degree-one section of `Sym ℰ`
attached to `x`. This is the form that *produces* the hypothesis `hg` rather than assuming it:
composed with the trivialisation a `Classifies` isomorphism gives, it says that the pulled-back
degree-one section of `x` is `e (q x)`, and at an `x` whose trivialised quotient is the unit the
section is therefore nowhere vanishing.

The first two comparisons are `pullbackSection_compCongrTrans_map`, the rest is
`chartFactorisationTwistIso_hom_pullbackSection`. -/
public theorem restrictChartFactorisationTwistIso_hom_pullbackSection (W : V.toScheme.Opens)
    (hWV : W ≤ V.ι ⁻¹ᵁ V) (hσV : V ≤ σ ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V))
    (hτ : W ≤ τ ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V)) (hf : W ≤ h ⁻¹ᵁ ⊤) (x : Γ(F, V)) :
    (restrictChartFactorisationTwistIso V hV σ τ hcs h hgh).hom.val.app (op W)
        (Scheme.Modules.pullbackSection V.ι
          ((Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F)) V W hWV
          (Scheme.Modules.pullbackSection σ (tautologicalDatumTwist F)
            (projectiveBundleToBase X F ⁻¹ᵁ V) V hσV
            (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
                (isQuasicoherentPieces_of_isQuasicoherent F))
              ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
              (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
              ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                  (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
                (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
                (unitSection (symGradedBundle F).toBase F V x)))))
      = Scheme.Modules.pullbackSection h
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ W hf
          (Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
            (isQuasicoherentPieces_of_isQuasicoherent F) hV x) :=
  (Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr
      (restrictChartFactorisationTwistIso_hom V hV σ τ hcs h hgh) (op W) _).trans
    ((pullbackSection_compCongrTrans_map V.ι σ τ hcs (tautologicalDatumTwist F)
          (chartFactorisationTwistIso V hV τ h hgh)
          (projectiveBundleToBase X F ⁻¹ᵁ V) V W hσV hWV hτ _).trans
      (chartFactorisationTwistIso_hom_pullbackSection V hV τ h hgh W hτ hf x))

/-- **`Stacks.RelativeProj.restrictChartFactorisationPullbackTwistIso` written out as the
composite of the three comparisons it is.** True by `rfl`, and at the level of morphisms for the
reason given at `chartFactorisationPullbackTwistIso_hom`. -/
public theorem restrictChartFactorisationPullbackTwistIso_hom {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) :
    (restrictChartFactorisationPullbackTwistIso V hV σ τ hcs h hgh hg).hom =
      ((Scheme.Modules.pullbackComp V.ι σ).app (tautologicalDatumTwist F) ≪≫
        (Scheme.Modules.pullbackCongr hcs).app (tautologicalDatumTwist F) ≪≫
        chartFactorisationPullbackTwistIso V hV τ h hgh hg).hom :=
  rfl

/-- **The object comparison over an affine open, read on the section the pulled-back tautological
map produces — at an arbitrary section `σ` of `π`.**

`Stacks.RelativeProj.restrictChartFactorisationPullbackTwistIso` is two
`AlgebraicGeometry.Scheme.Modules.pullback` comparisons in front of
`Stacks.RelativeProj.chartFactorisationPullbackTwistIso`, and this evaluates all of them on the
twice pulled-back section that `pullbackQuotientMap_tautologicalDatum_val_app` — which is already
stated at an arbitrary `σ` — produces. **The value is the section the pinning match
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` is stated on.**

The first two comparisons are `pullbackSection_compCongrTrans_map`, the rest is
`chartFactorisationPullbackTwistIso_hom_pullbackSection`. -/
public theorem restrictChartFactorisationPullbackTwistIso_hom_pullbackSection {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) (W : V.toScheme.Opens) (hWV : W ≤ V.ι ⁻¹ᵁ V)
    (hσV : V ≤ σ ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V))
    (hτ : W ≤ τ ⁻¹ᵁ (projectiveBundleToBase X F ⁻¹ᵁ V)) (x : Γ(F, V)) :
    (restrictChartFactorisationPullbackTwistIso V hV σ τ hcs h hgh hg).hom.val.app (op W)
        (Scheme.Modules.pullbackSection V.ι
          ((Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F)) V W hWV
          (Scheme.Modules.pullbackSection σ (tautologicalDatumTwist F)
            (projectiveBundleToBase X F ⁻¹ᵁ V) V hσV
            (Scheme.Modules.pullbackSection (bundlePresentationIso F).inv
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
                (isQuasicoherentPieces_of_isQuasicoherent F))
              ((symGradedBundle F).toBase ⁻¹ᵁ V) (projectiveBundleToBase X F ⁻¹ᵁ V)
              (preimage_bundlePresentationIso_inv_preimage_toBase V).ge
              ((Stacks.ProjectiveBundleSplitting.tautologicalMap F
                  (isQuasicoherentPieces_of_isQuasicoherent F)).val.app
                (op ((symGradedBundle F).toBase ⁻¹ᵁ V))
                (unitSection (symGradedBundle F).toBase F V x)))))
      = resT W (pullbackDegreeSection _
          (chartFactor _ (localDegreeOne V m₀).2 h hg) (localDegreeOne V x)) :=
  (Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr
      (restrictChartFactorisationPullbackTwistIso_hom V hV σ τ hcs h hgh hg) (op W) _).trans
    ((pullbackSection_compCongrTrans_map V.ι σ τ hcs (tautologicalDatumTwist F)
          (chartFactorisationPullbackTwistIso V hV τ h hgh hg)
          (projectiveBundleToBase X F ⁻¹ᵁ V) V W hσV hWV hτ _).trans
      (chartFactorisationPullbackTwistIso_hom_pullbackSection V hV τ h hgh hg W hτ x))

end RestrictChain

/-! ### The chart factorisation of an arbitrary section of `π` -/

section SectionChart

open Opposite
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (V : X.Opens) (σ : X ⟶ projectiveBundle X F)

/-- **The restriction to `V` of a section of `π`, read into the `SheafGradedAlgebra`
presentation, lies over `V`.** One cancellation: `bundlePresentationIso.inv` carries the
projection of the `Situation` presentation to the projection of the other
(`Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase`), and `σ` is a section of the
first.

This is the hypothesis of `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver` at
`w = 𝟙 V`, and it is named because `sectionChartMap` and `sectionChartMap_comp_chart` must pass
the *same* term. -/
public theorem comp_bundlePresentationIso_inv_comp_toBase
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    (V.ι ≫ σ ≫ (bundlePresentationIso F).inv) ≫ (symGradedBundle F).toBase
      = 𝟙 V.toScheme ≫ V.ι := by
  rw [Category.assoc, Category.assoc, bundlePresentationIso_inv_comp_toBase F, hσ,
    Category.comp_id, Category.id_comp]

/-- **The chart factorisation of an arbitrary section of `π : 𝐏(ℰ) ⟶ X` over an affine open.**

`Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver` says that the morphisms into the
relative `Proj` lying over a morphism to an affine open `V` are exactly the morphisms into the
chart `Proj Γ(V, Sym ℰ)` over `V`; this is the morphism into the chart that the restriction
`V.ι ≫ σ`, read along `bundlePresentationIso.inv`, comes from.

For the glued section of `Stacks.RelativeProj.globalSection` this morphism is
`Stacks.RelativeProj.localChartMap` by construction; for an arbitrary section nothing is known
about it beyond `sectionChartMap_comp_chart` below, which is exactly the chart factorisation
`Stacks.RelativeProj.chartFactorisationTwistIso` and
`…RelativeProj.restrictChartFactorisationPullbackTwistIso` ask for. -/
public def sectionChartMap (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (hV : IsAffineOpen V) :
    V.toScheme ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) :=
  ((Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver
      (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)) hV
      (symGradedBundle F) (𝟙 V.toScheme)).symm
    ⟨V.ι ≫ σ ≫ (bundlePresentationIso F).inv,
      comp_bundlePresentationIso_inv_comp_toBase V σ hσ⟩).1

/-- **The chart factorisation of an arbitrary section of `π`.** The pair
`(V.ι ≫ σ, sectionChartMap V σ hσ hV)` satisfies
`g ≫ bundlePresentationIso.inv = h ≫ chart V hV`, so it is an admissible input of
`Stacks.RelativeProj.chartFactorisationTwistIso` and of
`…RelativeProj.restrictChartFactorisationPullbackTwistIso` — which is item 1 of the route to
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.eq_of_classifies` fed with the `h` the
injectivity clause needs.

This is `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver_symm_apply_comp_chart`, one
reassociation. -/
public theorem sectionChartMap_comp_chart (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (hV : IsAffineOpen V) :
    (V.ι ≫ σ) ≫ (bundlePresentationIso F).inv =
      sectionChartMap V σ hσ hV ≫ (symGradedBundle F).chart V hV :=
  (Category.assoc _ _ _).trans
    (Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver_symm_apply_comp_chart
      (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)) hV
      (symGradedBundle F) (𝟙 V.toScheme)
      ⟨V.ι ≫ σ ≫ (bundlePresentationIso F).inv,
        comp_bundlePresentationIso_inv_comp_toBase V σ hσ⟩).symm

end SectionChart

end Stacks.RelativeProj

end
