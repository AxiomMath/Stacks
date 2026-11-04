module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleQuasicoherentGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.IteratedSliceCohomology
public import StacksFrontier.CategoryTheory.Adjunction.UnitTransportAlongEquivalences
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMateUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafPushforward

/-!
# Goodness of the cohomology sheaves of `Lπ_X^*K` is étale local on `X`

Let `X` be an algebraic space and `K` an object of `D(X_{spaces,étale}, 𝒪_X)` with
quasi-coherent cohomology sheaves. If, for every affine algebraic space `Y` and every object
`K_Y` of `D(Y_{spaces,étale}, 𝒪_Y)` with quasi-coherent cohomology sheaves, the cohomology sheaves
of `Lπ_Y^*K_Y` are good on the affine objects of the big sites of `Y`, then the cohomology sheaves
of `Lπ_X^*K` are good for the family of affine objects of `(Spaces/X)_fppf` lying over an affine
étale chart of `X`. This is the reduction "the question is étale local on `X`" of the proof of
Stacks 0DGR.

The three conditions are each read on the slices of the big sites of `X` at the affine étale charts
of `X`, which the identifications of `AlgebraicGeometry.BigEtaleSpaceSite.sliceRingedSiteHom` and
`AlgebraicGeometry.BigFppfSpaceSite.sliceRingedSiteHom` turn into the big sites of the chart: the
unit by `AlgebraicGeometry.RingedSite.Hom.isIso_unit_app_of_coversTop` and the transport of units
across equivalences, the cohomology by
`Stacks.Cohomology.LocalizedSite.iteratedSliceRightDerivedSectionsIso`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.homologyIn_good_derivedPullback_of_locallyGood`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedCategory.AdjunctionUnitTruncations

universe u

attribute [local instance] HasDerivedCategory.standard


attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- An étale chart of `X` in the big fppf site of algebraic spaces, read as an object of the
spaces-étale site of `X` in the big étale site. -/
abbrev etaleChart {X : T.Spaces} (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X) :
    Space.SpacesEtale E.fppfSite S E.fppf_mem (etaleSpace T E h X) :=
  ⟨Over.mk (etaleMap T E h W₀.obj.hom), by
    obtain ⟨W, hW⟩ := W₀
    cases E with
    | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
      change T.schemeSite = e3 at h
      cases h
      exact hW⟩

variable {T E h}


/-- Restriction of the cohomology sheaves of `Lπ_X^*K` to the slice at an affine étale chart. -/
abbrev sliceHomology {X : T.Spaces}
    (K : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O)))
    (q : ℤ) (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X) :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h W₀.obj.left))).O) :=
  (BigEtaleSpaceSite.sliceRingedSiteHom E
      (etaleChart T E h W₀).obj).toRingedToposSiteHom.pushforwardTopos.obj
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
      (E.bigEtaleRingedSite (etaleSpace T E h X)).O) (etaleChart T E h W₀).obj).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (E.bigEtaleRingedSite (etaleSpace T E h X))).O)) q).obj
        ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom).obj K)))

/-- **At an affine étale chart, the restricted cohomology sheaves of `Lπ_X^*K` are good**, granted
goodness for affine algebraic spaces. -/
theorem locallyGood_sliceHomology {X : T.Spaces}
    (hloc : ∀ Y : T.Spaces, (∃ W : T.Schemes, IsAffine ((BigFppfOver.toScheme T.schemeSite S
        T.scheme_mem).obj W) ∧ Nonempty
          ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ Y)) →
      ∀ KY : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h Y)).O)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj KY).IsQuasicoherentOnSite) →
      ∀ q : ℤ, LocallyGood T E h Y ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (E.bigEtaleRingedSite (etaleSpace T E h Y))).O)) q).obj
        ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h Y)).toRingedToposSiteHom).obj KY)))
    (K : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O)))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherentOnSite) (q : ℤ)
    (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X)
    (hW₀ : Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X W₀) :
    LocallyGood T E h W₀.obj.left (sliceHomology K q W₀) := by
  obtain ⟨KQ, hKQ, hiso⟩ :=
    BigEtaleSpaceSite.exists_slice_homology_derivedPullback_iso E (etaleChart T E h W₀) K
  have hKQqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj KQ).IsQuasicoherentOnSite :=
    fun i ↦ SheafOfModules.IsQuasicoherentOnSite.of_iso (hKQ i).some.symm
      (Space.SpacesEtale.isQuasicoherentOnSite_moduleToSmall _ S _ _ (etaleChart T E h W₀) _ (hK i))
  exact LocallyGood.of_iso T E h (hiso q).some.symm (hloc W₀.obj.left hW₀ KQ hKQqc q)

attribute [local instance] BigEtaleSpaceSite.hasExt_bigEtaleSpaceOver hasExt_bigFppfSpaceOver

attribute [local instance 2000] BigEtaleSpaceSite.enoughInjectives_modules

/-- The underlying abelian sheaf of the restriction of `𝓖` to the slice at `W`, read on the big
étale site of `W.left`, is the restriction of the underlying abelian sheaf of `𝓖` along
`Over.map W.hom`. -/
def _root_.AlgebraicGeometry.BigEtaleSpaceSite.toSheafSlicePushforwardIso {X' : E.Spaces}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O)) (W : Over X') :
    (SheafOfModules.toSheaf _).obj
        ((BigEtaleSpaceSite.sliceRingedSiteHom E W).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (E.bigEtaleRingedSite X').O) W).obj G)) ≅
      (W.iteratedSliceBackward.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (E.topology.over W.left) ((E.topology.over X').over W)).obj
        (((E.topology.over X').overPullback AddCommGrpCat.{u + 1} W).obj
          ((SheafOfModules.toSheaf _).obj G)) :=
  haveI := (BigEtaleSpaceSite.sliceRingedSiteHom E W).toRingedToposSiteHom.isContinuous
  Stacks.SheafOfModules.toSheafPushforwardIso _ _ ≪≫
    (W.iteratedSliceBackward.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (E.topology.over W.left) ((E.topology.over X').over W)).mapIso
      (Stacks.SheafOfModules.toSheafPushforwardIso (F := Over.forget W) (𝟙 _) G)

/-- **Étale cohomology over an affine object lying over a chart.** If the restriction of `𝓖` to
the slice at the chart `W`, read on the big étale site of `W`, has no higher cohomology on affine
objects, then `𝓖` has no higher cohomology on the affine objects `V` of `(Spaces/X)_étale` mapping
to `W`. -/
theorem isZero_moduleCohomology_bigEtale_of_slice {X' : E.Spaces}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O))
    (W : Over X')
    (hG : ∀ U : Over W.left, BigEtaleSpaceSite.IsAffineSchemeOver E W.left U → ∀ p : ℕ, 0 < p →
      IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf _).obj
        ((BigEtaleSpaceSite.sliceRingedSiteHom E W).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (E.bigEtaleRingedSite X').O) W).obj G))) p U))
    {V : Over X'} (g : V ⟶ W) (hV : BigEtaleSpaceSite.IsAffineSchemeOver E X' V)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      (Stacks.Cohomology.moduleCohomology.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O) V p G) := by
  obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hEv : (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O)
        (Opposite.op V)).Additive := by
    dsimp [SheafOfModules.evaluation]; infer_instance
  show IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O)
        (Opposite.op V)).rightDerived (p + 1)).obj G)
  have : HasExt.{u + 1} (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite X')).O)) :=
    Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _
  open Stacks.Cohomology.ModuleDirectImageOnACover in
  refine isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u + 1, u + 1} _ _ _ p G ?_
  refine IsZero.of_iso ?_
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u + 1, u + 1}
      (E.bigEtaleTopology X') ((SheafOfModules.toSheaf _).obj G) (p + 1) V)
  refine Stacks.Cohomology.LocalizedSite.isZero_rightDerivedSections_of_iteratedSlice.{
    u + 1, u + 1, u + 1} E.topology X' W (p + 1) g _ ?_
  exact ((hG (Over.mk g.left) hV (p + 1) (Nat.succ_pos p)).of_iso
    (((Sheaf.cohomologyPresheafFunctor _ (p + 1)).mapIso
      (BigEtaleSpaceSite.toSheafSlicePushforwardIso G W)).app (op (Over.mk g.left))).symm).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u + 1, u + 1}
      (E.bigEtaleTopology W.left) _ (p + 1) (Over.mk g.left)).symm

/-- Pullback of modules along two equal composites of morphisms of ringed sites. -/
private noncomputable def pullbackToposCompEqIso {A B₁ B₂ C : RingedSite.{u + 1, u + 1, u + 1}}
    {f₁ : A.Hom B₁} {g₁ : B₁.Hom C} {f₂ : A.Hom B₂} {g₂ : B₂.Hom C} (h : f₁.comp g₁ = f₂.comp g₂) :
    g₁.toRingedToposSiteHom.pullbackTopos ⋙ f₁.toRingedToposSiteHom.pullbackTopos ≅
      g₂.toRingedToposSiteHom.pullbackTopos ⋙ f₂.toRingedToposSiteHom.pullbackTopos :=
  RingedToposSiteHom.pullbackToposCompIso.{u + 1} _ _ ≪≫
    eqToIso (congrArg (fun φ ↦ φ.toRingedToposSiteHom.pullbackTopos) h) ≪≫
    (RingedToposSiteHom.pullbackToposCompIso.{u + 1} _ _).symm

/-- **The localized unit at an étale chart is the unit of `ε` of the chart**, through the
slice identifications: the unit of the localization of `ε_X` at the chart `W` is invertible at
`e_B^*N` exactly when the unit of `ε_{W.left}` is invertible at `N`. -/
theorem isIso_localized_unit_iff {X : T.Spaces}
  (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X)
    (N : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (E.bigEtaleRingedSite (etaleSpace T E h W₀.obj.left))).O)) :
    IsIso (((fppfToBigEtaleRingedHom T E h X).localized
      (etaleChart T E h W₀).obj).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app
        ((BigEtaleSpaceSite.sliceRingedSiteHom E
            (etaleChart T E h W₀).obj).toRingedToposSiteHom.pullbackTopos.obj
          N)) ↔
      IsIso ((epsilonHom T E h W₀.obj.left).pullbackPushforwardAdjunctionTopos.unit.app N) := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    have hsq : ((fppfToBigEtaleRingedHom T
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X).localized
        (etaleChart T
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl W₀).obj).comp
        (BigEtaleSpaceSite.sliceRingedSiteHom
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          (etaleChart T
            (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
            rfl W₀).obj) =
      (BigFppfSpaceSite.sliceRingedSiteHom T
        ((fppfToBigEtaleRingedHom T
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X).u.obj (etaleChart T
            (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
            rfl W₀).obj)).comp
        (fppfToBigEtaleRingedHom T
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl W₀.obj.left) := by
      refine RingedSite.Hom.ext_of_heq _ _ rfl (heq_of_eq ?_)
      ext V x
      rfl
    have := BigEtaleSpaceSite.isEquivalence_sliceRingedSiteHom_pullbackTopos
      (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (etaleChart T
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
        rfl W₀).obj
    have hQ := BigFppfSpaceSite.isEquivalence_sliceRingedSiteHom_pullbackTopos T
      ((fppfToBigEtaleRingedHom T
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
        rfl X).u.obj
        (etaleChart T
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl W₀).obj)
    have := hQ.full
    have := hQ.faithful
    exact Adjunction.isIso_unit_app_iff_of_isEquivalence _ _ _ _ (pullbackToposCompEqIso hsq) N

/-- **The localized unit at an étale chart is invertible** when the restriction to the chart is
locally good. -/
theorem isIso_localized_unit_of_locallyGood {X : T.Spaces}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite (etaleSpace T E h X))).O))
    (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X)
    (hG : LocallyGood T E h W₀.obj.left
      ((BigEtaleSpaceSite.sliceRingedSiteHom E
          (etaleChart T E h W₀).obj).toRingedToposSiteHom.pushforwardTopos.obj
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (E.bigEtaleRingedSite (etaleSpace T E h X)).O) (etaleChart T E h W₀).obj).obj G))) :
    IsIso (((fppfToBigEtaleRingedHom T E h X).localized
      (etaleChart T E h W₀).obj).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (E.bigEtaleRingedSite (etaleSpace T E h X)).O) (etaleChart T E h W₀).obj).obj G)) := by
  let adjB := (BigEtaleSpaceSite.sliceRingedSiteHom E
    (etaleChart T E h W₀).obj).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  have : IsIso adjB.counit := adjB.counit_isIso_of_R_fully_faithful
  exact (NatTrans.isIso_app_iff_of_iso _ ((asIso adjB.counit).app _)).1
    ((isIso_localized_unit_iff W₀ _).2 hG.1)

/-- **`ε_X^*` restricted to an étale chart is `ε^*` of the chart.** For an étale chart `W₀` of
`X`, the restriction of `ε_X^*𝓖` to the slice of the big fppf site at `W₀`, read on the big fppf
site of the chart, is `ε^*` of the chart applied to the restriction of `𝓖` to the chart. -/
theorem nonempty_fppfSlice_pullback_iso {X : T.Spaces}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (E.bigEtaleRingedSite (etaleSpace T E h X))).O))
    (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X) :
    Nonempty
      ((BigFppfSpaceSite.sliceRingedSiteHom T W₀.obj).toRingedToposSiteHom.pushforwardTopos.obj
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (bigFppfRingedSite T X).O) W₀.obj).obj ((epsilonHom T E h X).pullbackTopos.obj G)) ≅
      (epsilonHom T E h W₀.obj.left).pullbackTopos.obj
        ((BigEtaleSpaceSite.sliceRingedSiteHom E
            (etaleChart T E h W₀).obj).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (E.bigEtaleRingedSite (etaleSpace T E h X)).O) (etaleChart T E h W₀).obj).obj G))) := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    set E := BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    have hsq : ((fppfToBigEtaleRingedHom T E rfl X).localized (etaleChart T E rfl W₀).obj).comp
        (BigEtaleSpaceSite.sliceRingedSiteHom E (etaleChart T E rfl W₀).obj) =
      (BigFppfSpaceSite.sliceRingedSiteHom T
        ((fppfToBigEtaleRingedHom T E rfl X).u.obj (etaleChart T E rfl W₀).obj)).comp
        (fppfToBigEtaleRingedHom T E rfl W₀.obj.left) := by
      refine RingedSite.Hom.ext_of_heq _ _ rfl (heq_of_eq ?_)
      ext V x
      rfl
    let Φ := pullbackToposCompEqIso hsq
    have hQ := BigFppfSpaceSite.isEquivalence_sliceRingedSiteHom_pullbackTopos T
      ((fppfToBigEtaleRingedHom T E rfl X).u.obj (etaleChart T E rfl W₀).obj)
    have := hQ.full
    have := hQ.faithful
    let adjF := (BigFppfSpaceSite.sliceRingedSiteHom T
      ((fppfToBigEtaleRingedHom T E rfl X).u.obj
        (etaleChart T E rfl W₀).obj)).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    have : IsIso adjF.unit := adjF.unit_isIso_of_L_fully_faithful
    let adjB := (BigEtaleSpaceSite.sliceRingedSiteHom E
      (etaleChart T E rfl W₀).obj).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    have hB := BigEtaleSpaceSite.isEquivalence_sliceRingedSiteHom_pushforwardTopos E
      (etaleChart T E rfl W₀).obj
    have := hB.full
    have := hB.faithful
    have : IsIso adjB.counit := adjB.counit_isIso_of_R_fully_faithful
    exact ⟨(BigFppfSpaceSite.sliceRingedSiteHom T
        ((fppfToBigEtaleRingedHom T E rfl X).u.obj
          (etaleChart T E rfl W₀).obj)).toRingedToposSiteHom.pushforwardTopos.mapIso
      (((fppfToBigEtaleRingedHom T E rfl X).localizedPullbackToposSquare
          (etaleChart T E rfl W₀).obj).app G ≪≫
        ((fppfToBigEtaleRingedHom T E rfl X).localized
          (etaleChart T E rfl W₀).obj).toRingedToposSiteHom.pullbackTopos.mapIso
            ((asIso adjB.counit).app _).symm ≪≫ Φ.app _) ≪≫
      (asIso (adjF.unit.app _)).symm⟩

attribute [local instance 2000] enoughInjectives_bigFppfModules

/-- The underlying abelian sheaf of the restriction of `𝓖` to the slice at `W`, read on the big
fppf site of `W.left`, is the restriction of the underlying abelian sheaf of `𝓖` along
`Over.map W.hom`. -/
def toSheafSlicePushforwardIso {X' : T.Spaces}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X')).O)) (W : Over X') :
    (SheafOfModules.toSheaf _).obj
        ((BigFppfSpaceSite.sliceRingedSiteHom T W).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (bigFppfRingedSite T X').O) W).obj G)) ≅
      (W.iteratedSliceBackward.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (T.topology.over W.left) ((T.topology.over X').over W)).obj
        (((T.topology.over X').overPullback AddCommGrpCat.{u + 1} W).obj
          ((SheafOfModules.toSheaf _).obj G)) :=
  haveI := (BigFppfSpaceSite.sliceRingedSiteHom T W).toRingedToposSiteHom.isContinuous
  Stacks.SheafOfModules.toSheafPushforwardIso _ _ ≪≫
    (W.iteratedSliceBackward.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (T.topology.over W.left) ((T.topology.over X').over W)).mapIso
      (Stacks.SheafOfModules.toSheafPushforwardIso (F := Over.forget W) (𝟙 _) G)

/-- **Fppf cohomology over an affine object lying over a chart.** If the restriction of `𝓖` to
the slice at the chart `W`, read on the big fppf site of `W`, has no higher cohomology on affine
objects, then `𝓖` has no higher cohomology on the affine objects `V` of `(Spaces/X)_fppf` mapping
to `W`. -/
theorem isZero_moduleCohomology_bigFppf_of_slice {X' : T.Spaces}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X')).O))
    (W : Over X')
    (hG : ∀ U : Over W.left, BigFppfSpaceOver.IsAffineSchemeOver T W.left U → ∀ p : ℕ, 0 < p →
      IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf _).obj
        ((BigFppfSpaceSite.sliceRingedSiteHom T W).toRingedToposSiteHom.pushforwardTopos.obj
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (bigFppfRingedSite T X').O) W).obj G))) p U))
    {V : Over X'} (g : V ⟶ W) (hV : BigFppfSpaceOver.IsAffineSchemeOver T X' V)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      (Stacks.Cohomology.moduleCohomology.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X')).O) V p G) := by
  obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hEv : (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X')).O)
        (Opposite.op V)).Additive := by
    dsimp [SheafOfModules.evaluation]; infer_instance
  show IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X')).O)
        (Opposite.op V)).rightDerived (p + 1)).obj G)
  have : HasExt.{u + 1} (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X')).O)) :=
    Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _
  open Stacks.Cohomology.ModuleDirectImageOnACover in
  refine isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u + 1, u + 1} _ _ _ p G ?_
  refine IsZero.of_iso ?_
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u + 1, u + 1}
      (BigFppfSpaceOver.topology T X') ((SheafOfModules.toSheaf _).obj G) (p + 1) V)
  refine Stacks.Cohomology.LocalizedSite.isZero_rightDerivedSections_of_iteratedSlice.{
    u + 1, u + 1, u + 1} T.topology X' W (p + 1) g _ ?_
  exact ((hG (Over.mk g.left) hV (p + 1) (Nat.succ_pos p)).of_iso
    (((Sheaf.cohomologyPresheafFunctor _ (p + 1)).mapIso
      (toSheafSlicePushforwardIso G W)).app (op (Over.mk g.left))).symm).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u + 1, u + 1}
      (BigFppfSpaceOver.topology T W.left) _ (p + 1) (Over.mk g.left)).symm

/-! ### Covering families -/

/-- A covering sieve generated by a presieve is the sieve of a family of its arrows. -/
theorem exists_preZeroHypercover_of_generate_mem {C : Type (u + 1)} [Category.{u + 1} C]
    {J : GrothendieckTopology C} {U : C} {R : Presieve U} (hR : Sieve.generate R ∈ J U) :
    ∃ 𝒰 : PreZeroHypercover.{u + 1} U, 𝒰.sieve₀ ∈ J U ∧ ∀ i, ∃ g : 𝒰.X i ⟶ U, R g := by
  refine ⟨⟨Σ V : C, {g : V ⟶ U // R g}, fun i ↦ i.1, fun i ↦ i.2.1⟩, ?_, fun i ↦ ⟨i.2.1, i.2.2⟩⟩
  refine J.superset_covering ?_ hR
  rw [Sieve.generate_le_iff]
  intro V g hg
  exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (⟨V, g, hg⟩ : Σ V : C, {g : V ⟶ U // R g}))

/-- **The affine objects over affine étale charts cover `(Spaces/X)_fppf`**, as families. -/
theorem exists_fppf_cover_isAffineOverAffineEtale {X : T.Spaces} (U : Over X) :
    ∃ 𝒰 : PreZeroHypercover.{u + 1} U, 𝒰.sieve₀ ∈ BigFppfSpaceOver.topology T X U ∧
      ∀ i, IsAffineOverAffineEtale T X (𝒰.X i) := by
  have hc := (isCoverDense_isAffineOverAffineEtale (T := T) (X := X)).is_cover U
  obtain ⟨𝒰, h𝒰, hi⟩ := exists_preZeroHypercover_of_generate_mem (R := fun V _ ↦
    IsAffineOverAffineEtale T X V) (J := BigFppfSpaceOver.topology T X) (by
      refine (BigFppfSpaceOver.topology T X).superset_covering ?_ hc
      rintro Z f ⟨⟨Y, g, k, rfl⟩⟩
      exact ⟨Y.obj, g, k, Y.property, rfl⟩)
  exact ⟨𝒰, h𝒰, fun i ↦ (hi i).elim fun _ h ↦ h⟩

/-- **The objects of `(Spaces/X)_étale` whose image under `ε_X` is affine over an affine étale
chart cover every object for the étale topology.** -/
theorem generate_etale_isAffineOverAffineEtale_mem {X : T.Spaces} (U : Over (etaleSpace T E h X)) :
    Sieve.generate (fun V (_ : V ⟶ U) ↦
      IsAffineOverAffineEtale T X ((fppfToBigEtaleRingedHom T E h X).u.obj V)) ∈
        E.bigEtaleTopology (etaleSpace T E h X) U := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    have :=
      (BigEtaleSpaceSite.inclusion_isMorphismOfSites
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13) rfl
        X)).isContinuous
    have hcp := CoverPreserving.of_isContinuous
      (Space.SpacesEtale.inclusion
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X))
      (Space.SpacesEtale.topology
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X))
        ((BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12
          e13).bigEtaleTopology
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X))
    have h₁ := GrothendieckTopology.pullback_stable _
      ((Over.mkIdTerminal
        (X :=
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
        rfl X))).from U)
      (hcp.cover_preserve
          (Space.SpacesEtale.generate_affineSchemePresieve_mem
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
          (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
            rfl X)
          (Space.SpacesEtale.final
            (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
          (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
            rfl X))))
    refine GrothendieckTopology.superset_covering _ ?_
      (((BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).bigEtaleTopology
          (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X)).bind_covering h₁
        (fun Y _ _ ↦ BigEtaleSpaceSite.generate_affineSchemePresieve_mem
            (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13) Y))
    rintro Z'' _ ⟨Y, k, f, hf, hh, rfl⟩
    obtain ⟨W, a, b, ⟨W₀, a₁, a₂, hW₀, rfl⟩, hb⟩ := hf
    obtain ⟨A, k₁, k₂, hA, rfl⟩ := hh
    exact
      ⟨A, k₁, k₂ ≫ f,
        ⟨hA, W₀, hW₀,
        ⟨(fppfToBigEtaleRingedHom T
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13) rfl X).u.map
      (k₂ ≫ b ≫
          (Space.SpacesEtale.inclusion
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X)).map a₁)⟩⟩,
      (Category.assoc _ _ _).symm⟩

/-- **The affine étale charts of `X` cover the final object of `(Spaces/X)_étale`.** -/
theorem coversTop_etaleChart (X : T.Spaces) :
    (E.bigEtaleTopology (etaleSpace T E h X)).CoversTop
      (fun i : {W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X //
        Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X W₀} ↦
          (etaleChart T E h i.1).obj) := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    intro U
    have :=
      (BigEtaleSpaceSite.inclusion_isMorphismOfSites
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13) rfl
        X)).isContinuous
    have hcp := CoverPreserving.of_isContinuous
      (Space.SpacesEtale.inclusion
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X))
      (Space.SpacesEtale.topology
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X))
        ((BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12
          e13).bigEtaleTopology
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
          rfl X))
    have h₁ := GrothendieckTopology.pullback_stable _
      ((Over.mkIdTerminal
        (X :=
        (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
        rfl X))).from U)
      (hcp.cover_preserve
          (Space.SpacesEtale.generate_affineSchemePresieve_mem
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
          (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
            rfl X)
          (Space.SpacesEtale.final
            (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
          (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
          (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
            rfl X))))
    refine GrothendieckTopology.superset_covering _ ?_ h₁
    rintro Z f ⟨W, a, b, ⟨W₀, a₁, a₂, hW₀, rfl⟩, hb⟩
    exact
      ⟨⟨W₀, hW₀⟩,
        ⟨b ≫
        (Space.SpacesEtale.inclusion
        (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppfSite S
      (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).fppf_mem
      (etaleSpace T (BigEtaleSpaceSite.mk e1 e2 T.schemeSite e4 e5 e6 e7 e8 e9 e10 e11 e12 e13) rfl
        X)).map a₁⟩⟩

/-- `ε_X` carries the étale chart `W₀`, read in the big étale site, back to `W₀`. -/
def etaleChartIso {X : T.Spaces} (W₀ : Space.SpacesEtale T.schemeSite S T.scheme_mem X) :
    (fppfToBigEtaleRingedHom T E h X).u.obj (etaleChart T E h W₀).obj ≅
      (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj W₀ := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    exact Iso.refl _

/-- An object of `(Spaces/X)_étale` whose image under `ε_X` is affine is affine. -/
theorem isAffineSchemeOver_of_fppfToBigEtale_obj {X : T.Spaces} {V : Over (etaleSpace T E h X)}
    (hV : BigFppfSpaceOver.IsAffineSchemeOver T X ((fppfToBigEtaleRingedHom T E h X).u.obj V)) :
    BigEtaleSpaceSite.IsAffineSchemeOver E (etaleSpace T E h X) V := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    exact hV

/-- **Goodness of the cohomology sheaves of `Lπ_X^*K` is étale local on `X`.** If the cohomology
sheaves of `Lπ_Y^*K_Y` are good on the affine objects of the big sites of `Y` for every affine
algebraic space `Y` and every `K_Y` with quasi-coherent cohomology sheaves, then the cohomology
sheaves of `Lπ_X^*K` are good for the family of affine objects over affine étale charts of `X`,
for every `K` with quasi-coherent cohomology sheaves. -/
theorem homologyIn_good_derivedPullback_of_locallyGood {X : T.Spaces}
    (hloc : ∀ Y : T.Spaces, (∃ W : T.Schemes, IsAffine ((BigFppfOver.toScheme T.schemeSite S
        T.scheme_mem).obj W) ∧ Nonempty
          ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ Y)) →
      ∀ KY : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h Y)).O)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj KY).IsQuasicoherentOnSite) →
      ∀ q : ℤ, LocallyGood T E h Y ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (E.bigEtaleRingedSite (etaleSpace T E h Y))).O)) q).obj
        ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h Y)).toRingedToposSiteHom).obj KY)))
    (K : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O)))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherentOnSite) :
    HomologyIn (FppfToBigEtaleGood T E h X {V | IsAffineOverAffineEtale T X V})
      ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom).obj K) := by
  refine fun q ↦ Or.inl ⟨?_, fun V hV p hp ↦ ?_, fun V hV p hp ↦ ?_⟩
  · refine (fppfToBigEtaleRingedHom T E h X).isIso_unit_app_of_coversTop
      (coversTop_etaleChart X) _ (fun i ↦ ?_)
    exact (RingedSite.Hom.isIso_pullbackPushforwardAdjunctionTopos_unit_app_iff _ _).2
      (isIso_localized_unit_of_locallyGood _ i.1 (locallyGood_sliceHomology hloc K hK q i.1 i.2))
  · obtain ⟨hVa, W₀, hW₀, ⟨g⟩⟩ := hV
    have : (fppfToBigEtaleRingedHom T E h X).u.IsEquivalence :=
      fppfToBigEtaleRingedHom_u_isEquivalence (T := T) (X := X) E h
    exact isZero_moduleCohomology_bigEtale_of_slice _ (etaleChart T E h W₀).obj
      (locallyGood_sliceHomology hloc K hK q W₀ hW₀).2.1
      ((fppfToBigEtaleRingedHom T E h X).u.preimage (g ≫ (etaleChartIso W₀).inv))
      (isAffineSchemeOver_of_fppfToBigEtale_obj hVa) p hp
  · obtain ⟨hVa, W₀, hW₀, ⟨g⟩⟩ := hV
    exact isZero_moduleCohomology_bigFppf_of_slice _ W₀.obj
      (fun U hU p hp ↦ ((locallyGood_sliceHomology hloc K hK q W₀ hW₀).2.2 U hU p hp).of_iso
        (((Sheaf.cohomologyPresheafFunctor _ p).mapIso ((SheafOfModules.toSheaf _).mapIso
          (nonempty_fppfSlice_pullback_iso _ W₀).some)).app (op U))) g hVa p hp

end AlgebraicGeometry.BigFppfSpaceSite

end
