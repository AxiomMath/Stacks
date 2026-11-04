module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportAction

/-!
# `H⁰_c(X_K, ℱ_ρ)` in the sense of Remark 03UI (2) for a curve which is not projective

The Trace Formula chapter defines `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_!K)|_{X̄_k̄})` for a
compactification `j : X ⟶ X̄` over `k` (Remark 03UI (2)); this is
`Stacks.EtaleCohomology.galoisCompactSupportCohomology`. This file proves the last assertion of
Tag 03VL in that model: for a geometrically connected smooth curve `X` over `k` which is not
projective, `H⁰_c(X_K, ℱ_ρ) = 0`, for every algebraic extension `K` of `k`.

## Main results

* `AlgebraicGeometry.isZero_galoisCompactSupportCohomologyGroup_zero_of_not_isProjective`.

## Implementation notes

Degree zero of `RΓ(X̄_K, (j_!ℱ)|_{X̄_K})` is `Γ(X̄_K, (j_!ℱ)|_{X̄_K})`, and restriction to `X̄_K`
commutes with extension by zero around the cartesian square
`Y = X ×_{X̄} X̄_K ⟶ X̄_K` over `j`, so this is `Γ(X̄_K, j'_!(ℱ|_Y))` for the open immersion
`j' : Y ⟶ X̄_K`. The scheme `Y` is `X_K` (pasting of pullbacks), integral and not proper over `K`,
and `ℱ|_Y` is finite type locally constant, so
`Stacks.EtaleCohomology.subsingleton_globalSections_extensionByZero_uliftFunctor` applies.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Stacks.GroupCohomology Stacks.Frobenius
open Stacks.EtaleCohomology

universe u r

namespace AlgebraicGeometry

section Contains

variable (B : BigEtaleSite.{u})

/-- A scheme of finite type over a scheme of a big étale site lies in the site
(Stacks 000R (5)). -/
theorem contains_of_locallyOfFiniteType_of_quasiCompact {T S : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFiniteType g] [QuasiCompact g] (hS : B.Contains S) : B.Contains T :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g hS

/-- The base field of a nonempty scheme of a big étale site lies in the site. -/
theorem contains_spec_of_nonempty {k : Type u} [Field k] {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Spec (.of k)) (hX : B.Contains X) : B.Contains (Spec (.of k)) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of k) hX
    ((mk_le_size_of_nonempty f).trans (self_le_power _ one_le_aleph0))

end Contains

section Square

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (K : Type u) [Field K] [Algebra k K]

/-- The restriction of `j : X ⟶ X̄` to `X̄_K`: the fibre product `X ×_{X̄} X̄_K`. -/
abbrev compactificationRestrictionSource : Scheme.{u} :=
  pullback j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K)

/-- **`X ×_{X̄} X̄_K` is `X_K`**, by pasting the two cartesian squares. -/
def compactificationRestrictionSourceIso :
    compactificationRestrictionSource f j K ≅ fieldBaseChange (Over.mk f) K :=
  pullbackRightPullbackFstIso j.toBase (specAlgebraMap k K) j.immersion ≪≫
    pullback.congrHom (Over.w j.obj.hom) rfl

/-- The isomorphism `X ×_{X̄} X̄_K ≅ X_K` composed with the projection `X_K ⟶ X` is the first
projection of the fibre product. -/
theorem compactificationRestrictionSourceIso_hom_fst :
    (compactificationRestrictionSourceIso f j K).hom ≫ fieldBaseChangeProj (Over.mk f) K =
      pullback.fst j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K) := by
  simp [compactificationRestrictionSourceIso, fieldBaseChangeProj]

/-- The isomorphism `X ×_{X̄} X̄_K ≅ X_K` composed with the structure morphism `X_K ⟶ Spec K` is
the second projection `X ×_{X̄} X̄_K ⟶ X̄_K` followed by `X̄_K ⟶ Spec K`. -/
theorem compactificationRestrictionSourceIso_hom_snd :
    (compactificationRestrictionSourceIso f j K).hom ≫
        pullback.snd (Over.mk f).hom (specAlgebraMap k K) =
      pullback.snd j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K) ≫
        pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k K) := by
  simp [compactificationRestrictionSourceIso]
  rfl

end Square

section DegreeZero

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (K : Type u) [Field K] [Algebra k K]

/-- **Degree zero of `RΓ_c(X_K, ℱ)` in the sense of Remark 03UI (2)** is the module of global
sections `Γ(X̄_K, (j_!ℱ)|_{X̄_K})`, for a sheaf `ℱ` placed in degree zero. -/
def galoisCompactSupportCohomologyGroupZeroIso (F : EtaleModules.{u, r} Λ X) :
    galoisCompactSupportCohomologyGroup.{u, r} Λ f j K
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) 0 ≅
      (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk j.toBase) K)).obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj (Over.mk j.toBase) K)).obj
          ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F)) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) 0).mapIso
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk j.toBase) K)).mapIso
        (DerivedCategory.Plus.Q.mapIso
          ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) K)).mapCochainComplexPlus.mapIso
            (mapCochainComplexPlusSinglePlusIso
              (etaleModuleExtensionByZero.{u, r} Λ j.immersion) F) ≪≫
          mapCochainComplexPlusSinglePlusIso _ _))) ≪≫
    Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso _ _

end DegreeZero

section Vanishing

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f]
  (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] (Λ : Type r) [Ring Λ] [Finite Λ]

omit [Finite Λ] in
/-- Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site of an
arbitrary scheme, at the module universe `u + 1`. -/
local instance hasWeakSheafify_etaleOver_moduleCatU (S : Scheme.{u}) (W : S.Etale) :
    HasWeakSheafify (S.smallEtaleTopology.over W) (ModuleCat.{u + 1} Λ) :=
  letI := Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, r, u + 1}
    S.smallEtaleTopology Λ W
  inferInstance

omit [Finite Λ] in
/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site of an arbitrary
scheme, at the module universe `u + 1`. -/
local instance hasSheafify_etale_moduleCatU (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} Λ _

/-- **Stacks Project, Tag 03VL, last assertion, in the model of Remark 03UI (2):
`H⁰_c(X_K, ℱ_ρ) = 0` if `X` is not projective.** For a geometrically connected smooth curve `X`
over `k` which is not projective, any compactification `j : X ⟶ X̄` over `k`, an algebraic
extension `K` of `k`, a finite ring `Λ` and a finite `Λ`-module `M` with a continuous action `ρ`
of `π₁(X, η̄)`, the zeroth cohomology of `RΓ_c(X_K, ℱ_ρ) = RΓ(X̄_K, (j_!ℱ_ρ)|_{X̄_K})` vanishes. -/
theorem isZero_galoisCompactSupportCohomologyGroup_zero_of_not_isProjective
    (hnp : ¬ IsProjective f) (j : CompactificationOf (Over.mk f))
    (y : GeometricPoint (fieldBaseChange (Over.mk f) K))
    (M : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    IsZero (galoisCompactSupportCohomologyGroup.{u, r} Λ f j K
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj M)) 0) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f K
  have := nonempty_of_isCurve B X f
  have := isIntegral_fieldBaseChange f K
  have hXbar : B.Contains j.space := contains_of_locallyOfFiniteType_of_quasiCompact B j.toBase
    (contains_spec_of_nonempty B f X.2)
  have : Nonempty j.space := ⟨j.immersion (Classical.arbitrary X.1)⟩
  have hXbarK : B.Contains (fieldBaseChange (Over.mk j.toBase) K) :=
    contains_fieldBaseChange j.toBase K B hXbar
  have hY : B.Contains (compactificationRestrictionSource f j K) :=
    Scheme.size_pullback_lt _ _ X.2 hXbarK
  let hK := contains_fieldBaseChange_of_isCurve B X f K
  let e := compactificationRestrictionSourceIso f j K
  have : IsIntegral (compactificationRestrictionSource f j K) := IsIntegral.of_isIso e.inv
  have : ConnectedSpace (compactificationRestrictionSource f j K) :=
    e.inv.homeomorph.surjective.connectedSpace e.inv.homeomorph.continuous
  have hf : ¬ IsProper (pullback.snd j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K) ≫
      pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k K)) := by
    rw [← compactificationRestrictionSourceIso_hom_snd]
    intro h
    refine not_isProper_fieldBaseChange_of_not_isProjective B X f K hnp ?_
    have : e.inv ≫ e.hom ≫ pullback.snd (Over.mk f).hom (specAlgebraMap k K) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K) := by simp
    rw [← this]
    infer_instance
  let XKB := fieldBaseChangeObj B X f K hK
  let : ConnectedSpace XKB.1 := connectedSpace_fieldBaseChange f K
  let YB : B.Scheme := ⟨compactificationRestrictionSource f j K, hY⟩
  let eB : YB ⟶ XKB := ObjectProperty.homMk e.hom
  let N := (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
    (fieldBaseChangeObjProj B X f K hK).hom y)).obj M
  let HK := ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B XKB y Λ).inverse.obj N)
  have hH' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (compactificationRestrictionSource f j K).smallEtaleTopology
      (((Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).sheafPullback (ModuleCat.{u + 1} Λ)
        XKB.1.smallEtaleTopology (compactificationRestrictionSource f j K).smallEtaleTopology).obj
          HK.obj) :=
    have :=
      Stacks.ConstantSheaf.isClosedUnderIsomorphisms_isFiniteTypeLocallyConstantModuleSheaf.{u,
        u + 1, u + 1, r} (compactificationRestrictionSource f j K).smallEtaleTopology Λ
    ObjectProperty.prop_of_iso _ ((etaleSiteSheafPullbackModuleIsoSheafPullback B eB Λ).app HK.obj)
      (isFiniteTypeLocallyConstant_etaleSiteSheafPullbackModule B eB Λ HK.obj HK.property)
  have : IsProper (Over.mk j.toBase).hom := inferInstanceAs (IsProper j.toBase)
  have h := subsingleton_globalSections_extensionByZero_uliftFunctor Λ
    (pullback.snd j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K)) K
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k K)) hf _ hH'
  have e3 : (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj (Over.mk f) K)).obj
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).obj M) ≅
      (sheafCompose XKB.1.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj HK.obj :=
    (representationSheafPullbackIso B (fieldBaseChangeObjProj B X f K hK) Λ y).app M ≪≫
      (representationSheafIsoEtaleSite B XKB y Λ).app N
  have e2 : (etaleModuleInverseImage.{u, r} Λ
      (pullback.fst j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K))).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).obj M) ≅
      (sheafCompose (compactificationRestrictionSource f j K).smallEtaleTopology
        (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).sheafPullback (ModuleCat.{u + 1} Λ)
          XKB.1.smallEtaleTopology
            (compactificationRestrictionSource f j K).smallEtaleTopology).obj HK.obj) :=
    (eqToIso (congrArg (fun g ↦ etaleModuleInverseImage.{u, r} Λ g)
        (compactificationRestrictionSourceIso_hom_fst f j K).symm)).app _ ≪≫
      (etaleModuleInverseImageCompIso Λ e.hom (fieldBaseChangeProj (Over.mk f) K)).app _ ≪≫
      (etaleModuleInverseImage.{u, r} Λ e.hom).mapIso e3 ≪≫
      smallEtaleSheafPullbackModuleUliftIso e.hom Λ HK.obj
  have e1 := ((etaleModuleInverseImageExtensionByZeroIso Λ
    (IsPullback.of_hasPullback j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K))).app
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).obj M)).symm ≪≫
    (etaleModuleExtensionByZero.{u, r} Λ
      (pullback.snd j.immersion (fieldBaseChangeProj (Over.mk j.toBase) K))).mapIso e2
  have e0 := galoisCompactSupportCohomologyGroupZeroIso Λ f j K
    ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f K hK).hom) Λ).obj M) ≪≫
    (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk j.toBase) K)).mapIso e1
  exact @ModuleCat.isZero_of_subsingleton _ _ _ (subsingleton_of_moduleIso Λ e0.symm h)

end Vanishing

end AlgebraicGeometry
