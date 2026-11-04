module

import all StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreOverFieldValuedPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs

/-!
# The `0`-th Betti number of the fibres and the global functions of the fibres

Let `f : X ⟶ U` be a proper, flat morphism of finite presentation from an algebraic space to a
scheme, and `β₀(y) = dim_{κ(y)} H⁰(X_y, 𝒪)` the Betti number of Stacks 0E0R, defined through
`RΓ(Spec κ(y), Rf_{y,*}𝒪)`. This file compares it with `dim_k H⁰(X_k, 𝒪) = dim_k Γ(X_k, 𝒪)`
for the fibres over field-valued points:

* `β₀(y) ≤ 1` gives `dim_k Γ(X_k, 𝒪) ≤ 1` at every field-valued point over `y`;
* conversely, `dim_k Γ(X_k, 𝒪) ≤ 1` at every field-valued point over `y` gives `β₀(y) ≤ 1`.

This is used to deduce, from the upper semicontinuity of `β₀` (Stacks 0E0R) and Stacks 0E6B (a),
condition (o) of Stacks 0E0E for `dim H⁰ ≤ 1` on the fibres of a family of curves, and so for
`Curves^{h0,1}` (Stacks 0E6I).

## Main results

* `AlgebraicGeometry.Space.h0FibreRank_le_one_of_fibreBetti_le_one`
* `AlgebraicGeometry.Space.fibreBetti_le_one_of_forall_h0FibreRank_le_one`
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres_of_fibreBetti`
* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily`: condition (o) of Stacks
  0E0E for `Curves^{h0,1}`, unconditionally.

## Implementation notes

Nothing here is registered: the results are the inputs of Stacks 0E6I and 0E6K.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space.ProperFlatStein

universe u

-- `StacksDraft.PseudoCoherence.IsPseudoCoherent` and `fibreBetti` are stated in this model.
attribute [local instance 10000] HasDerivedCategory.standard

/-- Over a Noetherian ring, the cohomology modules of a pseudo-coherent complex are finite. -/
theorem StacksDraft.PseudoCoherence.moduleFinite_homology_of_isPseudoCoherent {R : Type u}
    [CommRing R] [IsNoetherianRing R] {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (m : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) m).obj K) := by
  obtain ⟨P, -, hP, ⟨e⟩⟩ :=
      StacksDraft.PseudoCoherence.finiteProjectiveRepresentative_of_pseudoCoherent hK
  have : Module.Finite R (P.X m) := (hP m).1
  have := CochainComplex.finite_homology_of_finite_cycles P m (Module.IsNoetherian.finite R _)
  let e1 := ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) m).mapIso e).toLinearEquiv
  let e2 := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) m).app P).toLinearEquiv
  exact Module.Finite.equiv (e2.symm.trans e1)

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ U)

/-- **`H⁰` of the cohomology of the base change of `𝒪_X` is `Γ(T, f'_*𝒪_{X_T})`**, for
`f' : X_T = X ×_U T ⟶ T` quasi-compact and quasi-separated over an affine `T`. -/
def homologyZeroBaseChangeDerivedSectionsIso
    (hqc : IsQuasiCompact B S hS (pullback.snd f (representedSpaceMap B S hS t)).hom)
    (hqs : IsQuasiSeparated B S hS (pullback.snd f (representedSpaceMap B S hS t)).hom) :
    (DerivedCategory.homologyFunctor _ 0).obj
        (baseChangeDerivedSections f t (structureModule X)) ≅
      (representedAffineSections B S hS T).obj
        ((modulePushforward B S hS (pullback.snd f (representedSpaceMap B S hS t))).obj
          (structureModule (pullback f (representedSpaceMap B S hS t)))) :=
  (DerivedCategory.homologyFunctor _ 0).mapIso ((representedAffineDerivedSections B S hS T).mapIso
      ((derivedModulePushforward B S hS (pullback.snd f (representedSpaceMap B S hS t))).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
            (smallEtaleRingedToposModulesHom B S hS
              (pullback.fst f (representedSpaceMap B S hS t)))).symm))) ≪≫
    representedAffineDerivedSectionsHomologyIso B S hS T _
      (qcohDerived_derivedModulePushforward_structureModule B S hS T
        (pullback.snd f (representedSpaceMap B S hS t)) hqc hqs) 0 ≪≫
    (representedAffineSections B S hS T).mapIso
      ((derivedModulePushforwardSingleHomologyZeroIso B S hS
        (pullback.snd f (representedSpaceMap B S hS t))).app _)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- `Γ(Spec k, 𝒪) = k` is a field, for the object of the site of a field-valued point. -/
theorem isField_siteObject (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsField Γ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _), ⊤) :=
  (Scheme.ΓSpecIso (.of p.carrier)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField _)

/-- The object of the site of a field-valued point is affine. -/
instance isAffine_siteObject (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The object of the site of a field-valued point is affine, in the unfolded spelling
of the source of its section. -/
instance isAffine_siteObject' (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Opposite.unop (Opposite.op
      (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS))))) :=
  inferInstanceAs (IsAffine (Spec _))

/-- **The `0`-th Betti number at the image of a field-valued point is the dimension of `H⁰` of the
fibre formed over that point.** -/
theorem fibreBetti_zero_schemePoint (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    fibreBetti f (structureModule X) 0 (schemePoint B S hS U p) =
      Module.finrank Γ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _), ⊤)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u}
          Γ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _), ⊤)) 0).obj
          (baseChangeDerivedSections f p.value (structureModule X))) := by
  let T₀ := p.siteObject B S hS (yoneda.obj U)
  let y₀ : (BigFppfOver.toScheme B S hS).obj T₀ := IsLocalRing.closedPoint p.carrier
  have hFfp : (structureSheafModule B S hS X).IsFinitePresentation := inferInstance
  have hF := isFlatOver_structureSheafModule B S hS f hfl
  have hA := finrank_homology_baseChangeDerivedSections_eq f hf hfp _ hFfp hF
    (residueFieldSiteHom B S hS T₀ y₀ ≫ p.value) p.value (residueFieldSiteHom B S hS T₀ y₀) rfl
    (isField_residueFieldSiteObj T₀ y₀) (isField_siteObject p) 0
  have hB := finrank_homology_baseChangeDerivedSections_eq f hf hfp _ hFfp hF
    (residueFieldSiteHom B S hS T₀ y₀ ≫ p.value)
    (residueFieldSiteHom B S hS U (((BigFppfOver.toScheme B S hS).map p.value).base y₀))
    (residueFieldSiteMap p.value y₀) (residueFieldSiteHom_comp p.value y₀).symm
    (isField_residueFieldSiteObj T₀ y₀) (isField_residueFieldSiteObj U _) 0
  exact hB.symm.trans hA

/-- Properness, flatness and finite presentation are inherited by the base change of `f`. -/
private theorem isProper_isFlat_isFinitePresentation_pullback_snd {T' : BigFppfOver B S hS}
    (t' : T' ⟶ U) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) :
    IsProper B S hS (pullback.snd f (representedSpaceMap B S hS t')).hom ∧
      IsFlat B S hS (pullback.snd f (representedSpaceMap B S hS t')).hom ∧
      IsFinitePresentation B S hS (pullback.snd f (representedSpaceMap B S hS t')).hom := by
  have hpb := IsPullback.of_hasPullback f (representedSpaceMap B S hS t')
  exact ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback hpb hf,
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb hfl,
    (isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
      hpb hfp⟩

/-- Over an affine `T` whose ring of functions is a field, `H⁰(X_T, 𝒪)` is finite-dimensional. -/
theorem moduleFinite_homology_baseChangeDerivedSections (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hK : IsField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (i : ℤ) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
        i).obj (baseChangeDerivedSections f t (structureModule X))) := by
  let gS := representedSpaceMap B S hS t
  have hpb := IsPullback.of_hasPullback f gS
  obtain ⟨hf', -, hfp'⟩ := isProper_isFlat_isFinitePresentation_pullback_snd f t hf hfl hfp
  have hFfp : (structureSheafModule B S hS X).IsFinitePresentation := inferInstance
  have hF := isFlatOver_structureSheafModule B S hS f hfl
  have hF'fp := isFinitePresentation_modulePullback (pullback.fst f gS) _ hFfp
  have : (structureSheafModule B S hS X).IsQuasicoherentOnSite :=
    @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _
      (isFinitePresentationOnSite_of_isFinitePresentation' _ hFfp)
  have : ((modulePullback B S hS (pullback.fst f gS)).obj
      (structureSheafModule B S hS X)).IsQuasicoherentOnSite :=
    @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _
      (isFinitePresentationOnSite_of_isFinitePresentation' _ hF'fp)
  have hF' := isFlatOver_modulePullback B S hS hpb _ hF
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent
      (baseChangeDerivedSections f t (structureModule X)) :=
    StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
      (isPerfect_representedAffineDerivedSections_obj B S hS T _
        (isPerfect_derivedModulePushforward_single_and_isIso_baseChange (pullback.snd f gS) hf'
          hfp' _ hF'fp hF').1)
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := by
    let := hK.toField
    infer_instance
  exact StacksDraft.PseudoCoherence.moduleFinite_homology_of_isPseudoCoherent hM i

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The global functions of an algebraic space without points form the zero ring. -/
theorem subsingleton_globalFunctions'_of_isEmpty {Z : AlgebraicSpaces B S hS}
    (hZ : IsEmpty (points B S hS Z.obj)) : Subsingleton (globalFunctions' B S hS Z.obj) := by
  refine ⟨fun a b => Subtype.ext (funext fun W => ?_)⟩
  have : IsEmpty ((BigFppfOver.toScheme B S hS).obj W.unop.obj.left) :=
    ⟨fun y => hZ.false (pointsMap B S hS _ W.unop.obj.hom
      (surjective_pointsToScheme B S hS W.unop.obj.left y).choose)⟩
  exact Subsingleton.elim (α := Γ((BigFppfOver.toScheme B S hS).obj W.unop.obj.left, ⊤)) _ _

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The fibre `X ×_U Spec k` of `h0Fibre` is the pullback of `f` along `Spec k ⟶ U`. -/
noncomputable def h0FibreIsoPullback (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    h0Fibre B S hS f p ≅ pullback f (representedSpaceMap B S hS p.value) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap p.value)).isoPullback

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The comparison `h0FibreIsoPullback` lies over `Spec k`. -/
theorem h0FibreIsoPullback_hom_snd (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    (h0FibreIsoPullback f p).hom ≫ pullback.snd f (representedSpaceMap B S hS p.value) =
      h0FibreProj B S hS f p :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap p.value)).isoPullback_hom_snd

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- **`β₀ ≤ 1` at the image of a field-valued point gives `dim_k H⁰(X_k, 𝒪) ≤ 1`.** -/
theorem h0FibreRank_le_one_of_fibreBetti_le_one (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (h : fibreBetti f (structureModule X) 0 (schemePoint B S hS U p) ≤ 1) :
    h0FibreRank B S hS f p ≤ 1 := by
  let gS := representedSpaceMap B S hS p.value
  let f' := pullback.snd f gS
  obtain ⟨-, -, hfp'⟩ := isProper_isFlat_isFinitePresentation_pullback_snd f p.value hf hfl hfp
  let e := h0FibreIsoPullback f p
  by_cases hx : Nonempty (points B S hS (pullback f gS).obj)
  · obtain ⟨x⟩ := hx
    let E := homologyZeroBaseChangeDerivedSectionsIso f p.value hfp'.2.1 hfp'.2.2
    have hfin := moduleFinite_homology_baseChangeDerivedSections f p.value hf hfl hfp
      (isField_siteObject p) 0
    have hfin' := Module.Finite.equiv E.toLinearEquiv
    have hN := E.toLinearEquiv.finrank_eq.symm.trans_le
      ((fibreBetti_zero_schemePoint f hf hfl hfp p).symm.trans_le h)
    have hq := SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((derivedModulePushforwardSingleHomologyZeroIso B S hS
        (pullback.snd f (representedSpaceMap B S hS p.value))).app _)
      (qcohDerived_derivedModulePushforward_structureModule B S hS _
        (pullback.snd f (representedSpaceMap B S hS p.value)) hfp'.2.1 hfp'.2.2 0)
    have hiso := isIso_structureSharp_of_finrank_le_one _
      (pullback.snd f (representedSpaceMap B S hS p.value)) (isField_siteObject p) x hq hfin' hN
    have hb := bijective_globalFunctionsMap_of_isIso_structureSharp B S hS _ f' hiso
    have hb' : Function.Bijective (globalFunctionsMap B S hS (h0FibreProj B S hS f p)) := by
      rw [← h0FibreIsoPullback_hom_snd f p]
      have hc := globalFunctionsMap_comp B S hS (h0FibreIsoPullback f p).hom
        (pullback.snd f (representedSpaceMap B S hS p.value))
      exact (congrArg (fun φ : globalFunctions' B S hS (yoneda.obj (p.siteObject B S hS _)) →+*
          globalFunctions' B S hS (h0Fibre B S hS f p).obj => Function.Bijective φ) hc).mpr
        ((globalFunctionsMapEquiv B S hS e).bijective.comp hb)
    exact (toENat_rank_eq_one_of_bijective _
      ((bijective_h0FibreAlgebraMap_iff B S hS f p).2 hb')).le
  · have := subsingleton_globalFunctions'_of_isEmpty (Z := h0Fibre B S hS f p)
      ⟨fun x => hx ⟨pointsMap B S hS _ e.hom.hom x⟩⟩
    unfold h0FibreRank
    let := (h0FibreAlgebraMap B S hS f p).toAlgebra
    rw [rank_subsingleton']
    simp

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- **`dim_k H⁰(X_k, 𝒪) ≤ 1` at all field-valued points over `y` gives `β₀(y) ≤ 1`.** -/
theorem fibreBetti_le_one_of_forall_h0FibreRank_le_one (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (y : (BigFppfOver.toScheme B S hS).obj U)
    (h : ∀ p : FieldValuedPoint B S hS (yoneda.obj U), schemePoint B S hS U p = y →
      h0FibreRank B S hS f p ≤ 1) :
    fibreBetti f (structureModule X) 0 y ≤ 1 := by
  obtain ⟨hf', hfl', hfp'⟩ :=
    isProper_isFlat_isFinitePresentation_pullback_snd f (residueFieldSiteHom B S hS U y) hf hfl hfp
  let E := homologyZeroBaseChangeDerivedSectionsIso f (residueFieldSiteHom B S hS U y)
    hfp'.2.1 hfp'.2.2
  show Module.finrank _ ((DerivedCategory.homologyFunctor (ModuleCat.{u}
    Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y), ⊤)) 0).obj
    (baseChangeDerivedSections f (residueFieldSiteHom B S hS U y) (structureModule X))) ≤ 1
  rw [E.toLinearEquiv.finrank_eq]
  -- all points of `Spec κ(y)` agree
  have hT : ∀ a b : points B S hS (yoneda.obj (residueFieldSiteObj B S hS U y)), a = b := fun a b =>
    injective_pointsToScheme B S hS (residueFieldSiteObj B S hS U y)
      (Subsingleton.elim
        (α := Spec (.of (((BigFppfOver.toScheme B S hS).obj U).residueField y))) _ _)
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y), ⊤) :=
    ⟨(isField_residueFieldSiteObj U y).exists_pair_ne⟩
  by_cases hx : Nonempty (points B S hS (pullback f (representedSpaceMap B S hS
      (residueFieldSiteHom B S hS U y))).obj)
  · obtain ⟨x⟩ := hx
    have hfib : ∀ q : FieldValuedPoint B S hS (yoneda.obj (residueFieldSiteObj B S hS U y)),
        Function.Bijective
        (algebraMap q.carrier (globalFunctions B (Spec (.of q.carrier)) q.contained
          (fibreOverFieldValuedPoint B S hS (pullback.snd f (representedSpaceMap B S hS
              (residueFieldSiteHom B S hS U y))).hom q))) := by
      intro q
      let q' := q.map B S hS _ (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y)).hom
      have hq' : schemePoint B S hS U q' = y := by
        refine (schemePoint_map_yoneda B S hS (residueFieldSiteHom B S hS U y) q).trans ?_
        exact Scheme.fromSpecResidueField_apply (X := (BigFppfOver.toScheme B S hS).obj U) y _
      have hne : ∃ x' : points B S hS X.obj,
          pointsMap B S hS X.obj f.hom x' = q'.class B S hS (yoneda.obj U) := by
        refine ⟨pointsMap B S hS _ (pullback.fst f (representedSpaceMap B S hS
            (residueFieldSiteHom B S hS U y))).hom x, ?_⟩
        rw [← pointsMap_comp_apply,
          show (pullback.fst f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))).hom ≫
              f.hom =
            (pullback.snd f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))).hom ≫
              (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y)).hom from
            congrArg
              (fun k : pullback f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y)) ⟶
                ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ => k.hom)
              (pullback.condition (f := f)
                (g := representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))),
          pointsMap_comp_apply,
          hT (pointsMap B S hS _
              (pullback.snd f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))).hom x)
            (q.class B S hS _)]
        rfl
      have := nontrivial_globalFunctions_h0Fibre B S hS f q' hne
      have hb := (bijective_h0FibreAlgebraMap_iff B S hS f q').1
        (bijective_of_toENat_rank_le_one _ (h q' hq'))
      have hb2 := bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective B S hS f.hom q'
        X.2 (isAlgebraicSpace_yoneda B S hS U) hb
      exact (bijective_algebraMap_globalFunctions_congr B
        (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS
          (pullback.snd f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))).hom
          (pullback f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))).2
          (isAlgebraicSpace_yoneda B S hS (residueFieldSiteObj B S hS U y)) q)
        (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f.hom X.2
          (isAlgebraicSpace_yoneda B S hS U) q')
        (fibreOverFieldValuedPointPullbackSndIso B S hS f (representedSpaceMap B S hS
            (residueFieldSiteHom B S hS U y)) q)).2 hb2
    have hI := (isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B S hS
      (pullback.snd f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))) hf' hfl' hfp'
          hfib).1
    obtain ⟨e⟩ := @representedAffineSections_modulePushforward_iso_of_isIso B S hS
        (residueFieldSiteObj B S hS U y) _ _
      (pullback.snd f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y))) hI
    exact (e.toLinearEquiv.finrank_eq.trans (Module.finrank_self _)).le
  · have hs := subsingleton_representedAffineSections_modulePushforward_of_isEmpty
      (residueFieldSiteObj B S hS U y)
      (pullback.snd f (representedSpaceMap B S hS (residueFieldSiteHom B S hS U y)))
      ⟨fun x => hx ⟨x⟩⟩
    exact (@Module.finrank_zero_of_subsingleton _ _ _ _ _ _ hs).trans_le zero_le_one

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The open locus of `dim H⁰ ≤ 1` on the fibres of a family of curves -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Betti numbers of a family depend on the module only up to isomorphism. -/
theorem fibreBetti_congr {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace U)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (e : F ≅ F') (i : ℤ) :
    fibreBetti f F i = fibreBetti f F' i :=
  funext fun _ => ((DerivedCategory.homologyFunctor _ i).mapIso
    ((representedAffineDerivedSections B S hS _).mapIso ((derivedModulePushforward B S hS _).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        ((modulePullback B S hS _).mapIso e))))).toLinearEquiv.finrank_eq

/-- **`dim H⁰` of the fibres along a cartesian square.** If `f₁ : X₁ ⟶ U₁` is the base change of
`f₂ : X₂ ⟶ U₂` along `g : U₁ ⟶ U₂`, the fibre of `f₁` over a field-valued point has the `dim H⁰`
of the fibre of `f₂` over its image. -/
theorem h0FibreRank_of_isPullback {U₁ U₂ : BigFppfOver B S hS} {X₁ X₂ : AlgebraicSpaces B S hS}
    {f₁ : X₁ ⟶ schemeSpace U₁} {f₂ : X₂ ⟶ schemeSpace U₂} {i : X₁ ⟶ X₂} (g : U₁ ⟶ U₂)
    (sqX : IsPullback i f₁ f₂ (schemeSpaceMap g))
    (p : FieldValuedPoint B S hS (yoneda.obj U₁)) :
    h0FibreRank B S hS f₁ p = h0FibreRank B S hS f₂ (p.map B S hS _ (yoneda.map g)) := by
  let p' := p.map B S hS _ (yoneda.map g)
  have sqG := AlgebraicSpaces.isPullback_fiberProduct B S hS f₂ (schemeSpaceMap p'.value)
  rw [show schemeSpaceMap p'.value = schemeSpaceMap p.value ≫ schemeSpaceMap g from
    schemeSpaceMap_comp p.value g] at sqG
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B S hS f₁
    (schemeSpaceMap p.value)).paste_horiz sqX
  let e := sq.isoIsPullback _ _ sqG
  have he : e.hom ≫ h0FibreProj B S hS f₂ p' = h0FibreProj B S hS f₁ p :=
    IsPullback.isoIsPullback_hom_snd _ _ sq sqG
  have hmap : h0FibreAlgebraMap B S hS f₁ p =
      (globalFunctionsMapEquiv B S hS e).toRingHom.comp (h0FibreAlgebraMap B S hS f₂ p') := by
    refine RingHom.ext fun c => ?_
    show globalFunctionsMap B S hS (h0FibreProj B S hS f₁ p) _ =
      globalFunctionsMap B S hS e.hom (globalFunctionsMap B S hS (h0FibreProj B S hS f₂ p') _)
    rw [← he]
    exact RingHom.congr_fun (globalFunctionsMap_comp B S hS e.hom _) _
  unfold h0FibreRank
  rw [hmap]
  exact toENat_rank_comp_ringEquiv _ _

end Space

namespace CurveFamily

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) of Stacks 0E0E for `dim H⁰ ≤ 1` on the fibres over fields**: the locus is
the set of points of the base where the `0`-th Betti number of the fibre is at most one, which is
open by the upper semicontinuity of Stacks 0E0R. -/
theorem isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres_of_fibreBetti :
    IsOpenCurvesLocus B hZ (HasH0RankLeOneOnFieldFibres (B := B) (hZ := hZ)) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  let β := Space.fibreBetti G.toBase (Space.structureModule G.total) 0
  have hFfp : (Space.structureSheafModule B integerBase hZ G.total).IsFinitePresentation :=
    inferInstance
  have hF := Space.isFlatOver_structureSheafModule B integerBase hZ G.toBase G.flat
  have hβ : UpperSemicontinuous β :=
    Space.upperSemicontinuous_fibreBetti G.toBase G.proper G.finitePresentation _ hFfp hF 0
  have hIic : β ⁻¹' Set.Iic 1 = β ⁻¹' Set.Iio 2 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Iio]
    omega
  refine ⟨Space.pointsToScheme B integerBase hZ G.base ⁻¹' (β ⁻¹' Set.Iic 1), ?_,
    fun F a => ?_⟩
  · rw [hIic]
    exact (hβ.isOpen_preimage 2).preimage
      (Space.schemePointsHomeomorph B integerBase hZ G.base).continuous
  · rw [Set.range_subset_iff]
    refine ⟨fun hR s => ?_, fun hΩ q => ?_⟩
    · obtain ⟨q, rfl⟩ := Quot.exists_rep s
      show β (Space.schemePoint B integerBase hZ G.base
        (q.map B integerBase hZ _ (yoneda.map a.baseMap))) ≤ 1
      rw [show β (Space.schemePoint B integerBase hZ G.base
          (q.map B integerBase hZ _ (yoneda.map a.baseMap))) =
          β (((BigFppfOver.toScheme B integerBase hZ).map a.baseMap)
            (Space.schemePoint B integerBase hZ F.base q)) from
        congrArg β (Space.schemePoint_map_yoneda B integerBase hZ a.baseMap q)]
      have hbc := Space.fibreBetti_baseChange G.toBase G.proper G.finitePresentation _ hFfp hF
        a.baseMap 0
      have hpb := IsPullback.of_hasPullback G.toBase (Space.representedSpaceMap B integerBase hZ
          a.baseMap)
      obtain ⟨hf', hfl', hfp'⟩ := Space.isProper_isFlat_isFinitePresentation_pullback_snd
        G.toBase a.baseMap G.proper G.flat G.finitePresentation
      rw [show β (((BigFppfOver.toScheme B integerBase hZ).map a.baseMap)
          (Space.schemePoint B integerBase hZ F.base q)) = _ from
        (congrFun hbc (Space.schemePoint B integerBase hZ F.base q)).symm]
      let e : (Space.modulePullback B integerBase hZ (pullback.fst G.toBase
          (Space.representedSpaceMap B integerBase hZ a.baseMap))).obj
          (Space.structureSheafModule B integerBase hZ G.total) ≅
          Space.structureModule (pullback G.toBase (Space.representedSpaceMap B integerBase hZ
              a.baseMap)) :=
        (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (Space.smallEtaleRingedToposModulesHom B integerBase hZ (pullback.fst G.toBase
              (Space.representedSpaceMap B integerBase hZ a.baseMap)))).symm
      refine (congrFun (Space.fibreBetti_congr _ e 0) _).trans_le ?_
      refine Space.fibreBetti_le_one_of_forall_h0FibreRank_le_one (pullback.snd G.toBase
          (Space.representedSpaceMap B integerBase hZ a.baseMap))
        hf' hfl' hfp' _ fun p _ => ?_
      rw [Space.h0FibreRank_of_isPullback a.baseMap hpb p, ← h0FibreRank_toBase_of_hom a p]
      exact hR p
    · rw [h0FibreRank_toBase_of_hom a q]
      exact Space.h0FibreRank_le_one_of_fibreBetti_le_one G.toBase G.proper G.flat
        G.finitePresentation _ (hΩ (q.class B integerBase hZ _))

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}`**, unconditionally: Stacks 0E0R at `i = 0`
through the Betti numbers of the fibres, and Stacks 0E6B (a). -/
theorem isOpenCurvesLocus_isH01CurveFamily :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := (isOpenCurvesLocus_hasH0RankLeOneOnFieldFibres_of_fibreBetti.and
    isOpenCurvesLocus_hasFibresOfDimensionOne) G
  exact ⟨W, hW, fun F a => (isH01CurveFamily_iff_of
    (fun f hf hfl hfp h => Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre
      B integerBase hZ f hf hfl hfp h) F).trans (hchar F a)⟩

end CurveFamily

end AlgebraicGeometry
