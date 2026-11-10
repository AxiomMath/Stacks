module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverPointVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageVanishingOnCoveringChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# Relative dimension at most one over a one-point base: `Rf_*𝒪_X` lies in `D^{≤ 1}`

Let `S` be any base scheme, let `U` be an object of the big fppf site over `S` whose underlying
scheme is affine, locally Noetherian and has at most one point (for instance the spectrum of a
field), and let `f : X ⟶ U` be a proper morphism of finite presentation of algebraic spaces over
`S` with relative dimension at most one (Stacks 06LR). Then:

* `X` has dimension at most one at every point: over a one-point base the relative dimension of
  Stacks 04NM is the dimension of Stacks 04N5;
* `X` is a scheme (Stacks 0ADD at every point and Stacks 03JH), Noetherian of dimension at most
  one, so `H^q(X, 𝓜) = 0` for quasi-coherent `𝓜` and `q ≥ 2` (Stacks 02UZ);
* hence `R^q f_*𝒪_X = 0` for `q ≥ 2`, and `Rf_*𝒪_X ∈ D^{[0, 1]}`.

This is the input "`H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2`" of the proof of the vanishing of the
obstruction groups of the Picard stack in Stacks 0DPJ, over an arbitrary base scheme. The
arguments are those of
`AlgebraicGeometry.CurveFamily.isZero_rightDerived_globalSectionsFunctor_of_subsingleton`,
which is stated for families of curves over the absolute base; nothing there depends on the
base scheme.

## Main results

All results are in the namespace `AlgebraicGeometry.Space`.

* `isRepresentable_of_hasRelativeDimensionLE_one_of_subsingleton`: `X` is a scheme.
* `isZero_rightDerived_modulePushforward_of_hasRelativeDimensionLE_one_of_subsingleton`:
  `R^q f_*𝓜 = 0` for `q ≥ 2` and `𝓜` quasi-coherent.
* `isLE_one_derivedModulePushforward_structureModule_of_subsingleton`: `Rf_*𝒪_X ∈ D^{≤ 1}`.

## Implementation notes

No declaration here carries a `stacks` attribute: these are steps of the proof of Stacks 0DPJ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.SiteModules

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

section Dimension

variable [hU : Subsingleton ((BigFppfOver.toScheme B S hS).obj U)]

include hU in
/-- **An algebraic space of relative dimension at most one over a one-point base has dimension at
most one**: at each point its dimension is the relative dimension there. -/
theorem dimension_le_one_of_hasRelativeDimensionLE_one_of_subsingleton
    (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    dimension B S hS X.obj X.property ≤ 1 := by
  refine iSup_le fun x => ?_
  obtain ⟨e, he, h⟩ := hd x
  rw [(hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton B S hS X.property hU
    f.hom x e).1 h]
  exact_mod_cast he

include hU in
/-- **The local rings of an algebraic space of relative dimension at most one over a one-point
base have dimension at most one** (Stacks 0BAN). -/
theorem localRingDimension_le_one_of_hasRelativeDimensionLE_one_of_subsingleton
    (hd : HasRelativeDimensionLE 1 B S hS f.hom) (x : points B S hS X.obj) :
    localRingDimension B S hS x ≤ 1 := by
  exact_mod_cast (le_iSup (fun y : points B S hS X.obj =>
    (localRingDimension B S hS y : WithBot ℕ∞)) x).trans
    ((dimension_eq_iSup_localRingDimension B S hS X.obj X.property).symm.le.trans
      (dimension_le_one_of_hasRelativeDimensionLE_one_of_subsingleton f hd))

variable [hAff : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [hNoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]

include hU hAff hNoeth in
/-- **A proper algebraic space of relative dimension at most one over an affine locally
Noetherian one-point base is a scheme.** It is separated, being proper over an affine scheme, and
locally Noetherian, being of finite type over a locally Noetherian scheme; its local rings have
dimension at most one, so every point lies in an open subspace which is a scheme (Stacks 0ADD),
and the schematic locus is everything (Stacks 03JH). -/
theorem isRepresentable_of_hasRelativeDimensionLE_one_of_subsingleton
    (hf : IsProper B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    X.obj.IsRepresentable :=
  isRepresentable_of_surjective_pointsMap_schematicLocus B S hS X.property
    fun x => (mem_range_pointsMap_schematicLocus_iff B S hS _ x).2
      (exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one B S hS
        X.property
        (isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal
          U hAff f.hom hf.1)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
          X.property (isAlgebraicSpace_yoneda B S hS U) f.hom hf.2.1.1
          (hasEtaleLocalProperty_of_representable B S hS _ _ U (Iso.refl _) hNoeth))
        x (localRingDimension_le_one_of_hasRelativeDimensionLE_one_of_subsingleton f hd x))

include hU hAff hNoeth in
/-- **The structure morphism is relatively representable**: its source is a scheme. -/
theorem relativelyRepresentable_of_hasRelativeDimensionLE_one_of_subsingleton
    (hf : IsProper B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    yoneda.relativelyRepresentable f.hom := by
  have := isRepresentable_of_hasRelativeDimensionLE_one_of_subsingleton f hf hd
  let e : yoneda.obj X.obj.reprX ≅ X.obj := X.obj.reprW
  let q : X.obj.reprX ⟶ U := yoneda.preimage (e.hom ≫ f.hom)
  have hq : f.hom = e.inv ≫ yoneda.map q := by simp [q]
  rw [hq]
  exact (MorphismProperty.cancel_left_of_respectsIso _ e.inv _).2
    (relativelyRepresentable_yoneda_map B S hS q)

include hU hAff hNoeth in
/-- **The chart of `X` over the identity chart of the base is a Noetherian scheme of dimension at
most one.** Its structure map to `X` is an isomorphism, being a base change of an identity; so
its scheme is proper over the affine Noetherian base, hence Noetherian, and its dimension is that
of `X`, which is at most one. -/
theorem noetherianSpace_and_dim_le_chartScheme_smallBaseChange_idEtaleChart_of_subsingleton
    (hf : IsProper B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom)
    (hp : yoneda.relativelyRepresentable f.hom) :
    NoetherianSpace (chartScheme ((smallBaseChange B S hS f hp).obj (idEtaleChart B S hS U))) ∧
      topologicalKrullDim (chartScheme ((smallBaseChange B S hS f hp).obj
        (idEtaleChart B S hS U))) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  set W := (smallBaseChange B S hS f hp).obj (idEtaleChart B S hS U)
  let Z := (SmallEtale.toOver B S hS X.1).obj W
  -- the structure map of `W` is an isomorphism, being a base change of an identity
  have : IsIso W.obj.hom :=
    (hp.isPullback (𝟙 (yoneda.obj U))).isIso_fst_of_isIso (inst := IsIso.id _)
  let qZ : Z ⟶ U := yoneda.preimage (W.obj.hom ≫ f.hom)
  let p : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk W.obj.hom
  have : IsIso p :=
    ⟨⟨ObjectProperty.homMk (inv W.obj.hom),
      InducedCategory.hom_ext (IsIso.hom_inv_id W.obj.hom),
      InducedCategory.hom_ext (IsIso.inv_hom_id W.obj.hom)⟩⟩
  have sq : IsPullback p (representedSpaceMap B S hS qZ) f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨InducedCategory.hom_ext (by
      change W.obj.hom ≫ f.hom = yoneda.map qZ ≫ 𝟙 _
      rw [Category.comp_id, Functor.map_preimage])⟩
  have hprop : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map qZ) :=
    isProper_toScheme_map_of_isProper_yoneda_map B S hS qZ
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf)
  let T := (BigFppfOver.toScheme B S hS).obj Z
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map qZ)
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map qZ)
  have : _root_.AlgebraicGeometry.IsNoetherian T := ⟨⟩
  refine ⟨inferInstanceAs (NoetherianSpace T), ?_⟩
  change topologicalKrullDim T ≤ _
  rw [← dimension_yoneda_eq_topologicalKrullDim B S hS Z,
    dimension_eq_of_iso B S hS (isAlgebraicSpace_yoneda B S hS Z) X.property (asIso W.obj.hom)]
  exact_mod_cast dimension_le_one_of_hasRelativeDimensionLE_one_of_subsingleton f hd

include hU hAff hNoeth in
/-- **`R^q f_*𝓜 = 0` for `q ≥ 2`** for a proper morphism of relative dimension at most one to an
affine locally Noetherian one-point base and a quasi-coherent `𝓜`: the base is affine and its
identity chart covers its small étale site, so this is the vanishing of `H^q(X, 𝓜)` on the
Noetherian scheme of dimension at most one which `X` is
(`noetherianSpace_and_dim_le_chartScheme_smallBaseChange_idEtaleChart_of_subsingleton`,
Stacks 02UZ). -/
theorem isZero_rightDerived_modulePushforward_of_hasRelativeDimensionLE_one_of_subsingleton
    (hf : IsProper B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) [M.IsQuasicoherentOnSite] {q : ℕ} (hq : 2 ≤ q) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := modulePushforward_additive B S hS f
    IsZero (((modulePushforward B S hS f).rightDerived q).obj M) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS f
  have hp := relativelyRepresentable_of_hasRelativeDimensionLE_one_of_subsingleton f hf hd
  let V := idEtaleChart B S hS U
  have hVaff : IsAffineChart B S hS (yoneda.obj U) V := hAff
  have hV : (SmallEtale.topology B S hS (yoneda.obj U)).CoversTop (fun _ : Unit => V) := fun V' =>
    (SmallEtale.topology B S hS (yoneda.obj U)).superset_covering
      (fun _ _ _ => ⟨(), ⟨(isTerminalIdEtaleChart B S hS U).from _⟩⟩)
      ((SmallEtale.topology B S hS (yoneda.obj U)).top_mem V')
  refine isZero_rightDerived_modulePushforward_of_coveringChart B S hS f hp hf.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hf.1) V hVaff hV M q ?_
  set W := (smallBaseChange B S hS f hp).obj V
  set C := chartSpace B S hS X W
  obtain ⟨hN, hdim⟩ :=
    noetherianSpace_and_dim_le_chartScheme_smallBaseChange_idEtaleChart_of_subsingleton f hf hd hp
  exact @isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_dim_le B S hS C
    _ (isTerminalIdEtaleChart B S hS _) hN _
    (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ _ inferInstance)
    1 q hdim (by omega)

include hU hAff hNoeth in
/-- **`Rf_*𝒪_X ∈ D^{≤ 1}`** for a proper morphism of relative dimension at most one to an affine
locally Noetherian one-point base: `R^q f_*𝒪_X = 0` for `q ≥ 2`. -/
theorem isLE_one_derivedModulePushforward_structureModule_of_subsingleton
    (hf : IsProper B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    ((derivedModulePushforward B S hS f).obj
      ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))).IsLE 1 := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := modulePushforward_additive B S hS f
  rw [DerivedCategory.isLE_iff]
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = n := ⟨n.toNat, by omega⟩
  have : (structureModule X).IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
  refine IsZero.of_iso
    (isZero_rightDerived_modulePushforward_of_hasRelativeDimensionLE_one_of_subsingleton f hf hd
      (structureModule X) (q := q) (by omega))
    ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((derivedModulePushforwardIsoTotalRightDerived B S hS f).app _) ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS f (structureModule X) 0 q q (by simp))

end Dimension

end AlgebraicGeometry.Space

end
