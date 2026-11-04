module

public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedPointGeneratingSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusClosedPoints

/-!
# The cohomological criterion for ampleness on a Noetherian algebraic space

Let `S` be a scheme, `X` a Noetherian algebraic space over `S` and `𝓛` an invertible
`𝒪_X`-module.  Stacks 0D2W asserts: if every coherent `𝒪_X`-module `𝓕` has some `n ≥ 1` with
`H¹(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0`, then `X` is a scheme and `𝓛` is ample on it.

For a global section `s` of `𝓛^{⊗ d}` the open subspace `U_s` over which `s` generates is affine
(`AlgebraicGeometry.Space.isAffineSpace_generatingSubspace`), and every closed point lies in some
`U_s` (`AlgebraicGeometry.Space.exists_mem_sectionGeneratingLocus_of_isClosed`).  Since `|X|` is a
Noetherian topological space, an open subspace containing every closed point is everything, so `X`
is a scheme (`AlgebraicGeometry.Space.isRepresentable_of_isNoetherian_of_isClosed_mem_range`). On
the scheme the generating locus of `s` is the nonvanishing locus of the restricted section
(`AlgebraicGeometry.Space.mem_sectionGeneratingLocus_iff_mem_nonvanishingLocus`), an affine open,
and every point of a quasi-compact scheme specializes to a closed point, so `𝓛` is ample
(`Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points`).

## Main results

* `AlgebraicGeometry.Space.baseChangeModuleTensorPowerIso`: the restriction of `𝓛^{⊗ n}` is the
  `n`-th tensor power of the restriction of `𝓛`.
* `AlgebraicGeometry.Space.exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep`:
  **Stacks 0D2W.**

## Implementation notes

"`X` is a scheme and `𝓛` is ample" is stated as: there are an object `U` of the site and an
isomorphism `yoneda.obj U ≅ X` such that the restriction `𝓛_U` of `𝓛` to the scheme underlying
`U` (`AlgebraicGeometry.Space.baseChangeModule`) is invertible and ample, in the shape of
`AlgebraicGeometry.Space.isRelativelyAmple_iff_exists_scheme`.  Cohomology is that of
`𝒪_X`-modules on the small étale site, as in Stacks 0D2V.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 0D2V](https://stacks.math.columbia.edu/tag/0D2V)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory

/-- **The restriction to a scheme over the space of a tensor product of quasi-coherent modules
is the tensor product of the restrictions**: the inverse image is monoidal (Stacks 03EL,
`AlgebraicGeometry.Space.modulePullbackTensorIso`) and so is the identity-chart restriction on
quasi-coherent modules (`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`). -/
noncomputable def baseChangeModuleTensorObjIso {X : AlgebraicSpaces B S hS}
    (A L : Modules.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherentOnSite)
    (hL : L.IsQuasicoherentOnSite) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) :
    baseChangeModule B S hS (A ⊗ L) U p ≅
      Stacks.RelativeVeryAmple.tensorModules ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS A U p) (baseChangeModule B S hS L U p) :=
  let g : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk p
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso (modulePullbackTensorIso B S hS g A L) ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS U _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g A hA)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g L hL) ≪≫
    eqToIso (_root_.AlgebraicGeometry.SmallEtale.tensorSheafBifunctorZariski_obj
      ((BigFppfOver.toScheme B S hS).obj U) _ _)

/-- The isomorphism `L^{⊗ (n + 2)} ≅ L^{⊗ (n + 1)} ⊗ L` of `𝒪_X`-modules, with the monoidal
product on the right. -/
noncomputable def invertibleTensorPowerSuccIsoTensorObj {X : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (n : ℕ) :
    invertibleTensorPower B S hS X.1 X.2 L ((n + 1 + 1 : ℕ) : ℤ) ≅
      invertibleTensorPower B S hS X.1 X.2 L ((n + 1 : ℕ) : ℤ) ⊗ L :=
  eqToIso (congrArg (fun m : ℤ => invertibleTensorPower B S hS X.1 X.2 L m)
      (by omega : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1)) ≪≫
    (@Stacks.SheafOfModules.Invertible.tensorPowerSuccIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) _).symm ≪≫
    (modulesTensorObjIso B S hS X.1 X.2 _ L).symm

/-- **The restriction of `𝓛^{⊗ (n + 1)}` to a scheme over the space is the `(n + 1)`-st tensor
power of the restriction of `𝓛`**: the inverse image and the restriction to the Zariski site are
both compatible with tensor products of quasi-coherent modules. -/
noncomputable def baseChangeModuleTensorPowerIso {X : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p)] :
    ∀ n : ℕ, baseChangeModule B S hS (invertibleTensorPower B S hS X.1 X.2 L ((n + 1 : ℕ) : ℤ))
        U p ≅ Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U p) ((n + 1 : ℕ) : ℤ)
  | 0 =>
    baseChangeModuleMapIso B S hS
      (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
        (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
        (structurePresheaf B S hS X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        _ _ L (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL)) U p ≪≫
      (Stacks.Ample.tensorPowModuleOneIso _ _).symm
  | n + 1 =>
    baseChangeModuleMapIso B S hS (invertibleTensorPowerSuccIsoTensorObj L n) U p ≪≫
      baseChangeModuleTensorObjIso _ L
        (isQuasicoherentOnSite_of_isInvertibleModule X _
          (@Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
            (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
            (structurePresheaf B S hS X.1)
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ L hL _))
        (isQuasicoherentOnSite_of_isInvertibleModule X L hL) U p ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModuleTensorPowerIso L U p n)
        (Stacks.Ample.tensorPowModuleOneIso ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U p)).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p) _ _ ≪≫
      eqToIso (congrArg (fun m : ℤ => Stacks.Ample.tensorPowModule
          ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p) m)
        (by omega))

attribute [local instance] pointTopology in
/-- **An affine open subspace of a scheme is an affine open of the scheme.**  If the open subspace
of `X ≅ yoneda.obj U` cut out by an open set `W` of points is an affine scheme, then the points of
the scheme underlying `U` mapping into `W` form an affine open. -/
theorem exists_isAffineOpen_of_isAffineSpace_openSubspaceOfPoints (U : BigFppfOver B S hS)
    {X : AlgebraicSpaces B S hS} (e : yoneda.obj U ≅ X.1) (W : Set (points B S hS X.1))
    (hW : IsOpen W) (haff : IsAffineSpace B S hS (openSubspaceOfPoints B S hS X.1 W).toFunctor) :
    ∃ O : ((BigFppfOver.toScheme B S hS).obj U).Opens, IsAffineOpen O ∧
      ∀ t, t ∈ O ↔
        pointsMap B S hS (yoneda.obj U) e.hom ((pointsEquivScheme B S hS U).symm t) ∈ W := by
  obtain ⟨A, hA, ⟨e₁⟩⟩ := haff
  let m : yoneda.obj A ⟶ yoneda.obj U := e₁.inv ≫ (openSubspaceOfPoints B S hS X.1 W).ι ≫ e.inv
  let φ : A ⟶ U := yoneda.preimage m
  have hm : yoneda.map φ = m := yoneda.map_preimage m
  have hopen : IsOpenImmersion B S hS (yoneda.map φ) := by
    rw [hm]
    exact MorphismProperty.comp_mem _ _ _ (isOpenImmersion_of_isIso B S hS _)
      (MorphismProperty.comp_mem _ _ _ (isOpenSubspace_openSubspaceOfPoints B S hS X.2 W hW).2
        (isOpenImmersion_of_isIso B S hS _))
  have hφ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map φ) :=
    (presheaf_yoneda_map_iff B S hS inferInstance φ).1 hopen
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hA
  refine ⟨((BigFppfOver.toScheme B S hS).map φ).opensRange, isAffineOpen_opensRange _,
    fun t => ?_⟩
  let πU := pointsEquivScheme B S hS U
  let πA := pointsEquivScheme B S hS A
  have hnat : ∀ w, (BigFppfOver.toScheme B S hS).map φ (πA w) =
      πU (pointsMap B S hS (yoneda.obj A) m w) := fun w => by
    rw [← hm]
    exact (pointsToScheme_pointsMap_yoneda B S hS φ w).symm
  have hcomp : ∀ w, pointsMap B S hS _ m w = pointsMap B S hS _ e.inv
      (pointsMap B S hS _ (openSubspaceOfPoints B S hS X.1 W).ι
        (pointsMap B S hS _ e₁.inv w)) := fun w => by
    simp only [m, pointsMap_comp_apply]
  have hinv : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ≅ G) y,
      pointsMap B S hS G f.inv (pointsMap B S hS F f.hom y) = y := fun f =>
    (pointsHomeomorphOfIso B S hS f).left_inv
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X.1) W
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨w, rfl⟩ := πA.surjective a
    rw [hnat, Equiv.symm_apply_apply, hcomp]
    erw [hinv e.symm]
    exact (Set.ext_iff.1 hrange _).1 (Set.mem_range_self _)
  · intro ht
    obtain ⟨v, hv⟩ := (Set.ext_iff.1 hrange _).2 ht
    refine ⟨πA (pointsMap B S hS _ e₁.hom v), ?_⟩
    rw [hnat, hcomp, hinv e₁, hv, hinv e, Equiv.apply_symm_apply]

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] pointTopology HasDerivedCategory.standard

/-- **Stacks 0D2W.**  Let `S` be a scheme, `X` a Noetherian algebraic space over `S` and `𝓛` an
invertible `𝒪_X`-module.  If every coherent `𝒪_X`-module `𝓕` has some `n ≥ 1` with
`H¹(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0`, then `X` is a scheme and `𝓛` is ample on it: there are an object `U`
of the site and an isomorphism `yoneda.obj U ≅ X` for which the restriction of `𝓛` to the scheme
underlying `U` is an invertible and ample module.  See the module docstring. -/
@[stacks 0D2W]
theorem exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hN : IsNoetherian B S hS hZ X.1) (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∃ n : ℕ, 1 ≤ n ∧ IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
            (twistStep B S hS X.1 X.2 L n F))) :
    ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
      (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom)),
      Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom) := by
  have hXN : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  have hcl := exists_mem_sectionGeneratingLocus_of_isClosed hZ X hN L h
  have hpow : ∀ d : ℕ, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      (invertibleTensorPower B S hS X.1 X.2 L d) := fun d =>
    @Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L hL d
  have hft : ∀ d : ℕ,
      SheafOfModules.IsFiniteTypeOnSite (invertibleTensorPower B S hS X.1 X.2 L d) := fun d =>
    have := isCoherentOnSite_of_isInvertible _ (hpow d)
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X _
  have hrep : X.1.IsRepresentable := by
    refine isRepresentable_of_isNoetherian_of_isClosed_mem_range B S hS hZ X.2 hN fun x hx => ?_
    obtain ⟨d, hd, s, hxs⟩ := hcl x hx
    obtain ⟨A, -, ⟨e⟩⟩ := isAffineSpace_generatingSubspace hZ X hN L h d hd s
    refine ⟨_, isOpenSubspace_generatingSubspace B S hS _ s (hft d),
      ⟨A, ⟨Functor.representableByEquiv.symm e.symm⟩⟩, ?_⟩
    rwa [range_pointsMap_ι_generatingSubspace]
  let U := X.1.reprX
  let eX : yoneda.obj U ≅ X.1 := X.1.reprW
  have hL' := isInvertibleModule_baseChangeModule L hL U eX.hom
  refine ⟨U, eX, hL', ?_⟩
  let T := (BigFppfOver.toScheme B S hS).obj U
  let πX := pointsHomeomorphOfIso B S hS eX
  have : CompactSpace (points B S hS X.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS X.2 hN.1
  have : CompactSpace T := (πX.symm.trans (schemePointsHomeomorph B S hS U)).compactSpace
  refine Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points T _ fun t ht => ?_
  set x := pointsMap B S hS (yoneda.obj U) eX.hom ((pointsEquivScheme B S hS U).symm t)
  obtain ⟨d, hd, s, hxs⟩ := hcl x <| by
    have hc := ((schemePointsHomeomorph B S hS U).symm.trans πX).isClosedMap _ ht
    rwa [Set.image_singleton] at hc
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  let M := invertibleTensorPower B S hS X.1 X.2 L ((k + 1 : ℕ) : ℤ)
  obtain ⟨O, hOaff, hO⟩ := exists_isAffineOpen_of_isAffineSpace_openSubspaceOfPoints U eX
    (sectionGeneratingLocus B S hS M s)
    (isOpen_sectionGeneratingLocus B S hS M s (hft (k + 1)))
    (isAffineSpace_generatingSubspace hZ X hN L h (k + 1) hd s)
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let g : Y ⟶ X := ObjectProperty.homMk eX.hom
  let M' := (modulePullback B S hS g).obj M
  have hM' : IsInvertibleModule Y M' :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertible_modulePullback_obj B S hS g M
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M (hpow _)))
  let s' := modulePullbackSections B S hS g M s
  let Mi := idChartRestriction B S hS U M'
  have : Stacks.Ample.IsInvertibleModule T Mi := isInvertible_idChartRestriction B S hS U M' hM'
  let σ₀ := idChartSection B S hS U M' s'
  let E : Mi ≅ Stacks.Ample.tensorPowModule T (baseChangeModule B S hS L U eX.hom)
      ((k + 1 : ℕ) : ℤ) :=
    (restrictToChartSchemeIdEtaleChartIso B S hS U M').symm ≪≫
      baseChangeModuleTensorPowerIso L U eX.hom k
  refine ⟨k + 1, by omega, E.hom.app ⊤ (Stacks.NonvanishingSpelling.sectionsEquiv T Mi σ₀), O,
    ?_, ?_, hOaff⟩
  · ext t'
    rw [SetLike.mem_coe, hO, Stacks.Ample.nonvanishingLocus_congr E,
      ← Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq T Mi σ₀,
      ← mem_sectionGeneratingLocus_iff_mem_nonvanishingLocus B S hS U M' hM' s' t',
      sectionGeneratingLocus_modulePullback_of_isFiniteTypeOnSite g M
        (isQuasicoherentOnSite_of_isInvertibleModule X M (hpow _)) (hft _) s, Set.mem_preimage]
    rfl
  · rwa [hO]

end AlgebraicGeometry.Space

end
