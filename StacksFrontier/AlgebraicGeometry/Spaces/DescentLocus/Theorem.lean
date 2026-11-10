module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.DescentSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.ImmersedOpenIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.StratumBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# The locus where a vector bundle descends along a proper flat morphism

Let `f : X ⟶ Y` be a flat, proper morphism of finite presentation of algebraic spaces over `S`,
let `E` be a finite locally free `𝒪_X`-module, and assume that `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` is an
isomorphism for every base change `f' : X' = X ×_Y Y' ⟶ Y'`. Then there is an immersion
`j : Z ⟶ Y` of finite presentation such that `g : Y' ⟶ Y` factors through `j` exactly when
`(g')^*E ≅ (f')^*N` for a finite locally free `𝒪_{Y'}`-module `N`
(`AlgebraicGeometry.Space.HasDescentAt`).

## Main results

* `exists_isImmersion_isFinitePresentation_factorsThrough_iff_hasDescentAt`: there is an
  immersion `j : Z ⟶ Y` of finite presentation through which `g : Y' ⟶ Y` factors exactly when
  `E` descends at `g`.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Space

namespace DescentStratum

open BottomRankLocus

attribute [local instance] pointTopology
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### A closed étale-locally constructible locus on an immersed subscheme -/

/-- **A closed, étale locally constructible set of points of an object `Q` of the site immersed
in an affine object `W` is cut out by a finitely generated ideal of `Γ(W)`**: there is `J` such
that a morphism `h : T ⟶ Q` from an affine object misses the set exactly when `J` generates the
unit ideal of `Γ(T)` along `h ≫ q`. -/
theorem exists_fg_ideal_of_isEtaleLocallyConstructible {Q W : BigFppfOver B S hS} (q : Q ⟶ W)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map q)]
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj Q)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Q)]
    {C : Set (points B S hS (yoneda.obj Q))} (hC : IsClosed C)
    (hCc : IsEtaleLocallyConstructible B S hS (yoneda.obj Q) C) :
    ∃ J : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤), J.FG ∧
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ h : T ⟶ Q, (Set.range (pointsMap B S hS (yoneda.obj T) (yoneda.map h)) ⊆ Cᶜ ↔
          J.map ((BigFppfOver.toScheme B S hS).map (h ≫ q)).appTop.hom = ⊤) := by
  let φ := schemePointsHomeomorph B S hS Q
  let Cs : Set ((BigFppfOver.toScheme B S hS).obj Q) := φ.symm ⁻¹' C
  have hCs : IsClosed Cs := hC.preimage φ.symm.continuous
  have hloc : IsLocallyConstructible C := by
    have h := hCc Q (𝟙 _) (isEtale_id B S hS _)
    rwa [pointsMap_id, Set.preimage_id] at h
  have hCsc : IsConstructible Cs :=
    ((φ.symm.isLocallyConstructible_preimage_iff C).mpr hloc).isConstructible
  have hcomp : IsCompact Csᶜ :=
    AlgebraicGeometry.ConnectedComponentSection.isCompact_of_isConstructible
      (isConstructible_compl.2 hCsc)
  obtain ⟨J, hJ, hJiff⟩ := exists_fg_ideal_range_subset_compl_iff_of_isImmersion
    ((BigFppfOver.toScheme B S hS).map q) hCs hcomp
  refine ⟨J, hJ, fun T hT h => ?_⟩
  have := hT
  rw [Functor.map_comp, ← hJiff ((BigFppfOver.toScheme B S hS).obj T)]
  constructor
  · rintro hh _ ⟨x, rfl⟩ hx
    apply hh (Set.mem_range_self ((schemePointsHomeomorph B S hS T).symm x))
    rwa [schemePointsHomeomorph_symm_naturality]
  · rintro hh _ ⟨p, rfl⟩ hp
    refine hh ⟨schemePointsHomeomorph B S hS T p, rfl⟩ ?_
    change φ.symm _ ∈ C
    rwa [← schemePointsHomeomorph_symm_naturality, Homeomorph.symm_apply_apply]

/-! ### Descent forces the bottom rank stratum -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hP : IsProper B S hS f.hom)
  (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
  (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
  (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
    IsIso (structureSharp B S hS (pullback.snd f g)))

include hP hfp hfl hE hiso in
/-- **Where `E` has rank `r` and descends at `g`, the morphism `g` is universally of bottom rank
`r` for `Rf_*E` in degree `0`**: for every `g' : Y'' ⟶ Y'`,
`H^0(L(g' ≫ g)^*Rf_*E) = f''_*E''` is finite locally free of rank `r`. -/
theorem isUniversallyFreeBottom_of_hasDescentAt {r : ℕ} {Y' : AlgebraicSpaces B S hS}
    (g : Y' ⟶ Y) (hg : Set.range (pointsMap B S hS Y'.1 g.hom) ⊆ rankFibreLocus f E r)
    (hd : HasDescentAt f E g) :
    IsUniversallyFreeBottom (pushforwardComplex f E) 0 r g := by
  intro Y'' g'
  obtain ⟨e⟩ := nonempty_pullbackHomology_pushforwardComplex_zero_iso f hP hfp hfl E hE (g' ≫ g)
  refine isFiniteLocallyFreeOfIntRank_of_iso B S hS e.symm
    (isFiniteLocallyFreeOfIntRank_pushforward_of_hasDescentAt f hiso hE (g' ≫ g) ?_
      (HasDescentAt.comp f E hd g'))
  rintro _ ⟨w, rfl⟩
  exact hg ⟨pointsMap B S hS _ g'.hom w, (pointsMap_comp_apply B S hS g'.hom g.hom w).symm⟩

/-! ### The descent locus on an affine chart -/

include hP hfp hfl hE hiso in
/-- **On an affine chart over the rank `r` locus on which the bottom rank stratum is cut out by
`I, J`, the descent locus is cut out by `I` and `J J₂` for a finitely generated `J₂`.** -/
theorem exists_isCutOutBy_descentSubfunctor_of_isCutOutBy (W : SmallEtale B S hS Y.1)
    (haff : IsAffine (chartScheme W)) {r : ℕ}
    (hrange : Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ⊆ rankFibreLocus f E r)
    {I J : Ideal Γ(chartScheme W, ⊤)} (hJ : J.FG)
    (hcut : IsCutOutBy (bottomRankSubfunctor (pushforwardComplex f E) 0 r) W.1.hom I J) :
    ∃ J₂ : Ideal Γ(chartScheme W, ⊤), J₂.FG ∧
      IsCutOutBy (descentSubfunctor f E) W.1.hom I (J * J₂) := by
  have := haff
  let c := chartToSpace B S hS Y W
  let L := Scheme.cutOutι I J
  have hLimm : AlgebraicGeometry.IsImmersion (Subobject.mk L).arrow := isImmersion_arrow_mk L
  let Q := subschemeObject B S hS (Subobject.mk L) hLimm
  let qs : Q ⟶ W.1.left := subschemeι B S hS (Subobject.mk L) hLimm
  have hqs : (BigFppfOver.toScheme B S hS).map qs = (Subobject.mk L).arrow :=
    toScheme_map_subschemeι B S hS _ _
  have harrow : (Subobject.underlyingIso L).hom ≫ L = (Subobject.mk L).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk L
  have hfac : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ t : T ⟶ W.1.left,
        (I.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom = ⊥ ∧
          J.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom = ⊤) ↔ ∃ h, h ≫ qs = t := by
    intro T hT t
    have := hT
    rw [← Scheme.exists_comp_cutOutι_iff_of_isAffine I J]
    constructor
    · intro ht
      have hmem : t ∈ (subschemePoints B S hS (Subobject.mk L)).obj (op T) :=
        (mem_subschemePoints_mk_iff L t).2 ht
      rwa [subschemePoints_eq_range B S hS qs (Iso.refl _) (Category.id_comp _)] at hmem
    · rintro ⟨h, rfl⟩
      refine (mem_subschemePoints_mk_iff L (h ≫ qs)).1 ?_
      rw [subschemePoints_eq_range B S hS qs (Iso.refl _) (Category.id_comp _)]
      exact ⟨h, rfl⟩
  have hrep : ∀ {T : BigFppfOver B S hS} (h : T ⟶ Q),
      representedSpaceMap B S hS (h ≫ qs) =
        representedSpaceMap B S hS h ≫ representedSpaceMap B S hS qs :=
    fun h => InducedCategory.hom_ext (Functor.map_comp yoneda h qs)
  have hsec : ∀ {T : BigFppfOver B S hS} (t : T ⟶ W.1.left),
      sectionMap T (Y.1.map t.op (yonedaEquiv W.1.hom)) = representedSpaceMap B S hS t ≫ c := by
    intro T t
    rw [sectionMap_map, sectionMap_yonedaEquiv]
  let qY := representedSpaceMap B S hS qs ≫ c
  have hq : IsUniversallyFreeBottom (pushforwardComplex f E) 0 r qY := by
    obtain ⟨ι, V, π, hVaff, hπ, hcov⟩ := exists_affine_open_family Q
    have hmem : Y.1.map qs.op (yonedaEquiv W.1.hom) ∈
        (bottomRankSubfunctor (pushforwardComplex f E) 0 r).obj (op Q) := by
      refine isEtaleLocalOnSource_bottomRankSubfunctor.mem_of_family _ π
        (fun i => by have := hπ i; infer_instance) hcov fun i => ?_
      have e : Y.1.map (π i).op (Y.1.map qs.op (yonedaEquiv W.1.hom)) =
          Y.1.map (π i ≫ qs).op (yonedaEquiv W.1.hom) := by
        rw [op_comp, Functor.map_comp_apply]
      rw [e]
      exact (hcut (V i) (hVaff i) (π i ≫ qs)).2 ((hfac (V i) (hVaff i) _).2 ⟨π i, rfl⟩)
    have h' : IsUniversallyFreeBottom (pushforwardComplex f E) 0 r
        (sectionMap Q (Y.1.map qs.op (yonedaEquiv W.1.hom))) := hmem
    rwa [hsec] at h'
  have hqr : Set.range (pointsMap B S hS (yoneda.obj Q) qY.hom) ⊆ rankFibreLocus f E r := by
    rintro _ ⟨p, rfl⟩
    exact hrange ⟨pointsMap B S hS _ (yoneda.map qs) p,
      (pointsMap_comp_apply B S hS (yoneda.map qs) W.1.hom p).symm⟩
  have hH := isFiniteLocallyFreeOfIntRank_stratumPushforward f E qY hP hfp hfl hE hq
  have hmain := fun {T' : AlgebraicSpaces B S hS} (h : T' ⟶ _) =>
    hasDescentAt_comp_iff_range_subset f E qY hE hiso hqr hH
      (fun h => isFiniteLocallyFreeOfIntRank_stratumPushforward_comp f E qY hP hfp hfl hE hq h)
      (fun h => isIso_moduleBaseChangeMap_of_isUniversallyFreeBottom f hP hfp hfl E hE qY hq h) h
  have hC := isClosed_stratumLocus f E qY hP hE hqr
  have hCc := isEtaleLocallyConstructible_stratumLocus f E qY hfp hE hqr hH
  have hqcL : QuasiCompact (Subobject.mk L).arrow := by
    rw [← harrow]
    exact @quasiCompact_comp _ _ _ _ _ (quasiCompact_of_isIso _)
      (Scheme.quasiCompact_cutOutι I J hJ)
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map qs) := hqcL
  have : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map qs) := by
    rwa [hqs]
  have : QuasiSeparated ((BigFppfOver.toScheme B S hS).map qs) :=
    (inferInstance : QuasiSeparated (Subobject.mk L).arrow)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) := haff
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj Q) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map qs)
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Q) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map qs)
  obtain ⟨J₂, hJ₂, hJ₂iff⟩ := exists_fg_ideal_of_isEtaleLocallyConstructible qs hC hCc
  refine ⟨J₂, hJ₂, fun T hT t => ?_⟩
  change HasDescentAt f E (sectionMap T (Y.1.map t.op (yonedaEquiv W.1.hom))) ↔ _
  rw [hsec, Ideal.map_mul]
  constructor
  · intro hd
    have hb : IsUniversallyFreeBottom (pushforwardComplex f E) 0 r
        (sectionMap T (Y.1.map t.op (yonedaEquiv W.1.hom))) := by
      rw [hsec]
      refine isUniversallyFreeBottom_of_hasDescentAt f hP hfp hfl E hE hiso _ ?_ hd
      rintro _ ⟨p, rfl⟩
      exact hrange ⟨pointsMap B S hS _ (yoneda.map t) p,
        (pointsMap_comp_apply B S hS (yoneda.map t) W.1.hom p).symm⟩
    obtain ⟨hI, hJt⟩ := (hcut T hT t).1 hb
    obtain ⟨h, rfl⟩ := (hfac T hT t).1 ⟨hI, hJt⟩
    rw [hrep] at hd
    have h2 := (hJ₂iff T hT h).1 ((hmain _).1 hd)
    exact ⟨hI, by rw [hJt, h2, Ideal.top_mul]⟩
  · rintro ⟨hI, hJJ⟩
    have hJt : J.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom = ⊤ :=
      eq_top_iff.2 (hJJ ▸ Ideal.mul_le_left)
    have h2 : J₂.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom = ⊤ :=
      eq_top_iff.2 (hJJ ▸ Ideal.mul_le_right)
    obtain ⟨h, rfl⟩ := (hfac T hT t).1 ⟨hI, hJt⟩
    rw [hrep]
    exact (hmain _).2 ((hJ₂iff T hT h).2 h2)

include hP hfp hfl hE hiso in
/-- **The descent locus is cut out by finitely generated ideals on affine charts through every
point.** -/
theorem exists_chart_isCutOutBy_descentSubfunctor (y : points B S hS Y.1) :
    ∃ V : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤),
        IsCutOutBy (descentSubfunctor f E) V.1.hom I J ∧ I.FG ∧ J.FG := by
  obtain ⟨r, hyr⟩ := exists_mem_rankFibreLocus f hiso hE y
  have hK := isPerfect_pushforwardComplex f hP hfp hfl E hE
  obtain ⟨V₁, ⟨v₁, hv₁⟩, -, m, n, A, ⟨M⟩⟩ := exists_chart_bottomModel_of_vanishing hK
    (fun Y' g j hj => isZero_pullbackHomology_pushforwardComplex f hP hfp hfl E hE g j hj) y
  have hcut₁ := isCutOutBy_bottomRankSubfunctor (r := r) V₁ M
  let ψ : chartScheme V₁ → points B S hS Y.1 := fun z =>
    pointsMap B S hS (yoneda.obj V₁.obj.left) V₁.obj.hom
      ((schemePointsHomeomorph B S hS V₁.obj.left).symm z)
  have hψ : Continuous ψ := (continuous_pointsMap B S hS V₁.obj.hom).comp
    (schemePointsHomeomorph B S hS V₁.obj.left).symm.continuous
  have hψp : ∀ p, ψ (pointsToScheme B S hS V₁.obj.left p) =
      pointsMap B S hS (yoneda.obj V₁.obj.left) V₁.obj.hom p := fun p => by
    change pointsMap B S hS _ _ ((schemePointsHomeomorph B S hS V₁.obj.left).symm
      (schemePointsHomeomorph B S hS V₁.obj.left p)) = _
    rw [Homeomorph.symm_apply_apply]
  have hOopen : IsOpen (ψ ⁻¹' rankFibreLocus f E r) :=
    (isOpen_rankFibreLocus f hP.2.2 E r).preimage hψ
  have hz : pointsToScheme B S hS V₁.obj.left v₁ ∈ ψ ⁻¹' rankFibreLocus f E r := by
    rwa [Set.mem_preimage, hψp, hv₁]
  obtain ⟨_, ⟨O, hO, rfl⟩, hzO, hOsub⟩ :=
    (chartScheme V₁).isBasis_affineOpens.exists_subset_of_mem_open hz hOopen
  let W := openChart B S hS Y.1 V₁ O
  have hWrange : Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) =
      pointsMap B S hS (yoneda.obj V₁.obj.left) V₁.1.hom ''
        (pointsToScheme B S hS V₁.obj.left ⁻¹' (O : Set (chartScheme V₁))) :=
    range_pointsMap_openChart V₁ O
  have hcut := hcut₁.comp (openSubHom _ O)
  obtain ⟨J₂, hJ₂, hcutD⟩ := exists_isCutOutBy_descentSubfunctor_of_isCutOutBy f hP hfp hfl E hE
    hiso W hO (r := r) (by
      rw [hWrange]
      rintro _ ⟨p, hp, rfl⟩
      rw [← hψp]
      exact hOsub hp)
    ((Matrix.fg_fittingIdeal_cokerTranspose_kernelRankStratum A _).map _) hcut
  refine ⟨W, ?_, hO, _, _, hcutD,
    (Matrix.fg_fittingIdeal_cokerTranspose_kernelRankStratum A _).map _,
    ((Matrix.fg_fittingIdeal_cokerTranspose_kernelRankStratum A _).map _).mul hJ₂⟩
  rw [hWrange]
  exact ⟨v₁, hzO, hv₁⟩

end DescentStratum

/-! ### The descent locus -/

open DescentStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ Y` be a flat, proper morphism of finite presentation of algebraic spaces over
`S`, and `E` a finite locally free `𝒪_X`-module. Assume that for every `g : Y' ⟶ Y`, with base
change `f' : X' = X ×_Y Y' ⟶ Y'`, the map `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` is an isomorphism. Then there
is an immersion `j : Z ⟶ Y` of finite presentation such that a morphism `g : Y' ⟶ Y` factors
through `j` exactly when there is a finite locally free `𝒪_{Y'}`-module `N` with
`(f')^*N ≅ (g')^*E` (`AlgebraicGeometry.Space.HasDescentAt`; the source's `(g')^*L` is a typo for
`(g')^*E`). -/
@[stacks 0D23]
theorem exists_isImmersion_isFinitePresentation_factorsThrough_iff_hasDescentAt
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom)
    (hP : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
    (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
      IsIso (structureSharp B S hS (pullback.snd f g))) :
    ∃ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ Y),
      IsImmersion B S hS j.hom ∧ IsFinitePresentation B S hS j.hom ∧
      ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
        (∃ h : Y' ⟶ Z, h ≫ j = g) ↔ HasDescentAt f E g := by
  have hchart := exists_chart_isCutOutBy_descentSubfunctor f hP hfp hfl E hE hiso
  have hloc := isEtaleLocalOnSource_descentSubfunctor f E hiso
  obtain ⟨hZ, himm⟩ := isAlgebraicSpace_and_isImmersion_of_isCutOutBy Y.2 hloc fun y => by
    obtain ⟨V, hV, haff, I, J, h, -⟩ := hchart y
    exact ⟨V, hV, haff, I, J, h⟩
  exact ⟨⟨_, hZ⟩, ObjectProperty.homMk (descentSubfunctor f E).ι, himm,
    isFinitePresentation_ι_of_isCutOutBy Y.2 hloc hchart,
    fun g => exists_comp_homMk_ι_descentSubfunctor_iff f E hiso hZ g⟩

end AlgebraicGeometry.Space

end
