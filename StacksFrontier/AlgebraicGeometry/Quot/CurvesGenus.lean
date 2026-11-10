module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.HigherDirectImageRank
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme

/-!
# The decomposition `Curves^{h0,1} = ∐_g Curves_g` by genus (towards Stacks 0E6K)

Stacks 0E6K decomposes the open substack `Curves^{h0,1}` of the stack of curves (Stacks 0E6I)
into open and closed substacks `Curves_g`, `g ≥ 0`: a family of curves `f : X → S` lies in
`Curves_g` when `f_*𝒪_X = 𝒪_S` universally, the fibres of `f` have dimension `1`, and
`R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`. The source proves this from the
discussion of Section 0E0E and Stacks 0E1J: for a family in `Curves^{h0,1}` the module
`R¹f_*𝒪_X` is finite locally free and its formation commutes with arbitrary base change, so its
rank is a locally constant function on the base whose formation commutes with base change.

This file proves the decomposition from those inputs. The inputs not proved here enter as
explicit hypotheses: the two cohomological inputs of Stacks 0E6I (`hopen`, Stacks 0E0R at `i = 0`;
`hpush`, Stacks 0E6B part (a)), in the form of
`AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_of`, and parts (2) and (3) of
Stacks 0E1J (`h2`, `h3`), in the vocabulary of
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology`. No declaration of this file
carries a `stacks` attribute.

## Main definitions

* `AlgebraicGeometry.CurveFamily.FirstHigherDirectImageCommutesWithBaseChange`: part (3) of the
  conclusion of Stacks 0E1J, `h^*(R¹f_*𝒪_X) = R¹f'_*𝒪_{X'}` for every base change of the family.
* `AlgebraicGeometry.IsGenusCurveFamily`: condition (1)(b) of Stacks 0E6K, the defining
  property of `Curves_g`.

## Main results

* `AlgebraicGeometry.IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus`: condition (o) of Section
  0E0E for a property `Q` implying a property `P` with condition (o), when `Q` is cut out by an
  open set of points over every family with `P`. This is the method of Section 0E0E relative to
  an open substack, the last paragraph of that section.
* `AlgebraicGeometry.isGenusCurveFamily_iff_of`: over a family `G` in `Curves^{h0,1}`, a family
  mapping to `G` is in `Curves_g` exactly when its base maps into the rank locus of `g` of
  `R¹f_*𝒪_G`.
* `AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of`: condition (o) for `Curves_g`.
* `AlgebraicGeometry.curvesGenus_decomposition_of`: over every family in `Curves^{h0,1}` the loci
  of the `Curves_g` form a partition of the base into open and closed subsets.
* `AlgebraicGeometry.curvesGenus_isOpenSubstack_and_factors_iff_and_decomposition_of`: the open
  substacks `Curves_g ⊂ Curves^{h0,1}`, their characterization (1), and the decomposition.

## Implementation notes

"Locally free of rank `g`" is the rank clause of Stacks 0409 on the small étale site of the base,
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`, the site on which
`AlgebraicGeometry.CurveFamily.firstDirectImage` lives. The rank loci of a finite locally
free module and their compatibility with pullback are
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus`.

The decomposition into open and closed substacks is stated on the scheme-valued points of
`Curves^{h0,1}`: an object of `Curves^{h0,1}` over a scheme `S` is a family `G` over `S` in
`Curves^{h0,1}`, the base change of `Curves_g` along it is the open subscheme of `S` read off by
condition (o), and these opens are pairwise disjoint, cover `S`, and are therefore also closed.

`Curves_g` is `AlgebraicGeometry.curvesSubstack` of `IsGenusCurveFamily g`, so an intersection
`Curves^{P} ∩ Curves_g` with another open substack is `IsOpenCurvesLocus.and`.

## References

* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_curvesGenus (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_curvesGenus :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_curvesGenus
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_curvesGenus (B := B) (hZ := hZ)).has_limit _

/-! ### Condition (o) relative to an open substack -/

/-- **Condition (o) of Stacks 0E0E relative to an open substack.** Let `P` satisfy condition (o)
and let `Q` imply `P`. If over every family `G` with `P` there is an open set of points of the
base such that a family mapping to `G` has `Q` exactly when its base maps into it, then `Q`
satisfies condition (o).

Over an arbitrary family `G`, the open subspace of its base given by condition (o) for `P` is
represented by an open subscheme `V`, and `G` is restricted to `V` by a cartesian lift `G_V ⟶ G`
of the inclusion. The restricted family has `P`, and every family with `P` mapping to `G` maps to
`G_V`; so the open set of points for `Q` over `G_V`, carried into the base of `G` by the open
immersion, is the one for `Q` over `G`. -/
theorem IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus {P Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hQP : ∀ F : CurveFamily B hZ, Q F → P F)
    (h : ∀ G : CurveFamily B hZ, P G →
      ∃ Ω : Set (Space.points B integerBase hZ (schemeSpace G.base).obj), IsOpen Ω ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Q F ↔ Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
            (schemeSpaceMap a.baseMap).hom) ⊆ Ω) :
    IsOpenCurvesLocus B hZ Q := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  obtain ⟨W, hW, hchar⟩ := hP G
  -- The open subspace `W` of the base is represented by an open subscheme `V` of the site.
  obtain ⟨V, j, hj, e, he⟩ : ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ G.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
    have key : ∀ (U' : BigFppfOver B integerBase hZ) (W' : Subfunctor (yoneda.obj U')),
        Space.IsOpenSubspace B integerBase hZ W' →
        ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ U'),
          IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
          ∃ e : yoneda.obj V ≅ W'.toFunctor, e.hom ≫ W'.ι = yoneda.map j := by
      intro U' W' hW'
      let h := hW'.2.rep.isPullback (𝟙 (yoneda.obj U'))
      let eMap := hW'.2.rep.fst (𝟙 (yoneda.obj U'))
      have : IsIso eMap := h.isIso_fst_of_isIso
      exact ⟨_, hW'.2.rep.snd (𝟙 (yoneda.obj U')), hW'.2.property_snd (𝟙 (yoneda.obj U')),
        asIso eMap, by simpa [eMap] using h.w⟩
    exact key G.base W hW
  -- The restriction of `G` to `V`, as a cartesian lift of `V ⟶ S`.
  have hfib : (curvesProjectionOver B hZ).IsFiberedInGroupoids := (curvesFiberedCategory B hZ).2
  obtain ⟨GV, φ, hφ⟩ := hfib.exists_lift j G rfl
  obtain ⟨i, hfac⟩ : ∃ i : GV.base ≅ V, φ.baseMap = i.hom ≫ j := by
    have := hφ
    refine ⟨eqToIso (IsHomLift.domain_eq (curvesProjectionOver B hZ) j φ), ?_⟩
    have h := IsHomLift.fac' (curvesProjectionOver B hZ) j φ
    change φ.baseMap = eqToHom _ ≫ j ≫ eqToHom (rfl : G.base = G.base) at h
    simp only [eqToHom_refl, Category.comp_id] at h
    exact h
  have hfactor : (schemeSpaceMap φ.baseMap).hom = (yoneda.map i.hom ≫ e.hom) ≫ W.ι := by
    change yoneda.map φ.baseMap = _
    rw [hfac, Functor.map_comp, Category.assoc, he]
    rfl
  have hPV : P GV := (hchar GV φ).mpr ⟨yoneda.map i.hom ≫ e.hom, hfactor.symm⟩
  have hrangeφ : Set.range (Space.pointsMap B integerBase hZ (schemeSpace GV.base).obj
        (schemeSpaceMap φ.baseMap).hom) =
      Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) := by
    rw [hfactor]
    exact Space.range_pointsMap_comp_isIso B integerBase hZ (yoneda.mapIso i ≪≫ e).hom W.ι
  have : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) := by
    rw [hfac, Functor.map_comp]
    infer_instance
  have hopenMap := Space.isOpenMap_pointsMap_yonedaMap_of_etale B integerBase hZ φ.baseMap
    inferInstance
  have hnat : ∀ w : Space.points B integerBase hZ (yoneda.obj GV.base),
      Space.pointsToScheme B integerBase hZ G.base
          (Space.pointsMap B integerBase hZ (yoneda.obj GV.base) (yoneda.map φ.baseMap) w) =
        (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap
          (Space.pointsToScheme B integerBase hZ GV.base w) :=
    fun w => Space.pointsToScheme_pointsMap_yoneda B integerBase hZ φ.baseMap w
  have hinj : Function.Injective (Space.pointsMap B integerBase hZ (schemeSpace GV.base).obj
      (schemeSpaceMap φ.baseMap).hom) := by
    intro p q hpq
    apply Space.injective_pointsToScheme B integerBase hZ GV.base
    apply ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap).isOpenEmbedding.injective
    rw [← hnat p, ← hnat q]
    exact congrArg (Space.pointsToScheme B integerBase hZ G.base) hpq
  obtain ⟨Ω', hΩ', hQV⟩ := h GV hPV
  -- Every family with `P` mapping to `G` maps to `G_V` over its morphism to `G`.
  have hlift : ∀ (F : CurveFamily B hZ) (a : F ⟶ G), P F → ∃ χ : F ⟶ GV, χ ≫ φ = a := by
    intro F a hPF
    obtain ⟨t, ht⟩ := (hchar F a).mp hPF
    let t' : yoneda.obj F.base ⟶ W.toFunctor := t
    have ht' : t' ≫ W.ι = yoneda.map a.baseMap := ht
    let f₀ : F.base ⟶ GV.base := Yoneda.fullyFaithful.preimage (t' ≫ e.inv ≫ yoneda.map i.inv)
    have hf₀ : f₀ ≫ φ.baseMap = a.baseMap := by
      apply Yoneda.fullyFaithful.map_injective
      have hW' : e.inv ≫ yoneda.map j = W.ι := (Iso.inv_comp_eq e).mpr he.symm
      have hmap : yoneda.map (f₀ ≫ φ.baseMap) = t' ≫ (e.inv ≫ yoneda.map j) := by
        rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, hfac]
        simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rw [hmap]
      exact (congrArg (fun m => t' ≫ m) hW').trans ht'
    obtain ⟨χ, ⟨-, hχ⟩, -⟩ := hfib.unique_lift φ a f₀ hf₀
    exact ⟨χ, hχ⟩
  have hrange : ∀ (F : CurveFamily B hZ) (χ : F ⟶ GV),
      Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
          (schemeSpaceMap (χ ≫ φ).baseMap).hom) =
        Space.pointsMap B integerBase hZ (schemeSpace GV.base).obj
            (schemeSpaceMap φ.baseMap).hom ''
          Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
            (schemeSpaceMap χ.baseMap).hom) := by
    intro F χ
    change Set.range (Space.pointsMap B integerBase hZ _
      (schemeSpaceMap (χ.baseMap ≫ φ.baseMap)).hom) = _
    rw [schemeSpaceMap_comp]
    change Set.range (Space.pointsMap B integerBase hZ _
      ((schemeSpaceMap χ.baseMap).hom ≫ (schemeSpaceMap φ.baseMap).hom)) = _
    rw [Space.pointsMap_comp, Set.range_comp]
  refine ⟨Space.pointsMap B integerBase hZ (schemeSpace GV.base).obj
      (schemeSpaceMap φ.baseMap).hom '' Ω', hopenMap _ hΩ', fun F a => ?_⟩
  constructor
  · intro hQF
    obtain ⟨χ, rfl⟩ := hlift F a (hQP F hQF)
    rw [hrange F χ]
    exact Set.image_mono ((hQV F χ).mp hQF)
  · intro hsub
    have hPF : P F := by
      refine (hchar F a).mpr ((Space.factorsThrough_openSubspace_iff_points B integerBase hZ
        (schemeSpace G.base).property (schemeSpace F.base).property W hW _).mpr ?_)
      rw [← hrangeφ]
      exact hsub.trans (Set.image_subset_range _ _)
    obtain ⟨χ, rfl⟩ := hlift F a hPF
    rw [hrange F χ] at hsub
    exact (hQV F χ).mpr ((Set.image_subset_image_iff hinj).mp hsub)

/-! ### The genus of a family in `Curves^{h0,1}` -/

namespace CurveFamily

/-- **Part (3) of the conclusion of Stacks 0E1J: `R¹f_*𝒪_X` commutes with base change.** For
every family `F` mapping to `X`, that is every base change of `X` along a morphism `h : S' → S`
of base schemes, the pullback `h^*(R¹f_*𝒪_X)` is `R¹f'_*𝒪_{X'}`. -/
def FirstHigherDirectImageCommutesWithBaseChange (X : CurveFamily B hZ) : Prop :=
  ∀ (F : CurveFamily B hZ) (a : F ⟶ X),
    Nonempty ((Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).obj
        (X.firstDirectImage B hZ) ≅ (F.firstDirectImage B hZ))

end CurveFamily

variable (B hZ) in
/-- **Condition (1)(b) of Stacks 0E6K, the families of `Curves_g`.** A family of curves
`f : X → S` with `f_*𝒪_X = 𝒪_S`, this holding after arbitrary base change, whose fibres have
dimension `1`, and whose first higher direct image `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of
rank `g`. -/
abbrev IsGenusCurveFamily (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsH01CurveFamily B hZ X ∧
    RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      (X.firstDirectImage B hZ) g

section Inputs

variable
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)

include hopen hpush h3 in
/-- **The genus of a family over a family in `Curves^{h0,1}`.** Let `G` be a family in
`Curves^{h0,1}` and suppose `R¹f_*𝒪_G` finite locally free with formation commuting with base
change (Stacks 0E1J, parts (2) and (3)). Then a family `F` mapping to `G` is in `Curves_g` exactly
when its base maps into the rank locus of `g` of `R¹f_*𝒪_G`. -/
theorem isGenusCurveFamily_iff_of (g : ℕ) {G : CurveFamily B hZ}
    (hG : IsH01CurveFamily B hZ G)
    (hR : SheafOfModules.IsFiniteLocallyFreeOnSite (G.firstDirectImage B hZ))
    (F : CurveFamily B hZ) (a : F ⟶ G) :
    IsGenusCurveFamily B hZ g F ↔
      Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
        (schemeSpaceMap a.baseMap).hom) ⊆ Space.rankLocus (G.firstDirectImage B hZ) g := by
  have hF : IsH01CurveFamily B hZ F :=
    (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom a hG
  obtain ⟨e⟩ := h3 G
    (CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions hG.1)
    F a
  rw [← Space.isFiniteLocallyFreeOfRank_modulePullback_iff (schemeSpaceMap a.baseMap) hR g]
  exact ⟨fun h => RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm h.2,
    fun h => ⟨hF, RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e h⟩⟩

include h2 in
/-- For a family in `Curves^{h0,1}`, `R¹f_*𝒪_X` is finite locally free in the covering-family
sense of Stacks 03DL (2), by part (2) of Stacks 0E1J. -/
theorem isFiniteLocallyFreeOnSite_firstHigherDirectImage_of {G : CurveFamily B hZ}
    (hG : IsH01CurveFamily B hZ G) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (G.firstDirectImage B hZ) :=
  Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree _
    (h2 G (CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions
      hG.1))

include hopen hpush h2 h3 in
/-- **Condition (o) of Stacks 0E0E for `Curves_g`, from the inputs of Stacks 0E6I and 0E1J.** The
locus is cut out, over a family in `Curves^{h0,1}`, by the open rank locus of `g` of
`R¹f_*𝒪`, and `Curves^{h0,1}` is open by Stacks 0E6I. -/
theorem isOpenCurvesLocus_isGenusCurveFamily_of (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsGenusCurveFamily B hZ g) :=
  IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus
    (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush) (fun _ h => h.1) fun G hG =>
      ⟨Space.rankLocus (G.firstDirectImage B hZ) g, Space.isOpen_rankLocus _ g,
        isGenusCurveFamily_iff_of hopen hpush h3 g hG
          (isFiniteLocallyFreeOnSite_firstHigherDirectImage_of h2 hG)⟩

include hopen hpush h2 h3 in
/-- **The decomposition `Curves^{h0,1} = ∐_g Curves_g` into open and closed substacks, read on a
scheme-valued point of `Curves^{h0,1}`.** For every family `G` over a scheme `S` in
`Curves^{h0,1}` there are subsets `Ω_g` of the points of `S`, open and closed, pairwise disjoint
and covering `S`, such that a family mapping to `G` is in `Curves_g` exactly when its base maps
into `Ω_g`: the base change of `Curves_g ⊂ Curves^{h0,1}` along `S → Curves^{h0,1}` is the open
and closed subscheme `Ω_g`, and these partition `S`. -/
theorem curvesGenus_decomposition_of (G : CurveFamily B hZ) (hG : IsH01CurveFamily B hZ G) :
    ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        (⋃ g, Ω g) = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsGenusCurveFamily B hZ g F ↔
            Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ Ω g := by
  have hR := isFiniteLocallyFreeOnSite_firstHigherDirectImage_of h2 hG
  let Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj) :=
    fun g => Space.rankLocus (G.firstDirectImage B hZ) g
  have hdisj : Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) := fun g g' hne =>
    Set.disjoint_left.mpr fun s hs hs' => hne (Space.eq_of_mem_rankLocus_of_mem_rankLocus hs hs')
  have hcov : (⋃ g, Ω g) = Set.univ :=
    Set.eq_univ_of_forall fun s => Set.mem_iUnion.mpr (Space.exists_mem_rankLocus hR s)
  refine ⟨Ω, fun g => ⟨Space.isOpen_rankLocus _ g, ?_⟩, hdisj, hcov,
    fun g => isGenusCurveFamily_iff_of hopen hpush h3 g hG hR⟩
  have hcompl : (Ω g)ᶜ = ⋃ g' ∈ {g' | g' ≠ g}, Ω g' := by
    ext s
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hs
      obtain ⟨g', hg'⟩ := Space.exists_mem_rankLocus hR s
      exact ⟨g', fun h => hs (h ▸ hg'), hg'⟩
    · rintro ⟨g', hne, hs'⟩ hs
      exact Set.disjoint_left.mp (hdisj hne) hs' hs
  exact isOpen_compl_iff.mp (hcompl ▸ isOpen_biUnion fun g' _ => Space.isOpen_rankLocus _ g')

include hopen hpush h2 h3 in
/-- **Stacks 0E6K, the decomposition and part (1), from the inputs of Stacks 0E6I and 0E1J.** If
the fibrewise condition `k = H⁰(X_k, 𝒪_{X_k})` satisfies condition (o) of Stacks 0E0E (Stacks
0E0R at `i = 0`) and implies `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)), and if for every
family with `κ(s) = H⁰(X_s, 𝒪_{X_s})` the module `R¹f_*𝒪_X` is finite locally free and commutes
with base change (Stacks 0E1J, parts (2) and (3)), then for every `g ≥ 0`
* `Curves_g` is an open substack of `Curves`, contained in `Curves^{h0,1}`;
* the classifying morphism of a family of curves `f : X → S` factors through `Curves_g` exactly
  when `f_*𝒪_X = 𝒪_S` universally, the fibres of `f` have dimension `1`, and `R¹f_*𝒪_X` is
  locally free of rank `g` (part (1));
* over every family in `Curves^{h0,1}`, with base `S`, the loci of the `Curves_g` are open and
  closed subsets of `S` which are pairwise disjoint and cover `S`: `Curves^{h0,1} = ∐_g Curves_g`
  as open and closed substacks. -/
theorem curvesGenus_isOpenSubstack_and_factors_iff_and_decomposition_of :
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isGenusCurveFamily_of hopen hpush h2 h3 g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isGenusCurveFamily_of hopen hpush h2 h3 g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsGenusCurveFamily B hZ g X → IsH01CurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsGenusCurveFamily B hZ g) = y) ↔
          IsGenusCurveFamily B hZ g (y.obj (Over.mk (𝟙 U.left))))) ∧
    ∀ G : CurveFamily B hZ, IsH01CurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g :=
  ⟨fun g => ⟨isOpenImmersion_curvesSubstackInclusion
      (isOpenCurvesLocus_isGenusCurveFamily_of hopen hpush h2 h3 g), fun _ h => h.1,
    fun U y hy => factors_curvesSubstack_iff
      (isOpenCurvesLocus_isGenusCurveFamily_of hopen hpush h2 h3 g) U y hy⟩,
    curvesGenus_decomposition_of hopen hpush h2 h3⟩

end Inputs

/-! ### `R¹f_*𝒪_X` of a scheme over a field, through Stacks 071N -/

section Comparison071N

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable
  (h071N : ∀ {T' T : BigFppfOver B integerBase hZ} (g : T' ⟶ T)
    (_hqc : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map g))
    (_hsep : IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map g))
    (F : ((BigFppfOver.toScheme B integerBase hZ).obj T').Modules) (_hF : F.IsQuasicoherent)
    (k : ℕ),
    have := Space.hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T')
      (isAlgebraicSpace_yoneda B integerBase hZ T')
    have := Space.modulePushforward_additive B integerBase hZ
      (Space.representedSpaceMap B integerBase hZ g)
    Nonempty (((Space.modulePushforward B integerBase hZ
        (Space.representedSpaceMap B integerBase hZ g)).rightDerived k).obj
        ((Space.representedAssociatedModule B integerBase hZ T'
          (isAlgebraicSpace_yoneda B integerBase hZ T')).obj F) ≅
      (Space.representedAssociatedModule B integerBase hZ T
          (isAlgebraicSpace_yoneda B integerBase hZ T)).obj
        (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived
          k).obj F)))
  {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
  (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
  (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)

include h071N in
/-- **`R¹f_*𝒪_X` of the family of curves of a proper morphism of schemes is the associated
module of the Zariski `R¹φ_*𝒪`.** For a proper morphism `φ : T → W` of schemes of the site, the
first higher direct image of the structure sheaf on the small étale site of `W` is the module
associated with the Zariski higher direct image `R¹φ_*𝒪_T`: this is Stacks 071N (the input
`h071N`, in its form for a quasi-compact separated morphism)
at the structure sheaf, which is quasi-coherent and is carried to the structure sheaf by the
associated-module functor. -/
theorem nonempty_firstHigherDirectImage_curveFamilyOfSchemeMorphism_iso_of :
    Nonempty ((CurveFamily.firstDirectImage B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim)) ≅
      (Space.representedAssociatedModule B integerBase hZ W
          (isAlgebraicSpace_yoneda B integerBase hZ W)).obj
        (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived
          1).obj
          (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj T).ringCatSheaf))) := by
  have := hproper
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T)
    (isAlgebraicSpace_yoneda B integerBase hZ T)
  have := Space.modulePushforward_additive B integerBase hZ
    (Space.representedSpaceMap B integerBase hZ g)
  obtain ⟨e⟩ := h071N g inferInstance inferInstance
    (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj T).ringCatSheaf)
    inferInstance 1
  exact ⟨((Space.modulePushforward B integerBase hZ
      (Space.representedSpaceMap B integerBase hZ g)).rightDerived 1).mapIso
        (Space.representedAssociatedModuleObjUnitIso B integerBase hZ T
          (isAlgebraicSpace_yoneda B integerBase hZ T)).symm ≪≫ e⟩

include h071N in
/-- **`R¹f_*𝒪_X` of a proper scheme over a field is locally free of rank the genus.** For a
proper morphism `φ : T → W` of schemes of the site with `W = Spec k` and `dim(T) ≤ 1`, the first
higher direct image of the structure sheaf of its family of curves is finite locally free on the
small étale site of `Spec k` of rank the genus `dim_k H¹(T, 𝒪_T)` (Stacks 0BY7).

By Stacks 071N (the input `h071N`) it is the module associated with the Zariski `R¹φ_*𝒪_T`
(`nonempty_firstHigherDirectImage_curveFamilyOfSchemeMorphism_iso_of`), which is free of rank
the genus on the one-point space `Spec k`
(`AlgebraicGeometry.isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_genus_of_eq_spec`);
the associated module of a module of rank `r` has rank `r` on the small étale site (Stacks 05VG
with the rank kept, `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule`),
read on the small étale site of the represented algebraic space through
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff`. -/
theorem isFiniteLocallyFreeOfRank_firstHigherDirectImage_curveFamilyOfSchemeMorphism_genus_of
    (k : Type u) [Field k] (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k)) :
    RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ
        (schemeSpace (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
          hdim).base).1
        (schemeSpace (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
          hdim).base).2)
      ((curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
        hdim).firstDirectImage B hZ)
      (genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)) := by
  obtain ⟨e⟩ := nonempty_firstHigherDirectImage_curveFamilyOfSchemeMorphism_iso_of h071N g hflat
    hproper hlfp hqc hsep hqsep hdim
  refine RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm ?_
  have hZar := isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_genus_of_eq_spec k
    ((BigFppfOver.toScheme B integerBase hZ).map g) hW hproper
  have hEt := SmallEtale.isFiniteLocallyFreeOfRank_associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B integerBase hZ).obj W) W.left.property _ _ hZar
  exact (Space.isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B integerBase hZ W _
    _).2 hEt

end Comparison071N

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

namespace CurveFamily

section OverField

variable
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
  {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
  (k : Type u) [Field k] (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
  (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
  (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)

include hpush hW in
/-- **Condition (2)(b) of Stacks 0E6K on a proper scheme over a field, from the rank of its
`R¹`.** For the family of curves of a proper scheme `X = T` of dimension at most one over a field
`k = W`: if `f_*𝒪 = 𝒪` universally follows from the fibrewise condition (Stacks 0E6B, part (a)),
and if for `X` in `Curves^{h0,1}` the module `R¹f_*𝒪_X` on the small étale site of `Spec k` is
locally free of rank the genus of `X` (Stacks 0BY7), then `X` is in `Curves_n` exactly when
`H⁰(X, 𝒪_X) = k`, `dim(X) = 1` and the genus of `X` is `n`. -/
theorem isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of
    (hrk : IsH01CurveFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) →
      RingedSite.IsFiniteLocallyFreeOfRank
        (Space.smallEtaleRingedSite B integerBase hZ
          (schemeSpace (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
            hdim).base).1
          (schemeSpace (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
            hdim).base).2)
        ((curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep
          hdim).firstDirectImage B hZ)
        (genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)))
    (n : ℕ) :
    IsGenusCurveFamily B hZ n
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) = n := by
  have hne : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).base) := by
    change Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj W)
    rw [hW]
    exact inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨x⟩ := hne
  let p := (Space.pointsEquivScheme B integerBase hZ _).symm x
  rw [← isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat hproper hlfp hqc
    hsep hqsep hdim]
  constructor
  · rintro ⟨hH, hn⟩
    exact ⟨hH, Space.eq_of_isFiniteLocallyFreeOfRank_of_isFiniteLocallyFreeOfRank (hrk hH) hn p⟩
  · rintro ⟨hH, hgen⟩
    exact ⟨hH, hgen ▸ hrk hH⟩

section OverFieldComparison071N

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

include hpush hW in
/-- **Condition (2)(b) of Stacks 0E6K on a proper scheme over a field.** For the family of curves
of a proper scheme `X = T` of dimension at most one over a field `k = W`: if `f_*𝒪 = 𝒪`
universally follows from the fibrewise condition (Stacks 0E6B, part (a), the input `hpush`), then
`X` is in `Curves_n` exactly when `H⁰(X, 𝒪_X) = k`, `dim(X) = 1` and the genus of `X` is `n`.

This is `isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of` with its rank input proved:
`R¹f_*𝒪_X` on the small étale site of `Spec k` is locally free of rank the genus of `X`
(`isFiniteLocallyFreeOfRank_firstHigherDirectImage_curveFamilyOfSchemeMorphism_genus_of`, from
Stacks 071N, the input `h071N`). -/
theorem isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of_rightDerivedComparison
    (h071N : ∀ {T' T : BigFppfOver B integerBase hZ} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map g))
      (_hsep : IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map g))
      (F : ((BigFppfOver.toScheme B integerBase hZ).obj T').Modules) (_hF : F.IsQuasicoherent)
      (k : ℕ),
      have := Space.hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T')
        (isAlgebraicSpace_yoneda B integerBase hZ T')
      have := Space.modulePushforward_additive B integerBase hZ
        (Space.representedSpaceMap B integerBase hZ g)
      Nonempty (((Space.modulePushforward B integerBase hZ
          (Space.representedSpaceMap B integerBase hZ g)).rightDerived k).obj
          ((Space.representedAssociatedModule B integerBase hZ T'
            (isAlgebraicSpace_yoneda B integerBase hZ T')).obj F) ≅
        (Space.representedAssociatedModule B integerBase hZ T
            (isAlgebraicSpace_yoneda B integerBase hZ T)).obj
          (((Scheme.Modules.pushforward
            ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived k).obj F)))
    (n : ℕ) :
    IsGenusCurveFamily B hZ n
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) = n :=
  isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat hproper hlfp hqc hsep
    hqsep hdim (fun _ =>
      isFiniteLocallyFreeOfRank_firstHigherDirectImage_curveFamilyOfSchemeMorphism_genus_of
        h071N g hflat hproper hlfp hqc hsep hqsep hdim k hW) n

end OverFieldComparison071N

end OverField

end CurveFamily

end AlgebraicGeometry

end
