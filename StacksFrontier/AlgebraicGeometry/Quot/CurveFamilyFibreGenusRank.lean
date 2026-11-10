module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.HigherDirectImageRank
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The genus of the fibres of a family of curves and the rank of `R¹f_*𝒪_X`

Let `f : X → S` be a family of curves (Stacks 0D4Z) with `k = H⁰(X_k, 𝒪_{X_k})` on every fibre over
a field. By parts (2) and (3) of Stacks 0E1J
(`CurveFamily.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre`
and `CurveFamily.nonempty_modulePullback_firstDirectImage_iso_of_bijective_algebraMap_fibre`)
`R¹f_*𝒪_X` is finite locally free and commutes with base change, so its rank at a point `s` of `S`
is the rank of `R¹` of the fibre `X_s`, which is the genus of `X_s` (Stacks 0BY7, through the
comparison of étale and Zariski cohomology of Stacks 071N). Hence:

* the rank of `R¹f_*𝒪_X` at the image of a field-valued point is the genus of the fibre there
  (`CurveFamily.mem_rankLocus_firstDirectImage_of_isPullback`);
* every fibre has genus `g` exactly when `R¹f_*𝒪_X` is locally free of rank `g`
  (`CurveFamily.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre`);
* the locus of points with fibres of genus `g` is the rank locus of `g`, which is open and closed
  (`CurveFamily.fibreGenusLocus_eq_rankLocus`,
  `CurveFamily.isClopen_fibreGenusLocus`), and it is compatible with base change
  (`CurveFamily.preimage_fibreGenusLocus`);
* on stable families, all fibres having genus `g` is the same as `R¹f_*𝒪_X` being locally free of
  rank `g` (`AlgebraicGeometry.isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus`).

These are the facts used for the genus decompositions of Stacks 0E6K, 0E78, 0E83 and 0E1K. No
declaration here carries a Stacks attribute.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-! ### `R¹` of a proper scheme over a field -/

/-- **`R¹φ_*𝒪` of a proper scheme over a field has rank the genus**, on the small étale site of
the represented algebraic space: for `φ : T ⟶ W` proper with `W = Spec k`, the first higher direct
image of the structure sheaf along the morphism of represented algebraic spaces is finite locally
free of rank `dim_k H¹(T, 𝒪_T)` (Stacks 0BY7). By Stacks 071N it is the module associated with the
Zariski `R¹φ_*𝒪_T`, which is free of rank the genus on the one-point space `Spec k`. -/
theorem isFiniteLocallyFreeOfRank_rightDerived_modulePushforward_schemeSpaceMap_genus
    (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k)) :
    have := Space.hasInjectiveResolutions_modules B integerBase hZ (schemeSpace T).1
      (schemeSpace T).2
    RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace W).1 (schemeSpace W).2)
      (((Space.modulePushforward B integerBase hZ (schemeSpaceMap g)).rightDerived 1).obj
        (Space.structureSheafModule B integerBase hZ (schemeSpace T)))
      (genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)) := by
  have := hproper
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T)
    (isAlgebraicSpace_yoneda B integerBase hZ T)
  have := Space.modulePushforward_additive B integerBase hZ
    (Space.representedSpaceMap B integerBase hZ g)
  obtain ⟨e₀⟩ :=
    Space.nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
      B integerBase hZ g inferInstance inferInstance
      (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj T).ringCatSheaf)
      inferInstance 1
  refine RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ (((Space.modulePushforward B integerBase hZ
      (Space.representedSpaceMap B integerBase hZ g)).rightDerived 1).mapIso
        (Space.representedAssociatedModuleObjUnitIso B integerBase hZ T
          (isAlgebraicSpace_yoneda B integerBase hZ T)).symm ≪≫ e₀).symm ?_
  have hZar := isFiniteLocallyFreeOfRank_rightDerived_pushforward_unit_genus_of_eq_spec k
    ((BigFppfOver.toScheme B integerBase hZ).map g) hW hproper
  have hEt := SmallEtale.isFiniteLocallyFreeOfRank_associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B integerBase hZ).obj W) W.left.property _ _ hZar
  exact (Space.isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B integerBase hZ W _
    _).2 hEt

/-! ### Rank loci and inverse images -/

/-- **The rank loci of the inverse image of a finite locally free module are the inverse images of
its rank loci.** -/
theorem Space.preimage_rankLocus_modulePullback {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {M : Space.Modules.{u, u} B S hS Y.1 Y.2}
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) (hMq : M.IsQuasicoherentOnSite) (n : ℕ) :
    Space.pointsMap B S hS X.1 f.hom ⁻¹' Space.rankLocus M n =
      Space.rankLocus ((Space.modulePullback B S hS f).obj M) n := by
  have hfM := Space.isFiniteLocallyFreeOnSite_modulePullback B S hS f M hMq hM
  have key : ∀ (y : Space.points B S hS X.1) (m : ℕ),
      y ∈ Space.rankLocus ((Space.modulePullback B S hS f).obj M) m →
        Space.pointsMap B S hS X.1 f.hom y ∈ Space.rankLocus M m := by
    intro y m hy
    obtain ⟨Z, z, hZ', rfl⟩ := (Space.mem_rankLocus_iff _ m y).mp hy
    exact Space.mem_rankLocus_of_isFreeOfRankOn_modulePullback f hM hZ' z
  ext y
  simp only [Set.mem_preimage]
  constructor
  · intro hy
    obtain ⟨m, hm⟩ := Space.exists_mem_rankLocus hfM y
    rwa [Space.eq_of_mem_rankLocus_of_mem_rankLocus hy (key y m hm)]
  · exact key y n

/-- **The rank loci depend only on the isomorphism class of the module.** -/
theorem Space.rankLocus_congr {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}
    {M N : Space.Modules.{u, u} B S hS Y.1 Y.2} (e : M ≅ N) (n : ℕ) :
    Space.rankLocus M n = Space.rankLocus N n := by
  have key : ∀ {M N : Space.Modules.{u, u} B S hS Y.1 Y.2} (e : M ≅ N)
      (V : SmallEtale B S hS Y.1), Space.IsFreeOfRankOn M V n → Space.IsFreeOfRankOn N V n := by
    rintro M N e V ⟨ι, ⟨hc⟩⟩
    exact ⟨fun i => ι i ≫ (SheafOfModules.overFunctor _ V).map e.hom,
      ⟨hc.ofIsoColimit (Cocone.ext ((SheafOfModules.overFunctor _ V).mapIso e) fun _ => rfl)⟩⟩
  ext x
  simp only [Space.rankLocus, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact exists_congr fun V => and_congr_left fun _ => ⟨key e V, key e.symm V⟩

namespace CurveFamily

/-! ### The rank at a point is the genus of the fibre -/

variable (X : CurveFamily B hZ)
  (h : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
      p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))))

omit h in
/-- The morphism of algebraic spaces of a field-valued point of the base is the one represented by
its value. -/
theorem homMk_yonedaEquiv_symm_value
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
      schemeSpace p.siteObject ⟶ schemeSpace X.base) = schemeSpaceMap p.value :=
  InducedCategory.hom_ext (yonedaEquiv.injective ((yonedaEquiv.apply_symm_apply _).trans
    (yonedaEquiv_yoneda_map p.value).symm))

omit h in
/-- The class of a field-valued point of the base is the image of the tautological point of its
spectrum. -/
theorem class_mem_range_pointsMap
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    p.class B integerBase hZ _ ∈ Set.range (Space.pointsMap B integerBase hZ
      (schemeSpace p.siteObject).obj (schemeSpaceMap p.value).hom) := by
  refine ⟨Space.FieldValuedPoint.class B integerBase hZ _
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := 𝟙 p.siteObject }, ?_⟩
  rw [Space.pointsMap_class]
  have hv : (schemeSpaceMap p.value).hom.app (Opposite.op p.siteObject) (𝟙 p.siteObject) =
      p.value := Category.id_comp p.value
  change Quot.mk _
      { carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase,
        value := (schemeSpaceMap p.value).hom.app (Opposite.op p.siteObject) (𝟙 p.siteObject) } =
      Quot.mk _ p
  rw [hv]

include h in
/-- **The rank of `R¹f_*𝒪_X` at a field-valued point is the genus of the fibre there.** For a
family of curves with `k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields and a presentation of the
fibre over a field-valued point `p` by a scheme `V`, the point of the base under `p` lies in the
rank locus of `R¹f_*𝒪_X` of the genus of `V`. -/
theorem mem_rankLocus_firstDirectImage_of_isPullback
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value)) :
    p.class B integerBase hZ _ ∈ Space.rankLocus (X.firstDirectImage B hZ)
      (genus ((BigFppfOver.toScheme B integerBase hZ).map v)) := by
  have hR := X.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre h
  have hyon : yonedaEquiv.symm p.value = yoneda.map p.value :=
    (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map p.value).symm
  rw [hyon] at hq
  have sq : IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v)
      X.toBase (schemeSpaceMap p.value) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hq.w) hq
  have hproper := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap sq
  obtain ⟨e⟩ := Space.nonempty_modulePullback_homology_one_derivedModulePushforward_iso X.toBase
    X.proper X.flat X.finitePresentation h
    (fun p j hj => X.isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct
      p j hj)
    (schemeSpaceMap p.value) (schemeSpaceMap v) (ObjectProperty.homMk q) sq
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (schemeSpace V).1
    (schemeSpace V).2
  have hV := isFiniteLocallyFreeOfRank_rightDerived_modulePushforward_schemeSpaceMap_genus
    p.carrier v hproper rfl
  rw [eqToHom_refl, Category.comp_id] at hV
  have hpull : RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace p.siteObject).1
        (schemeSpace p.siteObject).2)
      ((Space.modulePullback B integerBase hZ (schemeSpaceMap p.value)).obj
        (X.firstDirectImage B hZ))
      (genus ((BigFppfOver.toScheme B integerBase hZ).map v)) :=
    RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      ((((DerivedCategory.homologyFunctor _ 1).mapIso
          ((Space.smallEtaleDerivedModulePushforwardIso B integerBase hZ (schemeSpaceMap v)).app
            _) ≪≫
        Space.homologyDerivedModulePushforwardSingleIso B integerBase hZ (schemeSpaceMap v)
          (Space.structureSheafModule B integerBase hZ (schemeSpace V)) 0 1 1
          (by norm_num)).symm ≪≫ e.symm ≪≫
        (Space.modulePullback B integerBase hZ (schemeSpaceMap p.value)).mapIso
          X.homologyDerivedPushforwardIsoFirstHigherDirectImage)) hV
  exact (Space.isFiniteLocallyFreeOfRank_modulePullback_iff (schemeSpaceMap p.value) hR _).1 hpull
    (X.class_mem_range_pointsMap p)

omit h in
/-- **The fibre of a family of curves over a field is presented by a scheme**: it is the total
space of a family of curves over the one-point, affine, Noetherian scheme `Spec k`, hence
representable (Stacks 0ADD). -/
theorem exists_isPullback_yoneda_fieldValuedPoint
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) := by
  let Y := X.baseChange p.value
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of p.carrier)))
  have := Y.isRepresentable_total_of_subsingleton
  let e : yoneda.obj Y.total.obj.reprX ≅ Y.total.obj := Y.total.obj.reprW
  have hyon : yonedaEquiv.symm p.value = yoneda.map p.value :=
    (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map p.value).symm
  let v : Y.total.obj.reprX ⟶ p.siteObject :=
    Yoneda.fullyFaithful.preimage (e.hom ≫ pullback.snd X.toBase.hom (yoneda.map p.value))
  refine ⟨Y.total.obj.reprX, v, e.hom ≫ pullback.fst X.toBase.hom (yoneda.map p.value), ?_⟩
  rw [hyon, show yoneda.map v = e.hom ≫ pullback.snd X.toBase.hom (yoneda.map p.value) from
    Yoneda.fullyFaithful.map_preimage _]
  refine IsPullback.of_iso (IsPullback.of_hasPullback X.toBase.hom (yoneda.map p.value)) e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Iso.symm_hom]
    exact (Category.comp_id _).trans (e.inv_hom_id_assoc _).symm
  · simp only [Iso.refl_hom, Iso.symm_hom]
    exact (Category.comp_id _).trans (e.inv_hom_id_assoc _).symm
  · simp only [Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp only [Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-! ### The genus as a property of the fibres, and as the rank of `R¹f_*𝒪_X` -/

include h in
/-- **Every fibre has genus `g` exactly when `R¹f_*𝒪_X` is locally free of rank `g`**, for a
family of curves with `k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields. -/
theorem hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre (g : ℕ) :
    HasFieldPointFibreGenus B hZ X g ↔ HasGenus B hZ X g := by
  have hR := X.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre h
  constructor
  · intro hX
    have hall : ∀ x : Space.points B integerBase hZ (schemeSpace X.base).obj,
        x ∈ Space.rankLocus (X.firstDirectImage B hZ) g := by
      intro x
      obtain ⟨p, rfl⟩ := Quot.exists_rep x
      obtain ⟨V, v, q, hq, hg⟩ := hX p
      exact hg ▸ X.mem_rankLocus_firstDirectImage_of_isPullback h p v q hq
    exact RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      ((Space.modulePullbackIdIso B integerBase hZ (schemeSpace X.base)).app _)
      ((Space.isFiniteLocallyFreeOfRank_modulePullback_iff (𝟙 _) hR g).2
        fun x _ => hall x)
  · intro hX p
    obtain ⟨V, v, q, hq⟩ := X.exists_isPullback_yoneda_fieldValuedPoint p
    exact ⟨V, v, q, hq, Space.eq_of_mem_rankLocus_of_mem_rankLocus
      (X.mem_rankLocus_firstDirectImage_of_isPullback h p v q hq)
      (Space.mem_rankLocus_of_isFiniteLocallyFreeOfRank hX _)⟩

omit h in
variable (B hZ) in
/-- **The locus of points of the base whose fibre has genus `g`**: the classes of the field-valued
points over which the fibre is presented by a scheme of genus `g`. -/
def fibreGenusLocus (g : ℕ) : Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  {x | ∃ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    p.class B integerBase hZ _ = x ∧
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
        IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g}

include h in
/-- **The fibre genus locus of `g` is the rank locus of `g` of `R¹f_*𝒪_X`.** -/
theorem fibreGenusLocus_eq_rankLocus (g : ℕ) :
    fibreGenusLocus B hZ X g = Space.rankLocus (X.firstDirectImage B hZ) g := by
  ext x
  constructor
  · rintro ⟨p, rfl, V, v, q, hq, hg⟩
    exact hg ▸ X.mem_rankLocus_firstDirectImage_of_isPullback h p v q hq
  · intro hx
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨V, v, q, hq⟩ := X.exists_isPullback_yoneda_fieldValuedPoint p
    exact ⟨p, rfl, V, v, q, hq, Space.eq_of_mem_rankLocus_of_mem_rankLocus
      (X.mem_rankLocus_firstDirectImage_of_isPullback h p v q hq) hx⟩

include h in
/-- **The fibre genus loci are open and closed, pairwise disjoint, and cover the base.** -/
theorem isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ :
    (∀ g, IsClopen (fibreGenusLocus B hZ X g)) ∧
      Pairwise (fun g g' => Disjoint (fibreGenusLocus B hZ X g) (fibreGenusLocus B hZ X g')) ∧
        (⋃ g, fibreGenusLocus B hZ X g) = Set.univ := by
  have hR := X.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre h
  simp only [X.fibreGenusLocus_eq_rankLocus h]
  have hdisj : Pairwise (fun g g' => Disjoint (Space.rankLocus (X.firstDirectImage B hZ) g)
      (Space.rankLocus (X.firstDirectImage B hZ) g')) := fun g g' hne =>
    Set.disjoint_left.mpr fun s hs hs' => hne (Space.eq_of_mem_rankLocus_of_mem_rankLocus hs hs')
  have hcov : (⋃ g, Space.rankLocus (X.firstDirectImage B hZ) g) = Set.univ :=
    Set.eq_univ_of_forall fun s => Set.mem_iUnion.mpr (Space.exists_mem_rankLocus hR s)
  refine ⟨fun g => ⟨?_, Space.isOpen_rankLocus _ g⟩, hdisj, hcov⟩
  have hcompl : (Space.rankLocus (X.firstDirectImage B hZ) g)ᶜ =
      ⋃ g' ∈ {g' | g' ≠ g}, Space.rankLocus (X.firstDirectImage B hZ) g' := by
    ext s
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hs
      obtain ⟨g', hg'⟩ := Set.mem_iUnion.mp (hcov.symm ▸ Set.mem_univ s :
        s ∈ ⋃ g, Space.rankLocus (X.firstDirectImage B hZ) g)
      exact ⟨g', fun h' => hs (h' ▸ hg'), hg'⟩
    · rintro ⟨g', hne, hs'⟩ hs
      exact hne (Space.eq_of_mem_rankLocus_of_mem_rankLocus hs' hs)
  exact isOpen_compl_iff.mp (hcompl ▸ isOpen_biUnion fun g' _ => Space.isOpen_rankLocus _ g')

include h in
/-- **Every fibre has genus `g` exactly when the fibre genus locus of `g` is everything.** -/
theorem hasFieldPointFibreGenus_iff_fibreGenusLocus_eq_univ (g : ℕ) :
    HasFieldPointFibreGenus B hZ X g ↔ fibreGenusLocus B hZ X g = Set.univ := by
  constructor
  · intro hX
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    exact ⟨p, rfl, hX p⟩
  · intro hX p
    obtain ⟨V, v, q, hq⟩ := X.exists_isPullback_yoneda_fieldValuedPoint p
    have hx : p.class B integerBase hZ _ ∈ Space.rankLocus (X.firstDirectImage B hZ) g :=
      (X.fibreGenusLocus_eq_rankLocus h g) ▸ (hX.symm ▸ Set.mem_univ _)
    exact ⟨V, v, q, hq, Space.eq_of_mem_rankLocus_of_mem_rankLocus
      (X.mem_rankLocus_firstDirectImage_of_isPullback h p v q hq) hx⟩

include h in
/-- **The fibre genus loci are compatible with base change**: for a morphism of families `F ⟶ X`
the fibre genus locus of `g` of `F` is the inverse image of that of `X`, the family `X` having
`k = H⁰(X_k, 𝒪_{X_k})` on the fibres over fields. -/
theorem preimage_fibreGenusLocus {F : CurveFamily B hZ} (a : F ⟶ X)
    (hF : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj,
      Function.Bijective (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier))
        p.contained (Space.fibreOverFieldValuedPoint B integerBase hZ F.toBase.hom p))))
    (g : ℕ) :
    Space.pointsMap B integerBase hZ (schemeSpace F.base).obj (schemeSpaceMap a.baseMap).hom ⁻¹'
        fibreGenusLocus B hZ X g = fibreGenusLocus B hZ F g := by
  have hR := X.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre h
  obtain ⟨e⟩ := X.nonempty_modulePullback_firstDirectImage_iso_of_bijective_algebraMap_fibre h F a
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hR
  rw [X.fibreGenusLocus_eq_rankLocus h, F.fibreGenusLocus_eq_rankLocus hF,
    Space.preimage_rankLocus_modulePullback (schemeSpaceMap a.baseMap) hR inferInstance g,
    Space.rankLocus_congr e g]

end CurveFamily

variable (B hZ) in
/-- On stable families of curves, all fibres having genus `g` is the same as `R¹f_*𝒪_X` being a
locally free `𝒪_S`-module of rank `g`: the families of `𝓜̄_g` (Stacks 0E77) are those of part (1)
of Stacks 0E78. -/
theorem isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus (g : ℕ)
    (X : CurveFamily B hZ) :
    IsStableCurveFamilyOfFibreGenus B hZ g X ↔ IsStableCurveFamilyOfGenus B hZ g X :=
  ⟨fun h => ⟨h.1, (X.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions h.1.1.2)
      g).1 h.2⟩,
    fun h => ⟨h.1, (X.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions h.1.1.2)
      g).2 h.2⟩⟩

end AlgebraicGeometry

end
