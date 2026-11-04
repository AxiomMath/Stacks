module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointSectionReading
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Cube.SectionNeighbourhood
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport

/-!
# The open subspace where finitely many global sections generate a module

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `M` a quasi-coherent
`𝒪_X`-module and `s₀, …, sᵣ` global sections of `M`.  At a scheme point `t : h_T ⟶ X` the module
and its sections are read on `T` (`AlgebraicGeometry.Space.pointModule`,
`AlgebraicGeometry.Space.pointGlobalSection`).  This file shows that the scheme points at which the
read sections do not vanish simultaneously form an open subspace of `X`: the locus `X_s ⊆ X` of
the source (Stacks 0D2Y, read at the scheme points of `X`).

## Main definitions

* `AlgebraicGeometry.Space.IsGeneratedReading`: the read sections of `s` have no common zero on
  `T`.
* `AlgebraicGeometry.Space.sectionsGenerationSubfunctor`: the subfunctor of `X` of those scheme
  points.

## Main results

* `AlgebraicGeometry.Space.mem_nonvanishingLocus_pointGlobalSection_iff`: **the nonvanishing locus
  of a read section is compatible with base change**: a point of `T'` lies in it for the reading
  at `h ≫ t` exactly when its image in `T` lies in it for the reading at `t`.
* `AlgebraicGeometry.Space.isOpenSubspace_sectionsGenerationSubfunctor`: the subfunctor is an open
  subspace.
* `AlgebraicGeometry.Space.mem_sectionsGenerationSubfunctor_iff`: a scheme point lies in it exactly
  when the read sections have no common zero.

## References

* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)

/-- **The nonvanishing locus of a read global section is compatible with base change.** -/
theorem mem_nonvanishingLocus_pointGlobalSection_iff (hM : M.IsQuasicoherentOnSite)
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k')
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M)
    (x : (BigFppfOver.toScheme B S hS).obj T') :
    x ∈ Stacks.Ample.nonvanishingLocus (pointModule B S hS M T' k')
        (pointGlobalSection B S hS M T' k' σ) ↔
      (BigFppfOver.toScheme B S hS).map h x ∈ Stacks.Ample.nonvanishingLocus
        (pointModule B S hS M T k) (pointGlobalSection B S hS M T k σ) := by
  have := isIso_pointModuleComparison B S hS M hM h k k' e
  rw [← pointModuleComparison_pullbackGlobalSections B S hS M h k k' e σ,
    show (pointModuleComparison B S hS M h k k' e).val.app (op ⊤) =
      (asIso (pointModuleComparison B S hS M h k k' e)).hom.val.app (op ⊤) from rfl,
    AlgebraicGeometry.Cube.nonvanishingLocus_hom_app_top_of_iso,
    ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections]
  rfl

/-- **The reading of an invertible module at a scheme point is invertible.** -/
theorem isInvertibleModule_pointModule
    (hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property M)
    (T : BigFppfOver B S hS) (k : representedAlgebraicSpace B S hS T ⟶ X) :
    Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T)
      (pointModule B S hS M T k) := by
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T)
      (restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS T).1
        (representedAlgebraicSpace B S hS T).2 ((modulePullback B S hS k).obj M)
        (idEtaleChart B S hS T)) :=
    isInvertibleModule_baseChangeModule M hM T k.hom
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
    (restrictToChartSchemeIsoChartRestrictionSheaf B S hS (representedAlgebraicSpace B S hS T)
      ((modulePullback B S hS k).obj M) (idEtaleChart B S hS T))

variable {ι : Type*} (s : ι → (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M)

/-- The read sections of the family `s` along `k : h_T ⟶ X` have no common zero on `T`. -/
def IsGeneratedReading (T : BigFppfOver B S hS) (k : representedAlgebraicSpace B S hS T ⟶ X) :
    Prop :=
  ∀ x : (BigFppfOver.toScheme B S hS).obj T, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus
    (pointModule B S hS M T k) (pointGlobalSection B S hS M T k (s i))

/-- **Having no common zero is compatible with base change**: along `h ≫ k` it holds at a point
of `T'` exactly when it holds along `k` at its image. -/
theorem isGeneratedReading_comp_iff (hM : M.IsQuasicoherentOnSite) {T T' : BigFppfOver B S hS}
    (h : T' ⟶ T) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k') :
    IsGeneratedReading B S hS M s T' k' ↔
      ∀ x : (BigFppfOver.toScheme B S hS).obj T', ∃ i,
        (BigFppfOver.toScheme B S hS).map h x ∈ Stacks.Ample.nonvanishingLocus
          (pointModule B S hS M T k) (pointGlobalSection B S hS M T k (s i)) :=
  forall_congr' fun x => exists_congr fun i =>
    mem_nonvanishingLocus_pointGlobalSection_iff B S hS M hM h k k' e (s i) x

/-- The scheme point of `X` attached to a section of `X` over an object of the site. -/
abbrev sectionPoint {T : BigFppfOver B S hS} (x : X.1.obj (op T)) :
    representedAlgebraicSpace B S hS T ⟶ X :=
  ObjectProperty.homMk (yonedaEquiv.symm x)

/-- Precomposing the scheme point of a section `x` with `h : T' ⟶ T` gives the scheme point of the
restriction of `x` along `h`. -/
theorem representedMap_comp_sectionPoint {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (x : X.1.obj (op T)) :
    representedMap B S hS h ≫ sectionPoint B S hS x = sectionPoint B S hS (X.1.map h.op x) :=
  ObjectProperty.hom_ext _ (yonedaEquiv_symm_map h.op x).symm

/-- **The subfunctor of the scheme points of `X` at which the read sections of `s` have no common
zero.** -/
def sectionsGenerationSubfunctor (hM : M.IsQuasicoherentOnSite) : Subfunctor X.1 where
  obj T := {x | IsGeneratedReading B S hS M s T.unop (sectionPoint B S hS x)}
  map f x hx := (isGeneratedReading_comp_iff B S hS M s hM f.unop _ _
    (representedMap_comp_sectionPoint B S hS f.unop x)).2 fun _ => hx _

/-- A section `x` of `X` over `T` lies in the generation subfunctor exactly when the read sections
of `s` along its scheme point have no common zero on `T`. -/
theorem mem_sectionsGenerationSubfunctor_iff (hM : M.IsQuasicoherentOnSite)
    {T : BigFppfOver B S hS} (x : X.1.obj (op T)) :
    x ∈ (sectionsGenerationSubfunctor B S hS M s hM).obj (op T) ↔
      IsGeneratedReading B S hS M s T (sectionPoint B S hS x) :=
  Iff.rfl

variable (hinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property M)

include hinv in
/-- The union of the nonvanishing loci of the read sections along `k` is open. -/
theorem isOpen_iUnion_nonvanishingLocus_pointGlobalSection (T : BigFppfOver B S hS)
    (k : representedAlgebraicSpace B S hS T ⟶ X) :
    IsOpen (⋃ i, Stacks.Ample.nonvanishingLocus (pointModule B S hS M T k)
      (pointGlobalSection B S hS M T k (s i))) := by
  have := isInvertibleModule_pointModule B S hS M hinv T k
  exact isOpen_iUnion fun i => Stacks.NonvanishingOpen.isOpen_nonvanishingLocus _ _ _

/-- **The preimage of the generation subfunctor along a scheme point is the open subscheme where
the read sections have no common zero.** -/
theorem range_yoneda_map_eq_preimage_sectionsGenerationSubfunctor (hM : M.IsQuasicoherentOnSite)
    {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) {b : BigFppfOver B S hS} (i : b ⟶ A)
    (hirange : Set.range ((BigFppfOver.toScheme B S hS).map i) =
      ⋃ j, Stacks.Ample.nonvanishingLocus
        (pointModule B S hS M A (ObjectProperty.homMk q))
        (pointGlobalSection B S hS M A (ObjectProperty.homMk q) (s j)))
    (hiuniv : ∀ {A' : BigFppfOver B S hS} (g : A' ⟶ A),
      Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
        (⋃ j, Stacks.Ample.nonvanishingLocus
          (pointModule B S hS M A (ObjectProperty.homMk q))
          (pointGlobalSection B S hS M A (ObjectProperty.homMk q) (s j))) →
          ∃ h : A' ⟶ b, h ≫ i = g) :
    Subfunctor.range (yoneda.map i) =
      (sectionsGenerationSubfunctor B S hS M s hM).preimage q := by
  ext Y f
  have hmem : ∀ g : Y.unop ⟶ A,
      (q.app Y g ∈ (sectionsGenerationSubfunctor B S hS M s hM).obj Y ↔
        Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
          ⋃ j, Stacks.Ample.nonvanishingLocus
            (pointModule B S hS M A (ObjectProperty.homMk q))
            (pointGlobalSection B S hS M A (ObjectProperty.homMk q) (s j))) := by
    intro g
    have e : representedMap B S hS g ≫ (ObjectProperty.homMk q :
        representedAlgebraicSpace B S hS A ⟶ X) = sectionPoint B S hS (q.app Y g) := by
      refine ObjectProperty.hom_ext _ ?_
      show yoneda.map g ≫ q = yonedaEquiv.symm (q.app Y g)
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    show IsGeneratedReading B S hS M s Y.unop (sectionPoint B S hS (q.app Y g)) ↔ _
    rw [isGeneratedReading_comp_iff B S hS M s hM g _ _ e]
    simp only [Set.range_subset_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨g, rfl⟩
    refine (hmem _).2 ?_
    rintro z ⟨y, rfl⟩
    refine hirange ▸ ⟨(BigFppfOver.toScheme B S hS).map g y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    rfl
  · exact fun hf => hiuniv f ((hmem f).1 hf)

include hinv in
/-- The inclusion of the generation subfunctor is an open immersion. -/
theorem isOpenImmersion_ι_sectionsGenerationSubfunctor (hM : M.IsQuasicoherentOnSite) :
    IsOpenImmersion B S hS (sectionsGenerationSubfunctor B S hS M s hM).ι := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists fun A q => ?_
  obtain ⟨b, i, hi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver A
    ⟨_, isOpen_iUnion_nonvanishingLocus_pointGlobalSection B S hS M s hinv A
      (ObjectProperty.homMk q)⟩
  have hkey := range_yoneda_map_eq_preimage_sectionsGenerationSubfunctor B S hS M s hM q i
    hirange hiuniv
  have hmono : Mono i := inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hsq := Subfunctor.isPullback_fromPreimage (sectionsGenerationSubfunctor B S hS M s hM) q
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  refine ⟨b, Subfunctor.lift (yoneda.map i) hkey.le ≫
    (sectionsGenerationSubfunctor B S hS M s hM).fromPreimage q, i, ?_, hi⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, (sectionsGenerationSubfunctor B S hS M s hM).fromPreimage_ι q,
      ← Category.assoc, Subfunctor.lift_ι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) hkey.le) ≪≫ hsq.isoPullback) ?_ ?_
  · simp [hsq.isoPullback_hom_fst]
  · simp [hsq.isoPullback_hom_snd]

/-- The generation subfunctor is a sheaf: having no common zero is local on the source, a covering
sieve being jointly surjective on points. -/
theorem isSheaf_sectionsGenerationSubfunctor (hM : M.IsQuasicoherentOnSite) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (sectionsGenerationSubfunctor B S hS M s hM).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 X.2.isSheaf)]
  intro Y x hx z
  obtain ⟨A', h, hh, z', rfl⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hx z
  exact (isGeneratedReading_comp_iff B S hS M s hM h _ _
    (representedMap_comp_sectionPoint B S hS h x)).1 hh z'

include hinv in
/-- **The generation subfunctor is an open subspace.** -/
theorem isOpenSubspace_sectionsGenerationSubfunctor (hM : M.IsQuasicoherentOnSite) :
    IsOpenSubspace B S hS (sectionsGenerationSubfunctor B S hS M s hM) :=
  have hι := isOpenImmersion_ι_sectionsGenerationSubfunctor B S hS M s hinv hM
  ⟨IsAlgebraicSpace.of_relativelyRepresentable
    (isSheaf_sectionsGenerationSubfunctor B S hS M s hM) X.2 hι.rep, hι⟩

end AlgebraicGeometry.Space

end
