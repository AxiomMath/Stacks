module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.GeneratingLocusRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective

/-!
# The generating subspace of a section of an invertible module is affine over the space

Let `X` be an algebraic space, `𝓜` an invertible `𝒪_X`-module and `s` a global section of `𝓜`.
The inclusion `j : U_s ⟶ X` of the open subspace over which `s` generates `𝓜`
(`AlgebraicGeometry.Space.generatingSubspace`) is an affine morphism.  This is the first step of
the claim in the proof of Stacks 0D2W: "étale locally the morphism `j` is affine (by Morphisms,
Lemma 29.11.11), hence `j` is affine (Morphisms of Spaces, Lemma 67.20.3)".

Affineness is tested on affine étale charts `V ⟶ X` (Stacks 03WG): over such a chart the base
change of the inclusion of the open subspace cut out by an open set `W ⊆ |X|` is represented by
the open subscheme of `V` cut out by the preimage of `W`, which has to be affine
(`AlgebraicGeometry.Space.isAffineHom_ι_openSubspaceOfPoints`).  For the generating locus this
preimage is the generating locus of the pulled back section
(`AlgebraicGeometry.Space.sectionGeneratingLocus_modulePullback`), which on the scheme `V` is the
nonvanishing locus `V_{s_V}` of the restricted section
(`AlgebraicGeometry.Space.mem_sectionGeneratingLocus_iff_mem_nonvanishingLocus`); it is affine by
Stacks 01PV.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_ι_openSubspaceOfPoints`: the open subspace cut out by an
  open set of points is affine over the space as soon as its preimage in every affine étale chart
  is an affine open.
* `AlgebraicGeometry.Space.sectionGeneratingLocus_modulePullback`: the generating locus pulls back
  along étale morphisms.
* `AlgebraicGeometry.Space.isAffineHom_ι_generatingSubspace`: the inclusion of the generating
  subspace of a section of an invertible module is affine.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **An open subspace whose preimages in affine étale charts are affine opens is affine over the
space.**  Let `W` be an open set of points of `X`.  If for every étale morphism `g` from an affine
object `V` of the site the points of `V` mapping into `W` form an affine open of `V`, then the
inclusion of the open subspace cut out by `W` is an affine morphism (Stacks 03WG). -/
theorem isAffineHom_ι_openSubspaceOfPoints (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W)
    (h : ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ X.1), IsEtale B S hS g →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        ∃ O : ((BigFppfOver.toScheme B S hS).obj V).Opens, IsAffineOpen O ∧
          ∀ t, t ∈ O ↔
            pointsMap B S hS (yoneda.obj V) g ((pointsEquivScheme B S hS V).symm t) ∈ W) :
    IsAffineHom B S hS (openSubspaceOfPoints B S hS X.1 W).ι := by
  have hsrc : IsAlgebraicSpace B S hS (openSubspaceOfPoints B S hS X.1 W).toFunctor :=
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2 W hW).1
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (openSubspaceOfPoints B S hS X.1 W).ι
    hsrc X.2).out 3 2).mp ?_
  intro V g hg
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  obtain ⟨O, haff, hO⟩ := h _ g hg hVaff
  -- The open subscheme of `V` cut out by `O`, as an object of the site.
  obtain ⟨b, i, hiopen, hirange, hiuniv⟩ := exists_restrict_bigFppfOver
    ((BigAffineFppf.inclusion B S hS).obj V) O
  have _ := hiopen
  have _ : IsAffine O.toScheme := haff
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj b) :=
    IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq
      ((BigFppfOver.toScheme B S hS).map i) O.ι
      (hirange.trans (Scheme.Opens.range_ι _).symm)).hom
  -- The range of the inclusion is the base change of the open subspace.
  have hrange : Subfunctor.range (yoneda.map i) =
      (openSubspaceOfPoints B S hS X.1 W).preimage g := by
    refine range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS _ g i
      (O : Set _) hirange (fun {A'} h hh => hiuniv h hh) fun p => ?_
    refine Iff.trans ?_ (SetLike.mem_coe.trans (hO _)).symm
    rw [← pointsToScheme_class B S hS _ p]
    exact Iff.of_eq (congrArg (fun x => pointsMap B S hS _ g x ∈ W)
      ((pointsEquivScheme B S hS _).symm_apply_apply _).symm)
  -- The square is cartesian, so the base change is represented by the affine object `b`.
  have hmono : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map i)))
  have h2 : ∀ {T} (t : T ⟶ (BigAffineFppf.inclusion B S hS).obj V),
      X.1.map t.op (yonedaEquiv g) = g.app (op T) t := fun t => by
    rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have hmem : X.1.map i.op (yonedaEquiv g) ∈ (openSubspaceOfPoints B S hS X.1 W).obj (op b) := by
    have h1 : i ∈ (Subfunctor.range (yoneda.map i)).obj (op b) := ⟨𝟙 b, by simp⟩
    rw [hrange] at h1
    rw [h2]
    exact h1
  refine ⟨⟨b, ‹IsAffine ((BigFppfOver.toScheme B S hS).obj b)›⟩,
    yonedaEquiv.symm (⟨_, hmem⟩ : (openSubspaceOfPoints B S hS X.1 W).toFunctor.obj (op b)), i,
    ?_⟩
  have hsq := Subfunctor.isPullback_yoneda_of_forall_exists
    (openSubspaceOfPoints B S hS X.1 W) i (yonedaEquiv g) (⟨_, hmem⟩) rfl
    (fun T t ht => by
      change t ∈ (Subfunctor.range (yoneda.map i)).obj (op T)
      rw [hrange]
      rwa [h2] at ht)
  simpa using hsq

section Pullback

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] smallEtaleModulesAbelian

/-- **The generating locus pulls back along étale morphisms**: for an étale `g : Y ⟶ X`, the
generating locus of the pulled back section `g^* s` of `g^* 𝓜` is the preimage of the generating
locus of `s`.  The pullback is a left adjoint, so it carries the cokernel of `𝒪_X ⟶ 𝓜` to the
cokernel of `𝒪_Y ⟶ g^* 𝓜`, and supports pull back along étale morphisms (Stacks 04KA). -/
theorem sectionGeneratingLocus_modulePullback {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS X.1 X.2) (s : M.sections) :
    sectionGeneratingLocus B S hS ((modulePullback B S hS g).obj M)
        (modulePullbackSections B S hS g M s) =
      pointsMap B S hS Y.1 g.hom ⁻¹' sectionGeneratingLocus B S hS M s := by
  set φ := M.unitHomEquiv.symm s with hφ
  have hadd : (modulePullback B S hS g).Additive :=
    (modulePullbackAdjunction B S hS g).left_adjoint_additive
  have hpres : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS g) :=
    (modulePullbackAdjunction B S hS g).leftAdjoint_preservesColimits
  have hφ' : ((modulePullback B S hS g).obj M).unitHomEquiv.symm
      (modulePullbackSections B S hS g M s) =
      (modulePullbackUnitIso B S hS g).inv ≫ (modulePullback B S hS g).map φ :=
    Equiv.symm_apply_apply _ _
  have hepi : Epi (modulePullbackUnitIso B S hS g).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  let I : cokernel (C := Modules.{u, u} B S hS Y.1 Y.2)
      (((modulePullback B S hS g).obj M).unitHomEquiv.symm
        (modulePullbackSections B S hS g M s)) ≅
      (modulePullback B S hS g).obj (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ) :=
    cokernelIsoOfEq (C := Modules.{u, u} B S hS Y.1 Y.2) hφ' ≪≫
      @cokernelEpiComp (Modules.{u, u} B S hS Y.1 Y.2) _ _ _ _ _ _ _ hepi _ ≪≫
      (PreservesCokernel.iso (modulePullback B S hS g) φ).symm
  ext y
  rw [Set.mem_preimage, mem_sectionGeneratingLocus_iff, mem_sectionGeneratingLocus_iff,
    supportOfSheaf_eq_of_iso B S hS Y I, supportOfSheaf_modulePullback_of_isEtale B S hS g hg,
    Set.mem_preimage]

/-- **The inclusion of the generating subspace of a section of an invertible module is an affine
morphism.**  On an affine étale chart `V` the preimage of the generating locus is the nonvanishing
locus of the restricted section, which is affine by Stacks 01PV. -/
theorem isAffineHom_ι_generatingSubspace (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsInvertibleModule X M)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M) (s : M.sections) :
    IsAffineHom B S hS (generatingSubspace B S hS X.2 M s).ι := by
  refine isAffineHom_ι_openSubspaceOfPoints B S hS X _
    (isOpen_sectionGeneratingLocus B S hS M s hMft) ?_
  intro V g hg hVaff
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let g' : Y ⟶ X := ObjectProperty.homMk g
  let M' := (modulePullback B S hS g').obj M
  have hM' : IsInvertibleModule Y M' :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertible_modulePullback_obj B S hS g' M
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M hM))
  let s' := modulePullbackSections B S hS g' M s
  let T := (BigFppfOver.toScheme B S hS).obj V
  have : Stacks.Ample.IsInvertibleModule T (idChartRestriction B S hS V M') :=
    isInvertible_idChartRestriction B S hS V M' hM'
  refine ⟨⊤ ⊓ Stacks.NonvanishingOpen.nonvanishingOpen T (idChartRestriction B S hS V M')
      (Stacks.NonvanishingSpelling.sectionsEquiv T _ (idChartSection B S hS V M' s')),
    Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen _ _
      (isAffineOpen_top T), fun t => ?_⟩
  have hK := mem_sectionGeneratingLocus_iff_mem_nonvanishingLocus B S hS V M' hM' s' t
  have hP := congrArg (fun A => (pointsEquivScheme B S hS V).symm t ∈ A)
    (sectionGeneratingLocus_modulePullback B S hS g' hg M s)
  have hN := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq T
    (idChartRestriction B S hS V M') (idChartSection B S hS V M' s')
  refine (and_iff_right (Set.mem_univ t)).trans ?_
  refine (Iff.of_eq (congrArg (t ∈ ·) hN.symm)).trans (hK.symm.trans (Iff.of_eq hP))

end Pullback

end AlgebraicGeometry.Space

end
