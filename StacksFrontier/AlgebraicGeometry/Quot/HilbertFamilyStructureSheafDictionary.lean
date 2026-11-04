module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFinitePresentationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealChartFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The dictionary of Stacks 0D00 between a closed subspace and its structure-sheaf quotient

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `g : X ⟶ T` be a
morphism to another algebraic space, and let `Z ⊆ X` be a closed subspace with inclusion
`i : Z ⟶ X`. Stacks 0D00 identifies the Hilbert functor of a morphism with the Quot functor of
its structure sheaf, by translating the conditions the Hilbert functor imposes on `Z ⟶ T` into
the conditions the Quot functor imposes on the quotient `𝒪_X ⟶ i_*𝒪_Z`. This file proves the
proper-support and flatness entries of that dictionary, in both directions, the computation
`Supp(i_*𝒪_Z) = |i|(|Z|)`, and the converse construction of a Hilbert family from a quotient.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardStructureSheafIsoChartDirectImage`: the direct image
  `i_*𝒪_Z` of Stacks 03LU is isomorphic to the direct image along base change of étale charts.
* `AlgebraicGeometry.Space.hilbertFamilyOfQuotConditions`: a closed subspace of `X_T` whose
  structure-sheaf quotient is of finite presentation, flat over `T` and has support proper over
  `T` is a family classified by the Hilbert functor.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_pushforwardStructureSheaf`:
  `Supp(i_*𝒪_Z) = |i|(|Z|)` for a closed subspace `Z` of an algebraic space.
* `AlgebraicGeometry.Space.hasProperSupport_pushforwardStructureSheaf_iff`: `i_*𝒪_Z` has support
  proper over `T` in the sense of Stacks 0CZD exactly when `Z ⟶ T` is proper.
* `AlgebraicGeometry.Space.isFlatOver_pushforwardStructureSheaf_iff`: `i_*𝒪_Z` is flat over `T`
  in the sense of Stacks 05VV exactly when `Z ⟶ T` is a flat morphism.
* `AlgebraicGeometry.Space.exists_hilbertFamily_definingIdealSheaf_eq_of_quotConditions`: a
  sheaf of ideals of `𝒪_{X_T}` whose quotient is of finite presentation, flat over `T` and with
  support proper over `T` is the defining ideal sheaf of a family classified by the Hilbert
  functor.
* `AlgebraicGeometry.Space.definingIdealSheaf_hilbertFamily_injective`: distinct families
  classified by the Hilbert functor have distinct defining ideal sheaves.

## References

* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0CZB](https://stacks.math.columbia.edu/tag/0CZB)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two spellings of the direct image of the structure sheaf -/

section Comparison

variable (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The direct image `i_*𝒪_Z` of Stacks 03LU along the inclusion of a closed subspace is the
direct image along base change of étale scheme charts. -/
def pushforwardStructureSheafIsoChartDirectImage :
    pushforwardStructureSheaf B S hS X Z ≅
      chartDirectImage.{u, u} B S hS (subspaceInclusion B S hS X Z) Z.2.2
        (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩) :=
  modulePushforwardIsoChartDirectImage B S hS (subspaceInclusion B S hS X Z) Z.2.2 _

/-- The direct image of the structure sheaf of a closed subspace, in its chart spelling, is
quasi-coherent. -/
instance isQuasicoherentOnSite_chartDirectImage_structureSheafModule :
    (chartDirectImage.{u, u} B S hS (subspaceInclusion B S hS X Z) Z.2.2
      (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (pushforwardStructureSheafIsoChartDirectImage B S hS X Z)
    (isQuasicoherentOnSite_pushforwardStructureSheaf B S hS X Z)

/-! ### The support of the direct image of the structure sheaf -/

/-- **The support of `i_*𝒪_Z` is the point set of `Z`**, in the chart spelling of the direct
image.  For a closed subspace `Z` of an algebraic space `X` with inclusion `i`,

`Supp(i_*𝒪_Z) = |i|(|Z|)`. -/
theorem supportOfSheaf_chartDirectImage_structureSheafModule :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (chartDirectImage.{u, u} B S hS (subspaceInclusion B S hS X Z) Z.2.2
          (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩))) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact supportOfSheaf_smallEtaleAbelianPushforward_subset B S hS
      (subspaceInclusion B S hS X Z) Z.2.2
      ((SheafOfModules.toSheaf _).obj (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩))
  · exact range_subset_supportOfSheaf_chartDirectImage_structureSheafModule B S hS
      (subspaceInclusion B S hS X Z) Z.2.2

/-- **The support of `i_*𝒪_Z` is the point set of `Z`**, for the direct image of Stacks 03LU:
`Supp(i_*𝒪_Z) = |i|(|Z|)`. -/
theorem supportOfSheaf_pushforwardStructureSheaf :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (pushforwardStructureSheaf B S hS X Z)) =
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  rw [supportOfSheaf_eq_of_iso B S hS X (pushforwardStructureSheafIsoChartDirectImage B S hS X Z)]
  exact supportOfSheaf_chartDirectImage_structureSheafModule B S hS X Z

/-- The support of `i_*𝒪_Z` is closed, being the point set of a closed subspace. -/
theorem isClosed_supportOfSheaf_pushforwardStructureSheaf :
    IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
      (pushforwardStructureSheaf B S hS X Z))) := by
  rw [supportOfSheaf_pushforwardStructureSheaf B S hS X Z]
  exact isClosed_range_pointsMap_of_isClosedImmersion B S hS X.property Z.1.ι Z.2.2

end Comparison

/-! ### The proper-support entry of the dictionary -/

section Properness

variable {X T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The proper-support entry of the dictionary of Stacks 0D00, in both directions.**  Let
`g : X ⟶ T` be locally of finite type and let `Z ⊆ X` be a closed subspace with inclusion `i`.
The module `i_*𝒪_Z` has support proper over `T` in the sense of Stacks 0CZD exactly when the
composite `Z ⟶ T` is proper. -/
@[stacks 0D00 "the proper-support entry of the dictionary, both directions"]
theorem hasProperSupport_pushforwardStructureSheaf_iff (g : X ⟶ T)
    (hg : IsLocallyOfFiniteType B S hS g.hom) :
    HasProperSupport B S hS X.property T.property g.hom hg
        ((SheafOfModules.toSheaf _).obj (pushforwardStructureSheaf B S hS X Z)) ↔
      IsProper B S hS (Z.1.ι ≫ g.hom) := by
  have hsupp := supportOfSheaf_pushforwardStructureSheaf B S hS X Z
  have hcl := isClosed_supportOfSheaf_pushforwardStructureSheaf B S hS X Z
  refine ⟨fun ⟨_, hproper⟩ => ?_, fun hZ => ⟨hcl, (isProper_reducedClosedSubspace_iff_exists B S
    hS X.property T.property g.hom hg _ hcl).2 ⟨Z.1, Z.2, hsupp.symm, hZ⟩⟩⟩
  obtain ⟨W, hW, hWrange, hWproper⟩ :=
    (isProper_reducedClosedSubspace_iff_exists B S hS X.property T.property g.hom hg _ hcl).1
      hproper
  exact isProper_ι_comp_of_isProper_ι_comp B S hS X.property T.property g.hom hg _ hcl
    W hW hWrange hWproper Z.1 Z.2 hsupp.symm

/-- Proper support of a module isomorphic to `i_*𝒪_Z` transfers to `i_*𝒪_Z`. -/
private theorem hasProperSupport_pushforwardStructureSheaf_of_iso {X T : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (g : X ⟶ T) (hg : IsLocallyOfFiniteType B S hS g.hom)
    {M : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ pushforwardStructureSheaf B S hS X Z)
    (h : HasProperSupport B S hS X.property T.property g.hom hg
      ((SheafOfModules.toSheaf _).obj M)) :
    HasProperSupport B S hS X.property T.property g.hom hg
      ((SheafOfModules.toSheaf _).obj (pushforwardStructureSheaf B S hS X Z)) :=
  hasProperSupport_of_subset B S hS X.property T.property _ _
    (isClosed_supportOfSheaf_pushforwardStructureSheaf B S hS X Z)
    (le_of_eq (supportOfSheaf_eq_of_iso B S hS X e).symm) h

end Properness

/-! ### The flatness entry of the dictionary -/

section Flatness

variable {X T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **Flatness of `i_*𝒪_Z` over `T` gives flatness of `Z ⟶ T`**: if the direct image `i_*𝒪_Z`
of the structure sheaf of a closed subspace `Z ⊆ X` is flat over `T`, then the composite
`Z ⟶ T` is flat. This is the converse direction of the flatness entry of the dictionary of
Stacks 0D00. -/
theorem isFlat_of_isFlatOver_pushforwardStructureSheaf (g : X ⟶ T)
    (h : IsFlatOver B S hS X.property g.hom (pushforwardStructureSheaf B S hS X Z)) :
    IsFlat B S hS (Z.1.ι ≫ g.hom) :=
  isFlat_comp_of_isFlatOver_chartDirectImage B S hS (subspaceInclusion B S hS X Z) Z.2.2 g
    (IsFlatOver.of_iso B S hS X.property
      (pushforwardStructureSheafIsoChartDirectImage B S hS X Z) h)

/-- **Flatness of `Z ⟶ T` gives flatness of `i_*𝒪_Z` over `T`**, in the chart spelling of the
direct image: if the composite `Z ⟶ T` is flat, then the direct image along base change of
étale charts of the structure sheaf of `Z` is flat over `T`. This is the forward direction of
the flatness entry of the dictionary of Stacks 0D00. -/
theorem isFlatOver_chartDirectImage_structureSheafModule_of_isFlat (g : X ⟶ T)
    (hZ : IsFlat B S hS (Z.1.ι ≫ g.hom)) :
    IsFlatOver B S hS X.property g.hom
      (chartDirectImage.{u, u} B S hS (subspaceInclusion B S hS X Z) Z.2.2
        (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩)) := by
  intro d u
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS d.U.obj.left u
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X.1
    (pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom
      (p.class B S hS (yoneda.obj d.U.obj.left)))
  obtain ⟨q, hq, hu⟩ := exists_chartLift_of_chartPoint B S hS X.2 xbar d.U u ⟨p, hp, hxbar.symm⟩
  subst hu
  refine (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS g _
    ⟨d.U, q, hq⟩ d.V d.g d.comm).2 ?_
  by_cases hmem : xbar.image ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)
  · obtain ⟨zbar, hz⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS
      (subspaceInclusion B S hS X Z) Z.2.2 xbar hmem
    rw [← hz]
    exact (isFlat_comp_iff_isFlatOverAtGeometricPoint_chartDirectImage B S hS
      (subspaceInclusion B S hS X Z) Z.2.2 g).1 hZ zbar
  · refine isFlatOverAtGeometricPoint_of_subsingleton_geometricModuleStalk B S hS g _ xbar ?_
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    refine hmem ?_
    rw [← supportOfSheaf_chartDirectImage_structureSheafModule B S hS X Z]
    exact (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X _ xbar.image).2
      ⟨xbar, rfl, hnt⟩

/-- **Flatness of `Z ⟶ T` gives flatness of `i_*𝒪_Z` over `T`**, for the direct image of
Stacks 03LU. -/
theorem isFlatOver_pushforwardStructureSheaf_of_isFlat (g : X ⟶ T)
    (hZ : IsFlat B S hS (Z.1.ι ≫ g.hom)) :
    IsFlatOver B S hS X.property g.hom (pushforwardStructureSheaf B S hS X Z) :=
  IsFlatOver.of_iso B S hS X.property
    (pushforwardStructureSheafIsoChartDirectImage B S hS X Z).symm
    (isFlatOver_chartDirectImage_structureSheafModule_of_isFlat B S hS Z g hZ)

/-- **The flatness entry of the dictionary of Stacks 0D00, in both directions.**  For a closed
subspace `Z ⊆ X` with inclusion `i` and a morphism `g : X ⟶ T`, the module `i_*𝒪_Z` is flat over
`T` in the sense of Stacks 05VV exactly when the composite `Z ⟶ T` is a flat morphism. -/
theorem isFlatOver_pushforwardStructureSheaf_iff (g : X ⟶ T) :
    IsFlatOver B S hS X.property g.hom (pushforwardStructureSheaf B S hS X Z) ↔
      IsFlat B S hS (Z.1.ι ≫ g.hom) :=
  ⟨isFlat_of_isFlatOver_pushforwardStructureSheaf B S hS Z g,
    isFlatOver_pushforwardStructureSheaf_of_isFlat B S hS Z g⟩

end Flatness

/-! ### The converse construction of Stacks 0D00 -/

section Converse

variable {X Y : AlgebraicSpaces B S hS}

/-- The projection `X_T ⟶ T` of the base change to a scheme over `Y`, as a morphism of algebraic
spaces. -/
abbrev schemeBaseChangeProjectionHom (f : X ⟶ Y) (T : SchemesOverPresheaf B S hS Y) :
    schemeBaseChangeSpace f T ⟶ schemeOverSpace T :=
  ObjectProperty.homMk (pullback.snd f.hom T.hom)

/-- **Stacks 0D00, the converse construction.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces of finite presentation, let `T` be a scheme of the site over `Y`, and let `W` be a closed
subspace of the base change `X_T` with inclusion `i`.  If the quotient `𝒪_{X_T} ⟶ i_*𝒪_W` it
determines is flat over `T` and has support proper over `T`, and if the defining ideal sheaf of
`W` is of finite type and `hchart` relates finite type of its kernel ideal sheaf to finite
generation of the kernel ideals on étale surjective charts, then `W` is a family classified by
the Hilbert functor of `f` over `T`. -/
def hilbertFamilyOfClosedSubspace (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (T : SchemesOverPresheaf B S hS Y)
    (W : ClosedSubspaces B S hS (schemeBaseChange f T))
    (hft : SheafOfModules.IsFiniteTypeOnSite
      (definingIdealSheaf B S hS (schemeBaseChangeSpace f T) W).toSheafOfModules)
    (hchart : ∀ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ schemeBaseChange f T),
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS
            (subspaceInclusion B S hS (schemeBaseChangeSpace f T) W)).toSheafOfModules ↔
        ∀ A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
          (((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd b)).ker.ideal A).FG))
    (hflat : IsFlatOver B S hS (schemeBaseChangeSpace f T).property
      (schemeBaseChangeProjectionHom B S hS f T).hom
      (pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T) W))
    (hproper : HasProperSupport B S hS (schemeBaseChangeSpace f T).property
      (schemeOverSpace T).property (schemeBaseChangeProjectionHom B S hS f T).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isFinitePresentation_schemeBaseChangeProjection f hf T).1)
      ((SheafOfModules.toSheaf _).obj
        (pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T) W))) :
    HilbertFamily f T :=
  have hi : IsFinitePresentation B S hS
      (subspaceInclusion B S hS (schemeBaseChangeSpace f T) W).hom :=
    (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart B S hS
        (subspaceInclusion B S hS (schemeBaseChangeSpace f T) W) W.2.2 hchart).2
      (by
        rw [kernelIdealSheaf_eq_definingIdealSheaf B S hS (schemeBaseChangeSpace f T) W]
        exact hft)
  have hfp : IsFinitePresentation B S hS (W.1.ι ≫ pullback.snd f.hom T.hom) :=
    (isFinitePresentation_comp_iff_of_isClosedImmersion B S hS W.2.1
        (schemeBaseChangeSpace f T).property (schemeOverSpace T).property W.1.ι
        (pullback.snd f.hom T.hom) W.2.2
        (isFinitePresentation_schemeBaseChangeProjection f hf T)).2 hi
  have hfl : IsFlat B S hS
      (W.1.ι ≫ (schemeBaseChangeProjectionHom B S hS f T).hom) :=
    isFlat_of_isFlatOver_pushforwardStructureSheaf B S hS
      (X := schemeBaseChangeSpace f T) (T := schemeOverSpace T) W
      (schemeBaseChangeProjectionHom B S hS f T) hflat
  have hpr : IsProper B S hS
      (W.1.ι ≫ (schemeBaseChangeProjectionHom B S hS f T).hom) :=
    (hasProperSupport_pushforwardStructureSheaf_iff B S hS
      (X := schemeBaseChangeSpace f T) (T := schemeOverSpace T) W
      (schemeBaseChangeProjectionHom B S hS f T) _).1 hproper
  ⟨W.1, W.2, hfp, hfl, hpr⟩

/-- **Stacks 0D00, the converse construction from the sheaf of ideals.**  A quasi-coherent sheaf
of ideals `𝓘 ⊆ 𝒪_{X_T}` whose quotient `𝒪_{X_T}/𝓘` is of finite presentation, flat over `T` and
with support proper over `T` is the defining ideal sheaf of a family classified by the Hilbert
functor of `f` over `T`, given the hypotheses `hft` and `hchart` of
`AlgebraicGeometry.Space.hilbertFamilyOfClosedSubspace` for every closed subspace of `X_T`. -/
theorem exists_hilbertFamily_definingIdealSheaf_eq (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y)
    (I : (SheafOfModules.unit
      (structureRingSheaf B S hS (schemeBaseChangeSpace f T))).Submodule)
    (hqc : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hft : ∀ W : ClosedSubspaces B S hS (schemeBaseChange f T),
      SheafOfModules.IsFiniteTypeOnSite
        (definingIdealSheaf B S hS (schemeBaseChangeSpace f T) W).toSheafOfModules)
    (hchart : ∀ (W : ClosedSubspaces B S hS (schemeBaseChange f T))
      (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ schemeBaseChange f T),
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS
            (subspaceInclusion B S hS (schemeBaseChangeSpace f T) W)).toSheafOfModules ↔
        ∀ A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
          (((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd b)).ker.ideal A).FG))
    (hflat : IsFlatOver B S hS (schemeBaseChangeSpace f T).property
      (schemeBaseChangeProjectionHom B S hS f T).hom
      (cokernel I.ι : Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
        (schemeBaseChangeSpace f T).2))
    (hproper : HasProperSupport B S hS (schemeBaseChangeSpace f T).property
      (schemeOverSpace T).property (schemeBaseChangeProjectionHom B S hS f T).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isFinitePresentation_schemeBaseChangeProjection f hf T).1)
      ((SheafOfModules.toSheaf _).obj (cokernel I.ι :
        Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
          (schemeBaseChangeSpace f T).2))) :
    ∃ z : HilbertFamily f T,
      definingIdealSheaf B S hS (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩ = I := by
  obtain ⟨W, hW⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS
    (schemeBaseChangeSpace f T) I hqc
  subst hW
  refine ⟨hilbertFamilyOfClosedSubspace B S hS f hf T W (hft W) (hchart W) ?_ ?_, rfl⟩
  · exact IsFlatOver.of_iso B S hS (schemeBaseChangeSpace f T).property
      (conormalAlgebraDegreeZeroIso B S hS (schemeBaseChangeSpace f T) W) hflat
  · exact hasProperSupport_pushforwardStructureSheaf_of_iso B S hS W _ _
      (conormalAlgebraDegreeZeroIso B S hS (schemeBaseChangeSpace f T) W) hproper

/-- **Stacks 0D00, the converse construction.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces of finite presentation, let `T` be a scheme of the site over `Y`, and let `W` be a closed
subspace of the base change `X_T` with inclusion `i`.  If the quotient `𝒪_{X_T} ⟶ i_*𝒪_W` it
determines is of finite presentation, is flat over `T` and has support proper over `T`, then `W`
is a family classified by the Hilbert functor of `f` over `T`. -/
@[stacks 0D00 "the converse construction: a quotient of the structure sheaf is a Hilbert family"]
def hilbertFamilyOfQuotConditions (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (T : SchemesOverPresheaf B S hS Y)
    (W : ClosedSubspaces B S hS (schemeBaseChange f T))
    (hfpq : (pushforwardStructureSheaf B S hS
      (schemeBaseChangeSpace f T) W).IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (schemeBaseChangeSpace f T).property
      (schemeBaseChangeProjectionHom B S hS f T).hom
      (pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T) W))
    (hproper : HasProperSupport B S hS (schemeBaseChangeSpace f T).property
      (schemeOverSpace T).property (schemeBaseChangeProjectionHom B S hS f T).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isFinitePresentation_schemeBaseChangeProjection f hf T).1)
      ((SheafOfModules.toSheaf _).obj
        (pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T) W))) :
    HilbertFamily f T :=
  have hi : IsFinitePresentation B S hS
      (subspaceInclusion B S hS (schemeBaseChangeSpace f T) W).hom :=
    (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
        (subspaceInclusion B S hS (schemeBaseChangeSpace f T) W) W.2.2).2
      (by
        rw [kernelIdealSheaf_eq_definingIdealSheaf B S hS (schemeBaseChangeSpace f T) W]
        exact isFiniteTypeOnSite_definingIdealSheaf_of_isFinitePresentationOnSite B S hS
          (schemeBaseChangeSpace f T) W hfpq)
  have hfp : IsFinitePresentation B S hS (W.1.ι ≫ pullback.snd f.hom T.hom) :=
    (isFinitePresentation_comp_iff_of_isClosedImmersion B S hS W.2.1
        (schemeBaseChangeSpace f T).property (schemeOverSpace T).property W.1.ι
        (pullback.snd f.hom T.hom) W.2.2
        (isFinitePresentation_schemeBaseChangeProjection f hf T)).2 hi
  have hfl : IsFlat B S hS
      (W.1.ι ≫ (schemeBaseChangeProjectionHom B S hS f T).hom) :=
    isFlat_of_isFlatOver_pushforwardStructureSheaf B S hS
      (X := schemeBaseChangeSpace f T) (T := schemeOverSpace T) W
      (schemeBaseChangeProjectionHom B S hS f T) hflat
  have hpr : IsProper B S hS
      (W.1.ι ≫ (schemeBaseChangeProjectionHom B S hS f T).hom) :=
    (hasProperSupport_pushforwardStructureSheaf_iff B S hS
      (X := schemeBaseChangeSpace f T) (T := schemeOverSpace T) W
      (schemeBaseChangeProjectionHom B S hS f T) _).1 hproper
  ⟨W.1, W.2, hfp, hfl, hpr⟩

/-- **Stacks 0D00, the converse construction from the sheaf of ideals.**  A sheaf of ideals
`𝓘 ⊆ 𝒪_{X_T}` whose quotient `𝒪_{X_T}/𝓘` is of finite presentation, flat over `T` and with
support proper over `T` is the defining ideal sheaf of a family classified by the Hilbert functor
of `f` over `T`. -/
@[stacks 0D00 "the converse construction, from a quasi-coherent sheaf of ideals"]
theorem exists_hilbertFamily_definingIdealSheaf_eq_of_quotConditions (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y)
    (I : (SheafOfModules.unit
      (structureRingSheaf B S hS (schemeBaseChangeSpace f T))).Submodule)
    (hfpq : (cokernel I.ι : Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
      (schemeBaseChangeSpace f T).2).IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (schemeBaseChangeSpace f T).property
      (schemeBaseChangeProjectionHom B S hS f T).hom
      (cokernel I.ι : Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
        (schemeBaseChangeSpace f T).2))
    (hproper : HasProperSupport B S hS (schemeBaseChangeSpace f T).property
      (schemeOverSpace T).property (schemeBaseChangeProjectionHom B S hS f T).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isFinitePresentation_schemeBaseChangeProjection f hf T).1)
      ((SheafOfModules.toSheaf _).obj (cokernel I.ι :
        Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
          (schemeBaseChangeSpace f T).2))) :
    ∃ z : HilbertFamily f T,
      definingIdealSheaf B S hS (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩ = I := by
  have hcok : (cokernel I.ι : Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
      (schemeBaseChangeSpace f T).2).IsQuasicoherentOnSite := inferInstance
  have hunit : (SheafOfModules.unit
      (structureRingSheaf B S hS (schemeBaseChangeSpace f T)) :
        Modules.{u, u} B S hS (schemeBaseChangeSpace f T).1
          (schemeBaseChangeSpace f T).2).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  have hqc : I.toSheafOfModules.IsQuasicoherentOnSite :=
    @isQuasicoherent_left_of_shortExact _ _ _ _ _
      (ShortComplex.mk I.ι (cokernel.π I.ι) (cokernel.condition I.ι))
      (ShortComplex.shortExact_mk_cokernel_π I.ι)
      (fun G => (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS _ _ G).1)
      hunit hcok
  obtain ⟨W, hW⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS
    (schemeBaseChangeSpace f T) I hqc
  subst hW
  refine ⟨hilbertFamilyOfQuotConditions B S hS f hf T W ?_ ?_ ?_, rfl⟩
  · exact SheafOfModules.IsFinitePresentationOnSite.of_iso
      (conormalAlgebraDegreeZeroIso B S hS (schemeBaseChangeSpace f T) W) hfpq
  · exact IsFlatOver.of_iso B S hS (schemeBaseChangeSpace f T).property
      (conormalAlgebraDegreeZeroIso B S hS (schemeBaseChangeSpace f T) W) hflat
  · exact hasProperSupport_pushforwardStructureSheaf_of_iso B S hS W _ _
      (conormalAlgebraDegreeZeroIso B S hS (schemeBaseChangeSpace f T) W) hproper

/-- **Stacks 03MB for the families classified by the Hilbert functor.**  Two families over the
same scheme over `Y` with the same defining ideal sheaf are equal: a family is determined by its
closed subspace, and a closed subspace by its defining ideal sheaf. -/
theorem definingIdealSheaf_hilbertFamily_injective (f : X ⟶ Y)
    (T : SchemesOverPresheaf B S hS Y) :
    Function.Injective fun z : HilbertFamily f T =>
      definingIdealSheaf B S hS (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩ :=
  fun _ _ h => HilbertFamily.ext (congrArg Subtype.val
    (definingIdealSheaf_injective B S hS (schemeBaseChangeSpace f T) h))

end Converse

end AlgebraicGeometry.Space

end
