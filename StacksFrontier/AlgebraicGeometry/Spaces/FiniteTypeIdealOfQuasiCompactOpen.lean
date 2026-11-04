module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTrivialisationSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.HomOverIdealUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel

/-!
# A quasi-compact open subspace is cut out by a finite type quasi-coherent ideal

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` contained in a
big fppf site `B`, and let `U ⊆ X` be a quasi-compact open subspace.  This file produces a
quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` of finite type with `|X| ∖ |U| = |V(ℐ)|`, which is the
implication (2) ⟹ (3) of Tag 0855.

The argument is the source's.  Let `𝒥` be the sheaf of ideals cutting out the reduced closed
subspace on `T = |X| ∖ |U|`, which Stacks 03IP supplies in the form
`AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_idealZeroLocus_eq`.  On a chart of `X`
which comes from a chart of `U` the ideal `𝒥` is the unit ideal, so the inclusion `𝒥 ⟶ 𝒪_X`
becomes an isomorphism after restriction to the small étale site of `U`; in particular `𝒥|_U` is
`𝒪_U`, which is of finite type. Tag 0853,
`AlgebraicGeometry.Space.exists_etaleSubmodule_extension`, cuts `𝒥` down to a quasi-coherent
submodule `M ⊆ 𝒥` of finite type which still agrees with `𝒥` over `U`, and the sheaf of ideals `ℐ`
which is the image of `M` in `𝒪_X` is the required one: it is contained in `𝒥`, so its zero locus
contains `T`, and it is the unit ideal on every chart of `X` coming from a chart of `U`, so its
zero locus is contained in `T`.

## Main results

* `AlgebraicGeometry.Space.idealSheaf_obj_smallEtalePostcomp_eq_top`: a sheaf of ideals whose
  unit locus contains the image of an étale morphism is the whole structure sheaf on every chart
  obtained by postcomposing a chart of the source, and
  `AlgebraicGeometry.Space.surjective_idealSheaf_ι_val_app`: such a sheaf of ideals is surjective
  on sections there.
* `AlgebraicGeometry.Space.isIso_etaleModulePullback_map_idealSheaf_ι`: a sheaf of ideals which
  is the unit ideal on every such chart restricts along the morphism to the whole structure
  sheaf, and `AlgebraicGeometry.Space.isFiniteType_etaleModulePullback_unit`: the restriction of
  the structure sheaf along an étale morphism is of finite type.
* `AlgebraicGeometry.Space.exists_isFiniteTypeQuasicoherentIdeal_idealZeroLocus_eq_compl_range`:
  the implication.
* `AlgebraicGeometry.Space.hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace`:
  **the implication (2) ⟹ (3) of Tag 0855**, in the shape of condition (3)
  `AlgebraicGeometry.Space.HasFiniteTypeQuasicoherentIdealZeroLocus`.

## Implementation notes

Three passages are worth naming.

* The restriction of `𝒥` to `U` is read as the étale pullback
  `AlgebraicGeometry.Space.etaleModulePullback` along the inclusion, which is the form Tag 0853
  speaks in, and the comparison `𝒥|_U ≅ 𝒪_U` is established on sections, through
  `Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation`: the sections of a pullback
  along an étale morphism over a chart `V` of `U` *are*, by definition, the sections over the
  composite chart of `X` — that reading is
  `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleModulePullback_map_val_app`, which holds by
  `rfl` — and over such a chart `𝒥` is the unit ideal.
* Tag 0853 concludes Mathlib's `SheafOfModules.IsFiniteType` while condition (3) of Tag 0855 is
  stated with `SheafOfModules.IsFiniteTypeOnSite`, so both directions of the comparison of
  Stacks 03DL(5) with Mathlib's predicate are used, namely
  `Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType` and
  `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`.  Finite type of `𝒪_U` is obtained
  from finite type of `𝒪_X` by Stacks 03DO for the site predicate,
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`, rather than directly on the small
  étale site of `U`, because the pullback of modules of Stacks 03LU is the functor for which that
  statement is available; `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` is
  Stacks 03LW, which identifies it with étale restriction.
* The passage from the submodule `M ⊆ 𝒥` produced by Tag 0853 to a sheaf of *ideals* is
  `Stacks.SheafOfModules.monoRange`, the sectionwise image of a monomorphism of sheaves of
  modules.  The order isomorphism between subobjects and sheaf submodules is not used: it is
  pinned to a category whose objects and morphisms lie in the same universe and does not
  instantiate at the small étale site of an algebraic space.

## References

* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 03IP](https://stacks.math.columbia.edu/tag/03IP)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A sheaf of ideals is the whole structure sheaf on a chart pushed forward along an étale
morphism whose image lies in its unit locus.**  The points of such a chart of `X` are images of
points of the chart of `Y`, hence lie in the unit locus, and a sheaf of ideals whose unit locus
contains every point of a chart is the whole structure sheaf there. -/
theorem idealSheaf_obj_smallEtalePostcomp_eq_top {Y X : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : Set.range (pointsMap B S hS Y.1 g.hom) ⊆ idealUnitLocus B S hS X I)
    (V : SmallEtale B S hS Y.1) :
    I.obj (op ((smallEtalePostcomp B S hS g hg).obj V)) = ⊤ := by
  refine idealSheaf_obj_eq_top_of_range_subset_idealUnitLocus B S hS X I _ ?_
  rintro _ ⟨y, rfl⟩
  exact hI ⟨pointsMap B S hS _ V.1.hom y, (pointsMap_comp_apply B S hS V.1.hom g.hom y).symm⟩

/-- A sheaf of ideals which is the whole structure sheaf over a chart is surjective on sections
over that chart: every section of `𝒪_X` there is a section of the sheaf of ideals. -/
theorem surjective_idealSheaf_ι_val_app (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (W : SmallEtale B S hS X.1) (hW : I.obj (op W) = ⊤) :
    Function.Surjective (I.ι.val.app (op W)) :=
  fun z => ⟨⟨z, by rw [hW]; exact Submodule.mem_top⟩, rfl⟩

/-- **A sheaf of ideals which is the unit ideal on every chart coming from an étale morphism
restricts along that morphism to the whole structure sheaf.**  The inclusion `ℐ ⟶ 𝒪_X` is
injective on sections because it is a monomorphism and surjective on the relevant charts by
`AlgebraicGeometry.Space.surjective_idealSheaf_ι_val_app`, and the sections of a pullback along
an étale morphism over a chart of the source are the sections over the composite chart. -/
theorem isIso_etaleModulePullback_map_idealSheaf_ι {Y X : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : ∀ V : SmallEtale B S hS Y.1,
      I.obj (op ((smallEtalePostcomp B S hS g hg).obj V)) = ⊤) :
    IsIso ((etaleModulePullback.{u, u} B S hS g hg).map I.ι) := by
  have : Mono I.ι.val := (SheafOfModules.forget _).map_mono I.ι
  refine Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation _ _ fun V => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨PresheafOfModules.injective_of_mono I.ι.val
      (op ((smallEtalePostcomp B S hS g hg).obj V.unop)), ?_⟩
  exact surjective_idealSheaf_ι_val_app B S hS X I
    ((smallEtalePostcomp B S hS g hg).obj V.unop) (hI V.unop)

/-- **The restriction of the structure sheaf along an étale morphism of algebraic spaces is of
finite type.**  The structure sheaf is of finite type on any site; Stacks 03DO for the clause
03DL(5) carries that to the pullback of modules of Stacks 03LU, and Stacks 03LW identifies that
pullback with étale restriction. -/
theorem isFiniteType_etaleModulePullback_unit {Y X : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) :
    ((etaleModulePullback.{u, u} B S hS g hg).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2)).IsFiniteType :=
  have hOX : SheafOfModules.IsFiniteTypeOnSite
      (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ inferInstance
  (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
    (isFiniteTypeOnSite_modulePullback B S hS g _ hOX)).of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS g hg).app _)

/-- **A quasi-compact open subspace of a quasi-compact and quasi-separated algebraic space is the
complement of the zero locus of a finite type quasi-coherent sheaf of ideals.**  This is the
implication (2) ⟹ (3) of Tag 0855. -/
theorem exists_isFiniteTypeQuasicoherentIdeal_idealZeroLocus_eq_compl_range
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hYqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      IsFiniteTypeQuasicoherentIdeal B S hS X I ∧
        (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ = idealZeroLocus B S hS X I := by
  classical
  let Y := openSubspaceSpace B S hS U hU
  let j : Y ⟶ X := openSubspaceHom B S hS U hU
  have hje : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS U hU
  set T : Set (points B S hS X.1) := (Set.range (pointsMap B S hS Y.1 j.hom))ᶜ with hTdef
  have hTcl : IsClosed T := by
    rw [hTdef]
    exact (isOpen_range_pointsMap_of_isOpenImmersion B S hS j.hom hU.2).isClosed_compl
  obtain ⟨J, hJq, hJzero⟩ := exists_isQuasicoherentOnSite_idealZeroLocus_eq B S hS X T hTcl
  have hJunit : idealUnitLocus B S hS X J = Set.range (pointsMap B S hS Y.1 j.hom) := by
    have h : (idealUnitLocus B S hS X J)ᶜ = (Set.range (pointsMap B S hS Y.1 j.hom))ᶜ := by
      rw [← hTdef]
      exact hJzero
    simpa using congrArg compl h
  have hJtop : ∀ V : SmallEtale B S hS Y.1,
      J.obj (op ((smallEtalePostcomp B S hS j hje).obj V)) = ⊤ :=
    fun V => idealSheaf_obj_smallEtalePostcomp_eq_top B S hS j hje J hJunit.ge V
  obtain ⟨M, m, hmmono, hMq, hMft, hmsurj⟩ :
      ∃ (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (m : M ⟶ J.toSheafOfModules),
        Mono m ∧ M.IsQuasicoherentOnSite ∧ M.IsFiniteType ∧
          ∀ V : SmallEtale B S hS Y.1,
            Function.Surjective
              (m.val.app (op ((smallEtalePostcomp B S hS j hje).obj V))) := by
    have : IsIso ((etaleModulePullback.{u, u} B S hS j hje).map J.ι) :=
      isIso_etaleModulePullback_map_idealSheaf_ι B S hS j hje J hJtop
    have hft : ((etaleModulePullback.{u, u} B S hS j hje).obj J.toSheafOfModules).IsFiniteType :=
      (isFiniteType_etaleModulePullback_unit B S hS j hje).of_iso
        (asIso ((etaleModulePullback.{u, u} B S hS j hje).map J.ι)).symm
    have hq :
        ((etaleModulePullback.{u, u} B S hS j hje).obj
          J.toSheafOfModules).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_etaleModulePullback B S hS j hje J.toSheafOfModules hJq
    set F := (etaleModulePullback.{u, u} B S hS j hje).obj J.toSheafOfModules
    let eTop := Stacks.SheafOfModules.monoRangeIso (𝟙 F) inferInstance
    obtain ⟨K, hKq, hKft, hK⟩ := exists_etaleSubmodule_extension B S hS hZ X hXqc hXqs U hU hYqc
      J.toSheafOfModules hJq (Stacks.SheafOfModules.monoRange (𝟙 F) inferInstance)
      (SheafOfModules.IsQuasicoherentOnSite.of_iso eTop hq) (hft.of_iso eTop)
    refine ⟨_, K.ι, SheafOfModules.Submodule.instMonoι K, hKq, hKft, fun V z => ?_⟩
    have hz : z ∈ (etaleSubmoduleRestrict B S hS j hje K).obj (op V) := by
      rw [hK]
      exact ⟨z, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have hmono : Mono (m ≫ J.ι) := mono_comp m J.ι
  set I := Stacks.SheafOfModules.monoRange (m ≫ J.ι) hmono
  have eI := Stacks.SheafOfModules.monoRangeIso (m ≫ J.ι) hmono
  have hIJ : I ≤ J := Stacks.SheafOfModules.monoRange_le (m ≫ J.ι) hmono J m rfl
  have hItop : ∀ V : SmallEtale B S hS Y.1,
      I.obj (op ((smallEtalePostcomp B S hS j hje).obj V)) = ⊤ := fun V =>
    LinearMap.range_eq_top.2
      ((surjective_idealSheaf_ι_val_app B S hS X J
        ((smallEtalePostcomp B S hS j hje).obj V) (hJtop V)).comp (hmsurj V))
  refine ⟨I, ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso eI hMq,
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ (hMft.of_iso eI)⟩, ?_⟩
  show T = idealZeroLocus B S hS X I
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rw [← hJzero]
    exact idealZeroLocus_antitone B S hS X hIJ
  obtain ⟨A, a, haS, haE⟩ := Y.2.exists_atlas
  have hsub : Set.range (pointsMap B S hS Y.1 j.hom) ⊆ idealUnitLocus B S hS X I := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨w, hw⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 A a).1 haS y
    refine range_subset_idealUnitLocus_of_eq_top B S hS X I
      ((smallEtalePostcomp B S hS j hje).obj ⟨CostructuredArrow.mk a, haE⟩)
      (hItop ⟨CostructuredArrow.mk a, haE⟩) ⟨w, ?_⟩
    exact (pointsMap_comp_apply B S hS a j.hom w).trans
      (congrArg (fun z => pointsMap B S hS Y.1 j.hom z) hw)
  rw [hTdef]
  exact Set.compl_subset_compl.2 hsub

/-- Let `X` be a quasi-compact and quasi-separated algebraic space over `S` and let `U ⊆ X` be an
open subspace. If `U` is quasi-compact, then there is a finite type quasi-coherent sheaf of ideals
`ℐ ⊆ 𝒪_X` with `|X| ∖ |U| = |V(ℐ)|`.

This is
`AlgebraicGeometry.Space.exists_isFiniteTypeQuasicoherentIdeal_idealZeroLocus_eq_compl_range`,
which follows the source: the reduced sheaf of ideals of `|X| ∖ |U|` is cut down by Stacks 0853,
`AlgebraicGeometry.Space.exists_etaleSubmodule_extension`, to a quasi-coherent sheaf of ideals of
finite type with the same restriction to `U`. -/
@[stacks 0855 "part (2) implies part (3)"]
theorem hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {U : Subfunctor X.1} (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    HasFiniteTypeQuasicoherentIdealZeroLocus B S hS X U :=
  exists_isFiniteTypeQuasicoherentIdeal_idealZeroLocus_eq_compl_range B S hS hZ X hXqc hXqs U hU
    hUqc

end AlgebraicGeometry.Space

end
