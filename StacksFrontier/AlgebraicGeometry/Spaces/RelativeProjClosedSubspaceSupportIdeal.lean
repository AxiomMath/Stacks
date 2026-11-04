module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreePresenter
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubmoduleExhaustionQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionStep
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceChartBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceFiniteTypeIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullbackSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijectiveCovering

/-!
# Cutting out a closed subspace of a relative Proj in one degree, away from an open

Let `X` be a quasi-compact and quasi-separated algebraic space, `𝒜` a quasi-coherent graded
`𝒪_X`-algebra as in Situation 0849 with `π : P = Proj_X(𝒜) ⟶ X` quasi-compact, `i : Z ⟶ P` a
closed subspace locally of finite presentation and `U ⊆ |X|` a quasi-compact open missing the
image of `Z`, every `𝒜_n` being of finite type.  Stacks 085N asserts that there are `d > 0` and a
quasi-coherent finite type `ℱ ⊆ 𝒜_d` with `Z = Proj_X(𝒜/ℱ𝒜)` and the support of `𝒜_d/ℱ`
disjoint from `U`.

This file proves that statement from a quasi-coherent graded ideal `ℐ ⊆ 𝒜` whose restriction to
every étale scheme point `T ⟶ X` has the sections of the graded ideal of Stacks 0801 of
`Z ×_X T ⊆ Proj_T(𝒜|_T)` — the ideal of Stacks 085L — in the same form as
`RelativeProjSituation.exists_finiteType_iso_quotientProjHom_of_gradedIdeal` proves Stacks 085M
from it.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `disjoint_supportOfSheaf_cokernel_of_forall_mem`: a submodule `𝒦 ⊆ ℳ` containing every section
  of `ℳ` over the étale charts lying over an open `U` has `ℳ/𝒦` supported away from `U`.
* `exists_finiteType_le_forall_mem_of_isCompact`: on a qcqs space, a quasi-coherent `𝒩 ⊆ ℳ` which
  agrees with the finite type `ℳ` over a quasi-compact open `U` contains a quasi-coherent `𝒦` of
  finite type which still agrees with `ℳ` over `U`.
* `RelativeProjSituation.mem_gradedIdeal_of_range_subset`: over `U` every section of `𝒜` lies in
  `ℐ`, the base change of `Z` to a chart over `U` being empty
  (`…isEmpty_chartClosedSubscheme_of_disjoint`).
* `RelativeProjSituation.exists_finiteType_le_forall_iso_quotientProjHom_of_gradedIdeal`:
  Stacks 085M from `ℐ`, with a submodule `ℱ₁ ⊆ ℐ_d` such that every quasi-coherent `ℱ` with
  `ℱ₁ ⊆ ℱ ⊆ ℐ_d` cuts out `Z`.
* `RelativeProjSituation.exists_finiteType_iso_quotientProjHom_disjoint_support_of_gradedIdeal`:
  Stacks 085N from `ℐ`.

## Implementation notes

The source obtains the support clause on an affine étale chart from the scheme case Stacks 0803
and transports it to `X`.  Here it is obtained on `X` directly: `ℱ = ℱ₁ + ℱ₀`, where `ℱ₁` is the
submodule of Stacks 085M and `ℱ₀ ⊆ ℐ_d` is of finite type and all of `𝒜_d` over `U`.  The latter
comes from the extension result of Stacks 0829 in the form
`AlgebraicGeometry.Space.exists_finiteType_le_etaleSubmoduleRestrict`, applied on the open
subspace cut out by `U`, where `ℐ_d` agrees with the finite type `𝒜_d`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/- See `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceSupport`: these global
instances answer the abelian structure at an enlarged universe and must not be selected for the
quotient `ℳ/𝒦` of modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A chart of `Y` read as a chart of `X` through an étale `j : Y ⟶ X` lies over any `U` which
is the range of `j` on points. -/
private theorem range_pointsMap_postcomp_subset {X Y : AlgebraicSpaces B S hS} (j : Y ⟶ X)
    (hj : IsEtale B S hS j.hom) {U : Set (points B S hS X.1)}
    (hrange : Set.range (pointsMap B S hS _ j.hom) = U) (V : SmallEtale B S hS Y.1) :
    Set.range (pointsMap B S hS _ ((smallEtalePostcomp B S hS j hj).obj V).1.hom) ⊆ U := by
  rw [← hrange]
  rintro _ ⟨x, rfl⟩
  exact ⟨pointsMap B S hS _ V.1.hom x,
    (congrFun (pointsMap_comp B S hS _ V.1.hom j.hom) x).symm⟩

section Support

variable {X : AlgebraicSpaces B S hS}

/-- **A submodule which is everything over an open has quotient supported away from it.**  If
`𝒦 ⊆ ℳ` has every section of `ℳ` over every étale chart lying over `U`, then the support of
`ℳ/𝒦` is disjoint from `U`: over such a chart every section of the quotient is locally the image
of a section of `ℳ`, which lies in `𝒦` and so maps to zero. -/
theorem disjoint_supportOfSheaf_cokernel_of_forall_mem {M : Modules.{u, u} B S hS X.1 X.2}
    (K : M.Submodule) (U : Set (points B S hS X.1)) (hU : IsOpen U)
    (hKU : ∀ V : SmallEtale B S hS X.1, Set.range (pointsMap B S hS _ V.1.hom) ⊆ U →
      ∀ a : M.val.obj (op V), a ∈ K.obj (op V)) :
    Disjoint (supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj (cokernel K.ι))) U := by
  set j := openPointsSubspaceHom B S hS X U hU
  have hj : IsEtale B S hS j.hom := isEtale_openPointsSubspaceHom B S hS X U hU
  have hrange : Set.range (pointsMap B S hS _ j.hom) = U :=
    range_pointsMap_openPointsSubspaceHom B S hS X U hU
  rw [← hrange]
  refine (isZero_etaleModulePullback_iff_disjoint_supportOfSheaf B S hS j hj (cokernel K.ι)).1 ?_
  refine Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ fun V => ?_
  refine subsingleton_of_forall_eq 0 fun c => ?_
  -- `c` is a section of `ℳ/𝒦` over the chart `V ⟶ U ⟶ X`
  set V' := (smallEtalePostcomp B S hS j hj).obj V.unop
  have hV' := range_pointsMap_postcomp_subset B S hS j hj hrange V.unop
  change (cokernel K.ι).val.obj (op V') at c
  have hsurj := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (cokernel.π K.ι)
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (X := op V') c
    (hsurj.imageSieve_mem c) fun {Y} g hg => ?_
  obtain ⟨a, ha⟩ := hg
  have hY : Set.range (pointsMap B S hS _ Y.1.hom) ⊆ U := by
    refine subset_trans ?_ hV'
    rintro _ ⟨y, rfl⟩
    refine ⟨pointsMap B S hS _ (yoneda.map g.hom.left) y, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B S hS _ V'.1.hom), ← pointsMap_comp]
    congr 1
    exact CostructuredArrow.w g.hom
  have hzero : (cokernel.π K.ι).val.app (op Y) a = 0 :=
    Stacks.SheafOfModules.val_app_apply_eq_zero K.ι (cokernel.π K.ι)
      (cokernel.condition K.ι) (op Y) ⟨a, hKU Y hY a⟩
  exact ha.symm.trans hzero

end Support


section Extension

variable {X : AlgebraicSpaces B S hS}

/-- **A finite type submodule agreeing with `ℳ` over a quasi-compact open.**  Let `X` be
quasi-compact and quasi-separated, `ℳ` an `𝒪_X`-module of finite type and `𝒩 ⊆ ℳ` a
quasi-coherent submodule containing every section of `ℳ` over every étale chart lying over a
quasi-compact open `U`.  Then there is a quasi-coherent submodule `𝒦 ⊆ 𝒩` of finite type which
still contains every such section.

On the open subspace `X_U` cut out by `U` the inclusion `𝒩|_U ⟶ ℳ|_U` is bijective on sections,
so `𝒩|_U` is of finite type; Stacks 0829, in the form
`AlgebraicGeometry.Space.exists_finiteType_le_etaleSubmoduleRestrict`, gives a quasi-coherent
`𝒦₀ ⊆ 𝒩` of finite type whose restriction to `X_U` is everything, and `𝒦` is the image of `𝒦₀`
in `ℳ`.  An étale chart lying over `U` is a chart of `X_U`. -/
theorem exists_finiteType_le_forall_mem_of_isCompact (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {M : Modules.{u, u} B S hS X.1 X.2} (hMf : M.IsFiniteType) {N : M.Submodule}
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite)
    (U : Set (points B S hS X.1)) (hU : IsOpen U) (hUc : IsCompact U)
    (hNU : ∀ V : SmallEtale B S hS X.1, Set.range (pointsMap B S hS _ V.1.hom) ⊆ U →
      ∀ a : M.val.obj (op V), a ∈ N.obj (op V)) :
    ∃ K : M.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ K ≤ N ∧
        ∀ V : SmallEtale B S hS X.1, Set.range (pointsMap B S hS _ V.1.hom) ⊆ U →
          ∀ a : M.val.obj (op V), a ∈ K.obj (op V) := by
  have hW := isOpenSubspace_openSubspaceOfPoints B S hS X.2 U hU
  set Y := openPointsSubspace B S hS X U hU
  set j : Y ⟶ X := openPointsSubspaceHom B S hS X U hU
  have hj : IsEtale B S hS j.hom := isEtale_openPointsSubspaceHom B S hS X U hU
  have hrange : Set.range (pointsMap B S hS _ j.hom) = U :=
    range_pointsMap_openPointsSubspaceHom B S hS X U hU
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    isQuasiCompactSpace_of_isCompact_range B S hS X.2 hW
      (by rw [range_pointsMap_ι_openSubspaceOfPoints]; exact hUc)
  -- `𝒩|_U ⟶ ℳ|_U` is an isomorphism
  set ψ := (etaleModulePullback.{u, u} B S hS j hj).map N.ι
  have hψ : IsIso ψ := by
    refine Stacks.SheafOfModules.isIso_of_bijective_val_app_on ψ (fun _ => True)
      (fun V => ?_) (fun V _ => ⟨fun _ _ hab => Subtype.ext hab,
        fun a => ⟨⟨a, hNU _ (range_pointsMap_postcomp_subset B S hS j hj hrange V) a⟩, rfl⟩⟩)
    exact GrothendieckTopology.superset_covering _
      (fun Z f _ => Sieve.le_generate _ Z f trivial) (GrothendieckTopology.top_mem _ V)
  -- so `𝒩|_U` is of finite type, and so is the submodule of all of its sections
  let N' := (etaleModulePullback.{u, u} B S hS j hj).obj N.toSheafOfModules
  have hN'f : N'.IsFiniteType :=
    Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso (@asIso _ _ _ _ ψ hψ).symm
      (isFiniteType_etaleModulePullback B S hS j hj M hMf)
  let G := Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule (𝟙 N')
  have hGf : G.toSheafOfModules.IsFiniteType :=
    Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
      (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso (𝟙 N')) hN'f
  obtain ⟨K₀, hK₀q, hK₀f, hGK₀⟩ :=
    exists_finiteType_le_etaleSubmoduleRestrict B S hS hZ X hXqc hXqs hN j hj hYqc G hGf
  let K := Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule (K₀.ι ≫ N.ι)
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact hK₀q.of_iso (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso (K₀.ι ≫ N.ι))
  · exact Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
      (Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso (K₀.ι ≫ N.ι)) hK₀f
  · refine _root_.SheafOfModules.Submodule.le_iff.2 fun V x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact (K₀.ι.val.app V y).2
  · intro V hV a
    have hι : IsEtale B S hS (openSubspaceOfPoints B S hS X.1 U).ι := hj
    obtain ⟨V₀, rfl⟩ := exists_smallEtalePostcomp_eq_of_points B S hS
      (openSubspaceOfPoints B S hS X.1 U) hW hι V
      (by rw [range_pointsMap_ι_openSubspaceOfPoints]; exact hV)
    have hb : (⟨a, hNU _ hV a⟩ : N.toSheafOfModules.val.obj
        (op ((smallEtalePostcomp B S hS j hj).obj V₀))) ∈ G.obj (op V₀) := ⟨_, rfl⟩
    exact ⟨⟨_, _root_.SheafOfModules.Submodule.le_iff.1 hGK₀ _ hb⟩, rfl⟩

end Extension


/-! ### The closed subspace and the graded ideal over `U` -/

namespace RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal
open SheafOfModules.GradedAlgebra

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {s : RelativeProjSituation.{u, u}}
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- **The base change of `Z` to a scheme point lying over `U` is empty**, when the image of `Z`
in `X` misses `U`: a point of `Z ×_X T` maps to a point of `X` which is both in the image of `Z`
and in the image of `T`. -/
theorem isEmpty_chartClosedSubscheme_of_disjoint (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) (U : Set (points s.site s.base s.containsBase s.space.1))
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.Proj.1 s.π.hom
        (pointsMap s.site s.base s.containsBase Z.1 i.hom z)))
    (hf : Set.range (pointsMap s.site s.base s.containsBase _ f) ⊆ U) :
    IsEmpty ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.pullback
        (s.relativeProjPoints.fibreToSpace T f))) := by
  set R := (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep
  set g := s.relativeProjPoints.fibreToSpace T f
  refine ⟨fun z => ?_⟩
  set p := (pointsEquivScheme s.site s.base s.containsBase _).symm z
  have hw : R.fst g ≫ (Subfunctor.range i.hom).ι = yoneda.map (R.snd g) ≫ g := R.w g
  have hsq : g ≫ s.π.hom = yoneda.map (s.relativeProjPoints.fibreHom T f) ≫ f :=
    (s.relativeProjPoints.isPullback T f).w
  set q := pointsMap s.site s.base s.containsBase _ (Subfunctor.range i.hom).ι
    (pointsMap s.site s.base s.containsBase _ (R.fst g) p)
  have : Mono i.hom := mono_of_isClosedImmersion s.site s.base s.containsBase i.hom hi
  obtain ⟨z', hz'⟩ : q ∈ Set.range (pointsMap s.site s.base s.containsBase Z.1 i.hom) := by
    rw [← range_pointsMap_ι_range]
    exact ⟨_, rfl⟩
  have hmemU : pointsMap s.site s.base s.containsBase _ s.π.hom q ∈ U := by
    apply hf
    refine ⟨pointsMap s.site s.base s.containsBase _
      (yoneda.map (s.relativeProjPoints.fibreHom T f))
        (pointsMap s.site s.base s.containsBase _ (yoneda.map (R.snd g)) p), ?_⟩
    have key : yoneda.map (R.snd g) ≫ yoneda.map (s.relativeProjPoints.fibreHom T f) ≫ f =
        R.fst g ≫ (Subfunctor.range i.hom).ι ≫ s.π.hom :=
      (congrArg (yoneda.map (R.snd g) ≫ ·) hsq).symm.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ s.π.hom) hw).symm.trans (Category.assoc _ _ _)))
    simp only [q, ← pointsMap_comp_apply]
    exact (congrArg (fun φ => pointsMap s.site s.base s.containsBase _ φ p)
      ((Category.assoc _ _ _).trans key)).trans
        (pointsMap_comp_apply s.site s.base s.containsBase (R.fst g) _ p)
  exact Set.disjoint_left.1 hZU hmemU ⟨z', by simp only [hz']⟩

/-- **Over `U` every section of `𝒜` is an equation for `Z`.**  Let `ℐ ⊆ 𝒜` be a graded ideal whose
restriction to every étale scheme point `T ⟶ X` has the sections of the graded ideal of
Stacks 0801 of `Z ×_X T ⊆ Proj_T(𝒜|_T)`.  If the image of `Z` in `X` misses `U`, every section of
`𝒜_n` over an étale chart lying over `U` lies in `ℐ_n`: over such a chart `Z ×_X T` is empty, so
its graded ideal is everything. -/
theorem mem_gradedIdeal_of_range_subset
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom) (I : s.GradedIdeal)
    (hI : ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1),
      IsEtale s.site s.base s.containsBase f → ∀ (n : ℤ)
      (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
      haveI := quasiCompact_relativeProj_toBase hπ T f
      a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W) ↔
        ((I.quotientHomPoints.hom T f).app n).app W a = 0)
    (U : Set (points s.site s.base s.containsBase s.space.1))
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.Proj.1 s.π.hom
        (pointsMap s.site s.base s.containsBase Z.1 i.hom z)))
    (n : ℕ) (V : SmallEtale s.site s.base s.containsBase s.space.1)
    (hV : Set.range (pointsMap s.site s.base s.containsBase _ V.1.hom) ⊆ U)
    (a : (s.algebra.piece (n : ℤ)).val.obj (op V)) :
    a ∈ (I.piece (n : ℤ)).obj (op V) := by
  set T := V.1.left
  set f : yoneda.obj T ⟶ s.space.1 := V.1.hom
  have hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom :=
    isEtale_of_presheaf_etale s.site s.base s.containsBase V.2
  have := quasiCompact_relativeProj_toBase hπ T f
  have hempty := isEmpty_chartClosedSubscheme_of_disjoint i hi T f U hZU hV
  have hdisj : ((⊤ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
      Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
        Set.range (chartClosedSubscheme i hi T f ≫
          (relativeProj (s.relativeProjPoints.algebra T f)).toBase).base = ∅ := by
    rw [Set.range_eq_empty, Set.inter_empty]
  -- the chart `⊤ ⟶ T ⟶ X` is `V`
  let e : s.etalePointChart f hf ⊤ ≅ V :=
    (smallEtalePostcomp s.site s.base s.containsBase (pointHom (X := s.space) f) hf).mapIso
        ((isTerminalSelfOpensFunctorTop s.site s.base s.containsBase T).uniqueUpToIso
          (isTerminalIdEtaleChart s.site s.base s.containsBase T)) ≪≫
      eqToIso (smallEtalePostcomp_obj_idEtaleChart V)
  set b := (s.algebra.piece (n : ℤ)).val.map e.hom.op a
  set a' := (s.etalePointReading f hf (n : ℤ) ⊤).symm b
  have ha' := mem_twistKerGradedIdeal_of_disjoint (s.relativeProjPoints.algebra T f)
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
    (chartClosedSubscheme i hi T f) hdisj n le_rfl a'
  have hb : b ∈ (I.piece (n : ℤ)).obj (op (s.etalePointChart f hf ⊤)) :=
    (congrArg (· ∈ (I.piece (n : ℤ)).obj (op (s.etalePointChart f hf ⊤)))
      (Equiv.apply_symm_apply (s.etalePointReading f hf (n : ℤ) ⊤) b)).mp
        ((I.quotientHomPoints_app_eq_zero_iff f hf (n : ℤ) ⊤ a').1
          ((hI T f hf (n : ℤ) ⊤ a').1 ha'))
  have hmem := (I.piece (n : ℤ)).map_mem e.inv.op hb
  have hab : (s.algebra.piece (n : ℤ)).val.map e.inv.op b = a := by
    simp only [b]
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
      PresheafOfModules.map_id_apply]
  rwa [hab] at hmem

/-- **Stacks 085M, granted the ideal of Stacks 085L, in the form stable under enlarging `ℱ`.**
Under the hypotheses of `exists_finiteType_iso_quotientProjHom_of_gradedIdeal` there are `d > 0`
and a quasi-coherent `ℱ₁ ⊆ ℐ_d` of finite type such that `Z = Proj_X(𝒜/ℱ𝒜)` over `Proj_X(𝒜)`
for **every** quasi-coherent `ℱ` with `ℱ₁ ⊆ ℱ ⊆ ℐ_d`.

The proof is that of `exists_finiteType_iso_quotientProjHom_of_gradedIdeal`: on an affine étale
chart `T` the finite type `ℱ' ⊆ ℐ_d|_T` of Stacks 0802 lies in the chart kernel for `𝒜/ℱ₁𝒜`, hence
in the larger chart kernel for `𝒜/ℱ𝒜`, and that kernel is contained in the ideal of Stacks 0801
of `Z ×_X T` because `ℱ ⊆ ℐ_d`. -/
theorem exists_finiteType_le_forall_iso_quotientProjHom_of_gradedIdeal
    (hZ : s.site.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase hZ s.space.1)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hfp : IsLocallyOfFinitePresentation s.site s.base s.containsBase i.hom) (I : s.GradedIdeal)
    (hI : ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1),
      IsEtale s.site s.base s.containsBase f → ∀ (n : ℤ)
      (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
      haveI := quasiCompact_relativeProj_toBase hπ T f
      a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W) ↔
        ((I.quotientHomPoints.hom T f).app n).app W a = 0) :
    ∃ d : ℕ, 0 < d ∧ ∃ (F₁ : (s.algebra.piece (d : ℤ)).Submodule)
      (hF₁ : F₁.toSheafOfModules.IsQuasicoherentOnSite), F₁.toSheafOfModules.IsFiniteType ∧
        F₁ ≤ I.piece (d : ℤ) ∧
        ∀ (F : (s.algebra.piece (d : ℤ)).Submodule)
          (hF : F.toSheafOfModules.IsQuasicoherentOnSite), F₁ ≤ F → F ≤ I.piece (d : ℤ) →
            ∃ e : Z ≅ (GradedIdeal.ofDegree s F hF).quotientSituation.Proj,
              e.hom ≫ (GradedIdeal.ofDegree s F hF).quotientProjHom = i := by
  obtain ⟨T, f, hTaff, hfS, hf⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover _ _ _ _ s.space.2).1 hXqc
  have hfE := (isEtale_iff_presheaf_of_yoneda _ _ _ f).1 hf
  have := quasiCompact_relativeProj_toBase hπ T f
  have := hTaff
  set A := s.relativeProjPoints.algebra T f
  set D := Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A
  obtain ⟨d, hd, ℱ, -, hft, hle, hcut⟩ := exists_finiteType_ker_eq_ker_projQuotientHom A D
    (chartClosedSubscheme i hi T f)
    (locallyOfFinitePresentation_chartClosedSubscheme i hi hfp T f hfE)
  have hleI : ℱ ≤ (I.chartKernel T f).piece (d : ℤ) := by
    refine _root_.SheafOfModules.Submodule.le_iff.2 fun W a ha => ?_
    induction W with
    | op W =>
    exact (I.mem_chartKernel_iff T f _ W a).2
      ((hI T f hf _ W a).1 (_root_.SheafOfModules.Submodule.le_iff.1 hle _ ha))
  obtain ⟨F₁, hF₁, hF₁f, hF₁I, hℱF₁⟩ :=
    exists_finiteType_le_chartKernel hZ hXqc hXqs T f hf I ℱ hft hleI
  refine ⟨d, hd, F₁, hF₁, hF₁f, hF₁I, fun F hF h₁ h₂ => ?_⟩
  set J := GradedIdeal.ofDegree s F hF
  have hJI : ∀ n, J.piece n ≤ I.piece n := fun n => Ideal.ofDegree_le F s.mul_comm I.toIdeal h₂ n
  have hℱF : ℱ ≤ (J.chartKernel T f).piece (d : ℤ) :=
    hℱF₁.trans ((GradedIdeal.ofDegree s F₁ hF₁).chartKernel_mono T f
      (ofDegree_piece_mono hF₁ hF h₁) (d : ℤ))
  have hsub : ∀ n : ℤ, (J.chartKernel T f).piece n ≤ (twistKerGradedIdeal A D
      (chartClosedSubscheme i hi T f)).piece n := by
    intro n
    refine (J.chartKernel_mono T f hJI n).trans ?_
    refine _root_.SheafOfModules.Submodule.le_iff.2 fun W a ha => ?_
    induction W with
    | op W =>
    exact (hI T f hf n W a).2 ((I.mem_chartKernel_iff T f n W a).1 ha)
  refine exists_iso_quotientProjHom_of_chart_ker J i hi T f hfE hfS ?_
  exact (ker_relativeMapHom_eq_ker_projQuotientHom _
    (J.surjectiveOnAffineSections_quotientHomPoints T f)
    (J.chartKernel T f) (J.mem_chartKernel_iff T f)).trans (hcut (J.chartKernel T f) hℱF hsub).symm

/-- **Stacks 085N, granted the ideal of Stacks 085L.**  Let `X` be a quasi-compact and
quasi-separated algebraic space, `𝒜` a quasi-coherent graded `𝒪_X`-algebra with
`π : P = Proj_X(𝒜) ⟶ X` quasi-compact, `i : Z ⟶ P` a closed subspace locally of finite
presentation, and `U ⊆ |X|` a quasi-compact open missing the image of `Z`; assume every `𝒜_n` of
finite type.  Let `ℐ ⊆ 𝒜` be a quasi-coherent graded ideal whose restriction to every étale
scheme point `T ⟶ X` has the sections of the graded ideal of Stacks 0801 of
`Z ×_X T ⊆ Proj_T(𝒜|_T)`.  Then there are `d > 0` and a quasi-coherent finite type `ℱ ⊆ 𝒜_d` with
`Z = Proj_X(𝒜/ℱ𝒜)` over `P` and the support of `𝒜_d/ℱ` disjoint from `U`.

`ℱ` is the sum of the submodule `ℱ₁ ⊆ ℐ_d` of Stacks 085M, in the form
`exists_finiteType_le_forall_iso_quotientProjHom_of_gradedIdeal`, and of a finite type
quasi-coherent `ℱ₀ ⊆ ℐ_d` which is all of `𝒜_d` over `U`
(`AlgebraicGeometry.Space.exists_finiteType_le_forall_mem_of_isCompact`): over `U` every section
of `𝒜_d` lies in `ℐ_d` by `mem_gradedIdeal_of_range_subset`.  Enlarging `ℱ₁` keeps `Z` cut out,
and `𝒜_d/ℱ` is a quotient of `𝒜_d/ℱ₀`, which vanishes over `U`. -/
theorem exists_finiteType_iso_quotientProjHom_disjoint_support_of_gradedIdeal
    (hZ : s.site.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase hZ s.space.1)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hfp : IsLocallyOfFinitePresentation s.site s.base s.containsBase i.hom)
    (U : Set (points s.site s.base s.containsBase s.space.1))
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.Proj.1 s.π.hom
        (pointsMap s.site s.base s.containsBase Z.1 i.hom z)))
    (hUopen : IsOpen U) (hUqc : IsCompact U)
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType (s.algebra.piece (n : ℤ))) (I : s.GradedIdeal)
    (hI : ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1),
      IsEtale s.site s.base s.containsBase f → ∀ (n : ℤ)
      (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
      haveI := quasiCompact_relativeProj_toBase hπ T f
      a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W) ↔
        ((I.quotientHomPoints.hom T f).app n).app W a = 0) :
    ∃ d : ℕ, 0 < d ∧ ∃ (F : (s.algebra.piece (d : ℤ)).Submodule)
      (hF : F.toSheafOfModules.IsQuasicoherentOnSite), F.toSheafOfModules.IsFiniteType ∧
        (∃ e : Z ≅ (GradedIdeal.ofDegree s F hF).quotientSituation.Proj,
          e.hom ≫ (GradedIdeal.ofDegree s F hF).quotientProjHom = i) ∧
        Disjoint (supportOfSheaf s.site s.base s.containsBase s.space.1
          ((SheafOfModules.toSheaf (structureRingSheaf s.site s.base s.containsBase
            s.space)).obj (cokernel F.ι))) U := by
  obtain ⟨d, hd, F₁, hF₁, hF₁f, hF₁I, hiso⟩ :=
    exists_finiteType_le_forall_iso_quotientProjHom_of_gradedIdeal i hi hZ hXqc hXqs hπ hfp I hI
  obtain ⟨F₀, hF₀q, hF₀f, hF₀I, hF₀U⟩ :=
    exists_finiteType_le_forall_mem_of_isCompact s.site s.base s.containsBase hZ hXqc hXqs
      (hA d) (I.isQuasicoherent (d : ℤ)) U hUopen hUqc
      (fun V hV a => mem_gradedIdeal_of_range_subset i hi hπ I hI U hZU d V hV a)
  have hFqf := isQuasicoherentOnSite_isFiniteType_sup s.site s.base s.containsBase
    (s.isQuasicoherent (d : ℤ)) F₁ F₀ ⟨hF₁, hF₁f⟩ ⟨hF₀q, hF₀f⟩
  refine ⟨d, hd, F₁ ⊔ F₀, hFqf.1, hFqf.2,
    hiso (F₁ ⊔ F₀) hFqf.1 le_sup_left (sup_le hF₁I hF₀I), ?_⟩
  exact Set.disjoint_of_subset_left
    (supportOfSheaf_cokernel_subset_of_le s.site s.base s.containsBase s.space
      (le_sup_right (a := F₁) (b := F₀)))
    (disjoint_supportOfSheaf_cokernel_of_forall_mem s.site s.base s.containsBase F₀ U hUopen
      hF₀U)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
