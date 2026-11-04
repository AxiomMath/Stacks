module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeSandwich
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleSection
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDegreeIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteTypeSubmoduleDirectedFamily

/-!
# A closed subspace of finite presentation of a relative Proj is cut out by a finite type ideal

This file proves Stacks 085M.  Let `X` be a quasi-compact and quasi-separated algebraic space, `𝒜`
a quasi-coherent graded `𝒪_X`-algebra as in Situation 0849 with `π : Proj_X(𝒜) ⟶ X`
quasi-compact, and `i : Z ⟶ Proj_X(𝒜)` a closed subspace locally of finite presentation.  Then
there are `d > 0` and a quasi-coherent `𝒪_X`-submodule `ℱ ⊆ 𝒜_d` of finite type with
`Z = Proj_X(𝒜/ℱ𝒜)`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.chartKernel`: the kernel of the
  restriction of `𝒜 ⟶ 𝒜/𝒥` to a scheme point, a quasi-coherent graded ideal of `𝒜|_T`.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_finiteType_le_chartKernel`: a finite type
  `ℱ' ⊆ ker(𝒜|_T ⟶ (𝒜/ℐ)|_T)_d` on an affine étale chart lies in the kernel for `𝒜/ℱ𝒜` with
  `ℱ ⊆ ℐ_d` of finite type.
* `Space.RelativeProjSituation.exists_finiteType_iso_quotientProjHom_of_gradedIdeal`:
  Stacks 085M for a closed subspace given with the quasi-coherent graded ideal `ℐ` of Stacks 085L
  cutting it out on the étale scheme points.

## Implementation notes

The proof is the one of the source, through the case of schemes.  On an affine étale scheme chart
`T ⟶ X` the closed subscheme `Z ×_X T` of `Proj_T(𝒜|_T)` is locally of finite presentation, so
Stacks 0802 gives a finite type `ℱ' ⊆ ℐ_d|_T` such that every quasi-coherent graded ideal between
`ℱ'𝒜|_T` and `ℐ|_T` cuts out `Z ×_X T`
(`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_ker_eq_ker_projQuotientHom`).
The step that the source attributes to Stacks 0829 is the containment `ℱ' ⊆ ℱ|_T` for a finite
type quasi-coherent `ℱ ⊆ ℐ_d` on `X`: a local section of `ℱ'` over an affine open of `T` is read as
a section of `ℐ_d` over an affine étale chart of `X`, which lies in a finite type quasi-coherent
submodule of `ℐ_d` (`AlgebraicGeometry.Space.exists_finiteType_le_mem_of_isAffine`, the qcqs
exhaustion); these submodules form a directed family, and the finite type `ℱ'` on the
quasi-compact `T` lies in one member
(`Stacks.SheafOfModules.exists_le_of_isFiniteType_of_compactSpace_scheme`).  Then `ℱ𝒜 ⊆ ℐ`, so
the kernel of `𝒜|_T ⟶ (𝒜/ℱ𝒜)|_T` lies between `ℱ'𝒜|_T` and `ℐ|_T`, and it cuts out
`Z ×_X T`; one surjective étale chart suffices to conclude
(`AlgebraicGeometry.Space.RelativeProjSituation.exists_iso_quotientProjHom_of_chart_ker`).

## References

* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal
open SheafOfModules.GradedAlgebra

universe u

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {s : RelativeProjSituation.{u, u}}

namespace GradedIdeal

variable (J : s.GradedIdeal) (T : BigFppfOver s.site s.base s.containsBase)
  (f : yoneda.obj T ⟶ s.space.1)

/-- A submodule of a piece of `𝒜|_T` lies in another if this holds on sections over every open. -/
private theorem le_of_forall_mem_opens {n : ℤ}
    {F G : ((s.relativeProjPoints.algebra T f).piece n).Submodule}
    (h : ∀ (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
      a ∈ F.obj (op W) → a ∈ G.obj (op W)) : F ≤ G :=
  _root_.SheafOfModules.Submodule.le_iff.2 fun W => h W.unop

/-- **The kernel of `𝒜|_T ⟶ (𝒜/𝒥)|_T`** at a scheme point `f : T ⟶ X` of the base, as a
quasi-coherent graded ideal of `𝒜|_T`. -/
@[irreducible] def chartKernel : QcohGradedIdeal (s.relativeProjPoints.algebra T f) where
  toGradedIdeal := kernelGradedIdeal (J.quotientHomPoints.hom T f)
  isQuasicoherent := isQuasicoherent_kernelGradedIdeal_piece _

/-- A section lies in the chart kernel exactly when its image in `(𝒜/𝒥)|_T` vanishes. -/
theorem mem_chartKernel_iff (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    a ∈ ((J.chartKernel T f).piece n).toSubmodule.obj (op W) ↔
      ((J.quotientHomPoints.hom T f).app n).app W a = 0 := by
  unfold chartKernel
  exact mem_kernelGradedIdeal_iff _ n W a

/-- The chart kernels are monotone in the ideal. -/
theorem chartKernel_mono {I : s.GradedIdeal} (h : ∀ n, J.piece n ≤ I.piece n) (n : ℤ) :
    (J.chartKernel T f).piece n ≤ (I.chartKernel T f).piece n := by
  refine le_of_forall_mem_opens T f fun W a ha => ?_
  exact (I.mem_chartKernel_iff T f n W a).2
    (J.quotientHomPoints_app_eq_zero_of_le h T f n W a ((J.mem_chartKernel_iff T f n W a).1 ha))

end GradedIdeal

/-- The graded ideal generated by a submodule of one piece is monotone in the submodule. -/
theorem ofDegree_piece_mono {d : ℤ} {F F' : (s.algebra.piece d).Submodule}
    (hF : F.toSheafOfModules.IsQuasicoherentOnSite)
    (hF' : F'.toSheafOfModules.IsQuasicoherentOnSite) (h : F ≤ F') (n : ℤ) :
    (GradedIdeal.ofDegree s F hF).piece n ≤ (GradedIdeal.ofDegree s F' hF').piece n :=
  Ideal.ofDegree_le F s.mul_comm (GradedIdeal.ofDegree s F' hF').toIdeal
    (h.trans (le_generatedInDegree_self F')) n

section Approximation

/-- The quasi-coherent submodules of finite type of `ℐ_d`, as submodules of `𝒜_d`. -/
def FiniteTypeDegreeSubmodule (I : s.GradedIdeal) (d : ℤ) : Type (u + 1) :=
  {K : (s.algebra.piece d).Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
    K.toSheafOfModules.IsFiniteType ∧ K ≤ I.piece d}

namespace FiniteTypeDegreeSubmodule

variable {I : s.GradedIdeal} {d : ℤ}

/-- The zero submodule is a quasi-coherent submodule of finite type of `ℐ_d`. -/
instance : Nonempty (FiniteTypeDegreeSubmodule I d) :=
  ⟨⟨⊥, (isQuasicoherentOnSite_isFiniteType_bot s.site s.base s.containsBase
    (X := s.space) (M := s.algebra.piece d)).1,
    (isQuasicoherentOnSite_isFiniteType_bot s.site s.base s.containsBase
      (X := s.space) (M := s.algebra.piece d)).2, bot_le⟩⟩

/-- The supremum of two quasi-coherent submodules of finite type of `ℐ_d`. -/
def sup (K₁ K₂ : FiniteTypeDegreeSubmodule I d) : FiniteTypeDegreeSubmodule I d :=
  ⟨K₁.1 ⊔ K₂.1, (isQuasicoherentOnSite_isFiniteType_sup s.site s.base s.containsBase
      (s.isQuasicoherent d) K₁.1 K₂.1 ⟨K₁.2.1, K₁.2.2.1⟩ ⟨K₂.2.1, K₂.2.2.1⟩).1,
    (isQuasicoherentOnSite_isFiniteType_sup s.site s.base s.containsBase
      (s.isQuasicoherent d) K₁.1 K₂.1 ⟨K₁.2.1, K₁.2.2.1⟩ ⟨K₂.2.1, K₂.2.2.1⟩).2,
    sup_le K₁.2.2.2 K₂.2.2.2⟩

/-- The first submodule lies in the supremum. -/
theorem le_sup_left (K₁ K₂ : FiniteTypeDegreeSubmodule I d) : K₁.1 ≤ (sup K₁ K₂).1 :=
  _root_.le_sup_left

/-- The second submodule lies in the supremum. -/
theorem le_sup_right (K₁ K₂ : FiniteTypeDegreeSubmodule I d) : K₂.1 ≤ (sup K₁ K₂).1 :=
  _root_.le_sup_right

/-- The kernel of `𝒜|_T ⟶ (𝒜/𝒦𝒜)|_T` in degree `d`, for `𝒦 ⊆ ℐ_d`. -/
abbrev chartKernel (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)
    (K : FiniteTypeDegreeSubmodule I d) :
    ((s.relativeProjPoints.algebra T f).piece d).Submodule :=
  ((GradedIdeal.ofDegree s K.1 K.2.1).chartKernel T f).piece d

/-- The chart kernel in degree `d` is monotone in the finite type submodule `𝒦`. -/
theorem chartKernel_mono (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) {K K' : FiniteTypeDegreeSubmodule I d} (h : K.1 ≤ K'.1) :
    chartKernel T f K ≤ chartKernel T f K' :=
  (GradedIdeal.ofDegree s K.1 K.2.1).chartKernel_mono T f
    (ofDegree_piece_mono (F := K.1) (F' := K'.1) K.2.1 K'.2.1 h) d

/-- The chart kernels in degree `d` form a directed family. -/
theorem directed_chartKernel (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    Directed (· ≤ ·) (chartKernel (I := I) (d := d) T f) := fun K₁ K₂ =>
  ⟨sup K₁ K₂, chartKernel_mono T f (le_sup_left K₁ K₂), chartKernel_mono T f (le_sup_right K₁ K₂)⟩

end FiniteTypeDegreeSubmodule

variable (hZ : s.site.Contains (⊤_ Scheme.{u}))
  (hXqc : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
  (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase hZ s.space.1)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)

include hXqc hXqs hf in
/-- Over an affine open of the chart, a section of the kernel of `𝒜|_T ⟶ (𝒜/ℐ)|_T` lies in the
kernel for `𝒜/𝒦𝒜` with `𝒦 ⊆ ℐ_d` quasi-coherent of finite type. -/
theorem exists_mem_chartKernel_of_isAffineOpen (I : s.GradedIdeal) {d : ℤ}
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens} (hW : IsAffineOpen W)
    {y : Γ((s.relativeProjPoints.algebra T f).piece d, W)}
    (hy : ((I.quotientHomPoints.hom T f).app d).app W y = 0) :
    ∃ K : FiniteTypeDegreeSubmodule I d,
      y ∈ (FiniteTypeDegreeSubmodule.chartKernel T f K).obj (op W) := by
  obtain ⟨K, hKq, hKf, hKI, hK⟩ := exists_finiteType_le_mem_of_isAffine hZ hXqc hXqs
    (I.isQuasicoherent d) (s.etalePointChart f hf W) (isAffine_etalePointChart s f hf hW)
    ((I.quotientHomPoints_app_eq_zero_iff f hf d W y).1 hy)
  exact ⟨⟨K, hKq, hKf, hKI⟩, ((GradedIdeal.ofDegree s K hKq).mem_chartKernel_iff T f d W y).2
    (((GradedIdeal.ofDegree s K hKq).quotientHomPoints_app_eq_zero_iff f hf d W y).2
      (_root_.SheafOfModules.Submodule.le_iff.1 (le_generatedInDegree_self K) _ hK))⟩

include hXqc hXqs hf in
/-- **The finite type approximation on a chart (Stacks 0829).**
On an affine étale chart `T` of a qcqs base, a finite type `ℱ' ⊆ 𝒜|_T` in degree `d` contained in
the kernel of `𝒜|_T ⟶ (𝒜/ℐ)|_T` lies in the kernel of `𝒜|_T ⟶ (𝒜/ℱ𝒜)|_T` for a quasi-coherent
`ℱ ⊆ ℐ_d` of finite type. -/
theorem exists_finiteType_le_chartKernel
    [CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)]
    (I : s.GradedIdeal) {d : ℤ} (ℱ : ((s.relativeProjPoints.algebra T f).piece d).Submodule)
    (hℱ : SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules)
    (hle : ℱ ≤ (I.chartKernel T f).piece d) :
    ∃ (F : (s.algebra.piece d).Submodule) (hF : F.toSheafOfModules.IsQuasicoherentOnSite),
      F.toSheafOfModules.IsFiniteType ∧ F ≤ I.piece d ∧
        ℱ ≤ ((GradedIdeal.ofDegree s F hF).chartKernel T f).piece d := by
  have hloc : ∀ (V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (x : ((s.relativeProjPoints.algebra T f).piece d).val.obj (op V)), x ∈ ℱ.obj (op V) →
      ∃ R : Sieve V, R ∈ Opens.grothendieckTopology _ V ∧
        ∀ ⦃Y : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens⦄ (g : Y ⟶ V),
          R g → ∃ K : FiniteTypeDegreeSubmodule I d,
            ((s.relativeProjPoints.algebra T f).piece d).val.map g.op x ∈
            (FiniteTypeDegreeSubmodule.chartKernel T f K).obj (op Y) := by
    intro V x hx
    refine ⟨⟨fun W g => ∃ K : FiniteTypeDegreeSubmodule I d,
        ((s.relativeProjPoints.algebra T f).piece d).val.map g.op x ∈
          (FiniteTypeDegreeSubmodule.chartKernel T f K).obj (op W), ?_⟩, ?_, fun _ _ h => h⟩
    · rintro W W' g ⟨K, hK⟩ h
      refine ⟨K, ?_⟩
      rw [op_comp, PresheafOfModules.map_comp_apply]
      exact (FiniteTypeDegreeSubmodule.chartKernel T f K).map_mem h.op hK
    intro p hp
    obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ :=
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).isBasis_affineOpens
        |>.exists_subset_of_mem_open hp V.2
    refine ⟨W, homOfLE hWV, ?_, hpW⟩
    have hyℱ := ℱ.map_mem (homOfLE hWV).op hx
    exact exists_mem_chartKernel_of_isAffineOpen hZ hXqc hXqs T f hf I hW
      ((I.mem_chartKernel_iff T f d W _).1 (_root_.SheafOfModules.Submodule.le_iff.1 hle _ hyℱ))
  obtain ⟨K, hK⟩ := Stacks.SheafOfModules.exists_le_of_isFiniteType_of_compactSpace_scheme
    (FiniteTypeDegreeSubmodule.chartKernel T f) (FiniteTypeDegreeSubmodule.directed_chartKernel T f)
    ℱ hℱ hloc
  exact ⟨K.1, K.2.1, K.2.2.1, K.2.2.2, hK⟩

end Approximation

section Main

variable (hZ : s.site.Contains (⊤_ Scheme.{u}))
  (hXqc : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
  (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase hZ s.space.1)
  (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

include hXqc hXqs in
/-- **Stacks 085M, granted the ideal of Stacks 085L.**  Let `ℐ ⊆ 𝒜` be a quasi-coherent graded
ideal whose restriction to every étale scheme point `T ⟶ X` has the sections of the graded ideal
of Stacks 0801 of `Z ×_X T ⊆ Proj_T(𝒜|_T)`.  If `X` is quasi-compact and quasi-separated, `π` is
quasi-compact and `i` is locally of finite presentation, there are `d > 0` and a quasi-coherent
`ℱ ⊆ 𝒜_d` of finite type with `Z = Proj_X(𝒜/ℱ𝒜)` over `Proj_X(𝒜)`. -/
theorem exists_finiteType_iso_quotientProjHom_of_gradedIdeal
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
    ∃ d : ℕ, 0 < d ∧ ∃ (F : (s.algebra.piece (d : ℤ)).Submodule)
      (hF : F.toSheafOfModules.IsQuasicoherentOnSite), F.toSheafOfModules.IsFiniteType ∧
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
    refine GradedIdeal.le_of_forall_mem_opens T f fun W a ha => ?_
    exact (I.mem_chartKernel_iff T f _ W a).2
      ((hI T f hf _ W a).1 (_root_.SheafOfModules.Submodule.le_iff.1 hle _ ha))
  obtain ⟨F, hF, hFf, hFI, hℱF⟩ := exists_finiteType_le_chartKernel hZ hXqc hXqs T f hf I ℱ hft hleI
  refine ⟨d, hd, F, hF, hFf, ?_⟩
  set J := GradedIdeal.ofDegree s F hF
  have hJI : ∀ n, J.piece n ≤ I.piece n := fun n => Ideal.ofDegree_le F s.mul_comm I.toIdeal hFI n
  have hsub : ∀ n : ℤ, (J.chartKernel T f).piece n ≤ (twistKerGradedIdeal A D
      (chartClosedSubscheme i hi T f)).piece n := by
    intro n
    refine (J.chartKernel_mono T f hJI n).trans ?_
    refine GradedIdeal.le_of_forall_mem_opens T f fun W a ha => ?_
    exact (hI T f hf n W a).2 ((I.mem_chartKernel_iff T f n W a).1 ha)
  refine exists_iso_quotientProjHom_of_chart_ker J i hi T f hfE hfS ?_
  exact (ker_relativeMapHom_eq_ker_projQuotientHom _
    (J.surjectiveOnAffineSections_quotientHomPoints T f) (J.chartKernel T f)
    (J.mem_chartKernel_iff T f)).trans (hcut (J.chartKernel T f) hℱF hsub).symm

end Main

end AlgebraicGeometry.Space.RelativeProjSituation

end
