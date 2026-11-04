module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackModuleHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# An invertible module is trivialised by one surjective étale morphism

Let `U` be a scheme of the big fppf site of `S` and let `N` be an invertible `𝒪_U`-module on the
small étale site of the algebraic space `U` represents.  By Stacks 0B8Q on the small étale site,
`N` is trivial over the members of a covering sieve of every étale chart.  This file assembles
such local trivialisations into a single one: there is **one** surjective étale morphism
`q : c ⟶ U` of the site with `𝒪_c ≅ q^*N`.

## Main results

* `AlgebraicGeometry.Space.nonempty_structureModule_iso_chartModuleRestriction`: a
  trivialisation of an `𝒪_X`-module on the slice of the small étale site at an étale chart `V` is
  a trivialisation of its pullback to the algebraic space `V` represents.
* `AlgebraicGeometry.Space.exists_etaleCover_modulePullback_iso_structureModule`: an invertible
  module on a scheme `U` is trivial after pullback along each member of a family of étale
  morphisms out of affine schemes of the site which covers `U` and is bounded in size by `U`.
* `AlgebraicGeometry.Space.hom_ext_of_isEmpty_chartScheme`: on an algebraic space all of whose
  étale charts are empty any two homomorphisms of modules agree.
* `AlgebraicGeometry.Space.exists_surjective_etale_modulePullback_iso_of_etaleCover`: such a
  family of trivialisations glues to a trivialisation along the induced morphism out of the
  coproduct of the family.
* `AlgebraicGeometry.Space.exists_surjective_etale_modulePullback_iso_structureModule`: **an
  invertible module on a scheme of the big fppf site is trivialised by the inverse image along
  one surjective étale morphism of the site.**

## Implementation notes

*From the slice to the chart.*  Triviality is delivered by
`AlgebraicGeometry.Space.exists_covering_unitIso_of_isInvertible` on slices `X_étale/V`, whereas
the statement is about the pullback of modules of Stacks 03LU along `V ⟶ X`.
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso` identifies the two, and the reindexing
`AlgebraicGeometry.Space.chartModuleSliceReindex` carries the unit module of the slice to the
structure module of the chart on the nose.

*Size.*  The coproduct of a family lies in the site only under a uniform size bound
(`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`).  Indexing the charts by
the points of `U` would not do, as a scheme may have more points than its size; instead every
affine open `A` of `U` is covered by finitely many affine trivialising charts
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`), so the index type
is bounded by `#U.affineOpens * ℵ₀`, and each member, being quasi-compact and étale over `U`, by
the size of `U` (`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`).

*Gluing.*  The trivialisations of the members are glued along the open immersions `j_i` of the
members into the coproduct `c` by descent of homomorphisms of quasi-coherent modules,
`AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible`, applied
to the trivialisations and to their inverses
(`AlgebraicGeometry.Space.ModuleHomFamilyCompatible.inv`).  Compatibility on
overlaps is automatic: two members `j_i`, `j_i'` with `i ≠ i'` are disjoint, so an algebraic space
mapping compatibly to both has only empty étale charts, and for `i = i'` the two maps agree because
`j_i` is a monomorphism.

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### From a trivialisation on a slice to a trivialisation on the chart -/

/-- **A trivialisation of an `𝒪_X`-module on the slice `X_étale/V` at an étale chart `V` is a
trivialisation of its pullback to the algebraic space `V` represents.**  The pullback of modules
along `V ⟶ X` is restriction to the slice read through the comparison of Stacks 04M0
(`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`), and that reading carries the unit
module of the slice to the structure module of the chart on the nose. -/
theorem nonempty_structureModule_iso_chartModuleRestriction (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (e : SheafOfModules.unit ((structureRingSheaf B S hS X).over V) ≅ M.over V) :
    Nonempty (structureModule (chartSpace B S hS X V) ≅
      (chartModuleRestriction B S hS X V).obj M) :=
  ⟨(chartModuleSliceReindex B S hS X V).mapIso e ≪≫
    ((chartModuleRestrictionSliceIso B S hS X V).app M).symm⟩

/-! ### A bounded étale covering by trivialising affine charts -/

open Cardinal in
/-- **An invertible module on a scheme `U` of the site is trivial after pullback along each member
of a bounded étale covering of `U` by affine schemes of the site.**  The family consists of
étale morphisms `g i : X i ⟶ U` whose images cover `U`; it is indexed by a type of cardinality at
most the size of `U`, and every `X i` has size at most the size of `U`.

Every affine open `A` of `U` is an affine étale chart of the algebraic space `U` represents
(`AlgebraicGeometry.Space.openChart` of the identity chart), the module is trivial over the
members of a covering sieve of that chart (Stacks 0B8Q,
`AlgebraicGeometry.Space.exists_covering_unitIso_of_isInvertible`), and finitely many affine
members of that sieve cover `A`
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`). -/
theorem exists_etaleCover_modulePullback_iso_structureModule (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : IsInvertibleModule (schemeSpace U) N) :
    ∃ (ι : Type u) (X : ι → BigFppfOver B S hS) (g : ∀ i, X i ⟶ U),
      (∀ i, Etale ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj U,
        ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i))) ∧
      #ι ≤ ((BigFppfOver.toScheme B S hS).obj U).size ∧
      (∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤
        ((BigFppfOver.toScheme B S hS).obj U).size) ∧
      ∀ i, Nonempty (structureModule (schemeSpace (X i)) ≅
        (modulePullback B S hS (schemeSpaceMap (g i))).obj N) := by
  classical
  set Y : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj U with hYdef
  let t : SmallEtale B S hS (schemeSpace U).1 := idEtaleChart B S hS U
  let xA : Y.affineOpens → SmallEtale B S hS (schemeSpace U).1 := fun A =>
    openChart B S hS (schemeSpace U).1 t A.1
  have hxA : ∀ A, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (schemeSpace U).1).obj (xA A))) := fun A =>
    inferInstanceAs (IsAffine (A.1 : Scheme.{u}))
  have hinv := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN
  choose T hT htriv using fun A =>
    exists_covering_unitIso_of_isInvertible B S hS (schemeSpace U) N hinv (xA A)
  choose n z φ hzaff hzT hzcov hzet using fun A =>
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS _ (hxA A) (hT A)
  let ψ : ∀ i : (Σ A : Y.affineOpens, Fin (n A)), z i.1 i.2 ⟶ t := fun i =>
    φ i.1 i.2 ≫ openChartInclusion B S hS (schemeSpace U).1 t i.1.1
  let X : (Σ A : Y.affineOpens, Fin (n A)) → BigFppfOver B S hS := fun i =>
    (SmallEtale.toOver B S hS (schemeSpace U).1).obj (z i.1 i.2)
  let g : ∀ i, X i ⟶ U := fun i => (SmallEtale.toOver B S hS (schemeSpace U).1).map (ψ i)
  have hget : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (g i)) := fun i =>
    etale_toScheme_toOver_map B S hS _ (ψ i)
  refine ⟨Σ A : Y.affineOpens, Fin (n A), X, g, hget, ?_, ?_, ?_, ?_⟩
  · intro y
    have hy : y ∈ (⊤ : Y.Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨A, hA⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨k, w, hw⟩ := (Scheme.ofArrows_mem_etalePrecoverage_iff.mp (hzet A)).1 ⟨y, hA⟩
    refine ⟨⟨A, k⟩, w, ?_⟩
    have h2 := toScheme_map_toOver_map_openChartInclusion B S hS (schemeSpace U).1 t A.1
    show ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map
      (openChartInclusion B S hS (schemeSpace U).1 t A.1))) (((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS _).map (φ A k))) w) = y
    rw [hw, h2]
    rfl
  · have h1 : #(Σ A : Y.affineOpens, Fin (n A)) ≤ #(Y.affineOpens × ULift.{u} ℕ) := by
      refine mk_le_of_injective (f := fun i => (i.1, ULift.up (i.2 : ℕ))) ?_
      rintro ⟨A, k⟩ ⟨A', k'⟩ h
      simp only [Prod.mk.injEq, ULift.up.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact congrArg (Sigma.mk A) (Fin.ext h)
    refine h1.trans ?_
    have hN : #(ULift.{u} ℕ) = ℵ₀ := by simp
    rw [mk_prod, lift_id, lift_id, hN]
    exact (mul_le_max _ _).trans (max_le (max_le (Scheme.mk_affineOpens_le_size Y)
      (Scheme.aleph0_le_size Y)) (Scheme.aleph0_le_size Y))
  · intro i
    have := hzaff i.1 i.2
    have := hget i
    exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (g i))
  · intro i
    obtain ⟨e⟩ := htriv i.1 (φ i.1 i.2) (hzT i.1 i.2)
    obtain ⟨e'⟩ := nonempty_structureModule_iso_chartModuleRestriction (schemeSpace U) N
      (z i.1 i.2) e
    have hhom : chartToSpace B S hS (schemeSpace U) (z i.1 i.2) = schemeSpaceMap (g i) := by
      apply ObjectProperty.hom_ext
      exact (CostructuredArrow.w (ψ i).hom).symm.trans (Category.comp_id _)
    exact ⟨e' ≪≫ eqToIso (congrArg (fun f => (modulePullback B S hS f).obj N) hhom)⟩

/-! ### Gluing along the coproduct -/

/-- **On an algebraic space all of whose étale charts are empty, any two homomorphisms of modules
agree**: the sections of a module over an empty chart vanish, the empty sieve covering it
(`AlgebraicGeometry.Space.eq_zero_of_isEmpty_chart`). -/
theorem hom_ext_of_isEmpty_chartScheme {Y : AlgebraicSpaces B S hS}
    (hY : ∀ W : SmallEtale B S hS Y.1, IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj W)))
    {M P : Modules.{u, u} B S hS Y.1 Y.2} (f f' : M ⟶ P) : f = f' := by
  ext W x
  have h := fun σ => eq_zero_of_isEmpty_chart B S hS ⟨P.val.presheaf, P.isSheaf⟩ W.unop
    (hY W.unop) σ
  exact (h _).trans (h _).symm

open Cardinal in
/-- **Trivialisations along a bounded étale covering glue to one along a single surjective étale
morphism.**  Let `g i : X i ⟶ U` be étale morphisms of the site whose images cover `U`, indexed
by a type of cardinality at most `μ` with every `X i` of size at most `μ`, for a cardinal `μ` below
the cutoff, and let `N` be a quasi-coherent `𝒪_U`-module with `𝒪_{X i} ≅ (g i)^*N` for every
`i`.  Then the morphism `q : c ⟶ U` out of the coproduct `c` of the `X i` induced by the `g i` is
surjective and étale, and `𝒪_c ≅ q^*N`.

The trivialisations, read along the open immersions `j_i : X i ⟶ c`, descend together with their
inverses by Descent, Proposition 023T for quasi-coherent modules
(`AlgebraicGeometry.Space.existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible`): on an
overlap of two distinct members there is nothing to check since the `j_i` are disjoint, and a
member overlaps itself only along the diagonal since `j_i` is a monomorphism. -/
theorem exists_surjective_etale_modulePullback_iso_of_etaleCover (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : N.IsQuasicoherentOnSite) {ι : Type u} (X : ι → BigFppfOver B S hS)
    (g : ∀ i, X i ⟶ U) (hg : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (g i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ μ)
    (e : ∀ i, structureModule (schemeSpace (X i)) ≅
      (modulePullback B S hS (schemeSpaceMap (g i))).obj N) :
    ∃ (c : BigFppfOver B S hS) (q : c ⟶ U),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      Nonempty (structureModule (schemeSpace c) ≅
        (modulePullback B S hS (schemeSpaceMap q)).obj N) := by
  obtain ⟨V, j, hjopen, hjcov, ⟨hj⟩, ⟨hjsite⟩, -⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hX
  set q : V ⟶ U := Cofan.IsColimit.desc hjsite g with hqdef
  have hjq : ∀ i, j i ≫ q = g i := fun i => Cofan.IsColimit.fac hjsite g i
  have hfac : ∀ i, (BigFppfOver.toScheme B S hS).map (j i) ≫
      (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map (g i) := by
    intro i
    rw [← Functor.map_comp, hjq i]
  refine ⟨V, q, ?_, ?_, ?_⟩
  · rw [surjective_iff]
    intro t
    obtain ⟨i, y, hy⟩ := hcov t
    refine ⟨((BigFppfOver.toScheme B S hS).map (j i)) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac i, hy]
  · let 𝒰 : ((BigFppfOver.toScheme B S hS).obj V).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (BigFppfOver.toScheme B S hS).obj (X i)
        f := fun i => (BigFppfOver.toScheme B S hS).map (j i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjcov, hjopen⟩ }
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    show Etale ((BigFppfOver.toScheme B S hS).map (j i) ≫ _)
    rw [hfac i]
    exact hg i
  · classical
    have hmono : ∀ i, Mono (j i) := fun i => by
      apply (Over.forget (B.obj hS)).mono_of_mono_map
      apply B.inclusion.mono_of_mono_map
      show Mono ((BigFppfOver.toScheme B S hS).map (j i))
      have := hjopen i
      infer_instance
    set Ys : ι → Scheme.{u} := fun k => (BigFppfOver.toScheme B S hS).obj (X k) with hYs
    set eV : (∐ Ys) ≅ (BigFppfOver.toScheme B S hS).obj V :=
      (coproductIsCoproduct Ys).coconePointUniqueUpToIso hj with heV
    have hιe : ∀ i, Sigma.ι Ys i ≫ eV.hom = (BigFppfOver.toScheme B S hS).map (j i) := fun i =>
      IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Ys) hj (Discrete.mk i)
    set M := structureModule (schemeSpace V) with hM
    set P := (modulePullback B S hS (schemeSpaceMap q)).obj N with hP
    have hcomp : ∀ i, schemeSpaceMap (g i) = schemeSpaceMap (j i) ≫ schemeSpaceMap q := by
      intro i
      rw [← hjq i]
      exact (schemeSpaceFunctor B S hS).map_comp (j i) q
    let αIso : ∀ i, (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (j i))).obj M ≅
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (j i))).obj P := fun i =>
      (structureModulePullbackIso (schemeSpaceMap (j i))).symm ≪≫ e i ≪≫
        eqToIso (congrArg (fun f => (modulePullback B S hS f).obj N) (hcomp i)) ≪≫
        ((modulePullbackCompIso B S hS (schemeSpaceMap (j i)) (schemeSpaceMap q)).app N).symm
    let α : ∀ i, (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (j i))).obj M ⟶
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (j i))).obj P := fun i =>
      (αIso i).hom
    have hαiso : ∀ i, IsIso (α i) := fun i => (αIso i).isIso_hom
    have hα : ModuleHomFamilyCompatible M P
        (fun i => (schemeSpaceFunctor B S hS).map (j i)) α := by
      intro Y i i' a b h
      by_cases hii : i = i'
      · subst hii
        have hab : a = b := by
          apply ObjectProperty.hom_ext
          ext T x
          exact (cancel_mono (j i)).1 (congrArg (fun m => m.hom.app T x) h)
        subst hab
        rfl
      · refine hom_ext_of_isEmpty_chartScheme (fun W => ?_) _ _
        let a' : (SmallEtale.toOver B S hS Y.1).obj W ⟶ X i :=
          yoneda.preimage (W.1.hom ≫ a.hom)
        let b' : (SmallEtale.toOver B S hS Y.1).obj W ⟶ X i' :=
          yoneda.preimage (W.1.hom ≫ b.hom)
        have hab : a' ≫ j i = b' ≫ j i' := by
          apply yoneda.map_injective
          rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun m => W.1.hom ≫ m.hom) h).trans (Category.assoc _ _ _).symm)
        have hab' : (BigFppfOver.toScheme B S hS).map a' ≫ Sigma.ι Ys i =
            (BigFppfOver.toScheme B S hS).map b' ≫ Sigma.ι Ys i' := by
          rw [← cancel_mono eV.hom, Category.assoc, Category.assoc, hιe, hιe,
            ← Functor.map_comp, ← Functor.map_comp, hab]
        exact isEmpty_of_commSq_sigmaι_of_ne ⟨hab'⟩ hii
    have hMqc : M.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertible B S hS _ M
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (isInvertibleModule_structureModule _))
    have hPqc : P.IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (schemeSpaceMap q) N hN
    have hr : Sieve.generate (Presieve.ofArrows X j) ∈ BigFppfOver.topology B S hS V :=
      BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j hjopen hjcov
    obtain ⟨b, hb, -⟩ :=
      existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible V M P hMqc hPqc X j hr α hα
    obtain ⟨c, hc, -⟩ :=
      existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible V P M hPqc hMqc X j hr
        (fun i => CategoryTheory.inv (α i)) (hα.inv hαiso)
    have hid : ∀ {A : Modules.{u, u} B S hS _ _}, A.IsQuasicoherentOnSite → ∀ k : A ⟶ A,
        (∀ i, (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (j i))).map k = 𝟙 _) →
        k = 𝟙 A := fun hA k hk =>
      (existsUnique_modulePullback_map_eq_of_moduleHomFamilyCompatible V _ _ hA hA X j hr
        (fun i => 𝟙 _) (moduleHomFamilyCompatible_id _ _)).unique hk fun i =>
        CategoryTheory.Functor.map_id _ _
    have := hαiso
    refine ⟨⟨b, c, hid hMqc _ fun i => ?_, hid hPqc _ fun i => ?_⟩⟩ 
    · exact ((Functor.map_comp _ b c).trans (congrArg₂ (· ≫ ·) (hb i) (hc i))).trans
        (IsIso.hom_inv_id _)
    · exact ((Functor.map_comp _ c b).trans (congrArg₂ (· ≫ ·) (hc i) (hb i))).trans
        (IsIso.inv_hom_id _)

/-! ### The trivialising surjective étale morphism -/

/-- **An invertible module on a scheme of the big fppf site is trivialised by the inverse image
along one surjective étale morphism of the site.**  For a scheme `U` of the big fppf site of `S`
and an invertible `𝒪_U`-module `N` on the small étale site of the algebraic space `U` represents,
there is a surjective étale morphism `q : c ⟶ U` of the site with `𝒪_c ≅ q^*N`.

The morphism is the one out of the coproduct of the bounded family of trivialising affine charts
of `AlgebraicGeometry.Space.exists_etaleCover_modulePullback_iso_structureModule`, along which the
trivialisations glue by
`AlgebraicGeometry.Space.exists_surjective_etale_modulePullback_iso_of_etaleCover`; `N` is
quasi-coherent, being invertible
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible`). -/
theorem exists_surjective_etale_modulePullback_iso_structureModule (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    (hN : IsInvertibleModule (schemeSpace U) N) :
    ∃ (c : BigFppfOver B S hS) (q : c ⟶ U),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      Nonempty (structureModule (schemeSpace c) ≅
        (modulePullback B S hS (schemeSpaceMap q)).obj N) := by
  obtain ⟨ι, X, g, hg, hcov, hι, hX, he⟩ :=
    exists_etaleCover_modulePullback_iso_structureModule U N hN
  have e := fun i => (he i).some
  exact exists_surjective_etale_modulePullback_iso_of_etaleCover U N
    (isQuasicoherentOnSite_of_isInvertible B S hS _ N
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN))
    X g hg hcov U.left.property hι hX e

end AlgebraicGeometry.Space

end
