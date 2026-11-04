module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationEtaleDescent

/-!
# Finite presentation is local on an open covering

Let `X` be an algebraic space covered by open immersions `j_k : U_k ⟶ X`.  An `𝒪_X`-module whose
restriction to every `U_k` is of finite presentation on the small étale site is of finite
presentation.  Every étale chart `V` of `X` is covered by its Zariski-open charts lying over the
`U_k`; such a chart is the composite of an étale chart of `U_k` with `j_k`, and over it the module
has finite global presentations locally, because its restriction to `U_k` has, and a finite global
presentation is carried across the slice equivalence of Stacks 04M0
(`AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_postcomp`).

## Main results

* `SheafOfModules.IsFinitePresentationOnSite.of_isZero`: a zero module is of finite presentation.
* `AlgebraicGeometry.Space.SmallEtale.generate_openChart_mem`: the Zariski-open charts of a chart
  lying over the members of an open covering cover it.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isOpenImmersion_cover`: finite
  presentation is local on an open covering.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SheafOfModules

universe v r m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A zero sheaf of modules has a finite global presentation**: it is the cokernel of the zero
map between two empty coproducts of copies of the structure sheaf. -/
theorem hasFiniteGlobalPresentation_of_isZero {M : SheafOfModules.{m} R} (hM : IsZero M) :
    M.HasFiniteGlobalPresentation := by
  have hP : IsZero (uliftForPresentation.{u, v, r, m, max u v r} M) :=
    isZero_uliftForPresentation hM
  refine ⟨0, 0, uliftForPresentation.{u, v, r, m, max u v r} M,
    uliftForPresentation.{u, v, r, m, max u v r} M,
    fun i => i.elim0, fun i => i.elim0, ⟨?_⟩, ⟨?_⟩, 0, 0, by rw [zero_comp], ⟨?_⟩⟩
  iterate 2
    exact Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => j.elim0) (fun _ k _ => hP.eq_of_src k 0)
  · exact Cofork.IsColimit.mk _ (fun _ => 0)
      (fun s => by rw [comp_zero]; exact hP.eq_of_src 0 s.π)
      (fun _ k _ => hP.eq_of_src k 0)

/-- **A zero sheaf of modules is of finite presentation**: every object of the site is covered
by itself, and the restriction of a zero module to a slice is again zero. -/
theorem IsFinitePresentationOnSite.of_isZero {M : SheafOfModules.{m} R} (hM : IsZero M) :
    M.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation U := by
    refine ⟨ULift.{max u v} PUnit, fun _ => U, fun _ => 𝟙 U, ?_,
      fun _ => hasFiniteGlobalPresentation_of_isZero (isZero_over hM U)⟩
    have htop : Sieve.ofArrows (fun _ : ULift.{max u v} PUnit => U) (fun _ => 𝟙 U) = ⊤ := by
      refine le_antisymm le_top fun Z g _ => ?_
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨ULift.up PUnit.unit, g, by simp⟩
    rw [htop]
    exact J.top_mem U

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

attribute [local instance] pointTopology

/-! ### Charts lying over an open subspace -/

/-- **An étale chart whose points lie in the image of an open immersion is the composite of an
étale chart of the open subspace with the open immersion.** -/
theorem exists_smallEtalePostcomp_iso_of_range_subset (f : Y ⟶ X)
    (hf : IsOpenImmersion B S hS f.hom) (V : SmallEtale B S hS X.1)
    (hV : Set.range (pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom) ⊆
      Set.range (pointsMap B S hS Y.1 f.hom)) :
    ∃ A : SmallEtale B S hS Y.1,
      Nonempty ((smallEtalePostcomp B S hS f (isEtale_of_isOpenImmersion B S hS hf)).obj A ≅
        V) := by
  obtain ⟨a, ha⟩ := (factorsThrough_isOpenImmersion_iff_points B S hS Y.2 X.2
    (isAlgebraicSpace_yoneda B S hS V.obj.left) f.hom hf V.obj.hom).mpr hV
  have hchart : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk a) :=
    isEtaleChart_of_comp_etale B S hS f (isEtale_of_isOpenImmersion B S hS hf) a
      (by rw [ha]; exact V.property)
  refine ⟨⟨CostructuredArrow.mk a, hchart⟩, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom]
    exact ha.symm)

/-- **The two halves of a chart cut out by an open covering cover it.**  For a family of open
sets of points of `X` covering it, the Zariski-open charts of an étale chart `V` lying over the
members of the family form a covering of `V` in the small étale site. -/
theorem SmallEtale.generate_openChart_mem {ι : Type u} (V : SmallEtale B S hS X.1)
    (W : ι → Set (points B S hS X.1)) (hW : ∀ i, IsOpen (W i))
    (hcov : ∀ x, ∃ i, x ∈ W i) :
    Sieve.generate (Presieve.ofArrows
        (fun i ↦ openChart B S hS X.1 V
          ⟨(fun z ↦ pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
            ((schemePointsHomeomorph B S hS V.obj.left).symm z)) ⁻¹' W i,
            ((hW i).preimage ((continuous_pointsMap B S hS V.obj.hom).comp
              (schemePointsHomeomorph B S hS V.obj.left).symm.continuous))⟩)
        (fun _ ↦ openChartInclusion B S hS X.1 V _)) ∈
      SmallEtale.topology B S hS X.1 V := by
  set O : ι → ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Opens :=
    fun i ↦ ⟨(fun z ↦ pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
            ((schemePointsHomeomorph B S hS V.obj.left).symm z)) ⁻¹' W i,
            ((hW i).preimage ((continuous_pointsMap B S hS V.obj.hom).comp
              (schemePointsHomeomorph B S hS V.obj.left).symm.continuous))⟩ with hO
  set E : PreZeroHypercover.{u + 1} V :=
    { I₀ := ULift.{u + 1} ι
      X := fun i ↦ openChart B S hS X.1 V (O i.down)
      f := fun i ↦ openChartInclusion B S hS X.1 V (O i.down) }
  have hcovE : _root_.AlgebraicGeometry.IsEtaleCovering
      (⟨(SmallEtale.toSchemes B S hS X.1).obj V, E.map (SmallEtale.toSchemes B S hS X.1)⟩ :
        Covering B.Schemes) := by
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
      ((E.map (SmallEtale.toSchemes B S hS X.1)).map B.inclusion)).2 ⟨?_, ?_⟩
    · intro x
      obtain ⟨i, hi⟩ := hcov (pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
        ((schemePointsHomeomorph B S hS V.obj.left).symm x))
      refine ⟨ULift.up i, ?_⟩
      have heq := toScheme_map_toOver_map_openChartInclusion B S hS X.1 V (O i)
      obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (X := (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj V)) (O i)).ge hi
      refine ⟨y, ?_⟩
      change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map
        (openChartInclusion B S hS X.1 V (O i)))) y = x
      rw [heq]
      exact hy
    · intro i
      exact etale_toScheme_toOver_map B S hS X.1 (openChartInclusion B S hS X.1 V (O i.down))
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS X.1 V := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact B.presieve₀_mem_etalePrecoverage _ hcovE
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hpre)
  rintro Z g ⟨T, h, k, hk, rfl⟩
  obtain ⟨i⟩ := hk
  exact ⟨_, h, _, Presieve.ofArrows.mk i.down, rfl⟩

/-- The points of the Zariski-open chart of `V` over an open set `W` of points of `X` lie in
`W`. -/
theorem range_pointsMap_openChart_subset (V : SmallEtale B S hS X.1)
    (W : Set (points B S hS X.1)) (hW : IsOpen W) :
    Set.range (pointsMap B S hS (yoneda.obj (openChart B S hS X.1 V
        ⟨(fun z ↦ pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
            ((schemePointsHomeomorph B S hS V.obj.left).symm z)) ⁻¹' W,
            (hW.preimage ((continuous_pointsMap B S hS V.obj.hom).comp
              (schemePointsHomeomorph B S hS V.obj.left).symm.continuous))⟩).obj.left)
        (openChart B S hS X.1 V _).1.hom) ⊆ W := by
  rw [range_pointsMap_openChart]
  rintro _ ⟨p, hp, rfl⟩
  have hp' : pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
      ((schemePointsHomeomorph B S hS V.obj.left).symm (pointsToScheme B S hS V.obj.left p)) ∈
        W := hp
  rwa [← schemePointsHomeomorph_apply, Homeomorph.symm_apply_apply] at hp'

/-! ### Finite presentation is local on an open covering -/

/-- The sieve of the arrows into a chart from the charts over which a module has a finite global
presentation. -/
def finiteGlobalPresentationSieve (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) : Sieve V where
  arrows Z _ := (M.over Z).HasFiniteGlobalPresentation
  downward_closed {_ _} _ hZ g :=
    Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap M g hZ

/-- **Over a chart lying over an open subspace on which the module is of finite presentation, the
module has finite global presentations locally.** -/
theorem finiteGlobalPresentationSieve_mem_of_range_subset (f : Y ⟶ X)
    (hf : IsOpenImmersion B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : ((etaleModulePullback B S hS f
      (isEtale_of_isOpenImmersion B S hS hf)).obj M).IsFinitePresentationOnSite)
    (V : SmallEtale B S hS X.1)
    (hV : Set.range (pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom) ⊆
      Set.range (pointsMap B S hS Y.1 f.hom)) :
    finiteGlobalPresentationSieve B S hS M V ∈ SmallEtale.topology B S hS X.1 V := by
  have hfe := isEtale_of_isOpenImmersion B S hS hf
  obtain ⟨A, ⟨e⟩⟩ := exists_smallEtalePostcomp_iso_of_range_subset B S hS f hf V hV
  obtain ⟨I, Z, g, hcov, hpres⟩ := hM.locally_hasFiniteGlobalPresentation A
  have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS f hfe).cover_preserve hcov
  have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS f hfe) (Sieve.ofArrows Z g) ≤
      finiteGlobalPresentationSieve B S hS M ((ringedSitePostcomp B S hS f hfe).obj A) := by
    rintro T p ⟨Z₀, p₀, q, hp₀, rfl⟩
    obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hp₀
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      M (q ≫ (ringedSitePostcomp B S hS f hfe).map b)
      (hasFiniteGlobalPresentation_over_postcomp B S hS f hfe M (Z i) (hpres i))
  have hmem := (SmallEtale.topology B S hS X.1).pullback_stable e.inv
    ((SmallEtale.topology B S hS X.1).superset_covering hle hpush)
  exact hmem

/-- **Finite presentation on the small étale site is local on an open covering.**  If `X` is
covered by a family of open immersions `j_k : U_k ⟶ X` and the restriction of an `𝒪_X`-module to
each `U_k` is of finite presentation, then the module is of finite presentation. -/
theorem isFinitePresentationOnSite_of_isOpenImmersion_cover {ι : Type u}
    {U : ι → AlgebraicSpaces B S hS} (j : ∀ k, U k ⟶ X)
    (hj : ∀ k, IsOpenImmersion B S hS (j k).hom)
    (hcov : ∀ x : points B S hS X.1, ∃ k, x ∈ Set.range (pointsMap B S hS (U k).1 (j k).hom))
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ k, ((etaleModulePullback B S hS (j k)
      (isEtale_of_isOpenImmersion B S hS (hj k))).obj M).IsFinitePresentationOnSite) :
    M.IsFinitePresentationOnSite := by
  refine ⟨fun V ↦ ?_⟩
  refine ⟨{p : Σ Z : (smallEtaleRingedSite B S hS X.1 X.2).C, Z ⟶ V //
      (M.over p.1).HasFiniteGlobalPresentation}, fun p ↦ p.1.1, fun p ↦ p.1.2, ?_,
    fun p ↦ p.2⟩
  have hR := SmallEtale.generate_openChart_mem B S hS V
    (fun k ↦ Set.range (pointsMap B S hS (U k).1 (j k).hom))
    (fun k ↦ isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hj k)) hcov
  have hSieve : finiteGlobalPresentationSieve B S hS M V ∈
      SmallEtale.topology B S hS X.1 V := by
    refine (SmallEtale.topology B S hS X.1).transitive hR _ ?_
    rintro Z g ⟨T, q, k, ⟨i⟩, rfl⟩
    have hrange : Set.range (pointsMap B S hS (yoneda.obj Z.obj.left) Z.obj.hom) ⊆
        Set.range (pointsMap B S hS (U i).1 (j i).hom) := by
      have hw : yoneda.map q.hom.left ≫ (openChart B S hS X.1 V _).obj.hom = Z.obj.hom :=
        CostructuredArrow.w q.hom
      rw [← hw, pointsMap_comp, Set.range_comp]
      exact (Set.image_subset_range _ _).trans (range_pointsMap_openChart_subset B S hS V
        (Set.range (pointsMap B S hS (U i).1 (j i).hom))
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (hj i)))
    exact finiteGlobalPresentationSieve_mem_of_range_subset B S hS (j i) (hj i) M (h i) Z hrange
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hSieve
  intro Z g hg
  exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨⟨Z, g⟩, hg⟩, 𝟙 _, (Category.id_comp _).symm⟩

end AlgebraicGeometry.Space

end
