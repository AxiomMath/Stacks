module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoProjectionDescent

/-!
# Local finiteness of the weakly associated points, from one surjective chart to every chart

If the weakly associated points of the scheme of one surjective étale chart of `Y` are locally
finite, then so are those of the scheme of every étale chart of `Y`; the latter is
`AlgebraicGeometry.Space.HasLocallyFiniteWeaklyAssociatedPointsOnCharts`.

## Main results

* `AlgebraicGeometry.exists_isOpen_finite_preimage_inter_of_locallyQuasiFinite`: the preimage of
  a locally finite set of points of a scheme under a locally quasi-finite morphism is locally
  finite.
* `AlgebraicGeometry.schemeWeaklyAssociatedPoints_eq_preimage_of_etale`: along an étale morphism
  of schemes the weakly associated points are the inverse image of those of the target.
* `AlgebraicGeometry.Space.hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart`:
  local finiteness of the weakly associated points on the scheme of one surjective étale chart
  gives it on the scheme of every étale chart.

## References

* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 02NH](https://stacks.math.columbia.edu/tag/02NH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be a morphism of schemes, locally of finite type and locally quasi-finite, and
let `Z` be a set of points of `Y` such that every point of `Y` has an open neighbourhood meeting
`Z` in a finite set. Then every point of `X` has an open neighbourhood meeting `f⁻¹ Z` in a
finite set. -/
@[stacks 02NH "the preimage of a locally finite set under a locally quasi-finite morphism"]
theorem exists_isOpen_finite_preimage_inter_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {Z : Set Y}
    (hZ : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ (Z ∩ (W : Set Y)).Finite) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ (f.base ⁻¹' Z ∩ (Ω : Set X)).Finite := by
  obtain ⟨W, hxW, hWfin⟩ := hZ (f.base x)
  obtain ⟨W₀, hW₀aff, hxW₀, hW₀W⟩ := exists_isAffineOpen_mem_and_subset hxW
  obtain ⟨Ω, hΩaff, hxΩ, hΩW₀⟩ := exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ W₀) hxW₀
  refine ⟨Ω, hxΩ, ?_⟩
  let : IsAffine W₀.toScheme := hW₀aff
  let : IsAffine Ω.toScheme := hΩaff
  have he : Ω ≤ f ⁻¹ᵁ W₀ := hΩW₀
  have hfib : ∀ w : W₀.toScheme, ((f.resLE W₀ Ω he).base ⁻¹' {w}).Finite :=
    ((quasiFinite_conditions_iff_finite_fibers (f.resLE W₀ Ω he)).mp
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩).2
  have hcover : f.base ⁻¹' Z ∩ (Ω : Set X) ⊆
      ⋃ y ∈ Z ∩ (W₀ : Set Y), f.base ⁻¹' {y} ∩ (Ω : Set X) := by
    rintro p ⟨hpZ, hpΩ⟩
    exact Set.mem_biUnion ⟨hpZ, hΩW₀ hpΩ⟩ ⟨rfl, hpΩ⟩
  refine Set.Finite.subset
    ((hWfin.subset (Set.inter_subset_inter_right _ hW₀W)).biUnion fun y hy => ?_) hcover
  refine Set.Finite.subset ((hfib ⟨y, hy.2⟩).image Subtype.val) ?_
  rintro p ⟨hp, hpΩ⟩
  exact ⟨⟨p, hpΩ⟩, Subtype.ext ((Scheme.Hom.coe_resLE_apply f he ⟨p, hpΩ⟩).trans hp), rfl⟩

/-- For an étale morphism of schemes `f : X ⟶ Y`, the weakly associated points of `X` are the
preimage under `f` of the weakly associated points of `Y`. -/
@[stacks 05FP "the weakly associated points of a scheme etale over another, at the structure
sheaf"]
theorem schemeWeaklyAssociatedPoints_eq_preimage_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] :
    Stacks.Divisors.schemeWeaklyAssociatedPoints X =
      f.base ⁻¹' Stacks.Divisors.schemeWeaklyAssociatedPoints Y := by
  have : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward.{u} (Scheme.Hom.toRingCatSheafHom f)).IsRightAdjoint :=
    ⟨_, ⟨Scheme.Modules.pullbackPushforwardAdjunction f⟩⟩
  let e : (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom)
  refine Set.ext fun x => (isWeaklyAssociatedPoint_iff_of_iso e x).symm.trans ?_
  exact isWeaklyAssociatedPoint_pullback_iff_of_etale f (SheafOfModules.unit Y.ringCatSheaf) x

namespace Space

/-- Let `V₀` be a surjective étale chart of `Y`. If every point of the scheme of `V₀` has an open
neighbourhood containing only finitely many weakly associated points, then the same holds on the
scheme of every étale chart of `Y`, i.e.
`AlgebraicGeometry.Space.HasLocallyFiniteWeaklyAssociatedPointsOnCharts` holds. -/
theorem hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V₀ : SmallEtale B S hS Y)
    (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite) :
    HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y := by
  intro V v
  set P := SmallEtale.prodObj B S hS Y V V₀ with hP
  set pS := (BigFppfOver.toScheme B S hS).map (V.property.rep.fst' V₀.obj.hom) with hpS
  set qS := (BigFppfOver.toScheme B S hS).map (V.property.rep.snd V₀.obj.hom) with hqS
  have : Etale pS := etale_of_comp_etale_chart B S hS P.property V.property
    (V.property.rep.isPullback' V₀.obj.hom).w
  have : Etale qS := etale_of_comp_etale_chart B S hS P.property V₀.property rfl
  have hpsurj : Function.Surjective pS.base := by
    have hR : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (V.property.rep.fst' V₀.obj.hom)) := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (V.property.rep.isPullback V₀.obj.hom).flip hV₀
    have h1 := MorphismProperty.of_relative_map (F := yoneda) hR
    exact (show Surjective pS from h1).surj
  obtain ⟨p, hp⟩ := hpsurj v
  obtain ⟨Ω, hpΩ, hfin⟩ :=
    exists_isOpen_finite_preimage_inter_of_locallyQuasiFinite qS h₀ p
  have hPq := schemeWeaklyAssociatedPoints_eq_preimage_of_etale qS
  have hPp := schemeWeaklyAssociatedPoints_eq_preimage_of_etale pS
  refine ⟨⟨pS.base '' (Ω : Set _), pS.isOpenMap _ Ω.isOpen⟩, ⟨p, hpΩ, hp⟩, ?_⟩
  refine Set.Finite.subset ((hPq ▸ hfin).image pS.base) ?_
  rintro x ⟨hxwa, ω, hωΩ, rfl⟩
  exact ⟨ω, ⟨hPp ▸ hxwa, hωΩ⟩, rfl⟩

end Space

end AlgebraicGeometry

end
