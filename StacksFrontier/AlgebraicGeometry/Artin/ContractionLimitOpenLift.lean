module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionOpenPart
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.SpecStalkAffineNhdsSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LocallyNoetherianExtension

/-!
# Local lifts away from the closed subset

Let `V = lim V_i` be a cofiltered limit of affine stages and `ξ = (Z, u', x̂)` a triple over `V`.
For a point `v ∈ V ∖ Z` there is a local lift of `ξ` at some stage whose image contains `v`: on
the base change of a basic open `D(a_i)` of a stage containing the image of `v` and avoiding `Z`,
the triple `(∅, u'_k, ∅)`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_section_of_isLimit_baseChange`: a
  section of a limit preserving presheaf over the base change of the limit comes from a stage.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_localLift_of_not_mem`: the local lift at a
  point outside `Z`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

/-- The inclusion of an open subscheme, as a morphism of the site, is étale. -/
theorem etale_toScheme_map_openStageHom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (V : BigFppfOver B S hS) (U : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    Etale ((BigFppfOver.toScheme B S hS).map (openStageHom B S hS V U)) := by
  have h : Etale U.ι := inferInstance
  rw [toScheme_map_openStageHom]
  exact h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {κ : Cone D}

/-- **A section over the base change of the limit comes from a stage**, for a limit preserving
presheaf `G`: for `q : N ⟶ V_i` with `N` affine, every section of `G` over `V ×_{V_i} N` is the
restriction of a section over some `V_k ×_{V_i} N`. -/
theorem exists_stage_section_of_isLimit_baseChange (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v)
    (hG : LimitPreserving.{u, v, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) G)
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) (i : I)
    {N : BigFppfOver B S hS} (q : N ⟶ (D.obj i).obj)
    (hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (w : G.obj (op (pullback (κ.π.app i).hom q))) :
    ∃ (k : I) (f : k ⟶ i) (w' : G.obj (op (pullback (D.map f).hom q))),
      ∀ m : pullback (κ.π.app i).hom q ⟶ pullback (D.map f).hom q,
        m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (κ.π.app k).hom →
        m ≫ pullback.snd _ _ = pullback.snd _ _ → G.map m.op w' = w := by
  let E := D ⋙ ObjectProperty.ι _
  let κ' := (ObjectProperty.ι _).mapCone κ
  have hκ' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone κ') := hκ
  have hlim := isLimitMapOverBaseChangeCone E κ' i q (BigFppfOver.toScheme B S hS) hκ'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)) := hD i
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj N) := hN
  have hstage : ∀ k : Over i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((overBaseChangeDiagram E i q).obj k)) := fun k => by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj k.left)) := hD k.left
    exact isAffine_pullback (E.map k.hom) q
  have hvert : IsAffine ((BigFppfOver.toScheme B S hS).obj (overBaseChangeCone E κ' i q).pt) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj κ'.pt) := hpt
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (((Functor.const I).obj κ'.pt).obj i)) :=
      hpt
    exact isAffine_pullback (κ'.π.app i) q
  obtain ⟨hcol⟩ := hG (Over i) (overBaseChangeDiagram E i q)
    (overBaseChangeCone E κ' i q) hlim hstage hvert
  obtain ⟨k, y, hy⟩ := exists_eq_map_of_isColimit_mapCocone G (overBaseChangeDiagram E i q)
    (overBaseChangeCone E κ' i q) hcol w
  refine ⟨k.left, k.hom, y, fun m hm₁ hm₂ => ?_⟩
  have hm : m = (overBaseChangeCone E κ' i q).π.app k := by
    apply pullback.hom_ext
    · rw [hm₁]
      exact (pullback.lift_fst _ _ _).symm
    · rw [hm₂]
      exact (pullback.lift_snd _ _ _).symm
  rwa [hm]

omit [IsCofiltered I] in
/-- A triple with empty closed subset is the triple `(∅, u, ∅ ⟶ W)` of some `u : V ⟶ U'`. -/
theorem Triple.exists_eq_emptyTriple (c : ContractionSituation B S hS) {V : BigFppfOver B S hS}
    (t : Triple c V) (hZ : t.Z = ∅) : ∃ u, t = c.emptyTriple V u := by
  have key : ∀ W : Set (Space.points B S hS (yoneda.obj V)), W = Set.univ →
      IsIso (Space.openSubspaceOfPoints B S hS (yoneda.obj V) W).ι := by
    rintro W rfl
    exact (Subfunctor.eq_top_iff_isIso _).mp (Space.openSubspaceOfPoints_univ B S hS _)
  have := key t.Zᶜ (by rw [hZ, Set.compl_empty])
  exact ⟨inv (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).ι ≫ t.u,
    Triple.eq_emptyTriple c t _ hZ (by simp)⟩

/-- **The local lift at a point outside `Z`.** For a triple `ξ` over the limit `V` and a point
`v ∈ V ∖ Z`, some stage carries a local lift of `ξ` whose image in `V` contains `v`. -/
theorem exists_localLift_of_not_mem (c : ContractionSituation B S hS)
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) (ξ : Triple c κ.pt.obj)
    (v : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt)
    (hv : (Space.schemePointsHomeomorph B S hS κ.pt.obj).symm v ∉ ξ.Z) :
    ∃ (i : I) (L : LocalLift c κ ξ i), v ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (pullback.snd L.e.hom (κ.π.app i).hom)).base := by
  let Vs := (BigFppfOver.toScheme B S hS).obj κ.pt.obj
  have : IsAffine Vs := hpt
  let e := Space.schemePointsHomeomorph B S hS κ.pt.obj
  let Uc : Vs.Opens := ⟨(e.symm ⁻¹' ξ.Z)ᶜ, (ξ.isClosed_Z.preimage e.symm.continuous).isOpen_compl⟩
  obtain ⟨_, ⟨a, rfl⟩, hva, haU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Vs)) (show v ∈ Uc from hv)
  have : ∀ i, IsAffine ((D ⋙ LocallyNoetherianOver.toScheme B S hS).obj i) := hD
  obtain ⟨i, ai, hai⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit
    (D ⋙ LocallyNoetherianOver.toScheme B S hS) _ hκ a
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj) := hD i
  set U : ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj).Opens :=
    ((BigFppfOver.toScheme B S hS).obj (D.obj i).obj).basicOpen ai with hUdef
  let N := Space.openStage B S hS (D.obj i).obj U
  let q : N ⟶ (D.obj i).obj := Space.openStageHom B S hS (D.obj i).obj U
  have hq : (BigFppfOver.toScheme B S hS).map q = U.ι := Space.toScheme_map_openStageHom B S hS _ U
  have hqet : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    Space.etale_toScheme_map_openStageHom _ U
  have hN : IsAffine ((BigFppfOver.toScheme B S hS).obj N) :=
    (isAffineOpen_top _).basicOpen ai
  have hpre : (BigFppfOver.toScheme B S hS).map (κ.π.app i).hom ⁻¹ᵁ U = Vs.basicOpen a := by
    rw [Scheme.preimage_basicOpen, ← hai]
    rfl
  let p₀ : pullback (κ.π.app i).hom q ⟶ κ.pt.obj := pullback.fst _ _
  have hmemU : ∀ y, ((BigFppfOver.toScheme B S hS).map p₀).base y ∈ Vs.basicOpen a := fun y => by
    rw [← hpre]
    change ((BigFppfOver.toScheme B S hS).map p₀ ≫
      (BigFppfOver.toScheme B S hS).map (κ.π.app i).hom).base y ∈ U
    rw [← Functor.map_comp, pullback.condition, Functor.map_comp, hq]
    exact (Scheme.Opens.range_ι U).subset ⟨_, rfl⟩
  have hZ0 : (mapTriple c p₀ ξ).Z = ∅ := by
    change Space.pointsMap B S hS _ (yoneda.map p₀) ⁻¹' ξ.Z = ∅
    rw [pointsMap_yoneda_preimage_eq]
    ext x
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact fun hx => haU (hmemU _) hx
  obtain ⟨u₀, hu₀⟩ := Triple.exists_eq_emptyTriple c _ hZ0
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  have hU'lp := Space.limitPreserving_of_isLocallyOfFiniteType B S hS c.isOpenSubspace_U'.1
    (isLocallyOfFiniteType_terminal_of_isOpenSubspace c.isAlgebraicSpace_X'
      c.isLocallyOfFiniteType_X' c.isOpenSubspace_U')
  obtain ⟨k, f, w', hw'⟩ := exists_stage_section_of_isLimit_baseChange c.U'.toFunctor hU'lp hκ hD
    hpt i q hN (yonedaEquiv u₀)
  have hw : (κ.π.app k).hom ≫ (D.map f).hom = (κ.π.app i).hom :=
    congrArg (fun k => k.hom) (κ.w f)
  let π' : pullback (κ.π.app i).hom q ⟶ pullback (D.map f).hom q :=
    pullback.lift (pullback.fst _ _ ≫ (κ.π.app k).hom) (pullback.snd _ _) (by
      rw [Category.assoc, hw]
      exact pullback.condition)
  have hπ' : yoneda.map π' ≫ yonedaEquiv.symm w' = u₀ := by
    rw [yonedaEquiv_symm_naturality_left,
      hw' π' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), Equiv.symm_apply_apply]
  let E' : LocallyNoetherianOver B S hS :=
    ⟨pullback (D.map f).hom q,
      isLocallyNoetherian_pullback_of_etale_right _ q hqet (D.obj k).property⟩
  let e' : E' ⟶ D.obj k := ObjectProperty.homMk (pullback.fst (D.map f).hom q)
  let P' := pullback (pullback.fst (D.map f).hom q) (κ.π.app k).hom
  let m : P' ⟶ pullback (κ.π.app i).hom q :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, hw])
  have hmπ : m ≫ π' = pullback.fst (pullback.fst (D.map f).hom q) (κ.π.app k).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hagree : mapTriple c (pullback.fst e'.hom (κ.π.app k).hom)
      (c.emptyTriple E'.obj (yonedaEquiv.symm w')) =
      mapTriple c (pullback.snd e'.hom (κ.π.app k).hom) ξ := by
    change mapTriple c (pullback.fst (pullback.fst (D.map f).hom q) (κ.π.app k).hom)
      (c.emptyTriple _ (yonedaEquiv.symm w')) =
      mapTriple c (pullback.snd (pullback.fst (D.map f).hom q) (κ.π.app k).hom) ξ
    have hm₁ : m ≫ p₀ = pullback.snd (pullback.fst (D.map f).hom q) (κ.π.app k).hom :=
      pullback.lift_fst _ _ _
    rw [← emptyTriple_comp, ← hm₁, mapTriple_comp, hu₀, ← emptyTriple_comp, ← hπ',
      ← Category.assoc, ← Functor.map_comp, hmπ]
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj k).obj) := hD k
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj N) := hN
  refine ⟨k, LocalLift.mk E' e' (etale_pullback_fst _ q hqet) (isAffine_pullback (D.map f).hom q)
    (c.emptyTriple E'.obj (yonedaEquiv.symm w')) hagree, ?_⟩
  have hx : ((BigFppfOver.toScheme B S hS).map (κ.π.app i).hom).base v ∈ U := by
    change v ∈ (BigFppfOver.toScheme B S hS).map (κ.π.app i).hom ⁻¹ᵁ U
    rwa [hpre]
  obtain ⟨n, hn₀⟩ : ((BigFppfOver.toScheme B S hS).map (κ.π.app i).hom).base v ∈
      Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  have hn : ((BigFppfOver.toScheme B S hS).map q).base n =
      ((BigFppfOver.toScheme B S hS).map (κ.π.app i).hom).base v := by
    rwa [hq]
  obtain ⟨z₀, hz₀, -⟩ := exists_pullback_point (κ.π.app i).hom q v n hn.symm
  have e₁ : (BigFppfOver.toScheme B S hS).map π' ≫
      (BigFppfOver.toScheme B S hS).map (pullback.fst (D.map f).hom q) =
      (BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q) ≫
        (BigFppfOver.toScheme B S hS).map (κ.π.app k).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
  obtain ⟨z, -, hz⟩ := exists_pullback_point (pullback.fst (D.map f).hom q) (κ.π.app k).hom
    (((BigFppfOver.toScheme B S hS).map π').base z₀) v (by
      rw [← hz₀]
      exact congrArg (fun φ => φ.base z₀) e₁)
  exact ⟨z, hz⟩

end AlgebraicGeometry.Artin.ContractionSituation

end
