module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperBaseChange

/-!
# The tube lemma for a fibre product of the locally quasi-compact Zariski site

Let `S` be a locally quasi-compact Zariski situation, let `f : X ⟶ Y` and `j : U ⟶ Y` be
morphisms of its site and let `U ×_Y X` be their fibre product. Then:

* every open neighbourhood of a point of `U ×_Y X` contains a **tube** `V ×_Y W` around it, for
  `V` an open neighbourhood of the first coordinate and `W` an open neighbourhood of the second;
* a pair of points of `U` and `X` with the same image in `Y` is the pair of coordinates of a
  point of `U ×_Y X`.

Both follow from the presentation of `U ×_Y X` as the subspace `{p : U × X // j p.1 = f p.2}` of
the product.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_sitePullback_homeo`: the fibre
  product of the site is the subspace of the product cut out by the equality of the two images,
  compatibly with the two projections.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_tube_of_mem`: the tube lemma, every
  open neighbourhood of a point of `U ×_Y X` contains a tube `V ×_Y W` around it.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_site_pullback_point`: a matching
  pair of points comes from a point of the fibre product.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.over_pullback_map_left_fst`: `Over.pullback`
  commutes with the first projections.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.site_pullback_condition_apply`: the
  pullback square commutes, on a point.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_mem_of_over_hom` and
  `exists_over_hom_opensToSlice_factor`: an object over `T` maps into an open subobject of `Z`
  exactly when its image lies in the corresponding open subset of `Z.left`.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- If an open subobject of `Z` maps over `T` to an open subset `W` of `T`, then every point of
the corresponding open subset of `Z.left` has image in `W`. -/
theorem opensToSlice_mem_of_over_hom {T : S.category} {Z : Over T} {V : Opens Z.left.obj}
    {W : Opens T.obj}
    (cm : Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶
      (S.opensToSlice T).1.obj W)
    {q : Z.left.obj} (hq : q ∈ V) :
    (Z.hom : Z.left.obj → T.obj) q ∈ W := by
  obtain ⟨p, hp⟩ := exists_opensToSlice_preimage S (Z := Z) V hq
  have hw := congrArg
    (fun k : (Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom)).left ⟶ T =>
      (k : _ → T.obj) p) (Over.w cm)
  simp only [Over.mk_hom, site_hom_comp_apply, hp] at hw
  exact hw ▸ opensToSlice_hom_mem S W _

/-- A morphism of the localized site over `T` whose image lies in an open subset `V` of `Z.left`
factors through the open subobject of `Z` cut out by `V`. -/
theorem exists_over_hom_opensToSlice_factor {T : S.category} {Z E : Over T}
    (κ : E ⟶ Z) (V : Opens Z.left.obj)
    (hκ : ∀ e : E.left.obj, (κ.left : E.left.obj → Z.left.obj) e ∈ V) :
    ∃ θ : E ⟶ Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom),
      θ ≫ (Over.homMk (((S.opensToSlice Z.left).1.obj V).hom) :
        Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z) = κ := by
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_of_range_subset S κ.left
    (((S.opensToSlice Z.left).1.obj V).hom) ((S.opensToSlice Z.left).2 V).1
    (by
      rw [((S.opensToSlice Z.left).2 V).2]
      rintro q ⟨e, rfl⟩
      exact hκ e)
  refine ⟨Over.homMk ψ ?_, ?_⟩
  · simp only [Over.mk_hom]
    rw [← Category.assoc, hψ, Over.w]
  · exact Over.OverMorphism.ext (by simpa using hψ)

variable {X Y : S.category} (f : X ⟶ Y)

/-- The fibre product `U ×_Y X` of the site is homeomorphic to the subspace of `U × X` on which
the two images in `Y` agree, by a homeomorphism sending a point to its pair of coordinates. -/
theorem exists_sitePullback_homeo {U : S.category} (j : U ⟶ Y) :
    ∃ e : (Limits.pullback j f).obj ≃ₜ
        {p : U.obj × X.obj // (j : U.obj → Y.obj) p.1 = (f : X.obj → Y.obj) p.2},
      ∀ q, (e q : U.obj × X.obj) =
        ((Limits.pullback.fst j f : _ → _) q, (Limits.pullback.snd j f : _ → _) q) := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let c := cospan j f
  let _ : CreatesLimitsOfShape WalkingCospan S.qcSite.inclusion :=
    boundedSiteInclusionCreatesPullbacks S
  let _ : CreatesLimit c S.qcSite.inclusion := inferInstance
  let _ : CreatesLimit (c ⋙ S.qcSite.inclusion) locallyQuasiCompactHausdorffToTop :=
    inferInstance
  let _ : CreatesLimit c I := inferInstance
  let e := CategoryTheory.preservesLimitIso I c
  let cTop := cospan (I.map j) (I.map f)
  let hdiag : c ⋙ I ≅ cTop := cospanCompIso I j f
  let eTop := e.trans (HasLimit.isoOfNatIso hdiag)
  have hproj : ∀ i, eTop.hom ≫ limit.π cTop i =
      I.map (limit.π c i) ≫ hdiag.hom.app i := fun i => by
    dsimp [eTop]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← preservesLimitIso_hom_π]
    rfl
  have hprojL := hproj WalkingCospan.left
  have hprojR := hproj WalkingCospan.right
  simp only [hdiag, cospanCompIso_hom_app_left, cospanCompIso_hom_app_right] at hprojL hprojR
  rw [show limit.π cTop WalkingCospan.left = pullback.fst (I.map j) (I.map f) from
    PullbackCone.fst_limit_cone _ _] at hprojL
  rw [show limit.π cTop WalkingCospan.right = pullback.snd (I.map j) (I.map f) from
    PullbackCone.snd_limit_cone _ _] at hprojR
  exact ⟨TopCat.homeoOfIso (eTop.trans (TopCat.pullbackIsoProdSubtype (I.map j) (I.map f))),
    fun q => Prod.ext (ConcreteCategory.congr_hom hprojL q) (ConcreteCategory.congr_hom hprojR q)⟩

/-- **The tube lemma.** An open neighbourhood `N` of a point `q` of the fibre product `U ×_Y X`
contains a tube around `q`: there are an open neighbourhood `V` of the first coordinate of `q` in
`U` and an open neighbourhood `W` of its second coordinate in `X` such that every point of
`U ×_Y X` whose coordinates lie in `V` and in `W` lies in `N`. -/
theorem exists_tube_of_mem {U : S.category} (j : U ⟶ Y)
    (N : Opens (Limits.pullback j f).obj) {q : (Limits.pullback j f).obj} (hq : q ∈ N) :
    ∃ (V : Opens U.obj) (W : Opens X.obj),
      (Limits.pullback.fst j f : _ → _) q ∈ V ∧ (Limits.pullback.snd j f : _ → _) q ∈ W ∧
        ∀ q' : (Limits.pullback j f).obj,
          (Limits.pullback.fst j f : _ → _) q' ∈ V →
            (Limits.pullback.snd j f : _ → _) q' ∈ W → q' ∈ N := by
  obtain ⟨e, he⟩ := exists_sitePullback_homeo S f j
  have hind : Topology.IsInducing (fun q : (Limits.pullback j f).obj =>
      ((Limits.pullback.fst j f : _ → _) q, (Limits.pullback.snd j f : _ → _) q)) := by
    convert Topology.IsEmbedding.subtypeVal.isInducing.comp e.isInducing using 1
    exact funext fun q => (he q).symm
  obtain ⟨O, hO, hON⟩ := hind.isOpen_iff.1 N.isOpen
  have hq' : q ∈ (N : Set (Limits.pullback j f).obj) := hq
  rw [← hON] at hq'
  obtain ⟨V, W, hV, hW, hqV, hqW, hVW⟩ := isOpen_prod_iff.1 hO _ _ hq'
  exact ⟨⟨V, hV⟩, ⟨W, hW⟩, hqV, hqW, fun q' h1 h2 =>
    show q' ∈ (N : Set (Limits.pullback j f).obj) from hON ▸ hVW ⟨h1, h2⟩⟩

/-- A point of `U` and a point of `X` with the same image in `Y` are the two coordinates of a
point of the fibre product `U ×_Y X`. -/
theorem exists_site_pullback_point {U : S.category} (j : U ⟶ Y) (p : U.obj) (x : X.obj)
    (h : (j : U.obj → Y.obj) p = (f : X.obj → Y.obj) x) :
    ∃ q : (Limits.pullback j f).obj,
      (Limits.pullback.fst j f : _ → _) q = p ∧ (Limits.pullback.snd j f : _ → _) q = x := by
  obtain ⟨e, he⟩ := exists_sitePullback_homeo S f j
  have hq := he (e.symm ⟨(p, x), h⟩)
  rw [Homeomorph.apply_symm_apply] at hq
  exact ⟨e.symm ⟨(p, x), h⟩, (congrArg Prod.fst hq).symm, (congrArg Prod.snd hq).symm⟩

/-- Pulling back along `f` commutes with the first projections: the base change of a morphism
`h : P ⟶ Z` over `Y` is a morphism over the first projections. -/
theorem over_pullback_map_left_fst {P Z : Over Y} (h : P ⟶ Z) :
    ((Over.pullback f).map h).left ≫ Limits.pullback.fst Z.hom f =
      Limits.pullback.fst P.hom f ≫ h.left := by
  simp only [Over.pullback_map_left, Limits.pullback.lift_fst]

/-- The fibre product square commutes, read on a point. -/
theorem site_pullback_condition_apply {P : Over Y} (ρ : (Limits.pullback P.hom f).obj) :
    (f : X.obj → Y.obj) ((Limits.pullback.snd P.hom f : _ → _) ρ) =
      (P.hom : P.left.obj → Y.obj) ((Limits.pullback.fst P.hom f : _ → _) ρ) :=
  (ConcreteCategory.congr_hom (Limits.pullback.condition (f := P.hom) (g := f)) ρ).symm

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
