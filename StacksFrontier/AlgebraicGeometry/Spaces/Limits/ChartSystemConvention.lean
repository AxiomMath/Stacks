module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chapter's convention for systems with a chart system, and limits in the site

Section 70.2 of the source (tag 07SD) assumes that every ring it considers has its spectrum in
the big fppf site. For an inverse system `D` of algebraic spaces with affine transition
morphisms this is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the limit of the
charts `D k ×_{D i} Z`, over a stage `i`, at an affine point `Z` of `D i`, lies in the site.

This file proves two things about that convention.

* A system which comes with a *true* chart system satisfies it: an inverse system `V` of objects
  of the site with a cartesian transformation `v : V ⟶ D` by surjective étale morphisms, whose
  limit of underlying schemes lies in the site. The charts at `Z`, base changed along the
  surjective étale `Z' = Z ×_{D i} V i ⟶ Z`, are the base changes `V k ×_{V i} Z'`, so the limit
  of the charts is covered, flatly, by `lim V ×_{V i} Z'`, which lies in the site.
* For a cofiltered diagram `E` of the site with affine transition morphisms which satisfies the
  convention, a limit of the represented presheaves is a limit of the underlying schemes. The
  limit `L` of the underlying schemes is covered by the preimages of the affine opens of one
  stage, each of which lies in the site by the convention; the comparison morphism from the
  vertex is a monomorphism with a section over each of them, hence an isomorphism. The size of
  `L` itself is never bounded: the site's cutoff may be singular, so a union of fewer than
  cutoff many small opens need not be small.

## Main definitions

* `CategoryTheory.Limits.coneOfIsPullbackStages`: the base change, along `p : Y ⟶ T`, of a cone
  over a diagram lying over `T`, as a cone over a stage-wise base change of the diagram, and
  `CategoryTheory.Limits.isLimitConeOfIsPullbackStages`: it is a limit for connected shapes.
* `AlgebraicGeometry.isLimitMapConeToSchemeOfIsLimitMapConeYoneda`: the second result above.

## Main results

* `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_chartSystem`: the first result above.
* `AlgebraicGeometry.Space.AffineChartSystem.limitInSite_of_isPullback`: its form for one chart
  system.
* `AlgebraicGeometry.BigFppfOver.contains_of_isPullback_of_limitInSite`: the base change of a
  limit of underlying schemes along an affine point of a stage lies in the site under the
  convention for the charts at that point.
* `AlgebraicGeometry.BigFppfOver.toScheme_hom_ext_of_isLimit`,
  `AlgebraicGeometry.BigFppfOver.exists_toScheme_lift_of_isLimit`: a limit of the site has the
  universal property of a limit of schemes against test schemes in the site.
* `AlgebraicGeometry.Scheme.isIso_of_mono_of_iSup_eq_top`: a monomorphism of schemes with
  sections over an open cover of the target is an isomorphism.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 04T6](https://stacks.math.columbia.edu/tag/04T6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

/-! ### Base change of a limit through a cartesian transformation -/

section Cartesian

variable {K C : Type*} [Category K] [Category C] {F G : K ⥤ C}
  (α : ∀ k, G.obj k ⟶ F.obj k) (hα : ∀ {k l : K} (f : k ⟶ l), G.map f ≫ α l = α k ≫ F.map f)
  {T Y : C} (w : ∀ k, F.obj k ⟶ T) (p : Y ⟶ T) (γ : ∀ k, G.obj k ⟶ Y)
  (hγ : ∀ {k l : K} (f : k ⟶ l), G.map f ≫ γ l = γ k)
  (h : ∀ k, IsPullback (α k) (γ k) (w k) p)
  (cF : Cone F) (t : cF.pt ⟶ T) (ht : ∀ k, cF.π.app k ≫ w k = t)
  {P : C} (fst : P ⟶ cF.pt) (snd : P ⟶ Y) (hP : IsPullback fst snd t p)

/-- Given a diagram `G` which is the base change, stage by stage, of a diagram `F` over `T` along
`p : Y ⟶ T`, and a cone `cF` over `F` lying over `T` through `t`, the base change of `cF` along
`p` is a cone over `G`. -/
noncomputable def coneOfIsPullbackStages : Cone G where
  pt := P
  π :=
    { app k := (h k).lift (fst ≫ cF.π.app k) snd (by rw [Category.assoc, ht, hP.w])
      naturality {k l} f := by
        refine (h l).hom_ext ?_ ?_
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            IsPullback.lift_fst, Category.assoc, hα f, IsPullback.lift_fst_assoc, Cone.w]
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            IsPullback.lift_snd, Category.assoc, hγ f] }

/-- The vertex of the base-changed cone is the chosen fibre product. -/
@[simp]
theorem coneOfIsPullbackStages_pt :
    (coneOfIsPullbackStages α hα w p γ hγ h cF t ht fst snd hP).pt = P :=
  rfl

/-- **Base change commutes with connected limits, through a cartesian transformation.** If `G`
is, stage by stage, the base change of `F` along `p : Y ⟶ T`, then the base change along `p` of a
limit of `F` is a limit of `G`. This is `CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected`
applied to the cone of `CategoryTheory.Limits.coneOfIsPullbackStages`, the squares it asks for
being obtained by cancelling the stage-wise squares from the square of `P`. -/
noncomputable def isLimitConeOfIsPullbackStages [IsConnected K] (hcF : IsLimit cF) :
    IsLimit (coneOfIsPullbackStages α hα w p γ hγ h cF t ht fst snd hP) :=
  isLimitOfIsPullbackOfIsConnected { app := α, naturality := fun _ _ f => hα f } _ cF
    { hom := fst, w := fun k => ((h k).lift_fst _ _ _).symm }
    (fun k => IsPullback.of_right (h₁₂ := γ k) (h₂₂ := w k) (v₁₃ := p)
      (by simpa only [coneOfIsPullbackStages, IsPullback.lift_snd, ht] using hP.flip)
      ((h k).lift_fst _ _ _) (h k).flip) hcF

/-- The base change along `p : Y ⟶ T` of a diagram `F` lying over `T` through a compatible family
`w`. -/
@[sga "4 I 2.5"]
noncomputable abbrev pullbackDiagramAlong [HasPullbacks C] (F : K ⥤ C) {T Y : C}
    (w : ∀ k, F.obj k ⟶ T) (hw : ∀ {k l : K} (f : k ⟶ l), F.map f ≫ w l = w k) (p : Y ⟶ T) :
    K ⥤ C where
  obj k := pullback (w k) p
  map {k l} f := pullback.lift (pullback.fst _ _ ≫ F.map f) (pullback.snd _ _)
    (by rw [Category.assoc, hw f, pullback.condition])
  map_id k := by apply pullback.hom_ext <;> simp
  map_comp f g := by
    apply pullback.hom_ext <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

/-- The transition maps of `pullbackDiagramAlong` commute with the first projections. -/
theorem pullbackDiagramAlong_map_fst [HasPullbacks C] (F : K ⥤ C) {T Y : C}
    (w : ∀ k, F.obj k ⟶ T) (hw : ∀ {k l : K} (f : k ⟶ l), F.map f ≫ w l = w k) (p : Y ⟶ T)
    {k l : K} (f : k ⟶ l) :
    (pullbackDiagramAlong F w hw p).map f ≫ pullback.fst (w l) p = pullback.fst (w k) p ≫ F.map f :=
  pullback.lift_fst _ _ _

/-- The transition maps of `pullbackDiagramAlong` commute with the second projections. -/
theorem pullbackDiagramAlong_map_snd [HasPullbacks C] (F : K ⥤ C) {T Y : C}
    (w : ∀ k, F.obj k ⟶ T) (hw : ∀ {k l : K} (f : k ⟶ l), F.map f ≫ w l = w k) (p : Y ⟶ T)
    {k l : K} (f : k ⟶ l) :
    (pullbackDiagramAlong F w hw p).map f ≫ pullback.snd (w l) p = pullback.snd (w k) p :=
  pullback.lift_snd _ _ _

end Cartesian

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Scheme-valued points of a limit in the site -/

section SiteLimit

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ BigFppfOver B S hS}

/-- **Morphisms from a scheme of the site into a limit of the site are determined by their
projections.** The limit is only a limit in the site, but a scheme of the site becomes an object
of the site over `S` through either of the two morphisms, which agree over `S` because they agree
after a projection. -/
theorem BigFppfOver.toScheme_hom_ext_of_isLimit {c : Cone E} (hc : IsLimit c) {X : Scheme.{u}}
    (hX : B.Contains X) {a b : X ⟶ (BigFppfOver.toScheme B S hS).obj c.pt}
    (h : ∀ j, a ≫ (BigFppfOver.toScheme B S hS).map (c.π.app j) =
      b ≫ (BigFppfOver.toScheme B S hS).map (c.π.app j)) : a = b := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have hb : b ≫ B.inclusion.map c.pt.hom = a ≫ B.inclusion.map c.pt.hom := by
    rw [← BigFppfOver.toScheme_map_comp_hom (X := c.pt) (c.π.app j₀), ← Category.assoc, ← h j₀,
      Category.assoc]
  let T := siteObject B S hS hX (a ≫ B.inclusion.map c.pt.hom)
  let a' : T ⟶ c.pt := Over.homMk (ObjectProperty.homMk a) (ObjectProperty.hom_ext _ rfl)
  let b' : T ⟶ c.pt := Over.homMk (ObjectProperty.homMk b) (ObjectProperty.hom_ext _ hb)
  exact congrArg (BigFppfOver.toScheme B S hS).map
    (hc.hom_ext fun j => Over.OverMorphism.ext (ObjectProperty.hom_ext _ (h j)) : a' = b')

/-- **A compatible family of morphisms from a scheme of the site to the stages factors through a
limit of the site.** The family makes the scheme an object of the site over `S`, and a cone of the
site over the diagram. -/
theorem BigFppfOver.exists_toScheme_lift_of_isLimit {c : Cone E} (hc : IsLimit c)
    {X : Scheme.{u}} (hX : B.Contains X) (x : ∀ j, X ⟶ (BigFppfOver.toScheme B S hS).obj (E.obj j))
    (hx : ∀ {i j : J} (f : i ⟶ j), x i ≫ (BigFppfOver.toScheme B S hS).map (E.map f) = x j) :
    ∃ s : X ⟶ (BigFppfOver.toScheme B S hS).obj c.pt,
      ∀ j, s ≫ (BigFppfOver.toScheme B S hS).map (c.π.app j) = x j := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have hcomp : ∀ j, x j ≫ B.inclusion.map (E.obj j).hom =
      x j₀ ≫ B.inclusion.map (E.obj j₀).hom := by
    intro j
    rw [← hx (IsCofiltered.minToLeft j j₀), ← hx (IsCofiltered.minToRight j j₀),
      Category.assoc, Category.assoc, BigFppfOver.toScheme_map_comp_hom,
      BigFppfOver.toScheme_map_comp_hom]
  let T := siteObject B S hS hX (x j₀ ≫ B.inclusion.map (E.obj j₀).hom)
  let s : Cone E :=
    { pt := T
      π :=
        { app j := Over.homMk (ObjectProperty.homMk (x j)) (ObjectProperty.hom_ext _ (hcomp j))
          naturality {i j} f := Over.OverMorphism.ext
            (ObjectProperty.hom_ext _ ((Category.id_comp _).trans (hx f).symm)) } }
  exact ⟨(BigFppfOver.toScheme B S hS).map (hc.lift s), fun j => by
    rw [← Functor.map_comp, hc.fac]
    rfl⟩

/-- The comparison morphism from the underlying scheme of a limit of the site to the limit of the
underlying schemes is a monomorphism: the fibre product of it with itself has size at most that of
its source, hence lies in the site, where the two projections agree after every projection. -/
theorem BigFppfOver.mono_lift_mapCone_toScheme {c : Cone E} (hc : IsLimit c)
    {d : Cone (E ⋙ BigFppfOver.toScheme B S hS)} (hd : IsLimit d) :
    Mono (hd.lift ((BigFppfOver.toScheme B S hS).mapCone c)) := by
  set φ := hd.lift ((BigFppfOver.toScheme B S hS).mapCone c)
  have hfac : ∀ j, φ ≫ d.π.app j = (BigFppfOver.toScheme B S hS).map (c.π.app j) :=
    fun j => hd.fac _ j
  have hP : B.Contains (pullback φ φ) :=
    Scheme.size_pullback_lt φ φ c.pt.left.property c.pt.left.property
  have hfs : pullback.fst φ φ = pullback.snd φ φ :=
    BigFppfOver.toScheme_hom_ext_of_isLimit hc hP fun j => by
      rw [← hfac, ← Category.assoc, pullback.condition, Category.assoc]
  refine ⟨fun a b h => ?_⟩
  rw [← pullback.lift_fst a b h, hfs, pullback.lift_snd]

end SiteLimit

/-- **A monomorphism of schemes which has a section over every member of an open cover of its
target is an isomorphism.** Over each member the restriction is a monomorphism with a right
inverse, and being an isomorphism is local on the target. -/
theorem Scheme.isIso_of_mono_of_iSup_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] {ι : Type*}
    (U : ι → Y.Opens) (hU : iSup U = ⊤) (s : ∀ i, (U i : Scheme) ⟶ X)
    (hs : ∀ i, s i ≫ f = (U i).ι) : IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro i
  have hle : Set.range (s i) ⊆ Set.range (f ⁻¹ᵁ U i).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f ((s i) y) ∈ U i
    rw [← Scheme.Hom.comp_apply, hs]
    exact y.2
  let t := IsOpenImmersion.lift (f ⁻¹ᵁ U i).ι (s i) hle
  have ht : t ≫ f ∣_ U i = 𝟙 _ := by
    rw [← cancel_mono (U i).ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc,
      hs, Category.id_comp]
  have : IsSplitEpi (f ∣_ U i) := IsSplitEpi.mk' ⟨t, ht⟩
  have : Mono (f ∣_ U i) := mono_of_mono_fac (morphismRestrict_ι f (U i))
  exact isIso_of_mono_of_isSplitEpi _

/-- **The base change of a limit of the site along an affine point of a stage lies in the site,
under the convention for the charts at that point.** Let `C` be a chart system of the stages over
`i₀` at a point `ιs` of the stage `i₀` coming from the site. Each chart is the base change of its
stage along `ιs`, as schemes, so the base change of a limit of the underlying schemes along `ιs`
is a limit of the underlying schemes of the charts
(`CategoryTheory.Limits.isLimitConeOfIsPullbackStages`), which lies in the site when `C`
satisfies the convention. -/
theorem BigFppfOver.contains_of_isPullback_of_limitInSite {J : Type u} [Category.{u} J]
    [IsCofiltered J] {E : J ⥤ BigFppfOver B S hS} {i₀ : J} {Zs : BigAffineFppf B S hS}
    {ιs : (BigAffineFppf.inclusion B S hS).obj Zs ⟶ E.obj i₀}
    (C : Space.AffineChartSystem B S hS i₀ (E ⋙ yoneda) Zs (yoneda.map ιs))
    (hL : BigFppfOver.LimitInSite C.siteDiagram)
    {d : Cone (E ⋙ BigFppfOver.toScheme B S hS)} (hd : IsLimit d) {P : Scheme.{u}}
    (fst : P ⟶ d.pt) (snd : P ⟶ (BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj Zs))
    (hP : IsPullback fst snd (d.π.app i₀) ((BigFppfOver.toScheme B S hS).map ιs)) :
    B.Contains P := by
  let D' := E ⋙ BigFppfOver.toScheme B S hS
  let a : ∀ k : Over i₀, (underlyingDiagram C.siteDiagram).obj k ⟶ (Over.forget i₀ ⋙ D').obj k :=
    fun k => (BigFppfOver.toScheme B S hS).map (yoneda.preimage (C.stageMap k))
  let b : ∀ k : Over i₀, (underlyingDiagram C.siteDiagram).obj k ⟶
      (BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj Zs) :=
    fun k => (BigFppfOver.toScheme B S hS).map (yoneda.preimage (C.baseMap k))
  have hsq : ∀ k, IsPullback (a k) (b k) (D'.map k.hom) ((BigFppfOver.toScheme B S hS).map ιs) := by
    intro k
    have h2 : IsPullback (yoneda.preimage (C.stageMap k)) (yoneda.preimage (C.baseMap k))
        (E.map k.hom) ιs := by
      refine IsPullback.of_map_of_faithful yoneda ?_
      simp only [Functor.map_preimage]
      exact C.isPullback k
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      comp_preservesLimitsOfShape _ _
    exact h2.map (BigFppfOver.toScheme B S hS)
  have ha : ∀ {k l : Over i₀} (f : k ⟶ l),
      (underlyingDiagram C.siteDiagram).map f ≫ a l = a k ≫ (Over.forget i₀ ⋙ D').map f := by
    intro k l f
    show (BigFppfOver.toScheme B S hS).map (C.siteDiagram.map f) ≫ _ =
      _ ≫ (BigFppfOver.toScheme B S hS).map (E.map f.left)
    simp only [a, ← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    exact C.stageMap_naturality f
  have hb : ∀ {k l : Over i₀} (f : k ⟶ l),
      (underlyingDiagram C.siteDiagram).map f ≫ b l = b k := by
    intro k l f
    show (BigFppfOver.toScheme B S hS).map (C.siteDiagram.map f) ≫ _ = _
    simp only [b, ← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    simpa only [Functor.map_comp, Functor.map_preimage] using C.baseMap_naturality f
  have _ : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hlim := isLimitConeOfIsPullbackStages (G := underlyingDiagram C.siteDiagram)
    (F := Over.forget i₀ ⋙ D') a ha (fun k => D'.map k.hom) _ b hb hsq
    (d.whisker (Over.forget i₀)) (d.π.app i₀) (fun k => d.w k.hom) fst snd hP
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) _).symm hd)
  simpa only [coneOfIsPullbackStages_pt] using hL _ hlim

/-! ### Limits of the site whose limit of underlying schemes is formed in the site -/

section SchemeLimit

/-- **Under the chapter's convention, a limit of presheaves of a cofiltered diagram of the site
with affine transition morphisms is a limit of the underlying schemes.**

The limit `L` of the underlying schemes exists because the transition morphisms are affine, and
the comparison morphism from the underlying scheme of the vertex of `c` to `L` is a monomorphism
(`AlgebraicGeometry.BigFppfOver.mono_lift_mapCone_toScheme`), `c` being a limit of the site
because the Yoneda embedding reflects limits. Fix a stage `i₀`. For an affine open `U` of the
stage `i₀`, the preimage of `U` in `L` is the limit of the base changes along `U` of the stages
over `i₀` (`CategoryTheory.Limits.isLimitConeOfIsPullbackStages`), and those base changes are
the charts of the system at the affine point `U` of the stage `i₀`; so by the convention the
preimage lies in the site. It therefore maps to the vertex of `c`, compatibly with the
comparison morphism. These preimages cover `L`, so the comparison morphism is an
isomorphism. -/
noncomputable def isLimitMapConeToSchemeOfIsLimitMapConeYoneda
    {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ BigFppfOver B S hS)
    (hAffine : ∀ {i j : J} (f : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map f)))
    (hconv : Space.SiteContainsBaseChangeLimits B S hS (E ⋙ yoneda))
    (c : Cone E) (hc : IsLimit (yoneda.mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) := by
  have hcs : IsLimit c := isLimitOfReflects yoneda hc
  let D' := E ⋙ BigFppfOver.toScheme B S hS
  have _ : ∀ {i j : J} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (D'.map f) := hAffine
  let φ := limit.lift D' ((BigFppfOver.toScheme B S hS).mapCone c)
  have hmono : Mono φ := BigFppfOver.mono_lift_mapCone_toScheme hcs (limit.isLimit D')
  have : IsIso φ := by
    obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
    have hAffSp : ∀ {i j : J} (f : i ⟶ j), Space.IsAffineHom B S hS ((E ⋙ yoneda).map f) :=
      fun f => Space.isAffineHom_of_presheaf
        ((Space.presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsAffineHom)
          inferInstance (E.map f)).mpr (hAffine f))
    have key : ∀ U : (D'.obj i₀).affineOpens, B.Contains (limit.π D' i₀ ⁻¹ᵁ U.1 : Scheme) := by
      intro U
      have hU : B.Contains (U.1 : Scheme) :=
        Scheme.size_lt_of_isOpenImmersion U.1.ι (E.obj i₀).left.property
      let Zs : BigAffineFppf B S hS :=
        ⟨siteObject B S hS hU (U.1.ι ≫ B.inclusion.map (E.obj i₀).hom), U.2⟩
      let ιs : (BigAffineFppf.inclusion B S hS).obj Zs ⟶ E.obj i₀ :=
        Over.homMk (ObjectProperty.homMk U.1.ι) (ObjectProperty.hom_ext _ rfl)
      let Ch := Space.affineChartSystem B S hS i₀ (E ⋙ yoneda) Zs (yoneda.map ιs) hAffSp
      exact BigFppfOver.contains_of_isPullback_of_limitInSite Ch
        (hconv i₀ Zs (yoneda.map ιs) Ch.diagram Ch.iso) (limit.isLimit D')
        (limit.π D' i₀ ⁻¹ᵁ U.1).ι (limit.π D' i₀ ∣_ U.1) (isPullback_morphismRestrict _ _).flip
    have hsec : ∀ U : (D'.obj i₀).affineOpens, ∃ s : (limit.π D' i₀ ⁻¹ᵁ U.1 : Scheme) ⟶
        (BigFppfOver.toScheme B S hS).obj c.pt, s ≫ φ = (limit.π D' i₀ ⁻¹ᵁ U.1).ι := by
      intro U
      obtain ⟨s, hs⟩ := BigFppfOver.exists_toScheme_lift_of_isLimit hcs (key U)
        (fun j => (limit.π D' i₀ ⁻¹ᵁ U.1).ι ≫ limit.π D' j)
        (fun f => by
          rw [Category.assoc]
          exact congrArg (_ ≫ ·) (limit.w D' f))
      refine ⟨s, limit.hom_ext fun j => ?_⟩
      rw [Category.assoc, limit.lift_π]
      exact hs j
    exact Scheme.isIso_of_mono_of_iSup_eq_top φ
      (fun U : (D'.obj i₀).affineOpens => limit.π D' i₀ ⁻¹ᵁ U.1)
      ((limit.π D' i₀).iSup_preimage_eq_top (iSup_affineOpens_eq_top _))
      (fun U => (hsec U).choose) (fun U => (hsec U).choose_spec)
  have : IsIso ((limit.isLimit D').lift ((BigFppfOver.toScheme B S hS).mapCone c)) := this
  exact IsLimit.ofPointIso (limit.isLimit D')

end SchemeLimit

/-! ### Systems with a chart system satisfy the convention -/

section ChartSystem

/-- The stages of the base change along `p` of a chart system are base changes of the stages of a
system `V` with a cartesian transformation to the diagram, compatibly with the transition
morphisms. -/
theorem Space.AffineChartSystem.exists_isPullback_pullbackDiagramAlong
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : J} {Z : BigAffineFppf B S hS}
    {g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i}
    (C : Space.AffineChartSystem B S hS i D Z g)
    (V : J ⥤ BigFppfOver B S hS) (v : V ⋙ yoneda ⟶ D)
    (hcart : ∀ k : Over i,
      IsPullback (yoneda.map (V.map k.hom)) (v.app k.left) (v.app i) (D.map k.hom))
    {Z' : BigFppfOver B S hS} (p : Z' ⟶ (BigAffineFppf.inclusion B S hS).obj Z)
    (q : Z' ⟶ V.obj i) (hZ' : IsPullback (yoneda.map q) (yoneda.map p) (v.app i) g)
    (wk : ∀ k, C.siteDiagram.obj k ⟶ (BigAffineFppf.inclusion B S hS).obj Z)
    (hwk : ∀ k, yoneda.map (wk k) = C.baseMap k)
    (hw : ∀ {k l : Over i} (f : k ⟶ l), C.siteDiagram.map f ≫ wk l = wk k) :
    ∃ β : ∀ k : Over i, (pullbackDiagramAlong C.siteDiagram wk hw p).obj k ⟶ V.obj k.left,
      (∀ k, IsPullback (β k) (pullback.snd (wk k) p) (V.map k.hom) q) ∧
      ∀ {k l : Over i} (f : k ⟶ l),
        (pullbackDiagramAlong C.siteDiagram wk hw p).map f ≫ β l = β k ≫ V.map f.left := by
  let Q : Over i ⥤ BigFppfOver B S hS := pullbackDiagramAlong C.siteDiagram wk hw p
  have hout : ∀ k, IsPullback (yoneda.map (pullback.fst (wk k) p) ≫ C.stageMap k)
      (yoneda.map (pullback.snd (wk k) p)) (D.map k.hom) (yoneda.map p ≫ g) := fun k => by
    have h1 := (IsPullback.of_hasPullback (wk k) p).map yoneda
    rw [hwk] at h1
    exact h1.paste_horiz (C.isPullback k)
  have hβw : ∀ k, (yoneda.map (pullback.snd (wk k) p) ≫ yoneda.map q) ≫ v.app i =
      (yoneda.map (pullback.fst (wk k) p) ≫ C.stageMap k) ≫ D.map k.hom := fun k => by
    rw [Category.assoc, hZ'.w]
    exact (hout k).w.symm
  obtain ⟨β, hβ⟩ : ∃ β : ∀ k : Over i, Q.obj k ⟶ V.obj k.left,
      ∀ k, yoneda.map (β k) = (hcart k).lift _ _ (hβw k) :=
    ⟨fun k => yoneda.preimage ((hcart k).lift _ _ (hβw k)), fun k => Functor.map_preimage _ _⟩
  have hβpb : ∀ k, IsPullback (β k) (pullback.snd (wk k) p) (V.map k.hom) q := fun k => by
    refine IsPullback.of_map_of_faithful yoneda ?_
    rw [hβ]
    refine (IsPullback.of_bot (v₁₁ := (hcart k).lift _ _ (hβw k)) ?_
      ((hcart k).lift_fst _ _ _).symm (hcart k)).flip
    rw [(hcart k).lift_snd, hZ'.w]
    exact (hout k).flip
  have hβnat : ∀ {k l : Over i} (f : k ⟶ l), Q.map f ≫ β l = β k ≫ V.map f.left := by
    intro k l f
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hβ, hβ]
    refine (hcart l).hom_ext ?_ ?_
    · have h1 : yoneda.map (V.map f.left) ≫ yoneda.map (V.map l.hom) =
          yoneda.map (V.map k.hom) := by
        rw [← Functor.map_comp, ← V.map_comp, Over.w f]
      have h2 : yoneda.map (Q.map f) ≫ yoneda.map (pullback.snd (wk l) p) =
          yoneda.map (pullback.snd (wk k) p) := by
        rw [← Functor.map_comp, pullbackDiagramAlong_map_snd]
      simp only [Category.assoc, IsPullback.lift_fst, h1, reassoc_of% h2]
    · have h3 : yoneda.map (Q.map f) ≫ yoneda.map (pullback.fst (wk l) p) =
          yoneda.map (pullback.fst (wk k) p) ≫ yoneda.map (C.siteDiagram.map f) := by
        rw [← Functor.map_comp, pullbackDiagramAlong_map_fst, Functor.map_comp]
      have h4 : yoneda.map (V.map f.left) ≫ v.app l.left = v.app k.left ≫ D.map f.left :=
        v.naturality f.left
      simp only [Category.assoc, IsPullback.lift_snd, h4, IsPullback.lift_snd_assoc,
        reassoc_of% h3]
      exact congrArg (_ ≫ ·) (C.stageMap_naturality f)
  exact ⟨β, hβpb, hβnat⟩

/-- The limit of the underlying schemes of a chart system lies in the site once the stages of its
base change along a flat surjection `p` are base changes of the stages of a system `V` whose limit
lies in the site. -/
theorem Space.AffineChartSystem.limitInSite_of_isPullback_pullbackDiagramAlong
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : J} {Z : BigAffineFppf B S hS}
    {g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i}
    (C : Space.AffineChartSystem B S hS i D Z g) (V : J ⥤ BigFppfOver B S hS)
    {Z' : BigFppfOver B S hS} (p : Z' ⟶ (BigAffineFppf.inclusion B S hS).obj Z)
    (q : Z' ⟶ V.obj i) [Surjective ((BigFppfOver.toScheme B S hS).map p)]
    [Flat ((BigFppfOver.toScheme B S hS).map p)]
    (c : Cone (V ⋙ BigFppfOver.toScheme B S hS)) (hc : IsLimit c) (hsize : B.Contains c.pt)
    (wk : ∀ k, C.siteDiagram.obj k ⟶ (BigAffineFppf.inclusion B S hS).obj Z)
    (hw : ∀ {k l : Over i} (f : k ⟶ l), C.siteDiagram.map f ≫ wk l = wk k)
    (β : ∀ k : Over i, (pullbackDiagramAlong C.siteDiagram wk hw p).obj k ⟶ V.obj k.left)
    (hβpb : ∀ k, IsPullback (β k) (pullback.snd (wk k) p) (V.map k.hom) q)
    (hβnat : ∀ {k l : Over i} (f : k ⟶ l),
      (pullbackDiagramAlong C.siteDiagram wk hw p).map f ≫ β l = β k ≫ V.map f.left) :
    BigFppfOver.LimitInSite C.siteDiagram := by
  intro e he
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let Q : Over i ⥤ BigFppfOver B S hS := pullbackDiagramAlong C.siteDiagram wk hw p
  let T := BigFppfOver.toScheme B S hS
  let k₀ : Over i := Over.mk (𝟙 i)
  let t₁ : e.pt ⟶ T.obj ((BigAffineFppf.inclusion B S hS).obj Z) := e.π.app k₀ ≫ T.map (wk k₀)
  have ht₁ : ∀ k, e.π.app k ≫ T.map (wk k) = t₁ := fun k => by
    let h₀ : k ⟶ k₀ := Over.homMk k.hom (Category.comp_id _)
    have h := e.w h₀
    change e.π.app k ≫ T.map (C.siteDiagram.map h₀) = _ at h
    rw [← hw h₀, T.map_comp, ← Category.assoc, h]
  have hγ : ∀ {k l : Over i} (f : k ⟶ l),
      (Q ⋙ T).map f ≫ T.map (pullback.snd (wk l) p) = T.map (pullback.snd (wk k) p) :=
    fun f => by rw [Functor.comp_map, ← T.map_comp, pullbackDiagramAlong_map_snd]
  have _ : IsConnected (Over i) := IsCofiltered.isConnected _
  have lim₁ := isLimitConeOfIsPullbackStages (G := Q ⋙ T)
    (F := underlyingDiagram C.siteDiagram) (fun k => T.map (pullback.fst (wk k) p))
    (fun f => by
      show T.map (Q.map f) ≫ _ = _ ≫ T.map (C.siteDiagram.map f)
      rw [← T.map_comp, pullbackDiagramAlong_map_fst, T.map_comp])
    (fun k => T.map (wk k)) (T.map p) (fun k => T.map (pullback.snd (wk k) p)) hγ
    (fun k => (IsPullback.of_hasPullback (wk k) p).map T) e t₁ ht₁
    (pullback.fst t₁ (T.map p)) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) he
  have lim₂ := isLimitConeOfIsPullbackStages (G := Q ⋙ T)
    (F := Over.forget i ⋙ V ⋙ T) (fun k => T.map (β k))
    (fun f => by
      show T.map (Q.map f) ≫ _ = _ ≫ T.map (V.map f.left)
      rw [← T.map_comp, hβnat, T.map_comp])
    (fun k => T.map (V.map k.hom)) (T.map q) (fun k => T.map (pullback.snd (wk k) p)) hγ
    (fun k => (hβpb k).map T) (c.whisker (Over.forget i)) (c.π.app i) (fun k => c.w k.hom)
    (pullback.fst (c.π.app i) (T.map q)) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)
  have hsz := Scheme.size_congr (lim₁.conePointUniqueUpToIso lim₂)
  rw [coneOfIsPullbackStages_pt, coneOfIsPullbackStages_pt] at hsz
  have hsz₁ : B.Contains (pullback t₁ (T.map p)) := by
    show Scheme.size _ < _
    rw [hsz]
    exact Scheme.size_pullback_lt _ _ hsize Z'.left.property
  exact Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit B.cutoff_isStrongPrelimit
    (pullback.fst t₁ (T.map p)) hsz₁

/-- **A chart system of an inverse system with a cartesian chart system satisfies the
convention.** Let `C` be a chart system of `D` at the stage `i` and the affine point `g`, let
`v : V ⟶ D` be a transformation from a system of objects of the site whose squares over `i` are
cartesian, and let `Z'` be the base change of `v i` along `g`, given by `p : Z' ⟶ Z` and
`q : Z' ⟶ V i`, with `p` flat and surjective. If the limit of the underlying schemes of `V` lies in
the site, then so does the limit `L` of the underlying schemes of the charts.

Each `C k ×_Z Z'` is `D k ×_{D i} Z'`, which is `V k ×_{V i} Z'` because the squares of `v` are
cartesian. Base change commutes with the limits over the slice
(`CategoryTheory.Limits.isLimitConeOfIsPullbackStages`), and the slice is initial, so
`L ×_Z Z'` and `c.pt ×_{V i} Z'` are both limits of the same diagram of schemes, hence
isomorphic; the second lies in the site by Stacks 04T6. The projection `L ×_Z Z' ⟶ L` is a base
change of `p`, hence flat and surjective, so `L` lies in the site as well. -/
theorem Space.AffineChartSystem.limitInSite_of_isPullback
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    {D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : J} {Z : BigAffineFppf B S hS}
    {g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i}
    (C : Space.AffineChartSystem B S hS i D Z g)
    (V : J ⥤ BigFppfOver B S hS) (v : V ⋙ yoneda ⟶ D)
    (hcart : ∀ k : Over i,
      IsPullback (yoneda.map (V.map k.hom)) (v.app k.left) (v.app i) (D.map k.hom))
    {Z' : BigFppfOver B S hS} (p : Z' ⟶ (BigAffineFppf.inclusion B S hS).obj Z)
    (q : Z' ⟶ V.obj i) (hZ' : IsPullback (yoneda.map q) (yoneda.map p) (v.app i) g)
    [Surjective ((BigFppfOver.toScheme B S hS).map p)]
    [Flat ((BigFppfOver.toScheme B S hS).map p)]
    (c : Cone (V ⋙ BigFppfOver.toScheme B S hS)) (hc : IsLimit c) (hsize : B.Contains c.pt) :
    BigFppfOver.LimitInSite C.siteDiagram := by
  obtain ⟨wk, hwk⟩ : ∃ wk : ∀ k, C.siteDiagram.obj k ⟶ (BigAffineFppf.inclusion B S hS).obj Z,
      ∀ k, yoneda.map (wk k) = C.baseMap k :=
    ⟨fun k => yoneda.preimage (C.baseMap k), fun k => by simp⟩
  have hw : ∀ {k l : Over i} (f : k ⟶ l), C.siteDiagram.map f ≫ wk l = wk k := fun f =>
    yoneda.map_injective (by simpa only [Functor.map_comp, hwk] using C.baseMap_naturality f)
  obtain ⟨β, hβpb, hβnat⟩ := C.exists_isPullback_pullbackDiagramAlong V v hcart p q hZ' wk hwk hw
  exact C.limitInSite_of_isPullback_pullbackDiagramAlong V p q c hc hsize wk hw β hβpb hβnat

/-- **The chapter's convention holds for an inverse system with a chart system whose limit lies in
the site.** Let `V` be an inverse system of objects of the site with a transformation
`v : V ⟶ D` whose components are surjective and étale and whose naturality squares are
cartesian, and suppose the limit of the underlying schemes of `V` lies in the site. Then every
limit of base changes the convention `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`
quantifies over lies in the site.

At a stage `i`, an affine test object `Z` and a point `g` of `D i`, the base change `Z'` of the
chart `v i` along `g` is an object of the site because `v i` is representable, and it is
surjective and étale, hence flat, over `Z`;
`AlgebraicGeometry.Space.AffineChartSystem.limitInSite_of_isPullback` then applies to the lift
of the diagram of base changes. Neither algebraicity of the stages nor affineness of the
transition morphisms is used. -/
theorem Space.siteContainsBaseChangeLimits_of_chartSystem
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (V : J ⥤ BigFppfOver B S hS) (v : V ⋙ yoneda ⟶ D)
    (hvs : ∀ j, (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (v.app j))
    (hve : ∀ j, (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (v.app j))
    (hcart : ∀ {i j : J} (f : i ⟶ j),
      IsPullback (yoneda.map (V.map f)) (v.app i) (v.app j) (D.map f))
    (c : Cone (V ⋙ BigFppfOver.toScheme B S hS)) (hc : IsLimit c) (hsize : B.Contains c.pt) :
    Space.SiteContainsBaseChangeLimits B S hS D := by
  intro i Z g W hW
  obtain ⟨Z', p, q₀, hZ'⟩ := (hvs i).1 g
  have _ : Etale ((BigFppfOver.toScheme B S hS).map p) := (hve i).2 g q₀ p hZ'
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map p) := (hvs i).2 g q₀ p hZ'
  exact Space.AffineChartSystem.limitInSite_of_isPullback ⟨W, hW⟩ V v (fun k => hcart k.hom) p
    (yoneda.preimage q₀) (by rwa [Functor.map_preimage]) c hc hsize

end ChartSystem

end AlgebraicGeometry
