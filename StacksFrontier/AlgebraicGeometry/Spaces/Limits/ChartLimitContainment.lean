module

public import StacksFrontier.AlgebraicGeometry.Spaces.BigFppfLimitOfContains
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Limits of affine charts of an inverse system that stay in the site

Let `D` be an inverse system of presheaves on the big fppf site of `S`. A *cartesian system of
affine charts* of `D` at a stage `i₀` over a scheme-valued point `f₀ : h_{U₀} ⟶ D i₀` is a
diagram `V` of affine objects of the site, indexed by the stages above `i₀`, together with
natural maps `h_{V_j} ⟶ D j` and `h_{V_j} ⟶ h_{U₀}` exhibiting each `h_{V_j}` as the fibre
product `D j ×_{D i₀} h_{U₀}`. The cofiltered limit of the underlying affine schemes always
exists in the category of all schemes; the system *has contained chart limits* when that limit
is contained in the site, for every such chart system.

Under this condition the limit of the charts is a limit in the site, preserved by the underlying
scheme functor, and it represents the base change of the limit projection ([Stacks, Tag 07SF]).
The condition holds when the index category has fewer objects than the cofinality of the site's
cutoff, and it holds for inverse systems of objects of the site whose limit is itself in the
site, whatever the size of the index category.

## Main definitions

* `AlgebraicGeometry.Space.HasContainedChartLimits`: the condition.

## Main results

* `AlgebraicGeometry.Space.HasContainedChartLimits.of_mk_lt`: an index category smaller than the
  cofinality of the cutoff gives the condition.
* `AlgebraicGeometry.Space.HasContainedChartLimits.limitBridge`: the limit of a chart system in
  the site under the condition ([Stacks, Tag 07SF]).
* `AlgebraicGeometry.Space.HasContainedChartLimits.of_cartesian`: the condition passes along a
  cartesian natural transformation, in particular to base changes and along isomorphisms.
* `AlgebraicGeometry.Space.HasContainedChartLimits.restrict`: it passes to the stages above a
  fixed index of a directed set.

## Implementation notes

The chart system is part of the quantified data, together with its two natural maps, rather than
being the one chosen by `AlgebraicGeometry.Space.affineChartSystem`: then the condition is stable
under the operations above by pasting of cartesian squares, with no identification of chosen
fibre products.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Condition

variable {I : Type u} [Category.{u} I]

/-- **The limits of the affine charts of an inverse system stay in the site.** For every stage
`i₀`, every scheme-valued point `f₀ : h_{U₀} ⟶ D i₀` and every diagram `V` of affine objects of
the site indexed by the stages above `i₀` with natural maps `π : h_{V_j} ⟶ D j` and
`b : h_{V_j} ⟶ h_{U₀}` making each `h_{V_j}` the fibre product `D j ×_{D i₀} h_{U₀}`, the diagram
of underlying schemes has a limit whose vertex is contained in the site. -/
def HasContainedChartLimits (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (i₀ : I) (U₀ : BigFppfOver B S hS) (f₀ : yoneda.obj U₀ ⟶ D.obj i₀)
    (V : Over i₀ ⥤ BigFppfOver B S hS) (π : V ⋙ yoneda ⟶ Over.forget i₀ ⋙ D)
    (b : V ⋙ yoneda ⟶ (Functor.const (Over i₀)).obj (yoneda.obj U₀)),
    (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j))) →
    (∀ j : Over i₀, IsPullback (π.app j) (b.app j) (D.map j.hom) f₀) →
    ∃ c : Cone (V ⋙ BigFppfOver.toScheme B S hS), Nonempty (IsLimit c) ∧ B.Contains c.pt

variable {B S hS}

namespace HasContainedChartLimits

variable (B S hS) in
/-- **An index category smaller than the cofinality of the cutoff gives contained chart
limits.** If the cofiltered category `I` and each of its sets of morphisms have cardinality less
than the cofinality of the cutoff of the site, every inverse system indexed by `I` has contained
chart limits. -/
theorem of_mk_lt [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hI : #I < B.cutoff.ord.cof) (hhom : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) :
    HasContainedChartLimits B S hS D := by
  intro i₀ U₀ f₀ V π b hV _
  have hJ : #(Over i₀) < B.cutoff.ord.cof := mk_over_lt B.aleph0_lt_cutoff_cof hI hhom i₀
  have hV' : ∀ j, IsAffine ((V ⋙ BigFppfOver.toScheme B S hS).obj j) := hV
  have : HasLimit (V ⋙ BigFppfOver.toScheme B S hS) :=
    CofilteredLimit.hasLimit_of_isAffine (V ⋙ BigFppfOver.toScheme B S hS)
  exact ⟨limit.cone _, ⟨limit.isLimit _⟩,
    Scheme.size_lt_of_isLimit_of_isAffine B.aleph0_lt_cutoff _ hV' hJ
      (fun j => (V.obj j).left.property) (limit.isLimit _)⟩

variable (B S hS) in
/-- **A directed index set smaller than the cofinality of the cutoff gives contained chart
limits.** If `I` is a nonempty directed set of cardinality less than the cofinality of the
cutoff of the site, every inverse system indexed by `Iᵒᵖ` has contained chart limits. -/
theorem of_mk_lt_preorder {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hI : #I < B.cutoff.ord.cof) :
    HasContainedChartLimits B S hS D :=
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  of_mk_lt B S hS D
    ((Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ ↦ rfl, fun _ ↦ rfl⟩)).trans_lt hI)
    fun _ _ ↦ (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- **Contained chart limits pass along a cartesian natural transformation.** If `φ : D' ⟶ D`
has cartesian naturality squares and `D` has contained chart limits, then so does `D'`. -/
theorem of_cartesian {D D' : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : D' ⟶ D)
    (hφ : ∀ {i j : I} (g : i ⟶ j), IsPullback (D'.map g) (φ.app i) (φ.app j) (D.map g))
    (hD : HasContainedChartLimits B S hS D) : HasContainedChartLimits B S hS D' := by
  intro i₀ U₀ f₀ V π b hV hpb
  exact hD i₀ U₀ (f₀ ≫ φ.app i₀) V (π ≫ Functor.whiskerLeft (Over.forget i₀) φ) b hV
    fun j => (hpb j).paste_horiz (hφ j.hom).flip

/-- Contained chart limits are invariant under isomorphism of inverse systems. -/
theorem of_iso {D D' : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : D' ≅ D)
    (hD : HasContainedChartLimits B S hS D) : HasContainedChartLimits B S hS D' :=
  of_cartesian e.hom (fun g => IsPullback.of_vert_isIso ⟨e.hom.naturality g⟩) hD

end HasContainedChartLimits

end Condition

/-! ### The limit of a chart system -/

section LimitBridge

variable {B S hS} {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

namespace AffineChartSystem

variable (C : AffineChartSystem B S hS i₀ D U₀ f₀)

/-- The projections of the charts to their stages, as a natural transformation. -/
noncomputable def stageNatTrans : C.siteDiagram ⋙ yoneda ⟶ Over.forget i₀ ⋙ D where
  app := C.stageMap
  naturality _ _ g := C.stageMap_naturality g

/-- The projections of the charts to the chosen affine point, as a natural transformation to
the constant diagram. -/
noncomputable def baseNatTrans :
    C.siteDiagram ⋙ yoneda ⟶
      (Functor.const (Over i₀)).obj (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)) where
  app := C.baseMap
  naturality _ _ g := (C.baseMap_naturality g).trans (Category.comp_id _).symm

/-- **The limit of a chart system is contained in the site** when the inverse system has
contained chart limits. -/
theorem exists_isLimit_contains (hD : HasContainedChartLimits B S hS D) :
    ∃ c : Cone C.schemeDiagram, Nonempty (IsLimit c) ∧ B.Contains c.pt :=
  hD i₀ _ f₀ C.siteDiagram C.stageNatTrans C.baseNatTrans C.isAffine_obj C.isPullback

/-- **[Stacks, Tag 07SF], for a chart system with contained limit.** A chart system indexed by a
cofiltered slice whose diagram of schemes has a limit inside the site has a limit in the big
fppf site of `S`, whose underlying scheme is a limit of the underlying schemes of the charts and
which represents the base change of `limit.π D i₀` along `f₀`. -/
noncomputable def limitBridgeOfContains [IsCofiltered I]
    (h : ∃ c : Cone C.schemeDiagram, Nonempty (IsLimit c) ∧ B.Contains c.pt) :
    LimitBridge C := by
  classical
  have hc := h.choose_spec
  have _ : HasLimit C.siteDiagram :=
    BigFppfOver.hasLimit_of_isLimit_contains C.siteDiagram hc.1.some hc.2
  have _ := BigFppfOver.preservesLimit_toScheme_of_isLimit_contains C.siteDiagram hc.1.some hc.2
  have hyoneda : IsLimit (yoneda.mapCone (limit.cone C.siteDiagram)) :=
    isLimitOfPreserves yoneda (limit.isLimit C.siteDiagram)
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj
      (yoneda.mapCone (limit.cone C.siteDiagram))) :=
    (IsLimit.postcomposeHomEquiv C.iso (yoneda.mapCone (limit.cone C.siteDiagram))).symm
      hyoneda
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  exact
    { cone := limit.cone C.siteDiagram
      isLimit := limit.isLimit C.siteDiagram
      schemeIsLimit :=
        isLimitOfPreserves (BigFppfOver.toScheme B S hS) (limit.isLimit C.siteDiagram)
      iso := hpost.conePointUniqueUpToIso hbase
      iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j }

end AffineChartSystem

/-- **[Stacks, Tag 07SF] under contained chart limits.** The limit in the site of a chart system
of an inverse system with contained chart limits. -/
noncomputable def HasContainedChartLimits.limitBridge [IsCofiltered I]
    (hD : HasContainedChartLimits B S hS D) (C : AffineChartSystem B S hS i₀ D U₀ f₀) :
    AffineChartSystem.LimitBridge C :=
  C.limitBridgeOfContains (C.exists_isLimit_contains hD)

/-- **[Stacks, Tag 07SF], part (1), under contained chart limits.** If the transition morphisms
of a cofiltered inverse system are affine and its chart limits are contained, every projection
from its limit is affine. -/
theorem HasContainedChartLimits.isAffineHom_limitπ [IsCofiltered I]
    (hD : HasContainedChartLimits B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i : I) :
    IsAffineHom B S hS (limit.π D i) := by
  intro Z g
  let L := hD.limitBridge (affineChartSystem B S hS i D Z g hAffine)
  refine ⟨⟨L.cone.pt, L.isAffine_pt⟩, L.toLimit, yoneda.preimage L.toBase, ?_⟩
  rw [Functor.map_preimage]
  exact L.isPullback

end LimitBridge

/-! ### Products with a fixed object -/

section Products

variable {B S hS} {K : Type u} [Category.{u} K] [IsConnected K]

/-- **Products with a fixed object preserve limits that the underlying scheme functor
preserves.** If the index category is connected and the image of a cone `c` in schemes is a
limit, so is the image of `W ⨯ c`. -/
noncomputable def BigFppfOver.isLimitToSchemeMapConeProd {V : K ⥤ BigFppfOver B S hS}
    {c : Cone V} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (W : BigFppfOver B S hS) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.obj W).mapCone c)) := by
  haveI : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  refine isLimitOfIsPullbackOfIsConnected (I := K)
    (F := (V ⋙ prod.functor.obj W) ⋙ BigFppfOver.toScheme B S hS)
    (G := V ⋙ BigFppfOver.toScheme B S hS)
    { app := fun j => (BigFppfOver.toScheme B S hS).map
        (show (prod.functor.obj W).obj (V.obj j) ⟶ V.obj j from prod.snd)
      naturality := fun j k g => by
        simp only [Functor.comp_obj, Functor.comp_map]
        exact congrArg (BigFppfOver.toScheme B S hS).map (prod.map_snd _ _) }
    ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.obj W).mapCone c))
    ((BigFppfOver.toScheme B S hS).mapCone c)
    { hom := (BigFppfOver.toScheme B S hS).map
        (show (prod.functor.obj W).obj c.pt ⟶ c.pt from prod.snd)
      w := fun j => by
        simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
          Functor.mapCone_pt]
        exact congrArg (BigFppfOver.toScheme B S hS).map (prod.map_snd _ _).symm }
    (fun j => ?_) hc
  have h : IsPullback (prod.map (𝟙 W) (c.π.app j)) prod.snd prod.snd (c.π.app j) :=
    IsPullback.of_iso_pullback ⟨prod.map_snd _ _⟩ (pullbackProdSndIsoProd (c.π.app j) W).symm
      (pullback.lift_fst _ _ _) (by simp)
  exact h.map (BigFppfOver.toScheme B S hS)

/-- **Products with a fixed object on the right preserve limits that the underlying scheme
functor preserves.** If the index category is connected and the image of a cone `c` in schemes
is a limit, so is the image of `c ⨯ W`. -/
noncomputable def BigFppfOver.isLimitToSchemeMapConeProdFlip {V : K ⥤ BigFppfOver B S hS}
    {c : Cone V} (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (W : BigFppfOver B S hS) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.flip.obj W).mapCone c)) := by
  haveI : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  refine isLimitOfIsPullbackOfIsConnected (I := K)
    (F := (V ⋙ prod.functor.flip.obj W) ⋙ BigFppfOver.toScheme B S hS)
    (G := V ⋙ BigFppfOver.toScheme B S hS)
    { app := fun j => (BigFppfOver.toScheme B S hS).map
        (show (prod.functor.flip.obj W).obj (V.obj j) ⟶ V.obj j from prod.fst)
      naturality := fun j k g => by
        simp only [Functor.comp_obj, Functor.comp_map]
        exact congrArg (BigFppfOver.toScheme B S hS).map (prod.map_fst _ _) }
    ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.flip.obj W).mapCone c))
    ((BigFppfOver.toScheme B S hS).mapCone c)
    { hom := (BigFppfOver.toScheme B S hS).map
        (show (prod.functor.flip.obj W).obj c.pt ⟶ c.pt from prod.fst)
      w := fun j => by
        simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
          Functor.mapCone_pt]
        exact congrArg (BigFppfOver.toScheme B S hS).map (prod.map_fst _ _).symm }
    (fun j => ?_) hc
  have h : IsPullback prod.fst (prod.map (c.π.app j) (𝟙 W)) (c.π.app j) prod.fst :=
    IsPullback.of_iso_pullback ⟨(prod.map_fst _ _).symm⟩
      (pullbackProdFstIsoProd (c.π.app j) W).symm (by simp) (pullback.lift_snd _ _ _)
  exact h.flip.map (BigFppfOver.toScheme B S hS)

end Products

/-! ### Systems of objects of the site with a limit in the site -/

section Representable

variable {B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- **An inverse system of objects of the site whose limit is in the site has contained chart
limits.** If `c` is a cone over a cofiltered diagram `T : I ⥤ Sch/S` whose image in schemes is
a limit, then `T ⋙ yoneda` has contained chart limits, whatever the size of `I`: the limit of a
cartesian chart system `V_j = U₀ ×_{T i₀} T_j` over `p : U₀ ⟶ T i₀` is the fibre product
`U₀ ×_{T i₀} c.pt`, an object of the site. -/
theorem HasContainedChartLimits.of_isLimit_toScheme (T : I ⥤ BigFppfOver B S hS) {c : Cone T}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) :
    HasContainedChartLimits B S hS (T ⋙ yoneda) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  intro i₀ U₀ f₀ V π b hV hpb
  let p : U₀ ⟶ T.obj i₀ := yoneda.preimage f₀
  let pj : ∀ j : Over i₀, V.obj j ⟶ T.obj j.left :=
    fun j => yoneda.preimage (X := V.obj j) (Y := T.obj j.left) (π.app j)
  let qj : ∀ j : Over i₀, V.obj j ⟶ U₀ :=
    fun j => yoneda.preimage (X := V.obj j) (Y := U₀) (b.app j)
  have hpnat : ∀ {j k : Over i₀} (g : j ⟶ k), V.map g ≫ pj k = pj j ≫ T.map g.left :=
    fun {j k} g => yoneda.map_injective (by simpa [pj] using π.naturality g)
  have hqnat : ∀ {j k : Over i₀} (g : j ⟶ k), V.map g ≫ qj k = qj j :=
    fun {j k} g => yoneda.map_injective (by simpa [qj] using b.naturality g)
  have hsite : ∀ j : Over i₀, IsPullback (pj j) (qj j) (T.map j.hom) p := fun j =>
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa [pj, qj, p] using (hpb j).w))
      (by simpa [pj, qj, p] using hpb j)
  let ℓ : ∀ j : Over i₀, pullback (c.π.app i₀) p ⟶ V.obj j := fun j =>
    (hsite j).lift (pullback.fst _ _ ≫ c.π.app j.left) (pullback.snd _ _)
      (by rw [Category.assoc, c.w j.hom, pullback.condition])
  have hℓ₁ : ∀ j, ℓ j ≫ pj j = pullback.fst _ _ ≫ c.π.app j.left := fun j =>
    (hsite j).lift_fst _ _ _
  have hℓ₂ : ∀ j, ℓ j ≫ qj j = pullback.snd _ _ := fun j => (hsite j).lift_snd _ _ _
  have hℓnat : ∀ {j k : Over i₀} (g : j ⟶ k), ℓ j ≫ V.map g = ℓ k := fun {j k} g =>
    (hsite k).hom_ext
      (by rw [Category.assoc, hpnat, ← Category.assoc, hℓ₁, hℓ₁, Category.assoc, c.w g.left])
      (by rw [Category.assoc, hqnat, hℓ₂, hℓ₂])
  let F := BigFppfOver.toScheme B S hS
  let cF : Cone (V ⋙ F) :=
    { pt := F.obj (pullback (c.π.app i₀) p)
      π := { app := fun j => F.map (ℓ j)
             naturality := fun j k g => by
               dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
                 Functor.comp_map]
               rw [Category.id_comp, ← F.map_comp, hℓnat] } }
  have hcG : IsLimit ((F.mapCone c).whisker (Over.forget i₀)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) (F.mapCone c)).symm hcS
  have hcF : IsLimit cF := by
    have : IsConnected (Over i₀) := IsCofiltered.isConnected _
    refine isLimitOfIsPullbackOfIsConnected (I := Over i₀) (F := V ⋙ F)
      (G := Over.forget i₀ ⋙ T ⋙ F)
      { app := fun j => F.map (pj j)
        naturality := fun j k g => by
          dsimp only [Functor.comp_obj, Functor.comp_map, Over.forget_map]
          rw [← F.map_comp, ← F.map_comp, hpnat] }
      cF ((F.mapCone c).whisker (Over.forget i₀))
      { hom := F.map (pullback.fst _ _)
        w := fun j => by
          dsimp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
            Functor.whiskerLeft_app, Functor.mapCone_π_app, Over.forget_obj, cF]
          rw [← F.map_comp, ← F.map_comp, hℓ₁] } (fun j => ?_) hcG
    have s : IsPullback (ℓ j ≫ qj j) (pullback.fst (c.π.app i₀) p) p
        (c.π.app j.left ≫ T.map j.hom) := by
      rw [hℓ₂, c.w j.hom]
      exact (IsPullback.of_hasPullback (c.π.app i₀) p).flip
    exact (IsPullback.of_right s (hℓ₁ j) (hsite j).flip).map F
  exact ⟨cF, ⟨hcF⟩, (pullback (c.π.app i₀) p).left.property⟩

end Representable

/-! ### Restriction to the stages above an index -/

section Restrict

variable {B S hS} {I : Type u} [Preorder I] (a : I)

/-- A stage of the whole index set above a stage `k₀` of the stages above `a`, as a stage above
`a`. -/
abbrev restrictOverObj (k₀ : {i : I // a ≤ i}ᵒᵖ) (j : Over (op k₀.unop.1)) : {i : I // a ≤ i} :=
  ⟨j.left.unop, k₀.unop.2.trans (leOfHom j.hom.unop)⟩

/-- The stages above `k₀` in the whole index set, read as stages above `k₀` in the stages above
`a`. -/
noncomputable def restrictOverFunctor (k₀ : {i : I // a ≤ i}ᵒᵖ) :
    Over (op k₀.unop.1) ⥤ Over k₀ where
  obj j := Over.mk (show op (restrictOverObj a k₀ j) ⟶ k₀ from
    (homOfLE (show k₀.unop ≤ restrictOverObj a k₀ j from leOfHom j.hom.unop)).op)
  map {j j'} g := Over.homMk (show op (restrictOverObj a k₀ j) ⟶ op (restrictOverObj a k₀ j') from
    (homOfLE (show restrictOverObj a k₀ j' ≤ restrictOverObj a k₀ j from
      leOfHom g.left.unop)).op) (Subsingleton.elim _ _)
  map_id _ := Over.OverMorphism.ext (Subsingleton.elim _ _)
  map_comp _ _ := Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- Reading a stage above `k₀` of the stages above `a` in the whole index set and back is the
identity, up to the unique isomorphism. -/
noncomputable def restrictOverUnitIso (k₀ : {i : I // a ≤ i}ᵒᵖ) :
    𝟭 (Over k₀) ≅
      Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op ⋙ restrictOverFunctor a k₀ :=
  NatIso.ofComponents
    (fun j => Over.isoMk
      { hom := (homOfLE (show restrictOverObj a k₀
            ((Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op).obj j) ≤ j.left.unop from
            le_refl j.left.unop.1)).op
        inv := (homOfLE (show j.left.unop ≤ restrictOverObj a k₀
            ((Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op).obj j) from
            le_refl j.left.unop.1)).op
        hom_inv_id := Subsingleton.elim _ _
        inv_hom_id := Subsingleton.elim _ _ }
      (Subsingleton.elim _ _))
    (fun _ => Over.OverMorphism.ext (Subsingleton.elim _ _))

/-- **Contained chart limits pass to the stages above an index.** If an inverse system indexed
by `Iᵒᵖ` has contained chart limits, so does its restriction to the stages above `a`. -/
theorem HasContainedChartLimits.restrict {D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : HasContainedChartLimits B S hS D) :
    HasContainedChartLimits B S hS ((Subtype.mono_coe fun i => a ≤ i).functor.op ⋙ D) := by
  intro k₀ U₀ f₀ V π b hV hpb
  obtain ⟨c, ⟨hc⟩, hcont⟩ :=
    hD (op k₀.unop.1) U₀ f₀ (restrictOverFunctor a k₀ ⋙ V)
      (Functor.whiskerLeft (restrictOverFunctor a k₀) π)
      (Functor.whiskerLeft (restrictOverFunctor a k₀) b)
      (fun j => hV ((restrictOverFunctor a k₀).obj j))
      (fun j => hpb ((restrictOverFunctor a k₀).obj j))
  have : (Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op (X := k₀)).IsEquivalence := by
    refine (CategoryTheory.Equivalence.mk
      (Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op (X := k₀))
      (restrictOverFunctor a k₀) (restrictOverUnitIso a k₀)
      (NatIso.ofComponents (fun j => Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))
        (fun _ => Over.OverMorphism.ext (Subsingleton.elim _ _)))).isEquivalence_functor
  have hw : IsLimit
      (c.whisker (Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op (X := k₀))) :=
    IsLimit.whiskerEquivalence hc
      (Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op (X := k₀)).asEquivalence
  let e : V ⋙ BigFppfOver.toScheme B S hS ≅
      Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op (X := k₀) ⋙
        (restrictOverFunctor a k₀ ⋙ V) ⋙ BigFppfOver.toScheme B S hS :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (restrictOverUnitIso a k₀) (V ⋙ BigFppfOver.toScheme B S hS) ≪≫
        Functor.associator _ _ _
  exact ⟨(Cone.postcompose e.inv).obj
      (c.whisker (Over.post (Subtype.mono_coe fun i => a ≤ i).functor.op (X := k₀))),
    ⟨(IsLimit.postcomposeInvEquiv e _).symm hw⟩, hcont⟩

end Restrict

end AlgebraicGeometry.Space

end
