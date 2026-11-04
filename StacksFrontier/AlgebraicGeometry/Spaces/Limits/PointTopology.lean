module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The topology on the points of an inverse limit of algebraic spaces

Let `X = limit D` be the limit of a cofiltered inverse system `D` of algebraic spaces over a
scheme `S` with affine transition morphisms. The point topology of `X` is the infimum of the
topologies induced by the limit projections `|X| → |D i|`.

## Main results

* `AlgebraicGeometry.Space.pointTopology_limit`: the point topology of the limit is the
  inverse-limit topology.
* `AlgebraicGeometry.Space.pointTopology_limit_of_mono`: the same conclusion for a system with
  monomorphic transition morphisms, under a cardinality hypothesis free of cofinality.
* `AlgebraicGeometry.Space.exists_affine_etale_chart_point`: every point of an algebraic
  space is hit by an étale chart whose source is an affine object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Two criteria for openness in an inverse-limit topology -/

/-- A set which contains, around each of its points, the preimage of an open neighbourhood at
some stage is open for the infimum of the topologies induced by the maps to the stages. -/
private theorem isOpen_iInf_of_forall_exists_nbhd {ι : Type*} {X : Type*} {Y : ι → Type*}
    (t : ∀ i, TopologicalSpace (Y i)) (p : ∀ i, X → Y i) (W : Set X)
    (h : ∀ x ∈ W, ∃ (i : ι) (V : Set (Y i)), @IsOpen _ (t i) V ∧ p i x ∈ V ∧
      ∀ y, p i y ∈ V → y ∈ W) :
    @IsOpen X (⨅ i, TopologicalSpace.induced (p i) (t i)) W := by
  let _ : TopologicalSpace X := ⨅ i, TopologicalSpace.induced (p i) (t i)
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨i, V, hV, hxV, hsub⟩ := h x hx
  exact ⟨p i ⁻¹' V, fun y hy ↦ hsub y hy,
    hV.preimage (continuous_iff_le_induced.mpr (iInf_le _ i)), hxV⟩

/-- Given a continuous map `q : A → X` over open maps `f i : Aₛ i → Xₛ i` between stages, with
the lifting property for points in each square and the stages of `A` forming a neighbourhood
basis, the stages of `X` provide, around the image of any point of `A`, a neighbourhood basis of
the open sets of `X`. -/
private theorem exists_nbhd_of_chart {ι : Type*} {A X : Type*} {Aₛ : ι → Type*}
    {Xₛ : ι → Type*} [TopologicalSpace A] [TopologicalSpace X]
    [∀ i, TopologicalSpace (Aₛ i)] [∀ i, TopologicalSpace (Xₛ i)]
    (q : A → X) (r : ∀ i, A → Aₛ i) (p : ∀ i, X → Xₛ i) (f : ∀ i, Aₛ i → Xₛ i)
    (hcoord : ∀ i a, p i (q a) = f i (r i a)) (hcont : Continuous q)
    (hopen : ∀ i, IsOpenMap (f i))
    (hfiber : ∀ i x a, p i x = f i a → ∃ a' : A, q a' = x ∧ r i a' = a)
    (hbasis : ∀ a U, IsOpen U → a ∈ U →
      ∃ i V, IsOpen V ∧ r i a ∈ V ∧ ∀ a', r i a' ∈ V → a' ∈ U)
    (W : Set X) (hW : IsOpen W) (a : A) (haW : q a ∈ W) :
    ∃ i O, IsOpen O ∧ p i (q a) ∈ O ∧ ∀ x, p i x ∈ O → x ∈ W := by
  obtain ⟨i, V, hV, haV, hVW⟩ := hbasis a (q ⁻¹' W) (hW.preimage hcont) haW
  refine ⟨i, f i '' V, hopen i V hV, ⟨r i a, haV, (hcoord i a).symm⟩, ?_⟩
  rintro x ⟨a', ha'V, hxa'⟩
  obtain ⟨a'', hq, hr⟩ := hfiber i x a' hxa'.symm
  simpa [hq] using hVW a'' (hr ▸ ha'V)

/-- In a cofiltered limit of schemes with affine transition morphisms, the preimages of the
open sets of the stages form a neighbourhood basis. -/
private theorem exists_stage_nbhd_of_isLimit {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u})
    [∀ {j k : J} (g : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E.map g)]
    (c : Cone E) (hc : IsLimit c) (a : c.pt) (U : Set c.pt) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ (j : J) (V : Set (E.obj j)), IsOpen V ∧ c.π.app j a ∈ V ∧
      ∀ a', c.π.app j a' ∈ V → a' ∈ U := by
  have hbasis := isBasis_preimage_isAffineOpen E c hc
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd] at hbasis
  obtain ⟨W, hW, haW, hWU⟩ := hbasis (U := ⟨U, hU⟩) ha
  obtain ⟨j, V, -, rfl⟩ := hW
  exact ⟨j, V, V.2, haW, fun _ ha' ↦ hWU ha'⟩

/-- In a cofiltered limit of schemes with affine transition morphisms, the preimages of the
open sets of the stages form a neighbourhood basis. -/
alias exists_isOpen_stage_nbhd_of_isLimit := exists_stage_nbhd_of_isLimit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine étale charts through a point -/

/-- Every point of an algebraic space over `S` is the image of a point of an étale chart whose
source is an affine object of the big fppf site of `S`. -/
theorem exists_affine_etale_chart_point (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) :
    ∃ (U : BigAffineFppf B S hS)
      (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U) ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f ∧
        ∃ y, pointsMap B S hS
          (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U)) f y = x := by
  classical
  obtain ⟨V, g, hgSurj, hgEtale⟩ := hX.exists_atlas
  obtain ⟨y, hy⟩ := (surjective_iff_surjective_pointsMap B S hS X hX V g).mp hgSurj x
  obtain ⟨R, j, hj, hrange, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := pointsToScheme B S hS V y) (U := ⊤) (by simp)
  obtain ⟨z₀, hz₀⟩ := hrange
  let Usite : B.Schemes := ⟨Spec R, Scheme.size_lt_of_isOpenImmersion j V.left.property⟩
  let jsite : Usite ⟶ V.left :=
    B.inclusion.preimage (show B.inclusion.obj Usite ⟶ B.inclusion.obj V.left from j)
  let V₀ : BigFppfOver B S hS := Over.mk (jsite ≫ V.hom)
  let a : V₀ ⟶ V := Over.homMk jsite (by rfl)
  have hmap : (BigFppfOver.toScheme B S hS).map a = j := by
    show B.inclusion.map jsite = j
    exact B.inclusion.map_preimage _
  have haffine : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) := by
    show IsAffine (Spec R)
    infer_instance
  refine ⟨⟨V₀, haffine⟩, yoneda.map a ≫ g, ?_, (pointsEquivScheme B S hS V₀).symm z₀, ?_⟩
  · refine etale_comp_of_scheme B S hS a g ?_ hgEtale
    rw [hmap]
    infer_instance
  · have hz : pointsToScheme B S hS V₀ ((pointsEquivScheme B S hS V₀).symm z₀) = z₀ :=
      (pointsEquivScheme B S hS V₀).apply_symm_apply z₀
    have hy₀ : pointsMap B S hS (yoneda.obj V₀) (yoneda.map a)
        ((pointsEquivScheme B S hS V₀).symm z₀) = y := by
      refine injective_pointsToScheme B S hS V ?_
      rw [pointsToScheme_pointsMap, hmap, hz]
      exact hz₀
    rw [pointsMap_comp_apply]
    exact (congrArg (pointsMap B S hS (yoneda.obj V) g) hy₀).trans hy

/-! ### Stage neighbourhoods in a limit of objects of the site -/

/-- In a cofiltered limit of objects of the big fppf site of `S` whose underlying schemes have
affine transition morphisms, the preimages of the open sets of the stages form a neighbourhood
basis of the point topology of the limit. -/
private theorem exists_stage_nbhd_points_of_isLimit {J : Type u} [Category.{u} J]
    [IsCofiltered J] (R : J ⥤ BigFppfOver B S hS)
    [∀ {j k : J} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom ((R ⋙ BigFppfOver.toScheme B S hS).map g)]
    (c : Cone R) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (a : points B S hS (yoneda.obj c.pt)) (U : Set (points B S hS (yoneda.obj c.pt)))
    (hU : IsOpen U) (ha : a ∈ U) :
    ∃ (j : J) (V : Set (points B S hS (yoneda.obj (R.obj j)))), IsOpen V ∧
      pointsMap B S hS (yoneda.obj c.pt) (yoneda.map (c.π.app j)) a ∈ V ∧
      ∀ a', pointsMap B S hS (yoneda.obj c.pt) (yoneda.map (c.π.app j)) a' ∈ V → a' ∈ U := by
  classical
  obtain ⟨j, V, hV, hmem, hsub⟩ := exists_stage_nbhd_of_isLimit
    (R ⋙ BigFppfOver.toScheme B S hS) ((BigFppfOver.toScheme B S hS).mapCone c) hc
    (schemePointsHomeomorph B S hS c.pt a)
    ((schemePointsHomeomorph B S hS c.pt).symm ⁻¹' U)
    (hU.preimage (schemePointsHomeomorph B S hS c.pt).symm.continuous) (by simpa using ha)
  refine ⟨j, schemePointsHomeomorph B S hS (R.obj j) ⁻¹' V,
    hV.preimage (schemePointsHomeomorph B S hS (R.obj j)).continuous, ?_, ?_⟩
  · simpa only [Set.mem_preimage, Functor.mapCone_π_app, schemePointsHomeomorph_apply,
      pointsToScheme_pointsMap] using hmem
  · intro a' ha'
    rw [Set.mem_preimage, schemePointsHomeomorph_apply, pointsToScheme_pointsMap] at ha'
    have hmemU := hsub (schemePointsHomeomorph B S hS c.pt a') ha'
    rwa [Set.mem_preimage, Homeomorph.symm_apply_apply] at hmemU

/-! ### The topology of the limit -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The point topology of the limit of a cofiltered inverse system of algebraic spaces over `S`
with affine transition morphisms is the inverse-limit topology, provided every chart system of
`D` has a limit bridge. -/
theorem pointTopology_limit_of_limitBridge
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hbridge : ∀ {i₀ : I} {U₀ : BigAffineFppf B S hS}
      {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
      (C : AffineChartSystem B S hS i₀ D U₀ f₀), AffineChartSystem.LimitBridge C) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) := by
  classical
  refine le_antisymm
    (le_iInf fun i ↦ continuous_iff_le_induced.mp (continuous_pointsMap B S hS (limit.π D i))) ?_
  intro W hW
  refine isOpen_iInf_of_forall_exists_nbhd (fun i ↦ pointTopology B S hS (D.obj i)) _ W ?_
  intro x hx
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, f₀, hf₀, a₀, ha₀⟩ := exists_affine_etale_chart_point B S hS (D.obj i₀) (hD i₀)
    (pointsMap B S hS (limit D) (limit.π D i₀) x)
  set C := affineChartSystem B S hS i₀ D U₀ f₀ hAffine
  set L := hbridge C
  obtain ⟨a, ha, -⟩ := exists_points_of_isPullback B S hS L.isPullback x a₀ ha₀.symm
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  have hf : ∀ j : Over i₀, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (C.stageMap j) := fun j ↦
    presheaf_of_isPullback B S hS (C.isPullback j).flip hf₀
  obtain ⟨j, V, hV, hxV, hsub⟩ := exists_nbhd_of_chart
    (pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit)
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)))
    (fun j : Over i₀ ↦ pointsMap B S hS (limit D) (limit.π D j.left))
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j)) (C.stageMap j))
    (fun j y ↦ by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, L.toLimit_comp_limitπ j])
    (continuous_pointsMap B S hS L.toLimit)
    (fun j ↦ isOpenMap_pointsMap_of_presheafEtale B S hS (C.stageMap j) (hf j))
    (fun j z w hzw ↦ exists_points_of_isPullback B S hS (L.isPullback_stage j) z w hzw)
    (exists_stage_nbhd_points_of_isLimit B S hS C.siteDiagram L.cone L.schemeIsLimit)
    W hW a (ha ▸ hx)
  exact ⟨j.left, V, hV, ha ▸ hxV, hsub⟩

/-- The point topology of the limit of a cofiltered inverse system of algebraic spaces over `S`
with affine transition morphisms, indexed by a small enough category, is the infimum of the
topologies induced by the limit projections on points. -/
@[stacks 086V]
theorem pointTopology_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) :=
  pointTopology_limit_of_limitBridge B S hS D hD hAffine
    fun C => C.limitBridge hSize hHomSize

/-- The point topology of the limit of a cofiltered inverse system of algebraic spaces over `S`
with monomorphic affine transition morphisms, indexed by a category of size below the cutoff with
hom-sets bounded below the cutoff, is the inverse-limit topology. -/
theorem pointTopology_limit_of_mono {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) :=
  pointTopology_limit_of_limitBridge B S hS D hD hAffine
    fun C => C.limitBridgeOfMono hSize hν hHomSize hMono

/-- The point topology of the limit of a cofiltered inverse system of algebraic spaces over `S`
with affine transition morphisms and uniformly bounded base changes, indexed by a category of
size below the cutoff with hom-sets bounded below the cutoff, is the inverse-limit topology. -/
theorem pointTopology_limit_of_baseChangeSizeBounded {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) :=
  pointTopology_limit_of_limitBridge B S hS D hD hAffine
    fun C => C.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB

/-- Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms. Suppose that for every stage `i₀` and every affine étale chart `f₀` of `D i₀` the
system of base changes of the later stages along `f₀` has a limit in the site on whose points the
preimages of open sets of the charts form a neighbourhood basis. Then the point topology of the
limit of `D` is the infimum of the topologies induced by the limit projections. -/
theorem pointTopology_limit_of_chartLimit
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hchart : ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f₀ →
      ∃ L : AffineChartSystem.ChartLimit (affineChartSystem B S hS i₀ D U₀ f₀ hAffine),
        ∀ (a : points B S hS (yoneda.obj L.cone.pt))
          (U : Set (points B S hS (yoneda.obj L.cone.pt))),
          IsOpen U → a ∈ U →
          ∃ (j : Over i₀) (V : Set (points B S hS (yoneda.obj
              ((affineChartSystem B S hS i₀ D U₀ f₀ hAffine).siteDiagram.obj j)))),
            IsOpen V ∧ pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)) a ∈ V ∧
            ∀ a', pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)) a' ∈ V →
              a' ∈ U) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) := by
  classical
  refine le_antisymm
    (le_iInf fun i ↦ continuous_iff_le_induced.mp (continuous_pointsMap B S hS (limit.π D i))) ?_
  intro W hW
  refine isOpen_iInf_of_forall_exists_nbhd (fun i ↦ pointTopology B S hS (D.obj i)) _ W ?_
  intro x hx
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, f₀, hf₀, a₀, ha₀⟩ := exists_affine_etale_chart_point B S hS (D.obj i₀) (hD i₀)
    (pointsMap B S hS (limit D) (limit.π D i₀) x)
  set C := affineChartSystem B S hS i₀ D U₀ f₀ hAffine
  obtain ⟨L, hbasis⟩ := hchart i₀ U₀ f₀ hf₀
  obtain ⟨a, ha, -⟩ := exists_points_of_isPullback B S hS L.isPullback x a₀ ha₀.symm
  have hf : ∀ j : Over i₀, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (C.stageMap j) := fun j ↦
    presheaf_of_isPullback B S hS (C.isPullback j).flip hf₀
  obtain ⟨j, V, hV, hxV, hsub⟩ := exists_nbhd_of_chart
    (pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit)
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)))
    (fun j : Over i₀ ↦ pointsMap B S hS (limit D) (limit.π D j.left))
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j)) (C.stageMap j))
    (fun j y ↦ by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, L.toLimit_comp_limitπ j])
    (continuous_pointsMap B S hS L.toLimit)
    (fun j ↦ isOpenMap_pointsMap_of_presheafEtale B S hS (C.stageMap j) (hf j))
    (fun j z w hzw ↦ exists_points_of_isPullback B S hS (L.isPullback_stage j) z w hzw)
    hbasis W hW a (ha ▸ hx)
  exact ⟨j.left, V, hV, ha ▸ hxV, hsub⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The point topology of the limit of a cofiltered inverse system of algebraic spaces over `S`
with affine transition morphisms is the inverse-limit topology, provided the limits of the
affine charts of the system lie in the site. -/
theorem pointTopology_limit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) := by
  classical
  refine le_antisymm
    (le_iInf fun i ↦ continuous_iff_le_induced.mp (continuous_pointsMap B S hS (limit.π D i))) ?_
  intro W hW
  refine isOpen_iInf_of_forall_exists_nbhd (fun i ↦ pointTopology B S hS (D.obj i)) _ W ?_
  intro x hx
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, f₀, hf₀, a₀, ha₀⟩ := exists_affine_etale_chart_point B S hS (D.obj i₀) (hD i₀)
    (pointsMap B S hS (limit D) (limit.π D i₀) x)
  set C := affineChartSystem B S hS i₀ D U₀ f₀ hAffine
  set L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hconv)
  obtain ⟨a, ha, -⟩ := exists_points_of_isPullback B S hS L.isPullback x a₀ ha₀.symm
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  have hf : ∀ j : Over i₀, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (C.stageMap j) := fun j ↦
    presheaf_of_isPullback B S hS (C.isPullback j).flip hf₀
  obtain ⟨j, V, hV, hxV, hsub⟩ := exists_nbhd_of_chart
    (pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit)
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)))
    (fun j : Over i₀ ↦ pointsMap B S hS (limit D) (limit.π D j.left))
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j)) (C.stageMap j))
    (fun j y ↦ by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, L.toLimit_comp_limitπ j])
    (continuous_pointsMap B S hS L.toLimit)
    (fun j ↦ isOpenMap_pointsMap_of_presheafEtale B S hS (C.stageMap j) (hf j))
    (fun j z w hzw ↦ exists_points_of_isPullback B S hS (L.isPullback_stage j) z w hzw)
    (exists_stage_nbhd_points_of_isLimit B S hS C.siteDiagram L.cone L.schemeIsLimit)
    W hW a (ha ▸ hx)
  exact ⟨j.left, V, hV, ha ▸ hxV, hsub⟩

/-- The point topology of the limit of a cofiltered inverse system of algebraic spaces over `S`
with affine transition morphisms, indexed by a site-small category, is the infimum of the
topologies induced by the limit projections on points. -/
@[stacks 086V]
theorem pointTopology_limit_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) :=
  pointTopology_limit_of_siteContainsBaseChangeLimits B S hS D
      (IsSiteSmall.siteContainsBaseChangeLimits B S hS D hb) hD hAffine

end AlgebraicGeometry.Space

end
