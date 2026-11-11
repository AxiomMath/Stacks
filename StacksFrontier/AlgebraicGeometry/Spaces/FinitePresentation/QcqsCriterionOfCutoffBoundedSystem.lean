module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
import all StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion

/-!
# Stacks 0CP4 for an inverse system bounded by the cutoff

`AlgebraicGeometry.Space.qcqsLimitSquare_of_relativelyLimitPreserving` proves the implication
(2) ⇒ (3) of Stacks 0CP4 for size-bounded systems: a
relatively limit preserving morphism `f : X ⟶ Y` of algebraic spaces over `S` sees the inverse
limit of a cofiltered system of quasi-compact and quasi-separated algebraic spaces with affine
transition morphisms as the filtered colimit of its stages, stagewise. It asks the index category
to have fewer objects, and fewer morphisms between any two objects, than the cofinality of the
site's cutoff. This file proves the two stagewise halves for a system bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no condition on the cofinality.

The proof is the library's. At a stage `i₀` an affine étale atlas `U₀` and an affine étale atlas
`W₀` of its self-intersection are chosen, and both are base changed to systems of affine charts of
the later stages. The affine criterion, Stacks 06BC
(`AlgebraicGeometry.Space.relativelyLimitPreserving_iff_affineLimit_isPullback`), is applied to the
two chart systems and their limits, and the sheaf property of the stages descends the sections
found on the charts. The bound by the cofinality entered in two places only: the limits of the
chart systems, taken here with
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded` in place of
`AlgebraicGeometry.Space.AffineChartSystem.limitBridge`, and the affine criterion, which is read
here off Stacks 06BC, where it carries no size condition, rather than off
`AlgebraicGeometry.Space.AffineLimitSquare`.

## Main results

* `AlgebraicGeometry.Space.exists_stage_lift_of_relativelyLimitPreserving_of_isCutoffBoundedSystem`
  states that a morphism out of the limit whose composite with `f` comes from a stage comes from
  a stage.
* `AlgebraicGeometry.Space.exists_stage_eq_of_relativelyLimitPreserving_of_isCutoffBoundedSystem`
  states that two morphisms out of a stage that agree over the limit, and after `f` over a later
  stage, agree over a later stage.

## Implementation notes

The elementwise description of the comparison square, its Yoneda transport, the atlas data at a
stage and the descent along the atlas are private in
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentation/QcqsCriterion.lean`, which is imported
with `import all` so that they are used as they stand. Nothing here is registered: Stacks 0CP4 is
registered on `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae_qcqsLimitSquare`.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 06BC](https://stacks.math.columbia.edu/tag/06BC)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u v z z'

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The affine criterion of Stacks 06BC, applied to a chart system of a stage and its limit: the
comparison
map of morphism sets along the charts is injective and surjective stagewise. -/
private theorem chart_square_of_relativelyLimitPreserving {f : X ⟶ Y}
    (hA : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : C.LimitBridge) :
    (∀ (j : Over i₀) (ξ₁ ξ₂ : yoneda.obj (C.siteDiagram.obj j) ⟶ X),
        yoneda.map (L.cone.π.app j) ≫ ξ₁ = yoneda.map (L.cone.π.app j) ≫ ξ₂ →
        ∀ (k : Over i₀) (g : k ⟶ j),
          yoneda.map (C.siteDiagram.map g) ≫ ξ₁ ≫ f =
            yoneda.map (C.siteDiagram.map g) ≫ ξ₂ ≫ f →
          ∃ (m : Over i₀) (h : m ⟶ j),
            yoneda.map (C.siteDiagram.map h) ≫ ξ₁ =
              yoneda.map (C.siteDiagram.map h) ≫ ξ₂) ∧
      ∀ (j : Over i₀) (ξ : yoneda.obj L.cone.pt ⟶ X)
          (η : yoneda.obj (C.siteDiagram.obj j) ⟶ Y),
        ξ ≫ f = yoneda.map (L.cone.π.app j) ≫ η →
        ∃ (k : Over i₀) (g : k ⟶ j) (ζ : yoneda.obj (C.siteDiagram.obj k) ⟶ X),
          yoneda.map (L.cone.π.app k) ≫ ζ = ξ ∧
            ζ ≫ f = yoneda.map (C.siteDiagram.map g) ≫ η := by
  have hsq := (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mp hA
    (Over i₀) C.siteDiagram L.cone L.schemeIsLimit C.isAffine_obj L.isAffine_pt
  have h := (isPullback_colim_iff C.siteDiagram L.cone
    (Functor.whiskerRight f uliftFunctor.{u, u})).mp hsq
  exact ⟨(colimInj_yoneda_iff B S hS C.siteDiagram L.cone f).mpr
      ((colimInj_uliftFunctor_iff f).mp h.1),
    (colimSurj_yoneda_iff B S hS C.siteDiagram L.cone f).mpr
      ((colimSurj_uliftFunctor_iff f).mp h.2)⟩


/-! ### The two halves at a stage -/

/-- Stagewise injectivity of the comparison map, for a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms. -/
private theorem colimInj_limit_of_baseChangeSizeBounded {f : X ⟶ Y}
    (hA : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {ν : Cardinal.{u}} (hSize : #I < B.cutoff) (hν : ν < B.cutoff)
    (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν) (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) (x₁ x₂ : D.obj i₀ ⟶ X) (hx : limit.π D i₀ ≫ x₁ = limit.π D i₀ ≫ x₂)
    (j : I) (g : j ⟶ i₀) (hg : D.map g ≫ x₁ ≫ f = D.map g ≫ x₂ ≫ f) :
    ∃ (k : I) (h : k ⟶ i₀), D.map h ≫ x₁ = D.map h ≫ x₂ := by
  obtain ⟨sd⟩ := nonempty_stageData B S hS hZ D i₀ (hD i₀) (hqc i₀) (hqs i₀)
  obtain ⟨hinj, -⟩ := chart_square_of_relativelyLimitPreserving B S hS hA
    ((chartU B S hS D i₀ sd hAffine).limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB)
  set CU := chartU B S hS D i₀ sd hAffine with hCU
  set LU := CU.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB with hLU
  have hπ : yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      LU.toLimit ≫ limit.π D i₀ :=
    (LU.toLimit_comp_limitπ (Over.mk (𝟙 i₀))).symm
  have h1 : yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫
        CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₁ =
      yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫
        CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₂ := by
    rw [← Category.assoc, ← Category.assoc, hπ, Category.assoc, Category.assoc, hx]
  set hg0 : Over.mk g ⟶ Over.mk (𝟙 i₀) := Over.homMk g (Category.comp_id g) with hhg0
  have hnat : yoneda.map (CU.siteDiagram.map hg0) ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      CU.stageMap (Over.mk g) ≫ D.map g :=
    stageMap_naturality B S hS CU hg0
  have hstep : ∀ xx : D.obj i₀ ⟶ X,
      yoneda.map (CU.siteDiagram.map hg0) ≫ (CU.stageMap (Over.mk (𝟙 i₀)) ≫ xx) ≫ f =
        CU.stageMap (Over.mk g) ≫ D.map g ≫ xx ≫ f := fun xx => by
    rw [Category.assoc, ← Category.assoc, hnat, Category.assoc]
  have h2 : yoneda.map (CU.siteDiagram.map hg0) ≫
        (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₁) ≫ f =
      yoneda.map (CU.siteDiagram.map hg0) ≫
        (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₂) ≫ f := by
    rw [hstep x₁, hstep x₂, hg]
  obtain ⟨m, h', hm⟩ := hinj (Over.mk (𝟙 i₀)) (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₁)
    (CU.stageMap (Over.mk (𝟙 i₀)) ≫ x₂) h1 (Over.mk g) hg0 h2
  refine ⟨m.left, h'.left, ?_⟩
  refine hom_ext_of_etale_atlas B S hS (hD m.left).isSheaf hXsh (CU.stageMap m)
    (stageMap_surj B S hS D i₀ sd hAffine m) (stageMap_etale B S hS D i₀ sd hAffine m) ?_
  have hn : yoneda.map (CU.siteDiagram.map h') ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      CU.stageMap m ≫ D.map h'.left := stageMap_naturality B S hS CU h'
  rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc]
  exact hm

/-- Stagewise surjectivity of the comparison map, for a cofiltered inverse system of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms. -/
private theorem colimSurj_limit_of_baseChangeSizeBounded {f : X ⟶ Y}
    (hA : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    (hXsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {ν : Cardinal.{u}} (hSize : #I < B.cutoff) (hν : ν < B.cutoff)
    (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν) (hB : BaseChangeSizeBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (i₀ : I) (x : limit D ⟶ X) (y : D.obj i₀ ⟶ Y)
    (hxy : x ≫ f = limit.π D i₀ ≫ y) :
    ∃ (j : I) (g : j ⟶ i₀) (z : D.obj j ⟶ X),
      limit.π D j ≫ z = x ∧ z ≫ f = D.map g ≫ y := by
  obtain ⟨sd⟩ := nonempty_stageData B S hS hZ D i₀ (hD i₀) (hqc i₀) (hqs i₀)
  obtain ⟨-, hsurjU⟩ := chart_square_of_relativelyLimitPreserving B S hS hA
    ((chartU B S hS D i₀ sd hAffine).limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB)
  obtain ⟨hinjW, -⟩ := chart_square_of_relativelyLimitPreserving B S hS hA
    ((chartW B S hS D i₀ sd hAffine).limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB)
  set CU := chartU B S hS D i₀ sd hAffine with hCU
  set CW := chartW B S hS D i₀ sd hAffine with hCW
  set LU := CU.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB with hLU
  set LW := CW.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB with hLW
  have hπ0 : LU.toLimit ≫ limit.π D i₀ =
      yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫ CU.stageMap (Over.mk (𝟙 i₀)) :=
    LU.toLimit_comp_limitπ (Over.mk (𝟙 i₀))
  have hc1 : (LU.toLimit ≫ x) ≫ f =
      yoneda.map (LU.cone.π.app (Over.mk (𝟙 i₀))) ≫
        CU.stageMap (Over.mk (𝟙 i₀)) ≫ y := by
    rw [Category.assoc, hxy, ← Category.assoc, hπ0, Category.assoc]
  obtain ⟨k₁, h₁, ξ, hξ₁, hξ₂⟩ := hsurjU (Over.mk (𝟙 i₀)) (LU.toLimit ≫ x)
    (CU.stageMap (Over.mk (𝟙 i₀)) ≫ y) hc1
  have hnat1 : yoneda.map (CU.siteDiagram.map h₁) ≫ CU.stageMap (Over.mk (𝟙 i₀)) =
      CU.stageMap k₁ ≫ D.map h₁.left := stageMap_naturality B S hS CU h₁
  have hξ₂' : ξ ≫ f = CU.stageMap k₁ ≫ D.map h₁.left ≫ y := by
    rw [hξ₂, ← Category.assoc, hnat1, Category.assoc]
  have key : ∀ (a : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj sd.W₀) ⟶
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj sd.U₀))
      (T : ∀ m : Over i₀, yoneda.obj (CW.siteDiagram.obj m) ⟶ yoneda.obj (CU.siteDiagram.obj m)),
      LW.toLimit ≫ limit.π D i₀ = (LW.toBase ≫ a) ≫ sd.f₀ →
      (∀ m, T m ≫ CU.stageMap m = CW.stageMap m) →
      (∀ m, T m ≫ CU.baseMap m = CW.baseMap m ≫ a) →
      ∃ A : yoneda.obj LW.cone.pt ⟶ yoneda.obj LU.cone.pt, A ≫ LU.toLimit = LW.toLimit ∧
        ∀ m : Over i₀, A ≫ yoneda.map (LU.cone.π.app m) = yoneda.map (LW.cone.π.app m) ≫ T m :=
    fun a T hw hT₁ hT₂ =>
    ⟨LU.isPullback.lift _ _ hw, LU.isPullback.lift_fst _ _ _, fun m => by
      refine (CU.isPullback m).hom_ext ?_ ?_
      · rw [Category.assoc, ← LU.toLimit_comp_limitπ m, ← Category.assoc,
          LU.isPullback.lift_fst, LW.toLimit_comp_limitπ m, Category.assoc, hT₁]
      · rw [Category.assoc, LU.baseMap_comp m, LU.isPullback.lift_snd, Category.assoc, hT₂,
          ← Category.assoc, LW.baseMap_comp m]⟩
  obtain ⟨AA, hAA1, hkeyA⟩ := key (yoneda.map sd.α) (testFst B S hS D i₀ sd hAffine)
    (by rw [Category.assoc]; exact LW.isPullback.w)
    (testFst_stageMap B S hS D i₀ sd hAffine) (testFst_baseMap B S hS D i₀ sd hAffine)
  obtain ⟨BB, hBB1, hkeyB⟩ := key (yoneda.map sd.β) (testSnd B S hS D i₀ sd hAffine)
    (by rw [Category.assoc, ← sd.hαβ]; exact LW.isPullback.w)
    (testSnd_stageMap B S hS D i₀ sd hAffine) (testSnd_baseMap B S hS D i₀ sd hAffine)
  have hi1 : yoneda.map (LW.cone.π.app k₁) ≫ testFst B S hS D i₀ sd hAffine k₁ ≫ ξ =
      yoneda.map (LW.cone.π.app k₁) ≫ testSnd B S hS D i₀ sd hAffine k₁ ≫ ξ := by
    rw [← Category.assoc, ← hkeyA k₁, ← Category.assoc, ← hkeyB k₁, Category.assoc,
      Category.assoc, hξ₁, ← Category.assoc, ← Category.assoc, hAA1, hBB1]
  have hcomp : ∀ t : yoneda.obj (CW.siteDiagram.obj k₁) ⟶ yoneda.obj (CU.siteDiagram.obj k₁),
      t ≫ CU.stageMap k₁ = CW.stageMap k₁ →
        (t ≫ ξ) ≫ f = CW.stageMap k₁ ≫ D.map h₁.left ≫ y := by
    intro t ht
    rw [Category.assoc, hξ₂', ← Category.assoc, ht]
  have hi2 : (testFst B S hS D i₀ sd hAffine k₁ ≫ ξ) ≫ f =
      (testSnd B S hS D i₀ sd hAffine k₁ ≫ ξ) ≫ f := by
    rw [hcomp _ (testFst_stageMap B S hS D i₀ sd hAffine k₁),
      hcomp _ (testSnd_stageMap B S hS D i₀ sd hAffine k₁)]
  obtain ⟨k₂, h₂, hk₂⟩ := hinjW k₁ (testFst B S hS D i₀ sd hAffine k₁ ≫ ξ)
    (testSnd B S hS D i₀ sd hAffine k₁ ≫ ξ) hi1 k₁ (𝟙 k₁) (by rw [hi2])
  have hdesc : testFst B S hS D i₀ sd hAffine k₂ ≫
        (yoneda.map (CU.siteDiagram.map h₂) ≫ ξ) =
      testSnd B S hS D i₀ sd hAffine k₂ ≫
        (yoneda.map (CU.siteDiagram.map h₂) ≫ ξ) := by
    rw [← Category.assoc, ← testFst_naturality, ← Category.assoc, ← testSnd_naturality,
      Category.assoc, Category.assoc]
    exact hk₂
  obtain ⟨z, hz⟩ := exists_desc B S hS D i₀ sd hAffine hXsh hD k₂
    (yoneda.map (CU.siteDiagram.map h₂) ≫ ξ) hdesc
  refine ⟨k₂.left, h₂.left ≫ h₁.left, z, ?_, ?_⟩
  · refine hom_ext_of_etale_atlas B S hS (isSheaf_limit B S hS D fun i => (hD i).isSheaf)
      hXsh LU.toLimit (presheaf_of_isPullback B S hS LU.isPullback.flip sd.surj₀)
      (presheaf_of_isPullback B S hS LU.isPullback.flip sd.etale₀) ?_
    rw [← Category.assoc, LU.toLimit_comp_limitπ k₂, Category.assoc, hz, ← Category.assoc,
      ← Functor.map_comp, LU.cone.w h₂, hξ₁]
  · refine hom_ext_of_etale_atlas B S hS (hD k₂.left).isSheaf hYsh (CU.stageMap k₂)
      (stageMap_surj B S hS D i₀ sd hAffine k₂)
      (stageMap_etale B S hS D i₀ sd hAffine k₂) ?_
    rw [← Category.assoc, hz, Category.assoc, hξ₂', ← Category.assoc,
      stageMap_naturality, Category.assoc, D.map_comp, Category.assoc]


/-! ### The two halves for a system bounded by the cutoff -/

/-- **Stacks 0CP4, surjectivity, for an inverse system bounded by the cutoff.** Let `D` be a
cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces over `S` with
affine transition morphisms, bounded by the cutoff, with a limit cone `c`, and let `f : X ⟶ Y`
be a relatively limit preserving morphism of algebraic spaces. If `x : c.pt ⟶ X` lies over the
restriction to the limit of some `y : D i₀ ⟶ Y`, then `x` is the restriction of some
`z : D j ⟶ X` over a later stage `j`, lying over the restriction of `y`.

This is the surjectivity half of `AlgebraicGeometry.Space.affineLimitSquare_iff_qcqsLimitSquare`
with the bound by the cofinality of the cutoff traded for
`AlgebraicGeometry.Space.IsCutoffBoundedSystem`. -/
theorem exists_stage_lift_of_relativelyLimitPreserving_of_isCutoffBoundedSystem
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hDc : IsCutoffBoundedSystem B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    {c : Cone D} (hc : IsLimit c) {f : X ⟶ Y} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    (i₀ : I) (x : c.pt ⟶ X) (y : D.obj i₀ ⟶ Y) (hxy : x ≫ f = c.π.app i₀ ≫ y) :
    ∃ (j : I) (g : j ⟶ i₀) (z : D.obj j ⟶ X), c.π.app j ≫ z = x ∧ z ≫ f = D.map g ≫ y := by
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hDc
  obtain ⟨e, he⟩ : ∃ e : c.pt ≅ limit D, ∀ m : I, e.hom ≫ limit.π D m = c.π.app m :=
    ⟨hc.conePointUniqueUpToIso (limit.isLimit D), fun m => by simp⟩
  have hxy' : (e.inv ≫ x) ≫ f = limit.π D i₀ ≫ y := by
    rw [Category.assoc, hxy, ← he i₀, Category.assoc, ← Category.assoc e.inv e.hom,
      e.inv_hom_id]
    exact Category.id_comp _
  obtain ⟨j, g, z, hz₁, hz₂⟩ := colimSurj_limit_of_baseChangeSizeBounded B S hS hZ hf hX.isSheaf
    hY.isSheaf D hSize hν hHomSize hB hD hqc hqs hAffine i₀ (e.inv ≫ x) y hxy'
  refine ⟨j, g, z, ?_, hz₂⟩
  rw [← he j, Category.assoc, hz₁, ← Category.assoc, e.hom_inv_id]
  exact Category.id_comp _

/-- **Stacks 0CP4, injectivity, for an inverse system bounded by the cutoff.** Let `D` be a
cofiltered inverse system of quasi-compact and quasi-separated algebraic spaces over `S` with
affine transition morphisms, bounded by the cutoff, with a limit cone `c`, and let `f : X ⟶ Y`
be a relatively limit preserving morphism of algebraic spaces. Two morphisms `x₁ x₂ : D i₀ ⟶ X`
which agree over the limit and whose composites with `f` agree over a later stage agree over
some later stage.

This is the injectivity half of `AlgebraicGeometry.Space.affineLimitSquare_iff_qcqsLimitSquare`
with the bound by the cofinality of the cutoff traded for
`AlgebraicGeometry.Space.IsCutoffBoundedSystem`. -/
theorem exists_stage_eq_of_relativelyLimitPreserving_of_isCutoffBoundedSystem
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hDc : IsCutoffBoundedSystem B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    {c : Cone D} (hc : IsLimit c) {f : X ⟶ Y} (hX : IsAlgebraicSpace B S hS X)
    (hf : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    (i₀ : I) (x₁ x₂ : D.obj i₀ ⟶ X) (hx : c.π.app i₀ ≫ x₁ = c.π.app i₀ ≫ x₂)
    (j : I) (g : j ⟶ i₀) (hg : D.map g ≫ x₁ ≫ f = D.map g ≫ x₂ ≫ f) :
    ∃ (k : I) (h : k ⟶ i₀), D.map h ≫ x₁ = D.map h ≫ x₂ := by
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := hDc
  obtain ⟨e, he⟩ : ∃ e : c.pt ≅ limit D, ∀ m : I, e.hom ≫ limit.π D m = c.π.app m :=
    ⟨hc.conePointUniqueUpToIso (limit.isLimit D), fun m => by simp⟩
  have hx' : limit.π D i₀ ≫ x₁ = limit.π D i₀ ≫ x₂ := by
    rw [← Iso.cancel_iso_hom_left e, ← Category.assoc, ← Category.assoc, he i₀]
    exact hx
  exact colimInj_limit_of_baseChangeSizeBounded B S hS hZ hf hX.isSheaf D hSize hν hHomSize hB
    hD hqc hqs hAffine i₀ x₁ x₂ hx' j g hg

end AlgebraicGeometry.Space

end
