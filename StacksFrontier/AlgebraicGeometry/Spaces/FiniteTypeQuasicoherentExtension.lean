module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple

/-!
# Extending finite type quasi-coherent submodules along étale morphisms

Let `X` be an algebraic space over a scheme `S` and `F` a quasi-coherent `𝒪_X`-module.  This file
proves the two extension statements behind Stacks 0829, in the language of
`AlgebraicGeometry.Space.ChartSubmodule`:

* `AlgebraicGeometry.Space.exists_fg_comap_spanOfChart_eq` is **the exact extension across a
  quasi-compact open of an affine chart** (the content of Stacks 01PF over an affine scheme): a
  finite type quasi-coherent submodule of `F` over a quasi-compact open `Q` of an affine chart `V₀`
  is the restriction to `Q` of the submodule of `F|_{V₀}` spanned by finitely many sections over
  `V₀`, which may be taken to contain any given finitely generated submodule whose restriction to
  `Q` already lies in the given one.
* `AlgebraicGeometry.Space.chartExtensionProperty_of_isAffineSpace` is the affine case of the
  étale extension property `AlgebraicGeometry.Space.ChartExtensionProperty`: over an affine
  algebraic space étale over `X` every section over an affine chart lies in a finite type
  quasi-coherent submodule.

## Implementation notes

The exact extension is the quasi-coherence of the pushforward along the open immersion, computed
on charts.  The candidate submodule of the sections over `V₀` is the kernel of the map to the
finite product of the quotients of the sections over the members of a finite affine cover of
`Q` by the given submodule; `AlgebraicGeometry.Space.mem_chartSpan_of_forall_pullback` shows that
its restrictions span the given submodule over every member, and finitely many of its elements
already do because the given submodule is finitely generated there.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    {F : Modules.{u, u} B S hS X hX}

/-- The chart morphism `chartHomOfYoneda c hc` depends only on the morphism `c`: equal morphisms
give equal chart morphisms, whatever the proofs that they lie over `X`. -/
theorem chartHomOfYoneda_congr {V₀ T : SmallEtale B S hS X}
    {c c' : yoneda.obj T.1.left ⟶ yoneda.obj V₀.1.left} (h : c = c')
    (hc : c ≫ V₀.1.hom = T.1.hom) (hc' : c' ≫ V₀.1.hom = T.1.hom) :
    chartHomOfYoneda c hc = chartHomOfYoneda c' hc' := by
  subst h
  rfl

/-- An element of the span of the image of a set lies in the span of the image of a finite part. -/
private theorem exists_finset_subset_mem_span_image {R α N : Type*} [Semiring R]
    [AddCommMonoid N] [Module R N] (φ : α → N) {s : Set α} {x : N}
    (hx : x ∈ Submodule.span R (φ '' s)) :
    ∃ t : Finset α, ↑t ⊆ s ∧ x ∈ Submodule.span R (φ '' t) := by
  obtain ⟨t, ht, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun R).1 hx
  exact ⟨t, ht, (Submodule.mem_span_image_finset_iff_exists_fun R).2 ⟨c, rfl⟩⟩

/-! ### The exact extension across a quasi-compact open of an affine chart -/

/-- **A finite type quasi-coherent submodule over a quasi-compact open of an affine chart is
spanned by finitely many sections over the chart.**  Let `q : Q ⟶ V₀` be a monomorphism into the
presheaf represented by an affine chart `V₀`, covered by finitely many affine charts `Z i` over
`Q`, and let `D` be a chart submodule over `Q`.  Then there is a finitely generated submodule `M`
of the sections over `V₀`, containing a given finitely generated `N` whose restrictions to the
`Z i` lie in `D`, such that the chart submodule spanned by `M` restricts to exactly `D` on `Q`. -/
theorem exists_fg_comap_spanOfChart_eq (hF : IsCartesianOnAffineCharts F)
    {V₀ : SmallEtale B S hS X} (hV₀ : IsAffine (chartScheme V₀))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Q ⟶ yoneda.obj V₀.1.left) [Mono q] {n : ℕ}
    (Z : Fin n → SmallEtale B S hS X) (g : ∀ i, Z i ⟶ V₀)
    (z : ∀ i, yoneda.obj (Z i).1.left ⟶ Q) (hZ : ∀ i, IsAffine (chartScheme (Z i)))
    (hz : ∀ i, z i ≫ q = yoneda.map (g i).hom.left)
    (hcov : ∀ (R : SmallEtale B S hS X) (c : R ⟶ V₀) (yR : yoneda.obj R.1.left ⟶ Q),
      yR ≫ q = yoneda.map c.hom.left →
        Sieve.generate (fun R' (d : R' ⟶ R) => ∃ l, ∃ k : R' ⟶ Z l, k ≫ g l = d ≫ c) ∈
          SmallEtale.topology B S hS X R)
    (D : ChartSubmodule F (q ≫ V₀.1.hom))
    (N : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) (hN : N.FG)
    (hND : ∀ i, chartSpan F (g i) N ≤ D.obj (Z i) (z i)
      (by rw [← Category.assoc, hz i]; exact CostructuredArrow.w (g i).hom)) :
    ∃ (M : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀))) (hM : M.FG), N ≤ M ∧
      ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Q)
        (ha : a ≫ q ≫ V₀.1.hom = T.1.hom),
        ((ChartSubmodule.spanOfChart hF V₀ M hM).comap q (q ≫ V₀.1.hom) rfl).obj T a ha =
          D.obj T a ha := by
  classical
  have hzc : ∀ i, z i ≫ q ≫ V₀.1.hom = (Z i).1.hom := fun i => by
    rw [← Category.assoc, hz i]
    exact CostructuredArrow.w (g i).hom
  -- a chart over `Q` is determined by its image in `V₀`
  have hmono : ∀ {T : SmallEtale B S hS X} {a a' : yoneda.obj T.1.left ⟶ Q},
      a ≫ q = a' ≫ q → a = a' := fun h => (cancel_mono q).1 h
  -- the kernel `M'`
  let M' : Submodule (chartRing B S hS X hX V₀) (F.val.obj (op V₀)) :=
    ⨅ i, (D.obj (Z i) (z i) (hzc i)).comap (chartRes F (g i))
  have hcharts : ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Q)
      (ha : a ≫ q ≫ V₀.1.hom = T.1.hom), (a ≫ q) ≫ V₀.1.hom = T.1.hom := fun _ _ ha =>
    (Category.assoc _ _ _).trans ha
  -- the restrictions of the elements of `M'` lie in `D` over every chart of `Q`
  have hM'D : ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Q)
      (ha : a ≫ q ≫ V₀.1.hom = T.1.hom) {m : F.val.obj (op V₀)}, m ∈ M' →
        chartRes F (chartHomOfYoneda (a ≫ q) (hcharts T a ha)) m ∈ D.obj T a ha := by
    intro T a ha m hm
    refine D.mem_of_generate a ha
      (hcov T _ a (yoneda_map_chartHomOfYoneda _ (hcharts T a ha)).symm) fun {T'} d hd => ?_
    obtain ⟨l, k, hk⟩ := hd
    have h1 := D.map k (z l) (hzc l) ((Submodule.mem_iInf _).1 hm l)
    rw [modules_map_map] at h1 ⊢
    rw [hk] at h1
    refine D.obj.mem_congr _ (hmono ?_) _ _ h1
    rw [Category.assoc, hz l, ← yoneda_map_comp_left, hk, yoneda_map_comp_left,
      yoneda_map_chartHomOfYoneda, Category.assoc]
  -- over every member of the cover, `D` is spanned by the restrictions of `M'`
  have hspan : ∀ j, D.obj (Z j) (z j) (hzc j) ≤ chartSpan F (g j) M' := by
    intro j σ hσ
    refine mem_chartSpan_of_forall_pullback hF hV₀ (hZ j) (g j) Z g hZ
      (fun i => D.obj (Z i) (z i) (hzc i)) fun i => ?_
    have hP : IsAffine (chartScheme (pullback (g i) (g j))) :=
      SmallEtale.isAffine_of_isPullback_charts (IsPullback.of_hasPullback (g i) (g j)) hV₀
        (hZ i) (hZ j)
    have h1 := D.map (pullback.snd (g i) (g j)) (z j) (hzc j) hσ
    refine (D.obj_eq_span hF (hZ i) hP (pullback.fst (g i) (g j)) (z i) (hzc i)).le ?_
    refine D.obj.mem_congr _ (hmono ?_) _ _ h1
    rw [Category.assoc, Category.assoc, hz i, hz j, ← yoneda_map_comp_left,
      ← yoneda_map_comp_left, pullback.condition]
  -- finitely many elements of `M'` suffice
  choose G hG using fun j => D.fg_obj hF (hZ j) (z j) (hzc j)
  have hgen : ∀ j (y : G j), ∃ t : Finset (F.val.obj (op V₀)),
      (↑t ⊆ (M' : Set (F.val.obj (op V₀)))) ∧
        (y : F.val.obj (op (Z j))) ∈ chartSpan F (g j) (Submodule.span _ (t : Set _)) := by
    intro j y
    have hy : (y : F.val.obj (op (Z j))) ∈ D.obj (Z j) (z j) (hzc j) := by
      rw [← hG j]
      exact Submodule.subset_span y.2
    obtain ⟨t, ht, hyt⟩ := exists_finset_subset_mem_span_image _ (hspan j hy)
    exact ⟨t, ht, by rwa [chartSpan_span]⟩
  choose t ht hyt using hgen
  let tE : Finset (F.val.obj (op V₀)) := Finset.univ.biUnion fun j => Finset.univ.biUnion (t j)
  have htE : (↑tE : Set (F.val.obj (op V₀))) ⊆ M' := by
    intro w hw
    simp only [tE, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.mem_coe] at hw
    obtain ⟨j, y, hy⟩ := hw
    exact ht j y hy
  have hDZ : ∀ j, D.obj (Z j) (z j) (hzc j) ≤
      chartSpan F (g j) (Submodule.span _ (tE : Set (F.val.obj (op V₀)))) := by
    intro j
    rw [← hG j, Submodule.span_le]
    intro y hy
    refine chartSpan_mono F (g j) (Submodule.span_mono ?_) (hyt j ⟨y, hy⟩)
    intro w hw
    simp only [tE, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.mem_coe]
    exact ⟨j, ⟨y, hy⟩, hw⟩
  let M := Submodule.span (chartRing B S hS X hX V₀) (tE : Set (F.val.obj (op V₀))) ⊔ N
  have hM : M.FG := (Submodule.fg_span tE.finite_toSet).sup hN
  have hMM' : M ≤ M' := sup_le (Submodule.span_le.2 htE) fun m hm =>
    (Submodule.mem_iInf _).2 fun i => hND i (map_mem_chartSpan_of_mem F (g i) N hm)
  refine ⟨M, hM, le_sup_right, fun T a ha => le_antisymm ?_ ?_⟩
  · rintro σ ⟨R, hR, h⟩
    refine D.loc T a ha σ hR fun {T'} d hd => ?_
    have h' := h d hd
    change chartRes F d σ ∈ chartSpan F _ M at h'
    refine (Submodule.span_le.2 ?_) h'
    rintro _ ⟨m, hm, rfl⟩
    rw [← chartHomOfYoneda_congr (Category.assoc (yoneda.map d.hom.left) a q)
      (hcharts _ _ (chartOver_comp d ha))]
    exact hM'D T' (yoneda.map d.hom.left ≫ a) (chartOver_comp d ha) (hMM' hm)
  · intro σ hσ
    refine ⟨_, generate_affine_mem
      (hcov T _ a (yoneda_map_chartHomOfYoneda _ (hcharts T a ha)).symm), fun {T'} d hd => ?_⟩
    obtain ⟨T₁, m, d₁, ⟨⟨T₂, m₂, d₂, ⟨l, k, hk⟩, rfl⟩, hT₁⟩, rfl⟩ := hd
    have hdσ := D.map (m₂ ≫ d₂) a ha hσ
    have heq : yoneda.map (m₂ ≫ d₂).hom.left ≫ a = yoneda.map (m₂ ≫ k).hom.left ≫ z l := by
      refine hmono ?_
      rw [Category.assoc, Category.assoc, hz l]
      simp only [yoneda_map_comp_left, Category.assoc]
      rw [← yoneda_map_comp_left k (g l), hk, yoneda_map_comp_left, yoneda_map_chartHomOfYoneda]
    have h2 : chartRes F (m₂ ≫ d₂) σ ∈ chartSpan F ((m₂ ≫ k) ≫ g l) M := by
      have h3 := D.obj.mem_congr _ heq _ (by rw [← heq]; exact chartOver_comp _ ha) hdσ
      rw [D.obj_eq_span hF (hZ l) hT₁ (m₂ ≫ k) (z l) (hzc l)] at h3
      refine Submodule.span_le.2 ?_ h3
      rintro _ ⟨x, hx, rfl⟩
      exact map_mem_chartSpan F (g l) (m₂ ≫ k) M (chartSpan_mono F (g l) le_sup_left (hDZ l hx))
    have h4 := map_mem_chartSpan F _ m _ h2
    rw [modules_map_map] at h4
    change chartRes F (m ≫ m₂ ≫ d₂) σ ∈ chartSpan F _ M
    refine (chartSpan_congr F ?_ M).le h4
    apply SmallEtale.hom_ext'
    apply yoneda.map_injective
    rw [yoneda_map_chartHomOfYoneda]
    simp only [yoneda_map_comp_left, Category.assoc]
    rw [← yoneda_map_comp_left k (g l), hk, yoneda_map_comp_left, yoneda_map_chartHomOfYoneda]

/-! ### The étale extension property -/

variable (F) in
/-- **The étale extension property of Stacks 0829 over `π : Y ⟶ X`**: every section of `F` over
an affine chart of `Y` lies in a finite type quasi-coherent submodule of `F|_Y`, read on charts. -/
def ChartExtensionProperty {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X) : Prop :=
  ∀ (T : SmallEtale B S hS X) (a : yoneda.obj T.1.left ⟶ Y) (ha : a ≫ π = T.1.hom),
    IsAffine (chartScheme T) → ∀ σ : F.val.obj (op T), ∃ D : ChartSubmodule F π, σ ∈ D.obj T a ha

/-- Finitely many sections over affine charts of `Y` lie in one finite type quasi-coherent
submodule as soon as each of them lies in one. -/
theorem ChartExtensionProperty.exists_forall_mem (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Y ⟶ X} (hP : ChartExtensionProperty F π)
    {α : Type*} (s : Finset α) (T : α → SmallEtale B S hS X)
    (a : ∀ x, yoneda.obj (T x).1.left ⟶ Y) (ha : ∀ x, a x ≫ π = (T x).1.hom)
    (hT : ∀ x, IsAffine (chartScheme (T x))) (σ : ∀ x, F.val.obj (op (T x))) :
    ∃ D : ChartSubmodule F π, ∀ x ∈ s, σ x ∈ D.obj (T x) (a x) (ha x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨ChartSubmodule.bot hF π, by simp⟩
  | insert x s _ ih =>
    obtain ⟨D₁, h₁⟩ := hP (T x) (a x) (ha x) (hT x) (σ x)
    obtain ⟨D₂, h₂⟩ := ih
    refine ⟨D₁.sup hF D₂, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact D₁.le_sup_left hF D₂ _ _ _ h₁
    · exact D₁.le_sup_right hF D₂ _ _ _ (h₂ y hy)

/-- A section over an affine chart is a combination of the restrictions of finitely many sections
over a larger affine chart, `F` being cartesian on affine charts. -/
theorem exists_finset_mem_span_chartRes (hF : IsCartesianOnAffineCharts F)
    {T T' : SmallEtale B S hS X} (hT : IsAffine (chartScheme T)) (hT' : IsAffine (chartScheme T'))
    (κ : T' ⟶ T) (x : F.val.obj (op T')) :
    ∃ t : Finset (F.val.obj (op T)),
      x ∈ Submodule.span (chartRing B S hS X hX T') (chartRes F κ '' (t : Set _)) := by
  classical
  have hx : x ∈ Submodule.span (chartRing B S hS X hX T')
      (Set.range fun m : F.val.obj (op T) => chartRestrictLinear F κ m) := by
    rw [(chartBaseChange_surjective_iff_span_eq_top F κ).1 (hF T T' hT hT' κ).2]
    exact Submodule.mem_top
  obtain ⟨t, -, ht⟩ := exists_finset_subset_mem_span_image (chartRes F κ) (s := Set.univ)
    (by rwa [Set.image_univ])
  exact ⟨t, ht⟩

/-- The étale chart of `X` given by an affine algebraic space étale over `X`. -/
def affineChartOfIso {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X) (hπ : IsEtale B S hS π)
    {T₀ : BigFppfOver B S hS} (e : Y ≅ yoneda.obj T₀) : SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk (e.inv ≫ π), (isEtale_iff_presheaf_of_yoneda B S hS _).1
    (isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv) hπ)⟩

/-- The structure morphism of `affineChartOfIso π hπ e`, precomposed with `e.hom`, is `π`. -/
theorem affineChartOfIso_hom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X)
    (hπ : IsEtale B S hS π) {T₀ : BigFppfOver B S hS} (e : Y ≅ yoneda.obj T₀) :
    e.hom ≫ (affineChartOfIso π hπ e).1.hom = π := by
  change e.hom ≫ e.inv ≫ π = π
  rw [Iso.hom_inv_id_assoc]

/-- **The affine case of the étale extension property.** Over an affine algebraic space `V`
étale over `X`, a section over an affine chart of `V` is a combination of restrictions of finitely
many sections over `V` itself, which span a finite type quasi-coherent submodule of `F|_V`. -/
theorem chartExtensionProperty_of_isAffineSpace (hF : IsCartesianOnAffineCharts F)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X) (hπ : IsEtale B S hS π)
    (hY : IsAffineSpace B S hS Y) : ChartExtensionProperty F π := by
  classical
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hY
  let V₀ := affineChartOfIso π hπ e
  have hV₀ : IsAffine (chartScheme V₀) := hT₀
  intro T a ha hT σ
  have hc : (a ≫ e.hom) ≫ V₀.1.hom = T.1.hom := by
    change (a ≫ e.hom) ≫ e.inv ≫ π = T.1.hom
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact ha
  obtain ⟨t, ht⟩ := exists_finset_mem_span_chartRes hF hV₀ hT (chartHomOfYoneda _ hc) σ
  refine ⟨(ChartSubmodule.spanOfChart hF V₀ (Submodule.span _ (t : Set _))
    (Submodule.fg_span t.finite_toSet)).comap e.hom π (affineChartOfIso_hom π hπ e), ?_⟩
  exact ChartSubmodule.chartSpan_le_spanOfChart hF V₀ _
    (Submodule.fg_span t.finite_toSet) T _ hc (by rw [chartSpan_span]; exact ht)

/-! ### The step across an elementary distinguished square -/

/-- **The étale extension property propagates across an elementary distinguished square.**  Let
`(U ⊂ W, f : V ⟶ W)` be an elementary distinguished square over `X` with `W` quasi-separated, `U`
quasi-compact and `V` affine.  If the extension property holds over `U`, it holds over `W`.

Given a section over an affine chart `T` of `W`, its restrictions to finitely many affine charts
covering `T ×_W U` lie in a finite type quasi-coherent submodule `DU` over `U`, which may be taken
to contain also the restrictions to `V ×_W U` of the finitely many sections over `V` spanning the
restrictions of the section to `T ×_W V`.  The exact extension of `DU` from the quasi-compact
open `V ×_W U` of `V` to `V` is a submodule `DV` agreeing with `DU` on charts over both, and on
two charts of `V` with the same image in `W`, which over the diagonal is trivial and over `U`
reduces to the first agreement.  Glueing `DU` and `DV` gives the required submodule. -/
theorem chartExtensionProperty_of_isElementaryDistinguishedSquare
    (hZ : B.Contains (⊤_ Scheme.{u})) (hF : IsCartesianOnAffineCharts F)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W) (πW : W ⟶ X) (U : Subfunctor W)
    (f : V ⟶ W) (h : IsElementaryDistinguishedSquare B S hS hW U f)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) (hπV : IsEtale B S hS (f ≫ πW))
    (hV : IsAffineSpace B S hS V) (hPU : ChartExtensionProperty F (U.ι ≫ πW)) :
    ChartExtensionProperty F πW := by
  classical
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hV
  let QV := affineChartOfIso (f ≫ πW) hπV e
  have hQV : IsAffine (chartScheme QV) := hT₀
  have hQVc : CompactSpace (chartScheme QV) := inferInstance
  let aV : yoneda.obj QV.1.left ⟶ W := e.inv ≫ f
  have haV : aV ≫ πW = QV.1.hom := Category.assoc _ _ _
  have hUa : IsAlgebraicSpace B S hS U.toFunctor := h.isOpenSubspace.1
  have hιe : IsEtale B S hS U.ι := isEtale_of_isOpenImmersion B S hS h.isOpenSubspace.2
  have hVqc : IsQuasiCompactSpace B S hS V :=
    IsQuasiCompactSpace.of_iso B S hS (isQuasiCompact_yoneda_of_compact B S hS T₀ hQVc) e.symm
  intro T a ha hT σ
  have hTc : CompactSpace (chartScheme T) := inferInstance
  -- the charts of `T ×_W U`
  obtain ⟨nU, EU, eU, yU, hEU, hyU, hcovU⟩ :=
    exists_finite_affine_pullback_cover hZ hW hWqs hUa hUqc U.ι hιe T hTc a
  -- the charts of `T ×_W V`
  obtain ⟨nV, EV, eV, yV, hEV, hyV, hcovV⟩ :=
    exists_finite_affine_pullback_cover hZ hW hWqs h.isAlgebraicSpace hVqc f h.isEtale T hTc a
  have hcV : ∀ l, (yV l ≫ e.hom) ≫ QV.1.hom = (EV l).1.hom := fun l => by
    change (yV l ≫ e.hom) ≫ e.inv ≫ f ≫ πW = _
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hyV l, Category.assoc, ha]
    exact CostructuredArrow.w (eV l).hom
  let gV : ∀ l, EV l ⟶ QV := fun l => chartHomOfYoneda _ (hcV l)
  choose t ht using fun l => exists_finset_mem_span_chartRes hF hQV (hEV l) (gV l)
    (chartRes F (eV l) σ)
  let t₀ : Finset (F.val.obj (op QV)) := Finset.univ.biUnion t
  -- the charts of `V ×_W U`
  obtain ⟨nG, G, gG, uG, hG, huG, hcovG⟩ :=
    exists_finite_affine_pullback_cover hZ hW hWqs hUa hUqc U.ι hιe QV hQVc aV
  -- the submodule over `U`
  let α := Fin nU ⊕ (Fin nG × F.val.obj (op QV))
  let Tα : α → SmallEtale B S hS X := Sum.elim EU fun p => G p.1
  let aα : ∀ x, yoneda.obj (Tα x).1.left ⟶ U.toFunctor := fun x => match x with
    | Sum.inl l => yU l
    | Sum.inr p => uG p.1
  have haα : ∀ x, aα x ≫ U.ι ≫ πW = (Tα x).1.hom := fun x => match x with
    | Sum.inl l => by
      change yU l ≫ U.ι ≫ πW = (EU l).1.hom
      rw [← Category.assoc, hyU l, Category.assoc, ha]
      exact CostructuredArrow.w (eU l).hom
    | Sum.inr p => by
      change uG p.1 ≫ U.ι ≫ πW = (G p.1).1.hom
      rw [← Category.assoc, huG p.1, Category.assoc, haV]
      exact CostructuredArrow.w (gG p.1).hom
  have hTα : ∀ x, IsAffine (chartScheme (Tα x)) := fun x => match x with
    | Sum.inl l => hEU l
    | Sum.inr p => hG p.1
  let σα : ∀ x, F.val.obj (op (Tα x)) := fun x => match x with
    | Sum.inl l => chartRes F (eU l) σ
    | Sum.inr p => chartRes F (gG p.1) p.2
  let sα : Finset α := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.univ ×ˢ t₀).map ⟨Sum.inr, Sum.inr_injective⟩
  obtain ⟨DU, hDU⟩ := hPU.exists_forall_mem hF sα Tα aα haα hTα σα
  have hDUl : ∀ l, chartRes F (eU l) σ ∈ DU.obj (EU l) (yU l) (haα (Sum.inl l)) := fun l =>
    hDU (Sum.inl l) (Finset.mem_union_left _ (Finset.mem_map_of_mem _ (Finset.mem_univ _)))
  have hDUr : ∀ m, ∀ x ∈ t₀, chartRes F (gG m) x ∈ DU.obj (G m) (uG m) (haα (Sum.inr (m, x))) :=
    fun m x hx => hDU (Sum.inr (m, x)) (Finset.mem_union_right _ (Finset.mem_map_of_mem _
      (Finset.mem_product.2 ⟨Finset.mem_univ _, hx⟩)))
  -- the exact extension to `V`
  let VU := pullback U.ι aV
  have hVUc : pullback.fst U.ι aV ≫ U.ι ≫ πW = pullback.snd U.ι aV ≫ QV.1.hom := by
    rw [← Category.assoc, pullback.condition, Category.assoc, haV]
  let DVU := DU.comap (pullback.fst U.ι aV) (pullback.snd U.ι aV ≫ QV.1.hom) hVUc
  let zG : ∀ m, yoneda.obj (G m).1.left ⟶ VU := fun m =>
    pullback.lift (uG m) (yoneda.map (gG m).hom.left) (huG m)
  obtain ⟨M, hM, hNM, hMeq⟩ := exists_fg_comap_spanOfChart_eq hF hQV (pullback.snd U.ι aV) G gG
    zG hG (fun m => pullback.lift_snd _ _ _)
    (fun R c yR hyR => by
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (hcovG R c (yR ≫ pullback.fst U.ι aV) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, hyR]))
      rw [Sieve.generate_le_iff]
      rintro R' d ⟨l, k, hk, -⟩
      exact ⟨R', 𝟙 _, d, ⟨l, k, hk⟩, Category.id_comp _⟩)
    DVU (Submodule.span _ (t₀ : Set _)) (Submodule.fg_span t₀.finite_toSet) (fun m => by
      rw [chartSpan_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact DU.obj.mem_congr _ (pullback.lift_fst _ _ _).symm _ _ (hDUr m x hx))
  have heV : e.hom ≫ QV.1.hom = f ≫ πW := affineChartOfIso_hom (f ≫ πW) hπV e
  let DV := (ChartSubmodule.spanOfChart hF QV M hM).comap e.hom (f ≫ πW) heV
  have H1 : ∀ (R : SmallEtale B S hS X) (u : yoneda.obj R.1.left ⟶ U.toFunctor)
      (v : yoneda.obj R.1.left ⟶ V) (huv : v ≫ f = u ≫ U.ι)
      (hu : u ≫ U.ι ≫ πW = R.1.hom) (hv : v ≫ f ≫ πW = R.1.hom),
      DU.obj R u hu = DV.obj R v hv := by
    intro R u v huv hu hv
    have hw : u ≫ U.ι = (v ≫ e.hom) ≫ aV := by
      change _ = (v ≫ e.hom) ≫ e.inv ≫ f
      rw [Category.assoc, Iso.hom_inv_id_assoc, huv]
    let w : yoneda.obj R.1.left ⟶ VU := pullback.lift u (v ≫ e.hom) hw
    have hw' : w ≫ pullback.snd U.ι aV ≫ QV.1.hom = R.1.hom := by
      rw [pullback.lift_snd_assoc]
      change (v ≫ e.hom) ≫ e.inv ≫ f ≫ πW = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hv
    have h1 := hMeq R w hw'
    rw [ChartSubmodule.comap_obj] at h1
    refine (DU.obj.congr R (pullback.lift_fst _ _ _).symm hu
      (by rw [pullback.lift_fst]; exact hu)).trans (h1.symm.trans ?_)
    have hv'' : (v ≫ e.hom) ≫ QV.1.hom = R.1.hom := by
      change (v ≫ e.hom) ≫ e.inv ≫ f ≫ πW = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact hv
    exact (ChartSubmodule.spanOfChart hF QV M hM).obj.congr R (pullback.lift_snd _ _ _) _ hv''
  have H2 : ∀ (R : SmallEtale B S hS X) (v₁ v₂ : yoneda.obj R.1.left ⟶ V)
      (_ : v₁ ≫ f = v₂ ≫ f) (hv₁ : v₁ ≫ f ≫ πW = R.1.hom) (hv₂ : v₂ ≫ f ≫ πW = R.1.hom),
      DV.obj R v₁ hv₁ ≤ DV.obj R v₂ hv₂ := by
    intro R v₁ v₂ hv hv₁ hv₂ σ' hσ'
    refine DV.mem_of_generate v₂ hv₂
      (generate_mem_of_isElementaryDistinguishedSquare_overlap hW U f h R v₂ v₁ hv.symm)
      fun {R'} g hg => ?_
    have hm := DV.map g v₁ hv₁ hσ'
    rcases hg with hg | ⟨u, hu⟩
    · exact DV.obj.mem_congr _ hg.symm _ _ hm
    · have hu' : u ≫ U.ι ≫ πW = R'.1.hom := by
        rw [← Category.assoc, hu]
        simpa only [Category.assoc] using chartOver_comp g hv₂
      rw [← H1 R' u (yoneda.map g.hom.left ≫ v₂) (by rw [Category.assoc, hu]) hu' _]
      rw [H1 R' u (yoneda.map g.hom.left ≫ v₁) (by rw [Category.assoc, hu, hv]) hu' _]
      exact hm
  have hc : GlueCompatible DU DV := ⟨H1, fun R v₁ v₂ hv hv₁ hv₂ =>
    le_antisymm (H2 R v₁ v₂ hv hv₁ hv₂) (H2 R v₂ v₁ hv.symm hv₂ hv₁)⟩
  refine ⟨ChartSubmodule.glue (DU := DU) (DV := DV)
    (fun T a => generate_mem_of_isElementaryDistinguishedSquare hW U f h T a) hc,
    ⟨fun T' d u hu => ?_, fun T' d v hv => ?_⟩⟩
  · refine DU.mem_of_generate u _ (hcovU T' d u hu) fun {R'} d₂ hd₂ => ?_
    obtain ⟨l, k, hk1, hk2⟩ := hd₂
    have h1 := DU.map k (yU l) _ (hDUl l)
    rw [modules_map_map, hk1, ← modules_map_map] at h1
    exact DU.obj.mem_congr _ hk2 _ _ h1
  · refine DV.mem_of_generate v _ (hcovV T' d v hv) fun {R'} d₂ hd₂ => ?_
    obtain ⟨l, k, hk1, hk2⟩ := hd₂
    have hmem : chartRes F (eV l) σ ∈ DV.obj (EV l) (yV l) (by
        rw [← Category.assoc, hyV l, Category.assoc, ha]
        exact CostructuredArrow.w (eV l).hom) := by
      refine ChartSubmodule.chartSpan_le_spanOfChart hF QV M hM _ _ (hcV l) ?_
      refine chartSpan_mono F _ hNM ?_
      rw [chartSpan_span]
      refine Submodule.span_mono (Set.image_mono ?_) (ht l)
      intro x hx
      exact Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hx⟩
    have h1 := DV.map k (yV l) _ hmem
    rw [modules_map_map, hk1, ← modules_map_map] at h1
    exact DV.obj.mem_congr _ hk2 _ _ h1

/-! ### The étale extension property on a quasi-compact quasi-separated algebraic space -/

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The étale extension property on a quasi-compact quasi-separated algebraic space.**  Every
section of a quasi-coherent `𝒪_X`-module over an affine étale chart of `X` lies in a finite type
quasi-coherent submodule, read on charts.  This is the induction of Stacks 08GP: the affine case
is `AlgebraicGeometry.Space.chartExtensionProperty_of_isAffineSpace` and the step across an
elementary distinguished square is
`AlgebraicGeometry.Space.chartExtensionProperty_of_isElementaryDistinguishedSquare`. -/
theorem chartExtensionProperty_id (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hF : IsCartesianOnAffineCharts F) : ChartExtensionProperty F (𝟙 X) :=
  qcqs_induction_on_self B S hS hZ ⟨X, hX⟩ hqc hqs (fun _ π => ChartExtensionProperty F π)
    (fun V hV => chartExtensionProperty_of_isAffineSpace hF V.1.hom.hom V.2 hV)
    (fun W V U f hf hsq _ hWqs hUqc hVaff hPU _ _ =>
      chartExtensionProperty_of_isElementaryDistinguishedSquare hZ hF W.1.left.property hWqs
        W.1.hom.hom U f hsq hUqc (by rw [hf]; exact V.2) hVaff hPU)

end AlgebraicGeometry.Space

end
