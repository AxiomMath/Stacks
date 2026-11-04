module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSiteCharts

/-!
# Descent of sections along the total site of a simplicial semi-representable object

Let `K` be a simplicial semi-representable object of a site `(C, J)` and let `G` be a cartesian
sheaf of sets on the total site `(C/K)_total` (Stacks 0D8B, 07TF). Assume that any two vertices of
`K` over an object of `C` are locally the two vertices of an edge, and that any boundary of a
triangle of edges is locally filled by a `2`-simplex; a hypercovering has both properties.

A section `z` of `G` over a degree-zero object with chart `a : X ⟶ K_0` then *descends* along
every morphism `F : V ⟶ X` of `C` to every other degree-zero object: there is a unique section
over it agreeing with `z` on every object of the total site mapping to both compatibly with `F`.
These descents are compatible, and they assemble the value at any object `x` of the total site of
the direct image followed by the inverse image along the localization morphism `a`: the counit
`a^{-1} a_* G ⟶ G` is invertible. The argument is the source's (Stacks 0D8E), read on sections.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.HasLocalEdgesTotalSiteDescent`,
  `CategoryTheory.SimplicialSemiRepresentable.HasLocalTrianglesTotalSiteDescent`: the two local
  conditions on `K`.
* `CategoryTheory.SimplicialSemiRepresentable.IsSectionDescent`: a section is the descent of `z`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.exists_isDescent_totalSiteDescent`,
  `IsSectionDescent.unique`, `IsSectionDescent.map_eq`: existence, uniqueness and compatibility
  of descents.
* `CategoryTheory.Functor.IsCoverDense.isIso_of_isIso_whiskerLeft_totalSiteDescent`: restriction
  of sheaves of sets along a cover-dense functor reflects isomorphisms.
* `isIso_counit_app_of_isCartesianSheaf_totalSiteDescent` and
  `isIso_abelianCounit_app_of_isCartesianAbSheaf_totalSiteDescent`: the counit at a cartesian
  sheaf is invertible.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

/-- In the simplex category, `δ 1 ≫ δ 2 = δ 1 ≫ δ 1` as maps `⦋0⦌ ⟶ ⦋2⦌`. -/
theorem δ_one_comp_δ_two_totalSiteDescent :
    (SimplexCategory.δ 1 : ⦋0⦌ ⟶ ⦋1⦌) ≫ SimplexCategory.δ 2 =
      SimplexCategory.δ 1 ≫ SimplexCategory.δ 1 := by
  ext x; fin_cases x; rfl

/-- In the simplex category, `δ 0 ≫ δ 2 = δ 1 ≫ δ 0` as maps `⦋0⦌ ⟶ ⦋2⦌`. -/
theorem δ_zero_comp_δ_two_totalSiteDescent :
    (SimplexCategory.δ 0 : ⦋0⦌ ⟶ ⦋1⦌) ≫ SimplexCategory.δ 2 =
      SimplexCategory.δ 1 ≫ SimplexCategory.δ 0 := by
  ext x; fin_cases x; rfl

/-- In the simplex category, `δ 0 ≫ δ 1 = δ 0 ≫ δ 0` as maps `⦋0⦌ ⟶ ⦋2⦌`. -/
theorem δ_zero_comp_δ_one_totalSiteDescent :
    (SimplexCategory.δ 0 : ⦋0⦌ ⟶ ⦋1⦌) ≫ SimplexCategory.δ 1 =
      SimplexCategory.δ 0 ≫ SimplexCategory.δ 0 := by
  ext x; fin_cases x; rfl

/-- The source vertex of the edge `mkOfLe i j h : ⦋1⦌ ⟶ ⦋n⦌` is `i`. -/
theorem δ_one_comp_mkOfLe_totalSiteDescent (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    SimplexCategory.δ 1 ≫ SimplexCategory.mkOfLe i j h = SimplexCategory.const _ _ i := by
  ext x; fin_cases x; rfl

/-- The target vertex of the edge `mkOfLe i j h : ⦋1⦌ ⟶ ⦋n⦌` is `j`. -/
theorem δ_zero_comp_mkOfLe_totalSiteDescent (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    SimplexCategory.δ 0 ≫ SimplexCategory.mkOfLe i j h = SimplexCategory.const _ _ j := by
  ext x; fin_cases x; rfl

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C))

/-! ### Local edges and local triangles -/

/-- The sieve on `V` of the arrows along which the two vertices `a` and `b` become the source and
the target of an edge of `K`. -/
def edgeSieveTotalSiteDescent {V : C}
    (a b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌) : Sieve V where
  arrows V' g := ∃ e : (FormalCoproduct.incl C).obj V' ⟶ K _⦋1⦌,
    e ≫ K.δ 1 = (FormalCoproduct.incl C).map g ≫ a ∧
      e ≫ K.δ 0 = (FormalCoproduct.incl C).map g ≫ b
  downward_closed := by
    rintro V' V'' g ⟨e, h₁, h₀⟩ k
    exact ⟨(FormalCoproduct.incl C).map k ≫ e,
      by rw [Category.assoc, h₁, Functor.map_comp, Category.assoc],
      by rw [Category.assoc, h₀, Functor.map_comp, Category.assoc]⟩

/-- The sieve on `V` of the arrows along which three edges `e₀₁`, `e₀₂`, `e₁₂` become the three
faces of a `2`-simplex of `K`. -/
def triangleSieveTotalSiteDescent {V : C} (e₀₁ e₀₂ e₁₂ : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌) :
    Sieve V where
  arrows V' g := ∃ σ : (FormalCoproduct.incl C).obj V' ⟶ K _⦋2⦌,
    σ ≫ K.δ 2 = (FormalCoproduct.incl C).map g ≫ e₀₁ ∧
      σ ≫ K.δ 1 = (FormalCoproduct.incl C).map g ≫ e₀₂ ∧
        σ ≫ K.δ 0 = (FormalCoproduct.incl C).map g ≫ e₁₂
  downward_closed := by
    rintro V' V'' g ⟨σ, h₂, h₁, h₀⟩ k
    exact ⟨(FormalCoproduct.incl C).map k ≫ σ,
      by rw [Category.assoc, h₂, Functor.map_comp, Category.assoc],
      by rw [Category.assoc, h₁, Functor.map_comp, Category.assoc],
      by rw [Category.assoc, h₀, Functor.map_comp, Category.assoc]⟩

/-- Any two vertices of `K` over an object are locally the two vertices of an edge. -/
def HasLocalEdgesTotalSiteDescent : Prop :=
  ∀ ⦃V : C⦄ (a b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌), edgeSieveTotalSiteDescent K a b ∈ J V

/-- Any three edges of `K` over an object forming the boundary of a triangle are locally the
three faces of a `2`-simplex. -/
def HasLocalTrianglesTotalSiteDescent : Prop :=
  ∀ ⦃V : C⦄ (e₀₁ e₀₂ e₁₂ : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌),
    e₀₁ ≫ K.δ 1 = e₀₂ ≫ K.δ 1 → e₀₁ ≫ K.δ 0 = e₁₂ ≫ K.δ 1 → e₀₂ ≫ K.δ 0 = e₁₂ ≫ K.δ 0 →
      triangleSieveTotalSiteDescent K e₀₁ e₀₂ e₁₂ ∈ J V

variable {J K}

/-- **Filling a horn at vertex `0`.** Locally, two edges with a common source are two faces of a
`2`-simplex. -/
theorem exists_horn₀_totalSiteDescent (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    (e₀₁ e₀₂ : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌) (h : e₀₁ ≫ K.δ 1 = e₀₂ ≫ K.δ 1) :
    ∃ R : Sieve V, R ∈ J V ∧ ∀ ⦃V' : C⦄ (g : V' ⟶ V), R g →
      ∃ σ : (FormalCoproduct.incl C).obj V' ⟶ K _⦋2⦌,
        σ ≫ K.δ 2 = (FormalCoproduct.incl C).map g ≫ e₀₁ ∧
          σ ≫ K.δ 1 = (FormalCoproduct.incl C).map g ≫ e₀₂ := by
  refine ⟨Sieve.bind (edgeSieveTotalSiteDescent K (e₀₁ ≫ K.δ 0) (e₀₂ ≫ K.δ 0)).arrows
    (fun V' g hg => triangleSieveTotalSiteDescent K ((FormalCoproduct.incl C).map g ≫ e₀₁)
      ((FormalCoproduct.incl C).map g ≫ e₀₂) hg.choose),
    J.bind_covering (hE _ _) (fun V' g hg => hT _ _ _ ?_ ?_ ?_), ?_⟩
  · rw [Category.assoc, h, Category.assoc]
  · rw [Category.assoc, hg.choose_spec.1]
  · rw [Category.assoc, hg.choose_spec.2]
  · rintro V'' _ ⟨V', g', g, hg, ⟨σ, h₂, h₁, -⟩, rfl⟩
    exact ⟨σ, by rw [h₂, Functor.map_comp, Category.assoc],
      by rw [h₁, Functor.map_comp, Category.assoc]⟩

/-- **Filling a horn at vertex `1`.** Locally, two composable edges are two faces of a
`2`-simplex. -/
theorem exists_horn₁_totalSiteDescent (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    (e₀₁ e₁₂ : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌) (h : e₀₁ ≫ K.δ 0 = e₁₂ ≫ K.δ 1) :
    ∃ R : Sieve V, R ∈ J V ∧ ∀ ⦃V' : C⦄ (g : V' ⟶ V), R g →
      ∃ σ : (FormalCoproduct.incl C).obj V' ⟶ K _⦋2⦌,
        σ ≫ K.δ 2 = (FormalCoproduct.incl C).map g ≫ e₀₁ ∧
          σ ≫ K.δ 0 = (FormalCoproduct.incl C).map g ≫ e₁₂ := by
  refine ⟨Sieve.bind (edgeSieveTotalSiteDescent K (e₀₁ ≫ K.δ 1) (e₁₂ ≫ K.δ 0)).arrows
    (fun V' g hg => triangleSieveTotalSiteDescent K ((FormalCoproduct.incl C).map g ≫ e₀₁) hg.choose
      ((FormalCoproduct.incl C).map g ≫ e₁₂)),
    J.bind_covering (hE _ _) (fun V' g hg => hT _ _ _ ?_ ?_ ?_), ?_⟩
  · rw [Category.assoc, hg.choose_spec.1]
  · rw [Category.assoc, h, Category.assoc]
  · rw [Category.assoc, hg.choose_spec.2]
  · rintro V'' _ ⟨V', g', g, hg, ⟨σ, h₂, -, h₀⟩, rfl⟩
    exact ⟨σ, by rw [h₂, Functor.map_comp, Category.assoc],
      by rw [h₀, Functor.map_comp, Category.assoc]⟩

/-- **Filling a horn at vertex `2`.** Locally, two edges with a common target are two faces of a
`2`-simplex. -/
theorem exists_horn₂_totalSiteDescent (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    (e₀₂ e₁₂ : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌) (h : e₀₂ ≫ K.δ 0 = e₁₂ ≫ K.δ 0) :
    ∃ R : Sieve V, R ∈ J V ∧ ∀ ⦃V' : C⦄ (g : V' ⟶ V), R g →
      ∃ σ : (FormalCoproduct.incl C).obj V' ⟶ K _⦋2⦌,
        σ ≫ K.δ 1 = (FormalCoproduct.incl C).map g ≫ e₀₂ ∧
          σ ≫ K.δ 0 = (FormalCoproduct.incl C).map g ≫ e₁₂ := by
  refine ⟨Sieve.bind (edgeSieveTotalSiteDescent K (e₀₂ ≫ K.δ 1) (e₁₂ ≫ K.δ 1)).arrows
    (fun V' g hg => triangleSieveTotalSiteDescent K hg.choose ((FormalCoproduct.incl C).map g ≫ e₀₂)
      ((FormalCoproduct.incl C).map g ≫ e₁₂)),
    J.bind_covering (hE _ _) (fun V' g hg => hT _ _ _ ?_ ?_ ?_), ?_⟩
  · rw [Category.assoc, hg.choose_spec.1]
  · rw [Category.assoc, hg.choose_spec.2]
  · rw [Category.assoc, h, Category.assoc]
  · rintro V'' _ ⟨V', g', g, hg, ⟨σ, -, h₁, h₀⟩, rfl⟩
    exact ⟨σ, by rw [h₁, Functor.map_comp, Category.assoc],
      by rw [h₀, Functor.map_comp, Category.assoc]⟩

/-! ### Factoring two vertex maps through an edge -/

/-- The simplex map underlying a morphism to an object of degree zero is the constant map at the
vertex it picks. -/
theorem base_eq_const_totalSiteDescent {N : ℕ} {V W : C}
    {c : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌}
    {b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌}
    (t : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b) :
    t.base = (SimplexCategory.const ⦋0⦌ ⦋N⦌ (t.base.unop.toOrderHom 0)).op :=
  (Quiver.Hom.op_unop _).symm.trans (congrArg Quiver.Hom.op (SimplexCategory.eq_const_of_zero _))

/-- The underlying morphism of `C` of a cross morphism followed by `s` is that of `s`. -/
theorem totalForget_map_crossHom_comp_totalSiteDescent {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) {V : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ K.obj m) {y : Grothendieck (slices K)}
    (s : chartObjTotalSiteCharts K n (c ≫ K.map φ) ⟶ y) :
    (totalForget K).map (crossHomTotalSiteCharts φ c ≫ s) = (totalForget K).map s := by
  rw [CategoryTheory.Functor.map_comp, totalForget_map_chartHom_totalSiteCharts]
  exact Category.id_comp _

/-- A morphism to an object of degree zero factors through the cross morphism of an edge `ε`
having the vertex it picks as its vertex `i`. -/
private theorem exists_factor_vertex_totalSiteDescent {N : ℕ} {W V : C}
    {c₀ : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌} {b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌}
    (t : chartObjTotalSiteCharts K (op ⦋N⦌) c₀ ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b)
    (ε : ⦋1⦌ ⟶ ⦋N⦌) (i : Fin 2)
    (hi : SimplexCategory.δ i ≫ ε = SimplexCategory.const ⦋0⦌ ⦋N⦌ (t.base.unop.toOrderHom 0)) :
    ∃ s : chartObjTotalSiteCharts K (op ⦋1⦌) (c₀ ≫ K.map ε.op) ⟶
        chartObjTotalSiteCharts K (op ⦋0⦌) b,
      s.base = (SimplexCategory.δ i).op ∧ t = crossHomTotalSiteCharts ε.op c₀ ≫ s := by
  have hc := chart_comp_totalSiteCharts t
  rw [base_eq_const_totalSiteDescent t] at hc
  refine ⟨chartHomTotalSiteCharts (SimplexCategory.δ i).op ((totalForget K).map t) ?_, rfl, ?_⟩
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, hi]
    exact hc
  · refine total_hom_ext K _ _ ?_
      ((totalForget_map_crossHom_comp_totalSiteDescent ε.op c₀ _).trans
        (totalForget_map_chartHom_totalSiteCharts _ _ _)).symm
    change _ = ε.op ≫ (SimplexCategory.δ i).op
    rw [← op_comp, hi]
    exact base_eq_const_totalSiteDescent t

/-- **Two vertex maps factor through an edge.** Two morphisms from an object of the total site to
objects of degree zero factor, through a cross morphism, as the two vertex maps of an edge object,
in one of the two orientations. -/
theorem exists_edge_factor_totalSiteDescent {N : ℕ} {W V₁ V₂ : C}
    {c₀ : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌}
    {b₁ : (FormalCoproduct.incl C).obj V₁ ⟶ K _⦋0⦌} {b₂ : (FormalCoproduct.incl C).obj V₂ ⟶ K _⦋0⦌}
    (t₁ : chartObjTotalSiteCharts K (op ⦋N⦌) c₀ ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₁)
    (t₂ : chartObjTotalSiteCharts K (op ⦋N⦌) c₀ ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₂) :
    ∃ (e : (FormalCoproduct.incl C).obj W ⟶ K _⦋1⦌)
      (c : chartObjTotalSiteCharts K (op ⦋N⦌) c₀ ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) e)
      (s₁ : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₁)
      (s₂ : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₂),
      (totalForget K).map c = 𝟙 _ ∧ t₁ = c ≫ s₁ ∧ t₂ = c ≫ s₂ ∧
        ((s₁.base = (SimplexCategory.δ 1).op ∧ s₂.base = (SimplexCategory.δ 0).op) ∨
          (s₁.base = (SimplexCategory.δ 0).op ∧ s₂.base = (SimplexCategory.δ 1).op)) := by
  rcases le_total (t₁.base.unop.toOrderHom 0) (t₂.base.unop.toOrderHom 0) with h | h
  · let ε := SimplexCategory.mkOfLe _ _ h
    obtain ⟨s₁, hs₁, e₁⟩ := exists_factor_vertex_totalSiteDescent t₁ ε 1
      (δ_one_comp_mkOfLe_totalSiteDescent _ _ _ h)
    obtain ⟨s₂, hs₂, e₂⟩ := exists_factor_vertex_totalSiteDescent t₂ ε 0
      (δ_zero_comp_mkOfLe_totalSiteDescent _ _ _ h)
    exact ⟨_, crossHomTotalSiteCharts ε.op c₀, s₁, s₂,
      totalForget_map_chartHom_totalSiteCharts _ _ _, e₁, e₂, Or.inl ⟨hs₁, hs₂⟩⟩
  · let ε := SimplexCategory.mkOfLe _ _ h
    obtain ⟨s₁, hs₁, e₁⟩ := exists_factor_vertex_totalSiteDescent t₁ ε 0
      (δ_zero_comp_mkOfLe_totalSiteDescent _ _ _ h)
    obtain ⟨s₂, hs₂, e₂⟩ := exists_factor_vertex_totalSiteDescent t₂ ε 1
      (δ_one_comp_mkOfLe_totalSiteDescent _ _ _ h)
    exact ⟨_, crossHomTotalSiteCharts ε.op c₀, s₁, s₂,
      totalForget_map_chartHom_totalSiteCharts _ _ _, e₁, e₂, Or.inr ⟨hs₁, hs₂⟩⟩

/-- The chart of an edge object at a vertex is read off a morphism lying over that vertex. -/
theorem chart_vertex_totalSiteDescent {V W : C} {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌}
    {b : (FormalCoproduct.incl C).obj W ⟶ K _⦋0⦌} (i : Fin 2)
    (s : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b)
    (hs : s.base = (SimplexCategory.δ i).op) :
    e ≫ K.δ i = (FormalCoproduct.incl C).map ((totalForget K).map s) ≫ b := by
  have h := chart_comp_totalSiteCharts s
  rw [hs] at h
  exact h

/-- A morphism from an edge object to a vertex object, with the vertex picked by `i`, factors
through the cross morphism to its `i`-th vertex. -/
private theorem exists_eq_crossHom_comp_totalSiteDescent {V W : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌}
    {b : (FormalCoproduct.incl C).obj W ⟶ K _⦋0⦌} (i : Fin 2)
    (s : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b)
    (hs : s.base = (SimplexCategory.δ i).op) :
    ∃ r : chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ i).op) ⟶
        chartObjTotalSiteCharts K (op ⦋0⦌) b,
      s = crossHomTotalSiteCharts (SimplexCategory.δ i).op e ≫ r ∧
        (totalForget K).map r = (totalForget K).map s := by
  let r : chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ i).op) ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) b :=
    chartHomTotalSiteCharts (𝟙 _) ((totalForget K).map s) (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact chart_vertex_totalSiteDescent i s hs)
  have jr : (totalForget K).map r = (totalForget K).map s :=
    totalForget_map_chartHom_totalSiteCharts _ _ _
  refine ⟨r, total_hom_ext K _ _ ?_ ?_, jr⟩
  · change s.base = (SimplexCategory.δ i).op ≫ 𝟙 _
    rw [hs, Category.comp_id]
  · exact ((totalForget_map_crossHom_comp_totalSiteDescent _ e r).trans jr).symm

/-- A morphism lying over the identity of `C` does not change the underlying morphism of `C`
when composed on the left. -/
private theorem totalForget_map_comp_of_eq_id {N M : ℕ} {W : C}
    {c : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌} {c' : (FormalCoproduct.incl C).obj W ⟶ K _⦋M⦌}
    {y : Grothendieck (slices K)}
    (cr : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋M⦌) c')
    (s : chartObjTotalSiteCharts K (op ⦋M⦌) c' ⟶ y) (hcr : (totalForget K).map cr = 𝟙 W) :
    (totalForget K).map (cr ≫ s) = (totalForget K).map s :=
  ((totalForget K).map_comp cr s).trans ((congrArg (· ≫ _) hcr).trans (Category.id_comp _))

/-- Composing two inclusions of morphisms of `C` in the equation defining a pulled-back map. -/
private theorem eq_incl_map_comp {V₁ V₂ V₃ : C} {L : FormalCoproduct.{u} C}
    {x : (FormalCoproduct.incl C).obj V₁ ⟶ L} {g : V₁ ⟶ V₂} {g' : V₂ ⟶ V₃}
    {y : (FormalCoproduct.incl C).obj V₃ ⟶ L}
    (h : x = (FormalCoproduct.incl C).map g ≫ (FormalCoproduct.incl C).map g' ≫ y) :
    x = (FormalCoproduct.incl C).map (g ≫ g') ≫ y := by
  rw [Functor.map_comp, Category.assoc]
  exact h

/-! ### Descent of sections along a simplicial semi-representable object -/

section Descent

variable [J.toCoverage.HasPullbacks] (G : Sheaf (situation J K).totalTopology (Type u))

/-- Restricting a section of `G` along `f ≫ g` is restricting along `g`, then along `f`. -/
theorem map_comp_op_apply_totalSiteDescent {x y w : Grothendieck (slices K)} (f : x ⟶ y) (g : y ⟶ w)
    (s : G.obj.obj (op w)) :
    G.obj.map (f ≫ g).op s = G.obj.map f.op (G.obj.map g.op s) :=
  FunctorToTypes.map_comp_apply G.obj g.op f.op s

variable {X : C} (a : (FormalCoproduct.incl C).obj X ⟶ K _⦋0⦌)
  (z : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) a)))

/-- A section `w` over the degree-zero object with chart `b` is *the descent of `z` along `F`*
when it agrees with `z` on every object of the total site mapping to both, compatibly with `F`. -/
def IsSectionDescent {V : C} (b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌) (F : V ⟶ X)
    (w : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b))) : Prop :=
  ∀ ⦃N : ℕ⦄ ⦃W : C⦄ (c : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌)
    (t : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b)
    (t' : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) a),
      (totalForget K).map t ≫ F = (totalForget K).map t' → G.obj.map t.op w = G.obj.map t'.op z

variable {G a z}

/-- Descents restrict to descents. -/
theorem IsSectionDescent.pull {V V' : C} {b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌}
    {b' : (FormalCoproduct.incl C).obj V' ⟶ K _⦋0⦌} {F : V ⟶ X} {F' : V' ⟶ X}
    {w : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b))} (hw : IsSectionDescent G a z b F w)
    (r : chartObjTotalSiteCharts K (op ⦋0⦌) b' ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b)
    (hF : (totalForget K).map r ≫ F = F') :
    IsSectionDescent G a z b' F' (G.obj.map r.op w) := by
  intro N W c t t' h
  rw [← map_comp_op_apply_totalSiteDescent]
  exact hw c (t ≫ r) t' ((congrArg (· ≫ F) ((totalForget K).map_comp t r)).trans
    ((Category.assoc _ _ _).trans ((congrArg _ hF).trans h)))

variable (G) in
/-- **The two vertex restrictions along a loop agree.** If both vertices of an edge map to the
same degree-zero object along the same morphism of `C`, the two restrictions of a section of a
cartesian sheaf agree. This is where condition (3) of a hypercovering enters: the edge is,
locally, all three faces of a `2`-simplex. -/
theorem map_vertex_eq_of_loop_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌}
    (s s' : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) a)
    (hs : s.base = (SimplexCategory.δ 1).op) (hs' : s'.base = (SimplexCategory.δ 0).op)
    (hj : (totalForget K).map s = (totalForget K).map s')
    (z : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) a))) :
    G.obj.map s.op z = G.obj.map s'.op z := by
  set g := (totalForget K).map s with hg
  have h₁ : e ≫ K.δ 1 = (FormalCoproduct.incl C).map g ≫ a := chart_vertex_totalSiteDescent 1 s hs
  have h₀ : e ≫ K.δ 0 = (FormalCoproduct.incl C).map g ≫ a := by
    rw [hj]; exact chart_vertex_totalSiteDescent 0 s' hs'
  refine fibre_ext_totalSiteCharts J G ⦋1⦌ (componentObjTotalSiteCharts e)
    (hT e e e rfl (h₀.trans h₁.symm) rfl) _ _ ?_
  rintro Y f ⟨σ, hσ₂, hσ₁, hσ₀⟩
  set g' := (componentOverForget (K _⦋1⦌)).map f
  let c' := chartTotalSiteCharts (⟨op ⦋1⦌, Y⟩ : Grothendieck (slices K))
  have hY : c' = (FormalCoproduct.incl C).map g' ≫ e := chart_ι_totalSiteCharts f
  let ιf : chartObjTotalSiteCharts K (op ⦋1⦌) c' ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) e :=
    (Grothendieck.ι (slices K) (op ⦋1⦌)).map f
  have hιf : (totalForget K).map ιf = g' :=
    totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts f
  have hD : ∀ i : Fin 3, σ ≫ K.map (SimplexCategory.δ i).op =
      (FormalCoproduct.incl C).map (𝟙 _) ≫ c' := by
    intro i
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hY]
    fin_cases i
    · exact hσ₀
    · exact hσ₁
    · exact hσ₂
  let D : Fin 3 →
      (chartObjTotalSiteCharts K (op ⦋2⦌) σ ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) c') := fun i =>
    chartHomTotalSiteCharts (SimplexCategory.δ i).op (𝟙 _) (hD i)
  have hρ : ∀ i : Fin 2, c' ≫ K.map (SimplexCategory.δ i).op =
      (FormalCoproduct.incl C).map (𝟙 _) ≫ (FormalCoproduct.incl C).map (g' ≫ g) ≫ a := by
    intro i
    have hfi : e ≫ K.map (SimplexCategory.δ i).op = (FormalCoproduct.incl C).map g ≫ a := by
      fin_cases i
      · exact h₀
      · exact h₁
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hY]
    exact eq_incl_map_comp ((Category.assoc _ _ _).trans (congrArg _ hfi))
  let ρ : Fin 2 → (chartObjTotalSiteCharts K (op ⦋1⦌) c' ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) ((FormalCoproduct.incl C).map (g' ≫ g) ≫ a)) := fun i =>
    chartHomTotalSiteCharts (SimplexCategory.δ i).op (𝟙 _) (hρ i)
  let ψ : chartObjTotalSiteCharts K (op ⦋0⦌) ((FormalCoproduct.incl C).map (g' ≫ g) ≫ a) ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) a :=
    chartHomTotalSiteCharts (𝟙 _) (g' ≫ g)
      (by rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)
  have jD : ∀ i, (totalForget K).map (D i) = 𝟙 _ :=
    fun i => totalForget_map_chartHom_totalSiteCharts _ _ _
  have jρ : ∀ i, (totalForget K).map (ρ i) = 𝟙 _ :=
    fun i => totalForget_map_chartHom_totalSiteCharts _ _ _
  have jψ : (totalForget K).map ψ = g' ≫ g := totalForget_map_chartHom_totalSiteCharts _ _ _
  have e₁ : ιf ≫ s = ρ 1 ≫ ψ := by
    refine total_hom_ext K _ _ ?_ ?_
    · show 𝟙 _ ≫ s.base = (SimplexCategory.δ 1).op ≫ 𝟙 _
      rw [hs, Category.id_comp, Category.comp_id]
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hιf, jρ, jψ]
      exact (Category.id_comp _).symm
  have e₀ : ιf ≫ s' = ρ 0 ≫ ψ := by
    refine total_hom_ext K _ _ ?_ ?_
    · show 𝟙 _ ≫ s'.base = (SimplexCategory.δ 0).op ≫ 𝟙 _
      rw [hs', Category.id_comp, Category.comp_id]
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hιf, jρ, jψ, ← hj]
      exact (Category.id_comp _).symm
  have hv : ∀ (i j : Fin 3) (k l : Fin 2),
      (SimplexCategory.δ k : ⦋0⦌ ⟶ ⦋1⦌) ≫ SimplexCategory.δ i =
        SimplexCategory.δ l ≫ SimplexCategory.δ j → D i ≫ ρ k = D j ≫ ρ l := by
    intro i j k l h
    refine total_hom_ext K _ _ ?_ ?_
    · show (SimplexCategory.δ i).op ≫ (SimplexCategory.δ k).op =
        (SimplexCategory.δ j).op ≫ (SimplexCategory.δ l).op
      rw [← op_comp, ← op_comp, h]
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, jD, jD, jρ, jρ]
  have v₀ : D 2 ≫ ρ 1 = D 1 ≫ ρ 1 := hv 2 1 1 1 δ_one_comp_δ_two_totalSiteDescent
  have v₁ : D 2 ≫ ρ 0 = D 0 ≫ ρ 1 := hv 2 0 0 1 δ_zero_comp_δ_two_totalSiteDescent
  have v₂ : D 0 ≫ ρ 0 = D 1 ≫ ρ 0 := hv 0 1 0 0 δ_zero_comp_δ_one_totalSiteDescent.symm
  have bijD : ∀ i : Fin 3, Function.Bijective (G.obj.map (D i).op) := fun i =>
    bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.δ i) σ c' (hD i)
  have bijρ : ∀ i : Fin 2, Function.Bijective (G.obj.map (ρ i).op) := fun i =>
    bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.δ i) c' _ (hρ i)
  show G.obj.map ιf.op (G.obj.map s.op z) = G.obj.map ιf.op (G.obj.map s'.op z)
  rw [← map_comp_op_apply_totalSiteDescent, ← map_comp_op_apply_totalSiteDescent, e₁, e₀,
    map_comp_op_apply_totalSiteDescent, map_comp_op_apply_totalSiteDescent]
  set y := G.obj.map ψ.op z
  obtain ⟨y₁, hy₁⟩ := (bijρ 0).2 (G.obj.map (ρ 1).op y)
  have k : ∀ i : Fin 3, G.obj.map (D i ≫ ρ 0).op y₁ = G.obj.map (D i ≫ ρ 1).op y := fun i =>
    (map_comp_op_apply_totalSiteDescent G (D i) (ρ 0) y₁).trans ((congrArg _ hy₁).trans
      (map_comp_op_apply_totalSiteDescent G (D i) (ρ 1) y).symm)
  have k₀ := k 0
  have k₁ := k 1
  have k₂ := k 2
  rw [v₂] at k₀
  rw [v₁, v₀] at k₂
  have hinj : Function.Injective (G.obj.map (D 0 ≫ ρ 1).op) := by
    intro p q hpq
    exact (bijρ 1).1 ((bijD 0).1 ((map_comp_op_apply_totalSiteDescent G (D 0) (ρ 1) p).symm.trans
      (hpq.trans (map_comp_op_apply_totalSiteDescent G (D 0) (ρ 1) q))))
  have hyy : y₁ = y := hinj (k₂.trans (k₁.symm.trans k₀))
  rw [hyy] at hy₁
  exact hy₁.symm

variable (G a) in
/-- **The section `z` descends along the identity.** -/
theorem isDescent_self_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hT : HasLocalTrianglesTotalSiteDescent J K)
    (z : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) a))) :
    IsSectionDescent G a z a (𝟙 X) z := by
  intro N W c t t' h
  obtain ⟨e, cr, s₁, s₂, hcr, rfl, rfl, hb⟩ := exists_edge_factor_totalSiteDescent t t'
  have hj : (totalForget K).map s₁ = (totalForget K).map s₂ := by
    rw [totalForget_map_comp_of_eq_id _ _ hcr, totalForget_map_comp_of_eq_id _ _ hcr] at h
    exact (Category.comp_id _).symm.trans h
  rw [map_comp_op_apply_totalSiteDescent, map_comp_op_apply_totalSiteDescent]
  congr 1
  rcases hb with ⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩
  · exact map_vertex_eq_of_loop_totalSiteDescent G hG hT s₁ s₂ hb₁ hb₂ hj z
  · exact (map_vertex_eq_of_loop_totalSiteDescent G hG hT s₂ s₁ hb₂ hb₁ hj.symm z).symm

/-- **Descents are unique.** -/
theorem IsSectionDescent.unique (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    {V : C} {b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌} {F : V ⟶ X}
    {w w' : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b))}
    (hw : IsSectionDescent G a z b F w)
    (hw' : IsSectionDescent G a z b F w') : w = w' := by
  refine fibre_ext_totalSiteCharts J G ⦋0⦌ (componentObjTotalSiteCharts b)
    (hE b ((FormalCoproduct.incl C).map F ≫ a)) w w' ?_
  rintro Y f ⟨e, he₁, he₀⟩
  set g' := (componentOverForget (K _⦋0⦌)).map f
  let c' := chartTotalSiteCharts (⟨op ⦋0⦌, Y⟩ : Grothendieck (slices K))
  have hY : c' = (FormalCoproduct.incl C).map g' ≫ b := chart_ι_totalSiteCharts f
  let ιf : chartObjTotalSiteCharts K (op ⦋0⦌) c' ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b :=
    (Grothendieck.ι (slices K) (op ⦋0⦌)).map f
  have hιf : (totalForget K).map ιf = g' :=
    totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts f
  have h₁ : e ≫ K.map (SimplexCategory.δ 1).op = (FormalCoproduct.incl C).map (𝟙 _) ≫ c' := by
    rwa [CategoryTheory.Functor.map_id, Category.id_comp, hY]
  have h₀ : e ≫ K.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl C).map (g' ≫ F) ≫ a :=
    eq_incl_map_comp he₀
  let c₀ : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) c' :=
    chartHomTotalSiteCharts (SimplexCategory.δ 1).op _ h₁
  let s' : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) a :=
    chartHomTotalSiteCharts (SimplexCategory.δ 0).op _ h₀
  have jc₀ : (totalForget K).map c₀ = 𝟙 _ := totalForget_map_chartHom_totalSiteCharts _ _ _
  have js' : (totalForget K).map s' = g' ≫ F := totalForget_map_chartHom_totalSiteCharts _ _ _
  have hj : (totalForget K).map (c₀ ≫ ιf) ≫ F = (totalForget K).map s' := by
    rw [CategoryTheory.Functor.map_comp, jc₀, hιf, js']
    exact congrArg (· ≫ F) (Category.id_comp _)
  have k := (hw e (c₀ ≫ ιf) s' hj).trans (hw' e (c₀ ≫ ιf) s' hj).symm
  exact (bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.δ 1) e c' h₁).1
    ((map_comp_op_apply_totalSiteDescent G c₀ ιf w).symm.trans
      (k.trans (map_comp_op_apply_totalSiteDescent G c₀ ιf w')))

/-- **Descent is local.** A section whose restrictions along a covering family of `C/K_0` are
descents is a descent. -/
theorem isDescent_of_local_totalSiteDescent {V : C} {b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌}
    {F : V ⟶ X}
    {w : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b))} {R : Sieve V} (hR : R ∈ J V)
    (h : ∀ ⦃Y : ComponentOver (K _⦋0⦌)⦄ (f : Y ⟶ componentObjTotalSiteCharts b),
      R ((componentOverForget (K _⦋0⦌)).map f) →
        IsSectionDescent G a z (chartTotalSiteCharts (⟨op ⦋0⦌, Y⟩ : Grothendieck (slices K)))
          ((componentOverForget (K _⦋0⦌)).map f ≫ F)
          (G.obj.map ((Grothendieck.ι (slices K) (op ⦋0⦌)).map f).op w)) :
    IsSectionDescent G a z b F w := by
  intro N W c t t' ht
  refine fibre_ext_totalSiteCharts J G ⦋N⦌ (componentObjTotalSiteCharts c)
    (J.pullback_stable ((totalForget K).map t) hR) _ _ ?_
  intro Y f hf
  set g' := (componentOverForget (K _⦋N⦌)).map f
  let c' := chartTotalSiteCharts (⟨op ⦋N⦌, Y⟩ : Grothendieck (slices K))
  have hY : c' = (FormalCoproduct.incl C).map g' ≫ c := chart_ι_totalSiteCharts f
  let ιf : chartObjTotalSiteCharts K (op ⦋N⦌) c' ⟶ chartObjTotalSiteCharts K (op ⦋N⦌) c :=
    (Grothendieck.ι (slices K) (op ⦋N⦌)).map f
  have hιf : (totalForget K).map ιf = g' :=
    totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts f
  let fq :
      componentObjTotalSiteCharts ((FormalCoproduct.incl C).map (g' ≫ (totalForget K).map t) ≫ b) ⟶
        componentObjTotalSiteCharts b :=
    componentHomMkTotalSiteCharts _ b (g' ≫ (totalForget K).map t) rfl
  have jfq : (componentOverForget (K _⦋0⦌)).map fq = g' ≫ (totalForget K).map t :=
    componentOverForget_map_componentHomMk_totalSiteCharts _ _ _ _
  have hd := h fq (by rw [jfq]; exact hf)
  have htc := chart_comp_totalSiteCharts t
  have h'' : c' ≫ K.map t.base = (FormalCoproduct.incl C).map (𝟙 _) ≫
      (FormalCoproduct.incl C).map (g' ≫ (totalForget K).map t) ≫ b := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hY]
    exact eq_incl_map_comp ((Category.assoc _ _ _).trans (congrArg _ htc))
  let t'' : chartObjTotalSiteCharts K (op ⦋N⦌) c' ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌)
        ((FormalCoproduct.incl C).map (g' ≫ (totalForget K).map t) ≫ b) :=
    chartHomTotalSiteCharts t.base (𝟙 _) h''
  let ιfq : chartObjTotalSiteCharts K (op ⦋0⦌)
        ((FormalCoproduct.incl C).map (g' ≫ (totalForget K).map t) ≫ b) ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) b := (Grothendieck.ι (slices K) (op ⦋0⦌)).map fq
  have jt'' : (totalForget K).map t'' = 𝟙 _ := totalForget_map_chartHom_totalSiteCharts _ _ _
  have jιfq : (totalForget K).map ιfq = g' ≫ (totalForget K).map t :=
    (totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts fq).trans jfq
  have hsq : ιf ≫ t = t'' ≫ ιfq := by
    refine total_hom_ext K _ _ ?_ ?_
    · show 𝟙 _ ≫ t.base = t.base ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hιf, jt'', jιfq]
      exact (Category.id_comp _).symm
  have key := hd c' t'' (ιf ≫ t') ((congrArg (· ≫ _) jt'').trans ((Category.id_comp _).trans
    ((congrArg (· ≫ F) jfq).trans ((Category.assoc _ _ _).trans ((congrArg _ ht).trans
      ((congrArg (· ≫ _) hιf.symm).trans ((totalForget K).map_comp ιf t').symm))))))
  exact (map_comp_op_apply_totalSiteDescent G ιf t w).symm.trans
    ((congrArg (fun m => G.obj.map (Quiver.Hom.op m) w) hsq).trans
      ((map_comp_op_apply_totalSiteDescent G t'' ιfq w).trans
        (key.trans (map_comp_op_apply_totalSiteDescent G ιf t' z))))

/-- The diagram chase_totalSiteDescent shared by the transport lemmas. -/
theorem chase_totalSiteDescent {S E' E Q Q' P : Grothendieck (slices K)} (D : S ⟶ E') (D' : S ⟶ E)
    (hD : Function.Injective (G.obj.map D.op)) (s : E' ⟶ Q) (s' : E' ⟶ P) (cf : E ⟶ Q)
    (ct : E ⟶ Q') {ωf : G.obj.obj (op Q)} {ωt : G.obj.obj (op Q')} {y : G.obj.obj (op P)}
    (hrel : G.obj.map ct.op ωt = G.obj.map cf.op ωf)
    (hdesc : G.obj.map (D' ≫ ct).op ωt = G.obj.map (D ≫ s').op y)
    (heq : D ≫ s = D' ≫ cf) :
    G.obj.map s.op ωf = G.obj.map s'.op y := by
  refine hD ((map_comp_op_apply_totalSiteDescent G D s ωf).symm.trans ?_)
  refine (congrArg (fun m => G.obj.map (Quiver.Hom.op m) ωf) heq).trans ?_
  refine (map_comp_op_apply_totalSiteDescent G D' cf ωf).trans ?_
  refine (congrArg (G.obj.map D'.op) hrel.symm).trans ?_
  exact (map_comp_op_apply_totalSiteDescent G D' ct ωt).symm.trans
    (hdesc.trans (map_comp_op_apply_totalSiteDescent G D s' y))

omit [J.toCoverage.HasPullbacks] in
/-- The compatibility of underlying morphisms needed to test a descent in a transport. -/
theorem jcond_of_totalSiteDescent {S E' E Q Q' P : Grothendieck (slices K)} (D : S ⟶ E')
    (D' : S ⟶ E)
    (s : E' ⟶ Q) (s' : E' ⟶ P) (cf : E ⟶ Q) (ct : E ⟶ Q')
    (F : (totalForget K).obj Q ⟶ (totalForget K).obj P)
    (F' : (totalForget K).obj Q' ⟶ (totalForget K).obj P)
    (heq : D ≫ s = D' ≫ cf) (hc : (totalForget K).map cf ≫ F = (totalForget K).map ct ≫ F')
    (hj : (totalForget K).map s ≫ F = (totalForget K).map s') :
    (totalForget K).map (D' ≫ ct) ≫ F' = (totalForget K).map (D ≫ s') := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc, ← hc,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, ← heq, CategoryTheory.Functor.map_comp,
    Category.assoc, hj]

omit [J.toCoverage.HasPullbacks] in
/-- If `s ≫ F` and `s'` have the same underlying morphism of `C`, then so do `f ≫ s ≫ F` and
`f ≫ s'`. -/
theorem jcond_comp_left_totalSiteDescent {x y Q P : Grothendieck (slices K)} (f : x ⟶ y) (s : y ⟶ Q)
    (s' : y ⟶ P) {F : (totalForget K).obj Q ⟶ (totalForget K).obj P}
    (hj : (totalForget K).map s ≫ F = (totalForget K).map s') :
    (totalForget K).map (f ≫ s) ≫ F = (totalForget K).map (f ≫ s') := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc, hj]

/-- **The core of a transport along an edge.** Given a `2`-simplex `σ` one of whose faces is the
chart `c'` and another the pull-back of the edge `e`, a descent at one vertex of `e` related to a
section at the other vertex makes that section agree with `z` on the edge with chart `c'`. -/
theorem transport_core_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G) {V V'' : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌} {F : V ⟶ X} (p q : Fin 2)
    {ωf : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ p).op)))}
    {ωt : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ q).op)))}
    (hdesc : IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ q).op) F ωt)
    (hrel : G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ q).op e).op ωt =
      G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ p).op e).op ωf)
    {c' : (FormalCoproduct.incl C).obj V'' ⟶ K _⦋1⦌} {σ : (FormalCoproduct.incl C).obj V'' ⟶ K _⦋2⦌}
    (i k : Fin 3) (G₀ : V'' ⟶ V)
    (hσi : σ ≫ K.map (SimplexCategory.δ i).op = (FormalCoproduct.incl C).map (𝟙 _) ≫ c')
    (hσk : σ ≫ K.map (SimplexCategory.δ k).op = (FormalCoproduct.incl C).map G₀ ≫ e)
    (m : Fin 2)
    (s : chartObjTotalSiteCharts K (op ⦋1⦌) c' ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ p).op))
    (s' : chartObjTotalSiteCharts K (op ⦋1⦌) c' ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) a)
    (hs : s.base = (SimplexCategory.δ m).op) (hjs : (totalForget K).map s = G₀)
    (hj : (totalForget K).map s ≫ F = (totalForget K).map s')
    (hδ : (SimplexCategory.δ m : ⦋0⦌ ⟶ ⦋1⦌) ≫ SimplexCategory.δ i =
      SimplexCategory.δ p ≫ SimplexCategory.δ k) :
    G.obj.map s.op ωf = G.obj.map s'.op z := by
  let D : chartObjTotalSiteCharts K (op ⦋2⦌) σ ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) c' :=
    chartHomTotalSiteCharts (SimplexCategory.δ i).op (𝟙 _) hσi
  let D' : chartObjTotalSiteCharts K (op ⦋2⦌) σ ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) e :=
    chartHomTotalSiteCharts (SimplexCategory.δ k).op G₀ hσk
  have jD : (totalForget K).map D = 𝟙 _ := totalForget_map_chartHom_totalSiteCharts _ _ _
  have jD' : (totalForget K).map D' = G₀ := totalForget_map_chartHom_totalSiteCharts _ _ _
  have jcf : (totalForget K).map (crossHomTotalSiteCharts (SimplexCategory.δ p).op e) = 𝟙 _ :=
    totalForget_map_chartHom_totalSiteCharts _ _ _
  have jct : (totalForget K).map (crossHomTotalSiteCharts (SimplexCategory.δ q).op e) = 𝟙 _ :=
    totalForget_map_chartHom_totalSiteCharts _ _ _
  have heq : D ≫ s = D' ≫ crossHomTotalSiteCharts (SimplexCategory.δ p).op e := by
    refine total_hom_ext K _ _ ?_ ?_
    · show (SimplexCategory.δ i).op ≫ s.base =
        (SimplexCategory.δ k).op ≫ (SimplexCategory.δ p).op
      rw [hs, ← op_comp, ← op_comp, hδ]
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, jD, jD', jcf, hjs]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hc : (totalForget K).map (crossHomTotalSiteCharts (SimplexCategory.δ p).op e) ≫ F =
      (totalForget K).map (crossHomTotalSiteCharts (SimplexCategory.δ q).op e) ≫ F :=
    (congrArg (· ≫ F) jcf).trans (congrArg (· ≫ F) jct.symm)
  exact chase_totalSiteDescent D D'
    (bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.δ i) σ c' hσi).1 s s'
    (crossHomTotalSiteCharts (SimplexCategory.δ p).op e)
    (crossHomTotalSiteCharts (SimplexCategory.δ q).op e) hrel
    (hdesc σ _ _ (jcond_of_totalSiteDescent D D' s s'
      (crossHomTotalSiteCharts (SimplexCategory.δ p).op e)
      (crossHomTotalSiteCharts (SimplexCategory.δ q).op e) F F heq hc hj)) heq

omit [J.toCoverage.HasPullbacks] in
/-- A morphism `cr` lying over the identity of `C` may be cancelled on the left in an equality of
underlying morphisms `cr ≫ s ≫ F = cr ≫ s'`. -/
theorem jcond_cancel_totalSiteDescent {N : ℕ} {W : C} {c : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌}
    {e' : (FormalCoproduct.incl C).obj W ⟶ K _⦋1⦌} {Q P : Grothendieck (slices K)}
    (cr : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) e')
    (s : chartObjTotalSiteCharts K (op ⦋1⦌) e' ⟶ Q)
    (s' : chartObjTotalSiteCharts K (op ⦋1⦌) e' ⟶ P)
    {F : (totalForget K).obj Q ⟶ (totalForget K).obj P}
    (hcr : (totalForget K).map cr = 𝟙 W)
    (h : (totalForget K).map (cr ≫ s) ≫ F = (totalForget K).map (cr ≫ s')) :
    (totalForget K).map s ≫ F = (totalForget K).map s' := by
  rwa [totalForget_map_comp_of_eq_id _ _ hcr, totalForget_map_comp_of_eq_id _ _ hcr] at h

/-- **One case of a transport along an edge.** After a horn at the edge `e'` is filled on a covering
sieve, the core of the transport applies on each member of the sieve. -/
private theorem transport_horn_branch (hG : (situation J K).IsCartesianSheaf G) {V W : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌} {e' : (FormalCoproduct.incl C).obj W ⟶ K _⦋1⦌}
    {F : V ⟶ X} (p q : Fin 2)
    {ωf : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ p).op)))}
    {ωt : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ q).op)))}
    (hdesc : IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ q).op) F ωt)
    (hrel : G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ q).op e).op ωt =
      G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ p).op e).op ωf)
    {R : Sieve W} (hR : R ∈ J W) (i k : Fin 3) (m : Fin 2)
    (s : chartObjTotalSiteCharts K (op ⦋1⦌) e' ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ p).op))
    (s' : chartObjTotalSiteCharts K (op ⦋1⦌) e' ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) a)
    (hσ : ∀ ⦃V' : C⦄ (g'' : V' ⟶ W), R g'' → ∃ σ : (FormalCoproduct.incl C).obj V' ⟶ K _⦋2⦌,
      σ ≫ K.map (SimplexCategory.δ i).op = (FormalCoproduct.incl C).map g'' ≫ e' ∧
        σ ≫ K.map (SimplexCategory.δ k).op = (FormalCoproduct.incl C).map g'' ≫
          (FormalCoproduct.incl C).map ((totalForget K).map s) ≫ e)
    (hs : s.base = (SimplexCategory.δ m).op)
    (hj : (totalForget K).map s ≫ F = (totalForget K).map s')
    (hδ : (SimplexCategory.δ m : ⦋0⦌ ⟶ ⦋1⦌) ≫ SimplexCategory.δ i =
      SimplexCategory.δ p ≫ SimplexCategory.δ k) :
    G.obj.map s.op ωf = G.obj.map s'.op z := by
  refine fibre_ext_totalSiteCharts J G ⦋1⦌ (componentObjTotalSiteCharts e') hR _ _ ?_
  intro Y f hf
  obtain ⟨σ, hσi, hσk⟩ := hσ _ hf
  set g'' := (componentOverForget (K _⦋1⦌)).map f
  let c' := chartTotalSiteCharts (⟨op ⦋1⦌, Y⟩ : Grothendieck (slices K))
  have hY : c' = (FormalCoproduct.incl C).map g'' ≫ e' := chart_ι_totalSiteCharts f
  let ιf : chartObjTotalSiteCharts K (op ⦋1⦌) c' ⟶ chartObjTotalSiteCharts K (op ⦋1⦌) e' :=
    (Grothendieck.ι (slices K) (op ⦋1⦌)).map f
  have hιf : (totalForget K).map ιf = g'' :=
    totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts f
  have key := transport_core_totalSiteDescent hG p q hdesc hrel (c' := c') (σ := σ) i k
    (g'' ≫ (totalForget K).map s) (by rwa [CategoryTheory.Functor.map_id, Category.id_comp, hY])
    (eq_incl_map_comp hσk) m (ιf ≫ s) (ιf ≫ s')
    (by change 𝟙 _ ≫ s.base = _; rw [hs, Category.id_comp])
    (by rw [CategoryTheory.Functor.map_comp, hιf]; rfl)
    (jcond_comp_left_totalSiteDescent ιf s s' hj) hδ
  exact (map_comp_op_apply_totalSiteDescent G ιf s ωf).symm.trans
    (key.trans (map_comp_op_apply_totalSiteDescent G ιf s' z))

/-- **Transport of a descent to the source of an edge.** -/
theorem IsSectionDescent.transport₀ (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌}
    {F : V ⟶ X}
    {ω₀ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ 1).op)))}
    {ω₁ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ 0).op)))}
    (h₁ : IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ 0).op) F ω₁)
    (hrel : G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 0).op e).op ω₁ =
      G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 1).op e).op ω₀) :
    IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ 1).op) F ω₀ := by
  intro N W c t t' ht
  obtain ⟨e', cr, s, s', hcr, rfl, rfl, hb⟩ := exists_edge_factor_totalSiteDescent t t'
  have hj := jcond_cancel_totalSiteDescent cr s s' hcr ht
  rw [map_comp_op_apply_totalSiteDescent, map_comp_op_apply_totalSiteDescent]
  congr 1
  rcases hb with ⟨hb, -⟩ | ⟨hb, -⟩
  · obtain ⟨R, hR, hRσ⟩ := exists_horn₀_totalSiteDescent hE hT
      ((FormalCoproduct.incl C).map ((totalForget K).map s) ≫ e) e'
      ((Category.assoc _ _ _).trans (chart_vertex_totalSiteDescent 1 s hb).symm)
    exact transport_horn_branch hG 1 0 h₁ hrel hR 1 2 1 s s'
      (fun _ _ hg => (hRσ _ hg).imp fun _ => And.symm) hb hj
      δ_one_comp_δ_two_totalSiteDescent.symm
  · obtain ⟨R, hR, hRσ⟩ := exists_horn₁_totalSiteDescent hE hT e'
      ((FormalCoproduct.incl C).map ((totalForget K).map s) ≫ e)
      ((chart_vertex_totalSiteDescent 0 s hb).trans (Category.assoc _ _ _).symm)
    exact transport_horn_branch hG 1 0 h₁ hrel hR 2 0 0 s s' (fun _ _ hg => hRσ _ hg)
      hb hj δ_zero_comp_δ_two_totalSiteDescent

/-- **Transport of a descent to the target of an edge.** -/
theorem IsSectionDescent.transport₁ (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌}
    {F : V ⟶ X}
    {ω₀ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ 1).op)))}
    {ω₁ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ 0).op)))}
    (h₀ : IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ 1).op) F ω₀)
    (hrel : G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 1).op e).op ω₀ =
      G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 0).op e).op ω₁) :
    IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ 0).op) F ω₁ := by
  intro N W c t t' ht
  obtain ⟨e', cr, s, s', hcr, rfl, rfl, hb⟩ := exists_edge_factor_totalSiteDescent t t'
  have hj := jcond_cancel_totalSiteDescent cr s s' hcr ht
  rw [map_comp_op_apply_totalSiteDescent, map_comp_op_apply_totalSiteDescent]
  congr 1
  rcases hb with ⟨hb, -⟩ | ⟨hb, -⟩
  · obtain ⟨R, hR, hRσ⟩ := exists_horn₁_totalSiteDescent hE hT
      ((FormalCoproduct.incl C).map ((totalForget K).map s) ≫ e) e'
      ((Category.assoc _ _ _).trans (chart_vertex_totalSiteDescent 1 s hb).symm)
    exact transport_horn_branch hG 0 1 h₀ hrel hR 0 2 1 s s'
      (fun _ _ hg => (hRσ _ hg).imp fun _ => And.symm) hb hj
      δ_zero_comp_δ_two_totalSiteDescent.symm
  · obtain ⟨R, hR, hRσ⟩ := exists_horn₂_totalSiteDescent hE hT e'
      ((FormalCoproduct.incl C).map ((totalForget K).map s) ≫ e)
      ((chart_vertex_totalSiteDescent 0 s hb).trans (Category.assoc _ _ _).symm)
    exact transport_horn_branch hG 0 1 h₀ hrel hR 1 0 0 s s' (fun _ _ hg => hRσ _ hg)
      hb hj δ_zero_comp_δ_one_totalSiteDescent

/-- **A descent exists over the source of an edge whose target lies over `a`.** -/
theorem exists_isDescent_of_edge_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    (e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌)
    (F : V ⟶ X) (h₀ : e ≫ K.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl C).map F ≫ a) :
    ∃ w, IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ 1).op) F w := by
  let ψ : chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ 0).op) ⟶
      chartObjTotalSiteCharts K (op ⦋0⦌) a :=
    chartHomTotalSiteCharts (𝟙 _) F
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact h₀)
  have h₁ : IsSectionDescent G a z (e ≫ K.map (SimplexCategory.δ 0).op) F (G.obj.map ψ.op z) :=
    (isDescent_self_totalSiteDescent G a hG hT z).pull ψ
      ((congrArg (· ≫ 𝟙 X) (totalForget_map_chartHom_totalSiteCharts _ _ _)).trans
        (Category.comp_id _))
  obtain ⟨ω₀, hω₀⟩ := (bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.δ 1) e
    (e ≫ K.map (SimplexCategory.δ 1).op) (by simp)).2
      (G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 0).op e).op (G.obj.map ψ.op z))
  exact ⟨ω₀, h₁.transport₀ hG hE hT hω₀.symm⟩

/-- **Existence of descents.** Every section over a degree-zero object descends along every
morphism of `C` to every other degree-zero object. -/
theorem exists_isDescent_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V : C}
    (b : (FormalCoproduct.incl C).obj V ⟶ K _⦋0⦌)
    (F : V ⟶ X) : ∃ w, IsSectionDescent G a z b F w := by
  have hR := hE b ((FormalCoproduct.incl C).map F ≫ a)
  have hex : ∀ ⦃Y : ComponentOver (K _⦋0⦌)⦄ (f : Y ⟶ componentObjTotalSiteCharts b),
      edgeSieveTotalSiteDescent K b ((FormalCoproduct.incl C).map F ≫ a)
        ((componentOverForget (K _⦋0⦌)).map f) →
      ∃ w, IsSectionDescent G a z (chartTotalSiteCharts (⟨op ⦋0⦌, Y⟩ : Grothendieck (slices K)))
        ((componentOverForget (K _⦋0⦌)).map f ≫ F) w := by
    rintro Y f ⟨e, he₁, he₀⟩
    obtain ⟨w, hw⟩ := exists_isDescent_of_edge_totalSiteDescent hG hE hT e
      ((componentOverForget (K _⦋0⦌)).map f ≫ F)
      (eq_incl_map_comp he₀)
    have hY : chartTotalSiteCharts (⟨op ⦋0⦌, Y⟩ : Grothendieck (slices K)) =
        (FormalCoproduct.incl C).map ((componentOverForget (K _⦋0⦌)).map f) ≫ b :=
          chart_ι_totalSiteCharts f
    let r : chartObjTotalSiteCharts K (op ⦋0⦌)
          (chartTotalSiteCharts (⟨op ⦋0⦌, Y⟩ : Grothendieck (slices K))) ⟶
        chartObjTotalSiteCharts K (op ⦋0⦌) (e ≫ K.map (SimplexCategory.δ 1).op) :=
      chartHomTotalSiteCharts (𝟙 _) (𝟙 _) (by
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        exact ((hY.trans he₁.symm).trans (Category.id_comp _).symm).trans
          (congrArg (· ≫ _) ((FormalCoproduct.incl C).map_id _).symm))
    exact ⟨_, hw.pull r ((congrArg (· ≫ _) (totalForget_map_chartHom_totalSiteCharts _ _ _)).trans
      (Category.id_comp _))⟩
  obtain ⟨w, hw⟩ := exists_fibre_glue_totalSiteCharts J G ⦋0⦌ (componentObjTotalSiteCharts b) hR
    (fun Y f hf => (hex f hf).choose)
    (by
      intro Y Y' f g hf hgf
      refine IsSectionDescent.unique hG hE ((hex f hf).choose_spec.pull
        (b' := chartTotalSiteCharts (⟨op ⦋0⦌, Y'⟩ : Grothendieck (slices K)))
        ((Grothendieck.ι (slices K) (op ⦋0⦌)).map g) ?_) (hex (g ≫ f) hgf).choose_spec
      exact (congrArg (· ≫ _)
        (totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts g)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ F) ((componentOverForget (K _⦋0⦌)).map_comp g f).symm)))
  refine ⟨w, isDescent_of_local_totalSiteDescent hR fun Y f hf => ?_⟩
  rw [hw f hf]
  exact (hex f hf).choose_spec

/-- **Descents on the two vertices of an edge agree on the edge.** -/
theorem map_eq_of_edge_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {V V₁ V₂ : C}
    {e : (FormalCoproduct.incl C).obj V ⟶ K _⦋1⦌}
    {b₁ : (FormalCoproduct.incl C).obj V₁ ⟶ K _⦋0⦌} {b₂ : (FormalCoproduct.incl C).obj V₂ ⟶ K _⦋0⦌}
    {F₁ : V₁ ⟶ X} {F₂ : V₂ ⟶ X} {w₁ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b₁))}
    {w₂ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b₂))}
    (h₁ : IsSectionDescent G a z b₁ F₁ w₁)
    (h₂ : IsSectionDescent G a z b₂ F₂ w₂)
    (s₁ : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₁)
    (s₂ : chartObjTotalSiteCharts K (op ⦋1⦌) e ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₂)
    (hb₁ : s₁.base = (SimplexCategory.δ 1).op) (hb₂ : s₂.base = (SimplexCategory.δ 0).op)
    (hj : (totalForget K).map s₁ ≫ F₁ = (totalForget K).map s₂ ≫ F₂) :
    G.obj.map s₁.op w₁ = G.obj.map s₂.op w₂ := by
  obtain ⟨r₁, e₁, jr₁⟩ := exists_eq_crossHom_comp_totalSiteDescent 1 s₁ hb₁
  obtain ⟨r₂, e₂, jr₂⟩ := exists_eq_crossHom_comp_totalSiteDescent 0 s₂ hb₂
  have d₁ := h₁.pull r₁ (F' := (totalForget K).map s₁ ≫ F₁) (congrArg (· ≫ F₁) jr₁)
  have d₂ := h₂.pull r₂ (F' := (totalForget K).map s₁ ≫ F₁)
    ((congrArg (· ≫ F₂) jr₂).trans hj.symm)
  obtain ⟨ω, hω⟩ := (bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.δ 1) e
    (e ≫ K.map (SimplexCategory.δ 1).op) (by simp)).2
      (G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 0).op e).op (G.obj.map r₂.op w₂))
  have hωe := (d₂.transport₀ hG hE hT hω.symm).unique hG hE d₁
  refine (congrArg (fun m => G.obj.map (Quiver.Hom.op m) w₁) e₁).trans
    ((map_comp_op_apply_totalSiteDescent G _ r₁ w₁).trans ?_)
  refine Eq.trans ?_ ((congrArg (fun m => G.obj.map (Quiver.Hom.op m) w₂) e₂).trans
    (map_comp_op_apply_totalSiteDescent G _ r₂ w₂)).symm
  exact (congrArg (fun x => G.obj.map (crossHomTotalSiteCharts (SimplexCategory.δ 1).op e).op x)
    hωe).symm.trans hω

/-- **Descents are compatible.** Two descents, restricted along two morphisms out of one object
of the total site that are compatible with the morphisms of `C` they descend along, agree. -/
theorem IsSectionDescent.map_eq (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {N : ℕ} {W V₁ V₂ : C}
    {c : (FormalCoproduct.incl C).obj W ⟶ K _⦋N⦌}
    {b₁ : (FormalCoproduct.incl C).obj V₁ ⟶ K _⦋0⦌} {b₂ : (FormalCoproduct.incl C).obj V₂ ⟶ K _⦋0⦌}
    {F₁ : V₁ ⟶ X} {F₂ : V₂ ⟶ X} {w₁ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b₁))}
    {w₂ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b₂))}
    (h₁ : IsSectionDescent G a z b₁ F₁ w₁)
    (h₂ : IsSectionDescent G a z b₂ F₂ w₂)
    (t₁ : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₁)
    (t₂ : chartObjTotalSiteCharts K (op ⦋N⦌) c ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₂)
    (hj : (totalForget K).map t₁ ≫ F₁ = (totalForget K).map t₂ ≫ F₂) :
    G.obj.map t₁.op w₁ = G.obj.map t₂.op w₂ := by
  obtain ⟨e, cr, s₁, s₂, hcr, rfl, rfl, hb⟩ := exists_edge_factor_totalSiteDescent t₁ t₂
  have hj' : (totalForget K).map s₁ ≫ F₁ = (totalForget K).map s₂ ≫ F₂ := by
    rwa [totalForget_map_comp_of_eq_id _ _ hcr, totalForget_map_comp_of_eq_id _ _ hcr] at hj
  rw [map_comp_op_apply_totalSiteDescent, map_comp_op_apply_totalSiteDescent]
  congr 1
  rcases hb with ⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩
  · exact map_eq_of_edge_totalSiteDescent hG hE hT h₁ h₂ s₁ s₂ hb₁ hb₂ hj'
  · exact (map_eq_of_edge_totalSiteDescent hG hE hT h₂ h₁ s₂ s₁ hb₂ hb₁ hj'.symm).symm

/-- `IsSectionDescent.map_eq` for an arbitrary source object. -/
theorem IsSectionDescent.map_eq_of_obj (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) {y : Grothendieck (slices K)} {V₁ V₂ : C}
    {b₁ : (FormalCoproduct.incl C).obj V₁ ⟶ K _⦋0⦌} {b₂ : (FormalCoproduct.incl C).obj V₂ ⟶ K _⦋0⦌}
    {F₁ : V₁ ⟶ X} {F₂ : V₂ ⟶ X} {w₁ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b₁))}
    {w₂ : G.obj.obj (op (chartObjTotalSiteCharts K (op ⦋0⦌) b₂))}
    (h₁ : IsSectionDescent G a z b₁ F₁ w₁)
    (h₂ : IsSectionDescent G a z b₂ F₂ w₂) (t₁ : y ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₁)
    (t₂ : y ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) b₂)
    (hj : (totalForget K).map t₁ ≫ F₁ = (totalForget K).map t₂ ≫ F₂) :
    G.obj.map t₁.op w₁ = G.obj.map t₂.op w₂ := by
  obtain ⟨⟨⟨N⟩⟩, Y⟩ := y
  exact IsSectionDescent.map_eq
    (c := chartTotalSiteCharts (⟨op ⦋N⦌, Y⟩ : Grothendieck (slices K))) hG hE hT h₁ h₂ t₁ t₂ hj

end Descent

/-! ### Restriction along a cover-dense functor reflects isomorphisms -/

/-- **Restriction of sheaves of sets along a cover-dense functor reflects isomorphisms.** No local
fullness is needed: a morphism that is bijective on the sections over every object in the image
is locally injective and locally surjective. -/
theorem _root_.CategoryTheory.Functor.IsCoverDense.isIso_of_isIso_whiskerLeft_totalSiteDescent.{w,
    v₁, u₁}
    {C' : Type u₁} [Category.{v₁} C'] {D : Type w} [SmallCategory D] (G : C' ⥤ D)
    (K : GrothendieckTopology D) [G.IsCoverDense K] {F F' : Sheaf K (Type w)} (α : F ⟶ F')
    (h : IsIso (Functor.whiskerLeft G.op α.hom)) : IsIso α := by
  have hb : ∀ x : C', Function.Bijective (α.hom.app (op (G.obj x))) := fun x =>
    (isIso_iff_bijective _).1 (inferInstanceAs
      (IsIso ((Functor.whiskerLeft G.op α.hom).app (op x))))
  have : K.HasSheafCompose (forget (Type w)) := inferInstance
  refine (Sheaf.isLocallyBijective_iff_isIso α).1 ⟨?_, ?_⟩
  · constructor
    intro U s s' hs
    refine K.superset_covering ?_ (G.is_cover_of_isCoverDense K U.unop)
    rintro W g ⟨⟨x, lift, m, fac⟩⟩
    have hm : F.obj.map m.op s = F.obj.map m.op s' := (hb x).1 (by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hs])
    show F.obj.map g.op s = F.obj.map g.op s'
    rw [← fac, op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, hm]
  · constructor
    intro U t
    refine K.superset_covering ?_ (G.is_cover_of_isCoverDense K U)
    rintro W g ⟨⟨x, lift, m, fac⟩⟩
    obtain ⟨y, hy⟩ := (hb x).2 (F'.obj.map m.op t)
    refine ⟨F.obj.map lift.op y, ?_⟩
    rw [NatTrans.naturality_apply, hy, ← fac, op_comp, FunctorToTypes.map_comp_apply]

/-! ### Sections over the comma category of the counit -/

/-- The chart of the vertex `0` of an object of the total site. -/
def vertexChartTotalSiteDescent (y : Grothendieck (slices K)) :
    (FormalCoproduct.incl C).obj ((totalForget K).obj y) ⟶ K _⦋0⦌ :=
  chartTotalSiteCharts y ≫ K.map (SimplexCategory.const ⦋0⦌ y.base.unop 0).op

/-- The cross morphism from an object of the total site to its vertex `0`. -/
def vertexHomTotalSiteDescent (y : Grothendieck (slices K)) :
    y ⟶ chartObjTotalSiteCharts K (op ⦋0⦌) (vertexChartTotalSiteDescent y) :=
  crossHomTotalSiteCharts (SimplexCategory.const ⦋0⦌ y.base.unop 0).op (chartTotalSiteCharts y)

/-- The morphism to vertex `0` lies over the identity of `C`. -/
@[simp]
theorem totalForget_map_vertexHom_totalSiteDescent (y : Grothendieck (slices K)) :
    (totalForget K).map (vertexHomTotalSiteDescent y) = 𝟙 _ :=
  totalForget_map_chartHom_totalSiteCharts _ _ _

/-- Composing with the morphism to vertex `0` does not change the underlying morphism of `C`. -/
theorem totalForget_map_comp_vertexHom_totalSiteDescent {y y' : Grothendieck (slices K)}
    (f : y' ⟶ y) :
    (totalForget K).map (f ≫ vertexHomTotalSiteDescent y) = (totalForget K).map f :=
  ((totalForget K).map_comp f (vertexHomTotalSiteDescent y)).trans
    ((congrArg ((totalForget K).map f ≫ ·) (totalForget_map_vertexHom_totalSiteDescent y)).trans
      (Category.comp_id _))

section Sections

variable [J.toCoverage.HasPullbacks] (G : Sheaf (situation J K).totalTopology (Type u))

/-- For a cartesian sheaf `G`, restriction of sections along the morphism from `y` to its vertex
`0` is bijective. -/
theorem bijective_map_vertexHom_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (y : Grothendieck (slices K)) :
    Function.Bijective (G.obj.map (vertexHomTotalSiteDescent y).op) :=
  bijective_map_chartHom_id_totalSiteCharts J G hG (SimplexCategory.const ⦋0⦌ y.base.unop 0)
    (chartTotalSiteCharts y)
    (vertexChartTotalSiteDescent y) (by simp [vertexChartTotalSiteDescent])

variable (x : Grothendieck (slices K))

/-- The diagram whose limit computes the value at `x` of `a^{-1} a_* G`, for `a` the
localization morphism of the total site. -/
abbrev arrowDiagramTotalSiteDescent :
    StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op ⥤ Type u :=
  StructuredArrow.proj (op ((totalForget K).obj x)) (totalForget K).op ⋙ G.obj

/-- The arrow at the vertex `0` of an arrow of the comma category. -/
abbrev vertexArrowTotalSiteDescent
    (A : StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op) :
    StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op :=
  StructuredArrow.mk (Y := op (chartObjTotalSiteCharts K (op ⦋0⦌)
    (vertexChartTotalSiteDescent A.right.unop))) A.hom

/-- The morphism from the vertex arrow to the arrow. -/
def toVertexArrowTotalSiteDescent
    (A : StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op) :
    vertexArrowTotalSiteDescent x A ⟶ A :=
  StructuredArrow.homMk (vertexHomTotalSiteDescent A.right.unop).op
    ((congrArg (A.hom ≫ ·)
      ((congrArg Quiver.Hom.op (totalForget_map_vertexHom_totalSiteDescent _)).trans
        op_id)).trans (Category.comp_id _))

/-- The identity arrow of the comma category. -/
abbrev idArrowTotalSiteDescent : StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op :=
  StructuredArrow.mk (Y := op x) (𝟙 _)

/-- A section of the comma diagram is, at the vertex arrow of any arrow, a descent of its value
at the vertex arrow of the identity. -/
theorem isDescent_sections_totalSiteDescent (s : (arrowDiagramTotalSiteDescent G x).sections)
    (A : StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op) :
    IsSectionDescent G (vertexChartTotalSiteDescent x)
      (s.1 (vertexArrowTotalSiteDescent x (idArrowTotalSiteDescent x)))
      (vertexChartTotalSiteDescent A.right.unop)
      A.hom.unop (s.1 (vertexArrowTotalSiteDescent x A)) := by
  intro N W c t t' h
  let B : StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op :=
    StructuredArrow.mk (Y := op (chartObjTotalSiteCharts K (op ⦋N⦌) c)) ((totalForget K).map t').op
  let g : vertexArrowTotalSiteDescent x A ⟶ B := StructuredArrow.homMk t.op
    ((congrArg (· ≫ ((totalForget K).map t).op) (Quiver.Hom.op_unop A.hom).symm).trans
      (op_comp.symm.trans (congrArg Quiver.Hom.op h)))
  let g' : vertexArrowTotalSiteDescent x (idArrowTotalSiteDescent x) ⟶ B :=
    StructuredArrow.homMk t'.op (by
    show 𝟙 _ ≫ ((totalForget K).map t').op = ((totalForget K).map t').op
    exact Category.id_comp _)
  exact (s.2 g).trans (s.2 g').symm

variable {G}

/-- **Sections of the comma diagram are determined by their value at the identity.** -/
theorem sections_ext_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    {s s' : (arrowDiagramTotalSiteDescent G x).sections}
    (h : s.1 (idArrowTotalSiteDescent x) = s'.1 (idArrowTotalSiteDescent x)) : s = s' := by
  have h₀ : s.1 (vertexArrowTotalSiteDescent x (idArrowTotalSiteDescent x)) =
      s'.1 (vertexArrowTotalSiteDescent x (idArrowTotalSiteDescent x)) :=
    (bijective_map_vertexHom_totalSiteDescent G hG x).1
      ((s.2 (toVertexArrowTotalSiteDescent x (idArrowTotalSiteDescent x))).trans
      (h.trans (s'.2 (toVertexArrowTotalSiteDescent x (idArrowTotalSiteDescent x))).symm))
  refine Subtype.ext (funext fun A => ?_)
  have hs' := isDescent_sections_totalSiteDescent G x s' A
  rw [← h₀] at hs'
  have hA := IsSectionDescent.unique hG hE (isDescent_sections_totalSiteDescent G x s A) hs'
  exact (s.2 (toVertexArrowTotalSiteDescent x A)).symm.trans
    ((congrArg _ hA).trans (s'.2 (toVertexArrowTotalSiteDescent x A)))

/-- **Every section over `x` extends to a section of the comma diagram.** -/
theorem exists_sections_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K)
    (hT : HasLocalTrianglesTotalSiteDescent J K) (z : G.obj.obj (op x)) :
    ∃ s : (arrowDiagramTotalSiteDescent G x).sections, s.1 (idArrowTotalSiteDescent x) = z := by
  obtain ⟨z₀, hz₀⟩ := (bijective_map_vertexHom_totalSiteDescent G hG x).2 z
  have hd := fun A : StructuredArrow (op ((totalForget K).obj x)) (totalForget K).op =>
    exists_isDescent_totalSiteDescent (a := vertexChartTotalSiteDescent x) (z := z₀) hG hE hT
      (vertexChartTotalSiteDescent A.right.unop) A.hom.unop
  refine ⟨⟨fun A => G.obj.map (vertexHomTotalSiteDescent A.right.unop).op (hd A).choose, ?_⟩, ?_⟩
  · intro A A' g
    have hw := StructuredArrow.w g
    show G.obj.map g.right (G.obj.map (vertexHomTotalSiteDescent A.right.unop).op (hd A).choose) =
      G.obj.map (vertexHomTotalSiteDescent A'.right.unop).op (hd A').choose
    refine (map_comp_op_apply_totalSiteDescent G (g.right.unop)
      (vertexHomTotalSiteDescent A.right.unop) _).symm.trans ?_
    refine IsSectionDescent.map_eq_of_obj hG hE hT (hd A).choose_spec (hd A').choose_spec _ _ ?_
    have hw' := congrArg Quiver.Hom.unop hw
    change (totalForget K).map g.right.unop ≫ A.hom.unop = A'.hom.unop at hw'
    exact ((congrArg (· ≫ A.hom.unop)
      (totalForget_map_comp_vertexHom_totalSiteDescent g.right.unop)).trans hw').trans
      ((congrArg (· ≫ A'.hom.unop)
        (totalForget_map_vertexHom_totalSiteDescent A'.right.unop)).trans
        (Category.id_comp _)).symm
  · show G.obj.map (vertexHomTotalSiteDescent x).op (hd (idArrowTotalSiteDescent x)).choose = z
    exact (congrArg (fun w => G.obj.map (vertexHomTotalSiteDescent x).op w)
      (IsSectionDescent.unique hG hE
        (isDescent_self_totalSiteDescent G (vertexChartTotalSiteDescent x) hG hT z₀)
        (hd (idArrowTotalSiteDescent x)).choose_spec).symm).trans hz₀

/-- Evaluation at the identity arrow is a bijection on the limit of the comma diagram. -/
theorem bijective_limit_π_idArrow_totalSiteDescent (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K) (hT : HasLocalTrianglesTotalSiteDescent J K) :
    Function.Bijective
      (limit.π (arrowDiagramTotalSiteDescent G x) (idArrowTotalSiteDescent x)) := by
  refine ⟨fun l l' h => (Types.limitEquivSections _).injective
    (sections_ext_totalSiteDescent x hG hE h), fun z => ?_⟩
  obtain ⟨s, hs⟩ := exists_sections_totalSiteDescent x hG hE hT z
  exact ⟨(Types.limitEquivSections _).symm s,
    (Types.limitEquivSections_symm_apply _ s (idArrowTotalSiteDescent x)).trans hs⟩

/-- The counit of the adjunction of the localization functor of the total site at `x`, for sheaves
with values in any category with limits, through the limit formula for right Kan extensions. -/
private theorem counit_app_hom_app_aux {A : Type (u + 1)} [Category.{u} A]
    [HasLimitsOfSize.{u, u} A] (G : Sheaf (situation J K).totalTopology A) :
    (((totalForget K).sheafAdjunctionCocontinuous A ((situation J K).totalTopology)
        J).counit.app G).hom.app (op x) =
      ((totalForget K).op.ranObjObjIsoLimit G.obj (op ((totalForget K).obj x))).hom ≫
        limit.π (StructuredArrow.proj (op ((totalForget K).obj x)) (totalForget K).op ⋙ G.obj)
          (idArrowTotalSiteDescent x) := by
  have h₁ := congrArg (fun f => NatTrans.app f (op x))
    (Functor.sheafAdjunctionCocontinuous_counit_app_hom (totalForget K) A
      (situation J K).totalTopology J G)
  have h₂ := (totalForget K).op.ranObjObjIsoLimit_hom_π G.obj (op ((totalForget K).obj x))
    (idArrowTotalSiteDescent x)
  refine h₁.trans ?_
  refine Eq.trans ?_ h₂.symm
  rw [Functor.ranAdjunction_counit]
  exact (Category.id_comp _).symm.trans
    (congrArg (· ≫ _) (((totalForget K).op.ran.obj G.obj).map_id _).symm)

/-- The counit of the localization morphism of the total site at `x`, through the limit formula
for right Kan extensions. -/
theorem counit_app_hom_app_totalSiteDescent :
    ((totalLocalizationMorphism J K).adj.counit.app G).hom.app (op x) =
      ((totalForget K).op.ranObjObjIsoLimit G.obj (op ((totalForget K).obj x))).hom ≫
        limit.π (arrowDiagramTotalSiteDescent G x) (idArrowTotalSiteDescent x) :=
  counit_app_hom_app_aux x G

/-- **On a cartesian sheaf the counit `a^{-1} a_* G ⟶ G` of the localization morphism of the
total site is invertible**, as soon as any two vertices of `K` are locally joined by an edge and
any triangle of edges is locally filled. -/
theorem isIso_counit_app_of_isCartesianSheaf_totalSiteDescent
    (hG : (situation J K).IsCartesianSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K) (hT : HasLocalTrianglesTotalSiteDescent J K) :
    IsIso ((totalLocalizationMorphism J K).adj.counit.app G) := by
  have h :
      IsIso ((sheafToPresheaf _ _).map ((totalLocalizationMorphism J K).adj.counit.app G)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨x⟩
    refine (congrArg IsIso (counit_app_hom_app_totalSiteDescent (G := G) x)).mpr
      ((isIso_iff_bijective _).2 ?_)
    exact (bijective_limit_π_idArrow_totalSiteDescent x hG hE hT).comp
      ((isIso_iff_bijective _).1 (Iso.isIso_hom _))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- The counit of the abelian adjunction of the localization functor of the total site at `x`,
through the limit formula for right Kan extensions. -/
theorem abelianCounit_app_hom_app_totalSiteDescent
    (G : Sheaf (situation J K).totalTopology Ab.{u}) :
    (((totalForget K).sheafAdjunctionCocontinuous Ab.{u} ((situation J K).totalTopology)
        J).counit.app G).hom.app (op x) =
      ((totalForget K).op.ranObjObjIsoLimit G.obj (op ((totalForget K).obj x))).hom ≫
        limit.π (StructuredArrow.proj (op ((totalForget K).obj x)) (totalForget K).op ⋙ G.obj)
          (idArrowTotalSiteDescent x) :=
  counit_app_hom_app_aux x G

/-- **On a cartesian sheaf of abelian groups the counit `a^{-1} a_* G ⟶ G` of the localization
morphism of the total site is invertible**, under the same conditions on `K`. -/
theorem isIso_abelianCounit_app_of_isCartesianAbSheaf_totalSiteDescent
    (G : Sheaf (situation J K).totalTopology Ab.{u}) (hG : (situation J K).IsCartesianAbSheaf G)
    (hE : HasLocalEdgesTotalSiteDescent J K) (hT : HasLocalTrianglesTotalSiteDescent J K) :
    IsIso (((totalForget K).sheafAdjunctionCocontinuous Ab.{u} ((situation J K).totalTopology)
      J).counit.app G) := by
  have h : IsIso ((sheafToPresheaf _ _).map (((totalForget K).sheafAdjunctionCocontinuous Ab.{u}
      ((situation J K).totalTopology) J).counit.app G)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨x⟩
    refine (congrArg IsIso (abelianCounit_app_hom_app_totalSiteDescent x G)).mpr ?_
    have hf : IsIso ((forget Ab.{u}).map
        (((totalForget K).op.ranObjObjIsoLimit G.obj (op ((totalForget K).obj x))).hom ≫
          limit.π (StructuredArrow.proj (op ((totalForget K).obj x)) (totalForget K).op ⋙ G.obj)
            (idArrowTotalSiteDescent x))) := by
      refine (isIso_iff_bijective _).2 ?_
      rw [CategoryTheory.Functor.map_comp, ← preservesLimitIso_hom_π]
      exact ((bijective_limit_π_idArrow_totalSiteDescent
        (G := (sheafCompose _ (forget Ab.{u})).obj G) x hG hE
        hT).comp ((isIso_iff_bijective _).1 (Iso.isIso_hom _))).comp
        ((isIso_iff_bijective _).1 (inferInstance))
    exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (forget Ab.{u}) hf _
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

end Sections

end CategoryTheory.SimplicialSemiRepresentable

end
