module

public import StacksFrontier.Topology.Sheaves.ProperPushforward.SectionsOnQuasiCompactSubset
public import StacksFrontier.Topology.Simplicial.SheafSystemGerms

/-!
# Descent of cartesian sheaves along a proper hypercovering, on stalks

Let `Z` be a simplicial topological space with an augmentation `α : Z ⟶ W`, and let `S` be a
cartesian system of sheaves of sets on the spaces `Z_n` (Tag 09VM), that is, one whose transition
maps induce bijections on stalks. Write `a_* S` for the direct image along the augmentation, the
limit over `Δ` of the direct images `α_{n,*} S_n` (Tag 09W4 (4)).

Suppose `α_0` is a closed surjection with quasi-compact fibres, `α_1` is closed, two points of
`Z_0` with the same image are the vertices of a `1`-simplex, the `1`-simplices with a given first
vertex form a quasi-compact set, and three `1`-simplices forming the boundary of a triangle are
the edges of a `2`-simplex. These are the consequences of `Z ⟶ W` being a proper hypercovering
that the descent argument of Tag 0DAG uses. Then for every `u ∈ Z_0` over `x ∈ W` the projection
`a_* S ⟶ α_{0,*} S_0` induces a bijection `(a_* S)_x → (S_0)_u` on stalks.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialSheafSystem.EdgeRel`: two germs at the vertices of a
  `1`-simplex `w` are related by `w` when the two transition maps carry them to the same germ
  at `w`.

## Main results

* `Stacks.Topology.Simplicial.SimplicialSheafSystem.EdgeRel.triangle`: the cocycle condition,
  read off a `2`-simplex.
* `Stacks.Topology.Simplicial.SimplicialSheafSystem.EdgeRel.eq_of_degenerate`: a degenerate
  `1`-simplex relates a germ only to itself.

## References

* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Simplicial

universe u

namespace Stacks.Topology.Simplicial.SimplicialSheafSystem

variable {Z : SimplicialObject TopCat.{u}} {S : SimplicialSheafSystem Z (Type u)}

/-- The cartesian condition on a system: every transition map has an invertible adjoint. -/
def IsCartesianSystem (S : SimplicialSheafSystem Z (Type u)) : Prop :=
  ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (φ : n ⟶ m),
    IsIso (((Augmentation.adj (Z.map φ)).homEquiv _ _).symm (Augmentation.systemTransition Z S φ))

/-- Germ transport along equal maps agrees. -/
theorem GermTransport.of_eq {n m : SimplexCategoryᵒᵖ} {φ φ' : n ⟶ m} (e : φ = φ')
    {w : Z.obj n} {q : Z.obj m} {h : (S.component m).presheaf.stalk q}
    {k : (S.component n).presheaf.stalk w} (hk : S.GermTransport φ w q h k) :
    S.GermTransport φ' w q h k :=
  e ▸ hk

/-- Two germs `h` at `p` and `h'` at `p'` are related by the `1`-simplex `w` when the transition
maps along the two vertex maps carry them to the same germ at `w`. -/
def EdgeRel (S : SimplicialSheafSystem Z (Type u)) (w : Z.obj (op ⦋1⦌)) (p p' : Z.obj (op ⦋0⦌))
    (h : (S.component (op ⦋0⦌)).presheaf.stalk p)
    (h' : (S.component (op ⦋0⦌)).presheaf.stalk p') : Prop :=
  ∃ k, S.GermTransport (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op w p h k ∧
    S.GermTransport (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op w p' h' k

variable (hS : IsCartesianSystem S)
include hS

/-- A germ at the first vertex of a `1`-simplex is related to some germ at its second vertex. -/
theorem EdgeRel.exists {w : Z.obj (op ⦋1⦌)} {p p' : Z.obj (op ⦋0⦌)}
    (hp : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op w = p)
    (hp' : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op w = p')
    (h : (S.component (op ⦋0⦌)).presheaf.stalk p) : ∃ h', S.EdgeRel w p p' h h' := by
  obtain ⟨k, hk⟩ := exists_germTransport _ w hp h
  obtain ⟨h', hh'⟩ := exists_germTransport_of_isIso (hS _) hp' k
  exact ⟨h', k, hk, hh'⟩

/-- The germ related to a given one by a `1`-simplex is unique. -/
theorem EdgeRel.unique {w : Z.obj (op ⦋1⦌)} {p p' : Z.obj (op ⦋0⦌)}
    (hp : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op w = p)
    (hp' : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op w = p')
    {h : (S.component (op ⦋0⦌)).presheaf.stalk p}
    {h₁ h₂ : (S.component (op ⦋0⦌)).presheaf.stalk p'}
    (h₁r : S.EdgeRel w p p' h h₁) (h₂r : S.EdgeRel w p p' h h₂) : h₁ = h₂ := by
  obtain ⟨k₁, a₁, b₁⟩ := h₁r
  obtain ⟨k₂, a₂, b₂⟩ := h₂r
  obtain rfl := a₁.unique hp a₂
  exact GermTransport.inj (hS _) hp' b₁ b₂

/-- The germ relating to a given one by a `1`-simplex is unique. -/
theorem EdgeRel.unique_left {w : Z.obj (op ⦋1⦌)} {p p' : Z.obj (op ⦋0⦌)}
    (hp : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op w = p)
    (hp' : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op w = p')
    {h₁ h₂ : (S.component (op ⦋0⦌)).presheaf.stalk p}
    {h : (S.component (op ⦋0⦌)).presheaf.stalk p'}
    (h₁r : S.EdgeRel w p p' h₁ h) (h₂r : S.EdgeRel w p p' h₂ h) : h₁ = h₂ := by
  obtain ⟨k₁, a₁, b₁⟩ := h₁r
  obtain ⟨k₂, a₂, b₂⟩ := h₂r
  obtain rfl := b₁.unique hp' b₂
  exact GermTransport.inj (hS _) hp a₁ a₂

omit hS in
private theorem mkOfLe_op_comp_const_zero (a b : Fin 3) (hab : a ≤ b) :
    (SimplexCategory.mkOfLe (n := 2) a b hab).op ≫ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op =
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ a).op := by
  rw [← op_comp, SimplexCategory.const_comp]
  rfl

omit hS in
private theorem mkOfLe_op_comp_const_one (a b : Fin 3) (hab : a ≤ b) :
    (SimplexCategory.mkOfLe (n := 2) a b hab).op ≫ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op =
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ b).op := by
  rw [← op_comp, SimplexCategory.const_comp]
  rfl

/-- The germs related by the edge `(a, b)` of a `2`-simplex `σ` are the germs at the vertices
`a` and `b` of `σ` which the vertex maps carry to the same germ at `σ`. -/
private theorem edgeRel_iff_vertices (σ : Z.obj (op ⦋2⦌)) (a b : Fin 3) (hab : a ≤ b)
    {p p' : Z.obj (op ⦋0⦌)}
    (hp : Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ a).op σ = p)
    (hp' : Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ b).op σ = p')
    (h : (S.component (op ⦋0⦌)).presheaf.stalk p)
    (h' : (S.component (op ⦋0⦌)).presheaf.stalk p') :
    S.EdgeRel (Z.map (SimplexCategory.mkOfLe a b hab).op σ) p p' h h' ↔
      ∃ m, S.GermTransport (SimplexCategory.const ⦋0⦌ ⦋2⦌ a).op σ p h m ∧
        S.GermTransport (SimplexCategory.const ⦋0⦌ ⦋2⦌ b).op σ p' h' m := by
  have hpe : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op
      (Z.map (SimplexCategory.mkOfLe a b hab).op σ) = p := by
    rw [← hp, ← mkOfLe_op_comp_const_zero a b hab, Z.map_comp]
    rfl
  have hpe' : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op
      (Z.map (SimplexCategory.mkOfLe a b hab).op σ) = p' := by
    rw [← hp', ← mkOfLe_op_comp_const_one a b hab, Z.map_comp]
    rfl
  constructor
  · rintro ⟨k, hk, hk'⟩
    obtain ⟨m, hm⟩ := exists_germTransport (SimplexCategory.mkOfLe a b hab).op σ rfl k
    exact ⟨m, (GermTransport.comp hpe hk hm).of_eq (mkOfLe_op_comp_const_zero a b hab),
      (GermTransport.comp hpe' hk' hm).of_eq (mkOfLe_op_comp_const_one a b hab)⟩
  · rintro ⟨m, hm, hm'⟩
    obtain ⟨k, hk⟩ := exists_germTransport _ _ hpe h
    obtain ⟨m', hm''⟩ := exists_germTransport (SimplexCategory.mkOfLe a b hab).op σ rfl k
    obtain rfl : m' = m := ((GermTransport.comp hpe hk hm'').of_eq
      (mkOfLe_op_comp_const_zero a b hab)).unique hp hm
    obtain ⟨h'', hh''⟩ := exists_germTransport_of_isIso (hS _) hpe' k
    obtain rfl : h'' = h' := GermTransport.inj (hS _) hp'
      ((GermTransport.comp hpe' hh'' hm'').of_eq (mkOfLe_op_comp_const_one a b hab)) hm'
    exact ⟨k, hk, hh''⟩

/-- **The cocycle condition.** If the edges `(0, 1)` and `(0, 2)` of a `2`-simplex relate a germ
at its vertex `0` to germs at its vertices `1` and `2`, then its edge `(1, 2)` relates these. -/
theorem EdgeRel.triangle (σ : Z.obj (op ⦋2⦌)) {p₀ p₁ p₂ : Z.obj (op ⦋0⦌)}
    (hp₀ : Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0).op σ = p₀)
    (hp₁ : Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 1).op σ = p₁)
    (hp₂ : Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2).op σ = p₂)
    {h₀ : (S.component (op ⦋0⦌)).presheaf.stalk p₀}
    {h₁ : (S.component (op ⦋0⦌)).presheaf.stalk p₁}
    {h₂ : (S.component (op ⦋0⦌)).presheaf.stalk p₂}
    (r₀₁ : S.EdgeRel (Z.map (SimplexCategory.mkOfLe 0 1 (by decide)).op σ) p₀ p₁ h₀ h₁)
    (r₀₂ : S.EdgeRel (Z.map (SimplexCategory.mkOfLe 0 2 (by decide)).op σ) p₀ p₂ h₀ h₂) :
    S.EdgeRel (Z.map (SimplexCategory.mkOfLe 1 2 (by decide)).op σ) p₁ p₂ h₁ h₂ := by
  obtain ⟨m, a₀, a₁⟩ := (edgeRel_iff_vertices hS σ 0 1 _ hp₀ hp₁ h₀ h₁).1 r₀₁
  obtain ⟨m', b₀, b₂⟩ := (edgeRel_iff_vertices hS σ 0 2 _ hp₀ hp₂ h₀ h₂).1 r₀₂
  obtain rfl := a₀.unique hp₀ b₀
  exact (edgeRel_iff_vertices hS σ 1 2 _ hp₁ hp₂ h₁ h₂).2 ⟨m, a₁, b₂⟩

omit hS in
private theorem const_op_comp_const_op (i : Fin 2) :
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op ≫ (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op = 𝟙 _ := by
  rw [← op_comp]
  have : SimplexCategory.const ⦋0⦌ ⦋1⦌ i ≫ SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = 𝟙 _ := by
    ext x : 3
    simp [Fin.eq_zero]
  rw [this]
  rfl

omit hS in
/-- The vertices of a degenerate `1`-simplex. -/
theorem map_const_degenerate (i : Fin 2) (p : Z.obj (op ⦋0⦌)) :
    Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op (Z.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op p) =
      p := by
  rw [← ConcreteCategory.comp_apply, ← Z.map_comp, const_op_comp_const_op, Z.map_id]
  rfl

omit hS in
/-- A degenerate `1`-simplex relates a germ only to itself. -/
theorem EdgeRel.eq_of_degenerate {p : Z.obj (op ⦋0⦌)}
    {h h' : (S.component (op ⦋0⦌)).presheaf.stalk p}
    (r : S.EdgeRel (Z.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op p) p p h h') : h = h' := by
  obtain ⟨k, hk, hk'⟩ := r
  obtain ⟨m, hm⟩ := exists_germTransport (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op p rfl k
  have hid : Z.map (𝟙 (op ⦋0⦌)) p = p := by
    rw [Z.map_id]
    rfl
  have key : ∀ (i : Fin 2) (g : (S.component (op ⦋0⦌)).presheaf.stalk p),
      S.GermTransport (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op _ p g k → m = g := fun i g hg =>
    ((GermTransport.comp (map_const_degenerate i p) hg hm).of_eq
      (const_op_comp_const_op i)).unique hid (germTransport_id _ p g)
  exact (key 0 h hk).symm.trans (key 1 h' hk')

/-- A degenerate `1`-simplex relates every germ to itself. -/
theorem EdgeRel.degenerate (p : Z.obj (op ⦋0⦌)) (h : (S.component (op ⦋0⦌)).presheaf.stalk p) :
    S.EdgeRel (Z.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op p) p p h h := by
  obtain ⟨h', r⟩ := EdgeRel.exists hS (map_const_degenerate 0 p) (map_const_degenerate 1 p) h
  obtain rfl := EdgeRel.eq_of_degenerate r
  exact r

omit hS in
/-- The vertex `0` of the edge `(a, b)` of a `2`-simplex is its vertex `a`. -/
theorem map_const_zero_mkOfLe (σ : Z.obj (op ⦋2⦌)) (a b : Fin 3) (hab : a ≤ b) :
    Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op (Z.map (SimplexCategory.mkOfLe a b hab).op σ) =
      Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ a).op σ := by
  rw [← mkOfLe_op_comp_const_zero a b hab, Z.map_comp]
  rfl

omit hS in
/-- The vertex `1` of the edge `(a, b)` of a `2`-simplex is its vertex `b`. -/
theorem map_const_one_mkOfLe (σ : Z.obj (op ⦋2⦌)) (a b : Fin 3) (hab : a ≤ b) :
    Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op (Z.map (SimplexCategory.mkOfLe a b hab).op σ) =
      Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ b).op σ := by
  rw [← mkOfLe_op_comp_const_one a b hab, Z.map_comp]
  rfl

/-- **The cocycle condition, for three `1`-simplices bounding a `2`-simplex.** If `a` relates
`h₀` to `h₁`, `b` relates `h₀` to `h₂`, and `a`, `b`, `c` are the edges `(0, 1)`, `(0, 2)`,
`(1, 2)` of a `2`-simplex, then `c` relates `h₁` to `h₂`. -/
theorem EdgeRel.of_triangle {a b c : Z.obj (op ⦋1⦌)} (σ : Z.obj (op ⦋2⦌))
    (ha : Z.map (SimplexCategory.mkOfLe 0 1 (by decide)).op σ = a)
    (hb : Z.map (SimplexCategory.mkOfLe 0 2 (by decide)).op σ = b)
    (hc : Z.map (SimplexCategory.mkOfLe 1 2 (by decide)).op σ = c)
    {p₀ p₁ p₂ : Z.obj (op ⦋0⦌)}
    (hp₀ : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op a = p₀)
    (hp₁ : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op a = p₁)
    (hp₂ : Z.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op b = p₂)
    {h₀ : (S.component (op ⦋0⦌)).presheaf.stalk p₀}
    {h₁ : (S.component (op ⦋0⦌)).presheaf.stalk p₁}
    {h₂ : (S.component (op ⦋0⦌)).presheaf.stalk p₂}
    (r₀₁ : S.EdgeRel a p₀ p₁ h₀ h₁) (r₀₂ : S.EdgeRel b p₀ p₂ h₀ h₂) :
    S.EdgeRel c p₁ p₂ h₁ h₂ := by
  subst ha hb hc
  exact EdgeRel.triangle hS σ
    ((map_const_zero_mkOfLe σ 0 1 _).symm.trans hp₀)
    ((map_const_one_mkOfLe σ 0 1 _).symm.trans hp₁)
    ((map_const_one_mkOfLe σ 0 2 _).symm.trans hp₂) r₀₁ r₀₂

end Stacks.Topology.Simplicial.SimplicialSheafSystem

namespace Stacks.Topology.Simplicial

open Augmentation SimplicialSheafSystem

/-! ### Limits of cosimplicial types -/

/-- The degree-zero projection of a limit of a cosimplicial type is injective, and its image
consists of the elements on which the two maps induced by the vertices of the `1`-simplex
agree. -/
theorem cosimplicialLimit_π_zero {D : SimplexCategory ⥤ Type u} {c : Cone D} (hc : IsLimit c) :
    Function.Injective (c.π.app ⦋0⦌) ∧
      ∀ s₀ : D.obj ⦋0⦌, D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) s₀ =
        D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) s₀ → ∃ s, c.π.app ⦋0⦌ s = s₀ := by
  have hvert : ∀ (s₀ : D.obj ⦋0⦌), D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) s₀ =
      D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) s₀ → ∀ (n : SimplexCategory) (i : Fin (n.len + 1)),
      D.map (SimplexCategory.const ⦋0⦌ n 0) s₀ = D.map (SimplexCategory.const ⦋0⦌ n i) s₀ := by
    intro s₀ h n i
    have := cosimplicial_vertex_eq D (T := PUnit.{u + 1}) (↾fun _ => s₀) (by ext; exact h) n i
    exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : PUnit → D.obj n)) this) ⟨⟩
  refine ⟨fun s s' h => ?_, fun s₀ h => ?_⟩
  · apply (Types.isLimitEquivSections hc).injective
    apply Subtype.ext
    funext n
    change c.π.app n s = c.π.app n s'
    rw [← c.w (SimplexCategory.const ⦋0⦌ n 0)]
    exact congrArg (D.map (SimplexCategory.const ⦋0⦌ n 0)) h
  · refine ⟨(Types.isLimitEquivSections hc).symm
      ⟨fun n => D.map (SimplexCategory.const ⦋0⦌ n 0) s₀, fun {n m} f => ?_⟩, ?_⟩
    · change (D.map (SimplexCategory.const ⦋0⦌ n 0) ≫ D.map f) s₀ = _
      rw [← D.map_comp, SimplexCategory.const_comp]
      exact (hvert s₀ h m _).symm
    · rw [Types.isLimitEquivSections_symm_apply]
      change D.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) s₀ = s₀
      rw [SimplexCategory.const_eq_id, D.map_id]
      rfl

/-! ### Sections of the direct image along an augmentation -/

namespace Augmentation

variable (Y : SimplicialObject TopCat.{u}) (X : TopCat.{u})
  (a : Y ⟶ (SimplicialObject.const TopCat).obj X)

/-- On germs, the direct-image map attached to a triangle `f ≫ c = b` is the `f`-map. -/
theorem germ_pushTransition_app {B C W : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ W) (c : C ⟶ W) (h : f ≫ c = b)
    {F : sh B} {G : sh C} (t : G ⟶ (pf f).obj F) (V : Opens W)
    (s : G.obj.obj (op ((Opens.map c).obj V))) (p : B) (hp : b p ∈ V) (hp' : c (f p) ∈ V) :
    F.presheaf.germ ((Opens.map b).obj V) p hp ((pushTransition f b c h t).hom.app (op V) s) =
      F.presheaf.germ ((Opens.map f).obj ((Opens.map c).obj V)) p hp' (t.hom.app _ s) := by
  subst h
  rfl

/-- The vertex map `Y_1 → Y_0` attached to `i : [0] → [1]`. -/
abbrev vertex (i : Fin 2) : Y.obj (op ⦋1⦌) ⟶ Y.obj (op ⦋0⦌) :=
  Y.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op

/-- The augmentation is compatible with the vertex maps. -/
private theorem app_zero_vertex_aux (i : Fin 2) (w : Y.obj (op ⦋1⦌)) :
    a.app (op ⦋0⦌) (vertex Y i w) = a.app (op ⦋1⦌) w := by
  have e := ConcreteCategory.congr_hom (augmentation_w Y X a
    (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op) w
  rwa [ConcreteCategory.comp_apply] at e

/-- The projection of the direct image of a system to its degree-zero term, on sections over
`V`: a section of `a_* S` over `V` gives a section of `S_0` over `a_0⁻¹(V)`. -/
noncomputable def directImageSection₀ (S : SimplicialSheafSystem Y (Type u)) (V : Opens X)
    (t : (limit (pushforwardDiagram Y X a S)).obj.obj (op V)) :
    (S.component (op ⦋0⦌)).obj.obj (op ((Opens.map (a.app (op ⦋0⦌))).obj V)) :=
  (limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom.app (op V) t

/-- The projection to degree zero commutes with restriction. -/
theorem directImageSection₀_map (S : SimplicialSheafSystem Y (Type u)) {V V' : Opens X}
    (i : V' ⟶ V) (t : (limit (pushforwardDiagram Y X a S)).obj.obj (op V)) :
    directImageSection₀ Y X a S V' ((limit (pushforwardDiagram Y X a S)).obj.map i.op t) =
      (S.component (op ⦋0⦌)).obj.map ((Opens.map (a.app (op ⦋0⦌))).map i).op
        (directImageSection₀ Y X a S V t) :=
  ConcreteCategory.congr_hom
    ((limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom.naturality i.op) t

/-- The cone of sections over `V` of the limit of the cosimplicial direct images is a limit. -/
private noncomputable def isLimitSections (S : SimplicialSheafSystem Y (Type u)) (V : Opens X) :
    IsLimit ((TopCat.Sheaf.forget (Type u) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type u)).obj (op V)).mapCone
        (limit.cone (pushforwardDiagram Y X a S))) := by
  have : PreservesLimitsOfShape SimplexCategory (TopCat.Sheaf.forget (Type u) X) := by
    change PreservesLimitsOfShape SimplexCategory
      (sheafToPresheaf (Opens.grothendieckTopology X) (Type u))
    infer_instance
  have : PreservesLimitsOfShape SimplexCategory
      ((evaluation (Opens X)ᵒᵖ (Type u)).obj (op V)) := inferInstance
  exact isLimitOfPreserves _ (limit.isLimit _)

/-- Two sections of the direct image with the same projection to degree zero are equal. -/
theorem directImageSection₀_injective (S : SimplicialSheafSystem Y (Type u)) (V : Opens X) :
    Function.Injective (directImageSection₀ Y X a S V) :=
  (cosimplicialLimit_π_zero (isLimitSections Y X a S V)).1

/-- The germ at a `1`-simplex `w` of the `i`-th transport of a section is the germ of its image
under the `i`-th map of the diagram of direct images. -/
private theorem germ_transition_eq_germ_map (S : SimplicialSheafSystem Y (Type u)) (V : Opens X)
    (s : (S.component (op ⦋0⦌)).obj.obj (op ((Opens.map (a.app (op ⦋0⦌))).obj V)))
    (i : Fin 2) (w : Y.obj (op ⦋1⦌)) (hw : a.app (op ⦋1⦌) w ∈ V)
    (h : a.app (op ⦋0⦌) (vertex Y i w) ∈ V) :
    (S.component (op ⦋1⦌)).presheaf.germ _ w h
        ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op).app _ s) =
      (S.component (op ⦋1⦌)).presheaf.germ _ w hw
        (((pushforwardDiagram Y X a S).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).hom.app (op V) s) :=
  (germ_pushTransition_app (Y.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op) _ _
    (augmentation_w Y X a _) (systemTransition Y S (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op) V s w hw
      h).symm

/-- The germs at a `1`-simplex `w` of the two transports of the degree-zero projection of a
section of the direct image agree. -/
theorem germ_transition_directImageSection₀ (S : SimplicialSheafSystem Y (Type u)) (V : Opens X)
    (t : (limit (pushforwardDiagram Y X a S)).obj.obj (op V)) (w : Y.obj (op ⦋1⦌))
    (h₀ : a.app (op ⦋0⦌) (vertex Y 0 w) ∈ V) (h₁ : a.app (op ⦋0⦌) (vertex Y 1 w) ∈ V) :
    (S.component (op ⦋1⦌)).presheaf.germ _ w h₀
        ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).app _
          (directImageSection₀ Y X a S V t)) =
      (S.component (op ⦋1⦌)).presheaf.germ _ w h₁
        ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op).app _
          (directImageSection₀ Y X a S V t)) := by
  let D := pushforwardDiagram Y X a S
  have hw : a.app (op ⦋1⦌) w ∈ V := (app_zero_vertex_aux Y X a 0 w) ▸ h₀
  have hc : ∀ i : Fin 2, (limit.π D ⦋1⦌).hom.app (op V) t =
      (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)).hom.app (op V)
        (directImageSection₀ Y X a S V t) := fun i => by
    rw [← limit.w D (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)]
    rfl
  rw [germ_transition_eq_germ_map Y X a S V _ 0 w hw,
    germ_transition_eq_germ_map Y X a S V _ 1 w hw, ← hc 0, ← hc 1]

/-- A section of `S_0` over `a_0⁻¹(V)` whose two transports to `S_1` have the same germs at every
`1`-simplex over `V` is the degree-zero projection of a section of the direct image. -/
theorem exists_directImageSection₀_eq (S : SimplicialSheafSystem Y (Type u)) (V : Opens X)
    (s : (S.component (op ⦋0⦌)).obj.obj (op ((Opens.map (a.app (op ⦋0⦌))).obj V)))
    (hs : ∀ (w : Y.obj (op ⦋1⦌)) (h₀ : a.app (op ⦋0⦌) (vertex Y 0 w) ∈ V)
      (h₁ : a.app (op ⦋0⦌) (vertex Y 1 w) ∈ V),
      (S.component (op ⦋1⦌)).presheaf.germ _ w h₀
          ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).app _ s) =
        (S.component (op ⦋1⦌)).presheaf.germ _ w h₁
          ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op).app _ s)) :
    ∃ t, directImageSection₀ Y X a S V t = s := by
  let D := pushforwardDiagram Y X a S
  refine (cosimplicialLimit_π_zero (isLimitSections Y X a S V)).2 s ?_
  change (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)).hom.app (op V) s =
    (D.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)).hom.app (op V) s
  refine TopCat.Presheaf.section_ext (S.component (op ⦋1⦌)) _ _ _ fun w hw => ?_
  have h₀ : a.app (op ⦋0⦌) (vertex Y 0 w) ∈ V := (app_zero_vertex_aux Y X a 0 w).symm ▸ hw
  have h₁ : a.app (op ⦋0⦌) (vertex Y 1 w) ∈ V := (app_zero_vertex_aux Y X a 1 w).symm ▸ hw
  exact (germ_transition_eq_germ_map Y X a S V s 0 w hw h₀).symm.trans
    ((hs w h₀ h₁).trans (germ_transition_eq_germ_map Y X a S V s 1 w hw h₁))

end Augmentation

/-! ### Extending a family of germs along a quasi-compact subset -/

open Stacks.Topology.SectionsOnQuasiCompactSubset in
/-- **Stacks 09V3 in degree zero, for a family of germs.** Let `K` be a quasi-compact subset of
a space any two distinct points of which are separated by disjoint opens, and let `h` assign to
each point of `K` a germ of a sheaf of sets `F` there, in such a way that near each point of `K`
the germs are those of a single section. Then the germs are those of a single section on an open
neighbourhood of `K`. -/
theorem exists_germ_eq_of_isCompact {T : TopCat.{u}} (F : T.Sheaf (Type u)) {K : Set T}
    (hK : IsCompact K) (hSep : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      ∃ A B : Set T, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (h : ∀ x : K, F.presheaf.stalk x.1)
    (hloc : ∀ x : K, ∃ (U : Opens T) (_ : x.1 ∈ U) (s : F.presheaf.obj (op U)),
      ∀ (y : K) (hy : y.1 ∈ U), h y = F.presheaf.germ U y.1 hy s) :
    ∃ (U : Opens T) (hKU : K ⊆ U) (s : F.presheaf.obj (op U)),
      ∀ y : K, F.presheaf.germ U y.1 (hKU y.2) s = h y := by
  let σ : sectionsOn F.presheaf K :=
    ⟨fun z => ⟨z.1.1, h z.1⟩, fun z => by
      obtain ⟨U, hxU, s, hs⟩ := hloc z.1
      let V : Opens (TopCat.of K) := ⟨Subtype.val ⁻¹' (U : Set T),
        U.isOpen.preimage continuous_subtype_val⟩
      exact ⟨V, hxU, homOfLE le_top, U, fun y => y.2, s, fun y => by
        change (⟨y.1.1, h y.1⟩ : GermPullback.Germs F.presheaf) = ⟨y.1.1, _⟩
        rw [hs y.1 y.2]
        rfl⟩⟩
  obtain ⟨U, hKU, s, hs⟩ := exists_isOpen_restrictToSubset_eq F hK hSep σ
  refine ⟨U, hKU, s, fun y => ?_⟩
  have e := congrArg (fun τ : sectionsOn F.presheaf K => τ.1 ⟨y, trivial⟩) hs
  exact eq_of_heq ((Sigma.mk.inj_iff.1 e).2)

/-! ### Descent along a proper hypercovering -/

namespace Augmentation

variable (Y : SimplicialObject TopCat.{u}) (X : TopCat.{u})
  (a : Y ⟶ (SimplicialObject.const TopCat).obj X)

/-- The point-set consequences of an augmentation being a proper hypercovering which the
descent of sheaves along it uses: the augmentation in degree zero is a closed surjection with
quasi-compact fibres from a Hausdorff space, the augmentation in degree one is closed, the
vertex map `Y_1 → Y_0 × Y_0` is closed and hits every pair of points with the same image, and
three `1`-simplices bounding a triangle are the edges of a `2`-simplex. -/
structure DescentConditions : Prop where
  /-- The augmentation in degree zero is surjective. -/
  surjective₀ : Function.Surjective (a.app (op ⦋0⦌))
  /-- The augmentation in degree zero is a closed map. -/
  isClosedMap₀ : IsClosedMap (a.app (op ⦋0⦌))
  /-- Every fibre of the augmentation in degree zero is quasi-compact. -/
  isCompact_fiber₀ : ∀ x : X, IsCompact (a.app (op ⦋0⦌) ⁻¹' {x})
  /-- The space of `0`-simplices is Hausdorff. -/
  t2Space₀ : T2Space (Y.obj (op ⦋0⦌))
  /-- The augmentation in degree one is a closed map. -/
  isClosedMap₁ : IsClosedMap (a.app (op ⦋1⦌))
  /-- The vertex map `Y_1 → Y_0 × Y_0` is a closed map. -/
  isClosedMap_vertices : IsClosedMap (fun w : Y.obj (op ⦋1⦌) => (vertex Y 0 w, vertex Y 1 w))
  /-- Any two `0`-simplices with the same image in `X` are the vertices of a `1`-simplex. -/
  exists_edge : ∀ p q : Y.obj (op ⦋0⦌), a.app (op ⦋0⦌) p = a.app (op ⦋0⦌) q →
    ∃ w, vertex Y 0 w = p ∧ vertex Y 1 w = q
  /-- Three `1`-simplices bounding a triangle are the edges of a `2`-simplex. -/
  exists_triangle : ∀ e₀₁ e₀₂ e₁₂ : Y.obj (op ⦋1⦌), vertex Y 0 e₀₁ = vertex Y 0 e₀₂ →
    vertex Y 1 e₀₁ = vertex Y 0 e₁₂ → vertex Y 1 e₀₂ = vertex Y 1 e₁₂ →
    ∃ σ : Y.obj (op ⦋2⦌), Y.map (SimplexCategory.mkOfLe 0 1 (by decide)).op σ = e₀₁ ∧
      Y.map (SimplexCategory.mkOfLe 0 2 (by decide)).op σ = e₀₂ ∧
      Y.map (SimplexCategory.mkOfLe 1 2 (by decide)).op σ = e₁₂

variable {Y X a}

/-- The augmentation is compatible with the vertex maps. -/
theorem app_zero_vertex (i : Fin 2) (w : Y.obj (op ⦋1⦌)) :
    a.app (op ⦋0⦌) (vertex Y i w) = a.app (op ⦋1⦌) w :=
  app_zero_vertex_aux Y X a i w

/-- Germ transport of the germ of a section, at a point given up to equality. -/
private theorem germTransport_germ' {S : SimplicialSheafSystem Y (Type u)}
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Y.obj n) {q : Y.obj m} (hq : Y.map φ w = q)
    (V : Opens (Y.obj m)) (hqV : q ∈ V) (hw : Y.map φ w ∈ V)
    (s : (S.component m).presheaf.obj (op V)) :
    S.GermTransport φ w q ((S.component m).presheaf.germ V q hqV s)
      ((S.component n).presheaf.germ ((Opens.map (Y.map φ)).obj V) w hw
        ((S.transition φ).app (op V) s)) := by
  subst hq
  exact germTransport_germ φ w V hqV s

variable (H : DescentConditions Y X a) {S : SimplicialSheafSystem Y (Type u)}
  (hS : S.IsCartesianSystem)

include H hS

/-- A germ at `u` related along some `1`-simplex to a germ at a point `u'` over the same point
of `X`. -/
private theorem exists_transfer (u : Y.obj (op ⦋0⦌))
    (g : (S.component (op ⦋0⦌)).presheaf.stalk u) (u' : Y.obj (op ⦋0⦌))
    (hu' : a.app (op ⦋0⦌) u' = a.app (op ⦋0⦌) u) :
    ∃ h', ∃ w, vertex Y 0 w = u ∧ vertex Y 1 w = u' ∧ S.EdgeRel w u u' g h' := by
  obtain ⟨w, h0, h1⟩ := H.exists_edge u u' hu'.symm
  obtain ⟨h', r⟩ := EdgeRel.exists hS h0 h1 g
  exact ⟨h', w, h0, h1, r⟩

/-- The germ at `u'` obtained by transporting `g` along a `1`-simplex from `u` to `u'`. -/
private noncomputable def transfer (u : Y.obj (op ⦋0⦌))
    (g : (S.component (op ⦋0⦌)).presheaf.stalk u) (u' : Y.obj (op ⦋0⦌))
    (hu' : a.app (op ⦋0⦌) u' = a.app (op ⦋0⦌) u) :
    (S.component (op ⦋0⦌)).presheaf.stalk u' :=
  (exists_transfer H hS u g u' hu').choose

private theorem transfer_spec (u : Y.obj (op ⦋0⦌))
    (g : (S.component (op ⦋0⦌)).presheaf.stalk u) (u' : Y.obj (op ⦋0⦌))
    (hu' : a.app (op ⦋0⦌) u' = a.app (op ⦋0⦌) u) :
    ∃ w, vertex Y 0 w = u ∧ vertex Y 1 w = u' ∧ S.EdgeRel w u u' g (transfer H hS u g u' hu') :=
  (exists_transfer H hS u g u' hu').choose_spec

/-- The transported germ does not depend on the `1`-simplex: this is the cocycle condition,
applied to a `2`-simplex with a degenerate edge. -/
private theorem eq_transfer {u u' : Y.obj (op ⦋0⦌)}
    {g : (S.component (op ⦋0⦌)).presheaf.stalk u} (hu' : a.app (op ⦋0⦌) u' = a.app (op ⦋0⦌) u)
    {w : Y.obj (op ⦋1⦌)} (h0 : vertex Y 0 w = u) (h1 : vertex Y 1 w = u')
    {h' : (S.component (op ⦋0⦌)).presheaf.stalk u'} (r : S.EdgeRel w u u' g h') :
    h' = transfer H hS u g u' hu' := by
  obtain ⟨w₁, k0, k1, r₁⟩ := transfer_spec H hS u g u' hu'
  let d := Y.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op u'
  obtain ⟨σ, ha, hb, hc⟩ := H.exists_triangle w₁ w d (k0.trans h0.symm)
    (k1.trans (map_const_degenerate 0 u').symm) (h1.trans (map_const_degenerate 1 u').symm)
  exact (EdgeRel.eq_of_degenerate (EdgeRel.of_triangle hS σ ha hb hc k0 k1 h1 r₁ r)).symm

private theorem transfer_self (u : Y.obj (op ⦋0⦌))
    (g : (S.component (op ⦋0⦌)).presheaf.stalk u) : transfer H hS u g u rfl = g :=
  (eq_transfer H hS rfl (map_const_degenerate 0 u) (map_const_degenerate 1 u)
    (EdgeRel.degenerate hS u g)).symm

/-- Near every point of the fibre, the transported germs are the germs of a single section. -/
private theorem transfer_locally (u : Y.obj (op ⦋0⦌))
    (g : (S.component (op ⦋0⦌)).presheaf.stalk u) (u' : Y.obj (op ⦋0⦌))
    (hu' : a.app (op ⦋0⦌) u' = a.app (op ⦋0⦌) u) :
    ∃ (U : Opens (Y.obj (op ⦋0⦌))) (_ : u' ∈ U)
      (ρ : (S.component (op ⦋0⦌)).presheaf.obj (op U)),
      ∀ (u'' : Y.obj (op ⦋0⦌)) (hu'' : a.app (op ⦋0⦌) u'' = a.app (op ⦋0⦌) u) (h : u'' ∈ U),
        transfer H hS u g u'' hu'' = (S.component (op ⦋0⦌)).presheaf.germ U u'' h ρ := by
  let G₀ := (S.component (op ⦋0⦌)).presheaf
  let G₁ := (S.component (op ⦋1⦌)).presheaf
  obtain ⟨N, huN, t, rfl⟩ := G₀.exists_germ_eq g
  obtain ⟨N', hu'N', ρ, hρ⟩ := G₀.exists_germ_eq (transfer H hS u (G₀.germ N u huN t) u' hu')
  let τ₀ := (S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).app (op N) t
  let τ₁ := (S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op).app (op N') ρ
  let M := Stacks.Topology.SectionsOnQuasiCompactSubset.germEqOpens G₁ τ₀ τ₁
  -- A `1`-simplex from `u` to a point of `N'` lies in `M` exactly when the transported germ
  -- there is the germ of `ρ`.
  have key : ∀ (u'' : Y.obj (op ⦋0⦌)) (hu'' : a.app (op ⦋0⦌) u'' = a.app (op ⦋0⦌) u)
      (hN' : u'' ∈ N') (w : Y.obj (op ⦋1⦌)) (h0 : vertex Y 0 w = u) (h1 : vertex Y 1 w = u''),
      (w ∈ M ↔ transfer H hS u (G₀.germ N u huN t) u'' hu'' = G₀.germ N' u'' hN' ρ) := by
    intro u'' hu'' hN' w h0 h1
    have hw0 : vertex Y 0 w ∈ N := h0 ▸ huN
    have hw1 : vertex Y 1 w ∈ N' := h1 ▸ hN'
    have T₀ := germTransport_germ' (S := S) _ w h0 N huN hw0 t
    have T₁ := germTransport_germ' (S := S) _ w h1 N' hN' hw1 ρ
    refine ⟨fun hM => ?_, fun he => ?_⟩
    · obtain ⟨hx₀, hx₁, he⟩ := Stacks.Topology.SectionsOnQuasiCompactSubset.mem_germEqOpens.1 hM
      refine (eq_transfer H hS hu'' h0 h1 ⟨_, T₀, ?_⟩).symm
      rw [he]
      exact T₁
    · obtain ⟨h', k, a₀, a₁⟩ := EdgeRel.exists hS h0 h1 (G₀.germ N u huN t)
      obtain rfl : h' = G₀.germ N' u'' hN' ρ :=
        (eq_transfer H hS hu'' h0 h1 ⟨k, a₀, a₁⟩).trans he
      exact ⟨hw0, hw1, (a₀.unique h0 T₀).symm.trans (a₁.unique h1 T₁)⟩
  -- The pairs `(u, y)` reached by `1`-simplices outside `M` form a closed set.
  have hC := H.isClosedMap_vertices _ M.isOpen.isClosed_compl
  let Q : Set (Y.obj (op ⦋0⦌)) :=
    (fun y => (u, y)) ⁻¹' ((fun w : Y.obj (op ⦋1⦌) => (vertex Y 0 w, vertex Y 1 w)) ''
      (M : Set (Y.obj (op ⦋1⦌)))ᶜ)ᶜ
  have hQ : IsOpen Q := (hC.isOpen_compl).preimage (Continuous.prodMk_right u)
  have hu'Q : u' ∈ Q := by
    rintro ⟨w, hwM, hw⟩
    obtain ⟨h0, h1⟩ := Prod.ext_iff.1 hw
    exact hwM ((key u' hu' hu'N' w h0 h1).2 hρ.symm)
  refine ⟨⟨Q, hQ⟩ ⊓ N', ⟨hu'Q, hu'N'⟩, G₀.map (homOfLE inf_le_right).op ρ,
    fun u'' hu'' h => ?_⟩
  rw [G₀.germ_res_apply (homOfLE inf_le_right) u'' h ρ]
  obtain ⟨w, h0, h1⟩ := H.exists_edge u u'' hu''.symm
  refine (key u'' hu'' h.2 w h0 h1).1 ?_
  by_contra hwM
  exact h.1 ⟨w, hwM, Prod.ext h0 h1⟩

omit H hS in
/-- The germs at a `1`-simplex of the two transports of a section are equal exactly when the
`1`-simplex relates the germs of the section at its two vertices. -/
private theorem edgeRel_germ_iff {w : Y.obj (op ⦋1⦌)} {V : Opens (Y.obj (op ⦋0⦌))}
    (s : (S.component (op ⦋0⦌)).presheaf.obj (op V)) (h₀ : vertex Y 0 w ∈ V)
    (h₁ : vertex Y 1 w ∈ V) :
    S.EdgeRel w (vertex Y 0 w) (vertex Y 1 w) ((S.component (op ⦋0⦌)).presheaf.germ V _ h₀ s)
        ((S.component (op ⦋0⦌)).presheaf.germ V _ h₁ s) ↔
      (S.component (op ⦋1⦌)).presheaf.germ _ w h₀
          ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).app (op V) s) =
        (S.component (op ⦋1⦌)).presheaf.germ _ w h₁
          ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op).app (op V) s) := by
  have T₀ := germTransport_germ (S := S) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op w V h₀ s
  have T₁ := germTransport_germ (S := S) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op w V h₁ s
  exact ⟨fun ⟨_, a₀, a₁⟩ => (T₀.unique rfl a₀).trans (a₁.unique rfl T₁),
    fun e => ⟨_, T₀, e ▸ T₁⟩⟩

omit H hS in
/-- The stalk comparison map of the degree-zero projection sends the germ of a section of `a_* S`
to the germ of its degree-zero projection. -/
private theorem stalkComparison_π_zero_germ (u : Y.obj (op ⦋0⦌)) (V : Opens X)
    (hx : a.app (op ⦋0⦌) u ∈ V) (t : (limit (pushforwardDiagram Y X a S)).presheaf.obj (op V)) :
    Stacks.Sheaves.PullbackUnit.stalkComparison (a.app (op ⦋0⦌)) (Type u)
        (limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom u
        ((limit (pushforwardDiagram Y X a S)).presheaf.germ V (a.app (op ⦋0⦌) u) hx t) =
      (S.component (op ⦋0⦌)).presheaf.germ ((Opens.map (a.app (op ⦋0⦌))).obj V) u hx
        (directImageSection₀ Y X a S V t) :=
  ConcreteCategory.congr_hom
    (Stacks.Sheaves.PullbackUnit.germ_stalkComparison (a.app (op ⦋0⦌)) (Type u)
      (limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom u V hx) t

/-- Two sections of `a_* S` whose degree-zero projections have the same germ at `u` have
degree-zero projections with the same germs along the whole fibre through `u`. -/
private theorem preimage_subset_germEqOpens_directImageSection₀ (u : Y.obj (op ⦋0⦌))
    {V V' : Opens X} (hxV : a.app (op ⦋0⦌) u ∈ V) (hxV' : a.app (op ⦋0⦌) u ∈ V')
    (t : (limit (pushforwardDiagram Y X a S)).obj.obj (op V))
    (t' : (limit (pushforwardDiagram Y X a S)).obj.obj (op V'))
    (hξ : (S.component (op ⦋0⦌)).presheaf.germ _ u hxV (directImageSection₀ Y X a S V t) =
      (S.component (op ⦋0⦌)).presheaf.germ _ u hxV' (directImageSection₀ Y X a S V' t')) :
    a.app (op ⦋0⦌) ⁻¹' {a.app (op ⦋0⦌) u} ⊆
      (Stacks.Topology.SectionsOnQuasiCompactSubset.germEqOpens (S.component (op ⦋0⦌)).presheaf
        (directImageSection₀ Y X a S V t) (directImageSection₀ Y X a S V' t') : Set _) := by
  intro p hp
  have hpx : a.app (op ⦋0⦌) p = a.app (op ⦋0⦌) u := hp
  obtain ⟨w, h0, h1⟩ := H.exists_edge u p hpx.symm
  have hv : ∀ i : Fin 2, a.app (op ⦋0⦌) (vertex Y i w) = a.app (op ⦋0⦌) u := fun i => by
    rw [app_zero_vertex, ← app_zero_vertex 0 w, h0]
  have m : ∀ {W : Opens X}, a.app (op ⦋0⦌) u ∈ W → ∀ i : Fin 2,
      vertex Y i w ∈ (Opens.map (a.app (op ⦋0⦌))).obj W := fun {W} hW i => by
    change a.app (op ⦋0⦌) (vertex Y i w) ∈ W
    rw [hv i]
    exact hW
  have r := (edgeRel_germ_iff (directImageSection₀ Y X a S V t) (m hxV 0) (m hxV 1)).2
    (germ_transition_directImageSection₀ Y X a S V t w (m hxV 0) (m hxV 1))
  have r' := (edgeRel_germ_iff (directImageSection₀ Y X a S V' t') (m hxV' 0)
    (m hxV' 1)).2 (germ_transition_directImageSection₀ Y X a S V' t' w (m hxV' 0) (m hxV' 1))
  subst h0 h1
  have e₀ : (S.component (op ⦋0⦌)).presheaf.germ _ _ (m hxV 0)
      (directImageSection₀ Y X a S V t) = (S.component (op ⦋0⦌)).presheaf.germ _ _ (m hxV' 0)
        (directImageSection₀ Y X a S V' t') := hξ
  rw [e₀] at r
  exact ⟨m hxV 1, m hxV' 1, EdgeRel.unique hS rfl rfl r r'⟩

/-- **Descent along a proper hypercovering, on stalks: injectivity.** Two sections whose
projections have the same germ at `u` have projections with the same germs along the whole fibre,
hence agree near the fibre. -/
private theorem injective_stalkComparison_π_zero (u : Y.obj (op ⦋0⦌)) :
    Function.Injective (Stacks.Sheaves.PullbackUnit.stalkComparison (a.app (op ⦋0⦌)) (Type u)
      (limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom u) := by
  let G₀ := (S.component (op ⦋0⦌)).presheaf
  let L := (limit (pushforwardDiagram Y X a S)).presheaf
  let x := a.app (op ⦋0⦌) u
  intro ξ ξ' hξ
  obtain ⟨V, hxV, t, rfl⟩ := L.exists_germ_eq ξ
  obtain ⟨V', hxV', t', rfl⟩ := L.exists_germ_eq ξ'
  have hfib := preimage_subset_germEqOpens_directImageSection₀ H hS u hxV hxV' t t'
    ((stalkComparison_π_zero_germ u V hxV t).symm.trans
      (hξ.trans (stalkComparison_π_zero_germ u V' hxV' t')))
  set s := directImageSection₀ Y X a S V t
  set s' := directImageSection₀ Y X a S V' t'
  obtain ⟨N, hN, hxN, hNsub⟩ :=
    Stacks.Topology.SectionsOnQuasiCompactSubset.exists_isOpen_preimage_subset_of_isClosedMap
      H.isClosedMap₀ (Opens.isOpen _) hfib
  let V'' : Opens X := V ⊓ V' ⊓ ⟨N, hN⟩
  let i : V'' ⟶ V := homOfLE (inf_le_left.trans inf_le_left)
  let i' : V'' ⟶ V' := homOfLE (inf_le_left.trans inf_le_right)
  have hx'' : x ∈ V'' := ⟨⟨hxV, hxV'⟩, hxN⟩
  have heq : L.map i.op t = L.map i'.op t' := by
    apply directImageSection₀_injective Y X a S V''
    rw [directImageSection₀_map, directImageSection₀_map]
    refine TopCat.Presheaf.section_ext (S.component (op ⦋0⦌)) _ _ _ fun p hp => ?_
    obtain ⟨hp₁, hp₂, hp₃⟩ := hNsub hp.2
    change G₀.germ _ p hp (G₀.map _ s) = G₀.germ _ p hp (G₀.map _ s')
    rw [G₀.germ_res_apply, G₀.germ_res_apply]
    exact hp₃
  rw [← L.germ_res_apply i x hx'' t, ← L.germ_res_apply i' x hx'' t', heq]

/-- A section of `S_0` near the fibre over `a_0(u)` whose germs along the fibre are the
transported germs of `ξ` has two transports to `S_1` with the same germs along the fibre in
degree one. -/
private theorem preimage_subset_germEqOpens_transition (u : Y.obj (op ⦋0⦌))
    (ξ : (S.component (op ⦋0⦌)).presheaf.stalk u) {N : Opens X} (hxN : a.app (op ⦋0⦌) u ∈ N)
    (s : (S.component (op ⦋0⦌)).presheaf.obj (op ((Opens.map (a.app (op ⦋0⦌))).obj N)))
    (hs : ∀ (p : Y.obj (op ⦋0⦌)) (hp : a.app (op ⦋0⦌) p = a.app (op ⦋0⦌) u)
      (hpN : p ∈ (Opens.map (a.app (op ⦋0⦌))).obj N),
      (S.component (op ⦋0⦌)).presheaf.germ _ p hpN s = transfer H hS u ξ p hp) :
    a.app (op ⦋1⦌) ⁻¹' {a.app (op ⦋0⦌) u} ⊆
      (Stacks.Topology.SectionsOnQuasiCompactSubset.germEqOpens (S.component (op ⦋1⦌)).presheaf
        ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op).app (op _) s)
        ((S.transition (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op).app (op _) s) : Set _) := by
  intro w hw
  have hwx : a.app (op ⦋1⦌) w = a.app (op ⦋0⦌) u := hw
  have hv : ∀ i : Fin 2, a.app (op ⦋0⦌) (vertex Y i w) = a.app (op ⦋0⦌) u := fun i =>
    (app_zero_vertex i w).trans hwx
  have m : ∀ i : Fin 2, vertex Y i w ∈ (Opens.map (a.app (op ⦋0⦌))).obj N := fun i => by
    change a.app (op ⦋0⦌) (vertex Y i w) ∈ N
    rw [hv i]
    exact hxN
  obtain ⟨b₀, k₀, k₁, r₀⟩ := transfer_spec H hS u ξ _ (hv 0)
  obtain ⟨b₁, l₀, l₁, r₁⟩ := transfer_spec H hS u ξ _ (hv 1)
  obtain ⟨σ, ha, hb, hc⟩ := H.exists_triangle b₀ b₁ w (k₀.trans l₀.symm) k₁ l₁
  have r := EdgeRel.of_triangle hS σ ha hb hc k₀ k₁ l₁ r₀ r₁
  rw [← hs _ (hv 0) (m 0), ← hs _ (hv 1) (m 1)] at r
  exact ⟨m 0, m 1, (edgeRel_germ_iff s (m 0) (m 1)).1 r⟩

/-- **Descent along a proper hypercovering, on stalks: surjectivity.** Transport a germ at `u`
along the fibre, extend the transported germs to a section near the fibre, and shrink until the
two transports to `Y_1` agree. -/
private theorem surjective_stalkComparison_π_zero (u : Y.obj (op ⦋0⦌)) :
    Function.Surjective (Stacks.Sheaves.PullbackUnit.stalkComparison (a.app (op ⦋0⦌)) (Type u)
      (limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom u) := by
  let G₀ := (S.component (op ⦋0⦌)).presheaf
  let x := a.app (op ⦋0⦌) u
  have := H.t2Space₀
  intro ξ
  obtain ⟨O, hKO, s₁, hs₁⟩ := exists_germ_eq_of_isCompact (S.component (op ⦋0⦌))
    (H.isCompact_fiber₀ x) (fun p _ q _ hpq => t2_separation hpq)
    (fun p => transfer H hS u ξ p.1 p.2) (fun p => by
      obtain ⟨U, hU, ρ, hρ⟩ := transfer_locally H hS u ξ p.1 p.2
      exact ⟨U, hU, ρ, fun q hq => hρ q.1 q.2 hq⟩)
  obtain ⟨N₁, hN₁, hxN₁, hN₁sub⟩ :=
    Stacks.Topology.SectionsOnQuasiCompactSubset.exists_isOpen_preimage_subset_of_isClosedMap
      H.isClosedMap₀ O.isOpen hKO
  let O₁ : Opens (Y.obj (op ⦋0⦌)) := (Opens.map (a.app (op ⦋0⦌))).obj ⟨N₁, hN₁⟩
  let j₁ : O₁ ⟶ O := homOfLE hN₁sub
  let s₂ := G₀.map j₁.op s₁
  have hs₂ : ∀ (p : Y.obj (op ⦋0⦌)) (hp : a.app (op ⦋0⦌) p = x) (hpO : p ∈ O₁),
      G₀.germ O₁ p hpO s₂ = transfer H hS u ξ p hp := fun p hp hpO => by
    rw [G₀.germ_res_apply]
    exact hs₁ ⟨p, hp⟩
  obtain ⟨N₂, hN₂, hxN₂, hN₂sub⟩ :=
    Stacks.Topology.SectionsOnQuasiCompactSubset.exists_isOpen_preimage_subset_of_isClosedMap
      H.isClosedMap₁ (Opens.isOpen _)
        (preimage_subset_germEqOpens_transition H hS u ξ (N := ⟨N₁, hN₁⟩) hxN₁ s₂ hs₂)
  let N : Opens X := ⟨N₁, hN₁⟩ ⊓ ⟨N₂, hN₂⟩
  let j : (Opens.map (a.app (op ⦋0⦌))).obj N ⟶ O₁ :=
    (Opens.map (a.app (op ⦋0⦌))).map (homOfLE inf_le_left)
  let s₃ := G₀.map j.op s₂
  obtain ⟨t, ht⟩ := exists_directImageSection₀_eq Y X a S N s₃ (fun w h₀ h₁ => by
    have hw₂ : a.app (op ⦋1⦌) w ∈ N₂ := by
      rw [← app_zero_vertex 0 w]
      exact h₀.2
    obtain ⟨m₀, m₁, he⟩ := hN₂sub hw₂
    exact (germ_transition_congr S (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op w h₀ m₀
      (G₀.germ_res_apply j _ h₀ s₂)).trans (he.trans (germ_transition_congr S
        (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op w h₁ m₁ (G₀.germ_res_apply j _ h₁ s₂)).symm))
  have hxN : x ∈ N := ⟨hxN₁, hxN₂⟩
  refine ⟨_, (stalkComparison_π_zero_germ u N hxN t).trans ?_⟩
  rw [ht]
  have hu₃ : u ∈ (Opens.map (a.app (op ⦋0⦌))).obj N := hxN
  exact (G₀.germ_res_apply j u hu₃ s₂).trans ((hs₂ u rfl _).trans (transfer_self H hS u ξ))

/-- **Descent along a proper hypercovering, on stalks.** For a cartesian system `S` and a point
`u ∈ Y_0`, the projection of the direct image `a_* S` to `a_{0,*} S_0` induces a bijection from
the stalk of `a_* S` at `a_0(u)` to the stalk of `S_0` at `u`. -/
theorem bijective_stalkComparison_π_zero (u : Y.obj (op ⦋0⦌)) :
    Function.Bijective (Stacks.Sheaves.PullbackUnit.stalkComparison (a.app (op ⦋0⦌)) (Type u)
      (limit.π (pushforwardDiagram Y X a S) ⦋0⦌).hom u) :=
  ⟨injective_stalkComparison_π_zero H hS u, surjective_stalkComparison_π_zero H hS u⟩

end Augmentation

end Stacks.Topology.Simplicial
