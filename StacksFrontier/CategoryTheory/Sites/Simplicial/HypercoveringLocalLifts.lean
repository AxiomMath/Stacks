module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyZeroRepresentatives
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSiteDescent

/-!
# Local edges and local triangles of a hypercovering

Let `K` be a hypercovering of the final presheaf of a site `(C, J)` (Stacks 09VU). Condition (2)
says that any two vertices of `K` over an object of `C` are, locally, the two vertices of an edge;
condition (3) in degree two says that any three edges of `K` over an object forming the boundary
of a triangle are, locally, the three faces of a `2`-simplex. This file proves both, as the
properties `HasLocalEdgesTotalSiteDescent` and `HasLocalTrianglesTotalSiteDescent`.

## Main results

* `hasLocalEdges_of_hypercovering_hypercoveringLocalLifts`: any two vertices of a hypercovering
  are locally the two vertices of an edge.
* `hasLocalTriangles_of_hypercovering_hypercoveringLocalLifts`: any boundary of a triangle in a
  hypercovering is locally the boundary of a `2`-simplex.

## References

* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C]

/-! ### Compatible boundaries of a triangle -/

section Boundary

/-- Two faces of the standard `2`-simplex meet in exactly one vertex. -/
theorem eq_of_δ_eq_δ_hypercoveringLocalLifts {j j' : Fin 3} (hjj : j ≠ j') {x y x' y' : Fin 2}
    (h : (SimplexCategory.δ j).toOrderHom x = (SimplexCategory.δ j').toOrderHom y)
    (h' : (SimplexCategory.δ j).toOrderHom x' = (SimplexCategory.δ j').toOrderHom y') :
    x = x' ∧ y = y' := by
  revert j j' x y x' y'
  decide

/-- A morphism `⦋0⦌ ⟶ ⦋1⦌` is one of the two coface maps `δ 0` and `δ 1`. -/
theorem eq_δ_of_zero_hypercoveringLocalLifts (θ : ⦋0⦌ ⟶ ⦋1⦌) :
    θ = SimplexCategory.δ 0 ∨ θ = SimplexCategory.δ 1 := by
  have : ∀ a : Fin 2, θ.toOrderHom 0 = a → θ = SimplexCategory.δ (1 - a) := by
    intro a ha
    ext x
    fin_cases x
    fin_cases a <;> simp_all <;> rfl
  rcases Fin.exists_fin_two.mp ⟨θ.toOrderHom 0, rfl⟩ with h | h
  · exact Or.inr ((this 0 h).trans (by rfl))
  · exact Or.inl ((this 1 h).trans (by rfl))

/-- A constant morphism `Δ ⟶ ⦋1⦌` factors through `⦋0⦌` as the constant map at its value. -/
theorem const_comp_eq_hypercoveringLocalLifts {Δ : SimplexCategory} (θ : Δ ⟶ ⦋1⦌)
    (hθ : ∀ p, θ.toOrderHom p = θ.toOrderHom 0) :
    θ = SimplexCategory.const Δ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋1⦌ (θ.toOrderHom 0) := by
  ext p
  exact congrArg Fin.val (hθ p)

variable {A : Type*} [Category A] (K : SimplicialObject A) {Z : A} (e : Fin 3 → (Z ⟶ K _⦋1⦌))

/-- A family of three edges forms the boundary of a triangle. -/
structure IsTriangleBoundary : Prop where
  v₂ : e 0 ≫ K.δ 0 = e 1 ≫ K.δ 0
  v₁ : e 0 ≫ K.δ 1 = e 2 ≫ K.δ 0
  v₀ : e 1 ≫ K.δ 1 = e 2 ≫ K.δ 1

variable {K e}

/-- The edges of a triangle boundary agree at common vertices: if `θ ≫ δ j = θ' ≫ δ j'` for
vertices `θ`, `θ'` of `⦋1⦌`, then the corresponding vertices of `e j` and `e j'` coincide. -/
theorem IsTriangleBoundary.vertex (he : IsTriangleBoundary K e) (j j' : Fin 3) (θ θ' : ⦋0⦌ ⟶ ⦋1⦌)
    (h : θ ≫ SimplexCategory.δ j = θ' ≫ SimplexCategory.δ j') :
    e j ≫ K.map θ.op = e j' ≫ K.map θ'.op := by
  have h0 := congrArg (fun f => (SimplexCategory.Hom.toOrderHom f) 0) h
  rcases eq_δ_of_zero_hypercoveringLocalLifts θ with rfl | rfl <;>
    rcases eq_δ_of_zero_hypercoveringLocalLifts θ' with rfl | rfl <;>
    fin_cases j <;> fin_cases j' <;> revert h0 <;>
    first
      | (intro; rfl)
      | (intro; exact he.v₂) | (intro; exact he.v₂.symm)
      | (intro; exact he.v₁) | (intro; exact he.v₁.symm)
      | (intro; exact he.v₀) | (intro; exact he.v₀.symm)
      | (intro h0; exact absurd h0 (by decide))

/-- **Faces of a boundary agree on common subsimplices.** -/
theorem IsTriangleBoundary.compat (he : IsTriangleBoundary K e) {Δ : SimplexCategory} (j j' : Fin 3)
    (θ θ' : Δ ⟶ ⦋1⦌) (h : θ ≫ SimplexCategory.δ j = θ' ≫ SimplexCategory.δ j') :
    e j ≫ K.map θ.op = e j' ≫ K.map θ'.op := by
  by_cases hjj : j = j'
  · subst hjj
    rw [cancel_mono] at h
    rw [h]
  have hp : ∀ p, (SimplexCategory.δ j).toOrderHom (θ.toOrderHom p) =
      (SimplexCategory.δ j').toOrderHom (θ'.toOrderHom p) :=
    fun p => congrArg (fun f => (SimplexCategory.Hom.toOrderHom f) p) h
  have hc : ∀ p, θ.toOrderHom p = θ.toOrderHom 0 ∧ θ'.toOrderHom p = θ'.toOrderHom 0 :=
    fun p => eq_of_δ_eq_δ_hypercoveringLocalLifts hjj (hp p) (hp 0)
  rw [const_comp_eq_hypercoveringLocalLifts θ fun p => (hc p).1,
    const_comp_eq_hypercoveringLocalLifts θ' fun p => (hc p).2, op_comp, op_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  congr 1
  refine he.vertex j j' _ _ ?_
  ext x
  fin_cases x
  exact congrArg Fin.val (hp 0)

end Boundary

/-! ### The morphism to the matching object of a boundary -/

section Matching

variable {A : Type*} [Category A] {K : SimplicialObject A} {Z : A} {e : Fin 3 → (Z ⟶ K _⦋1⦌)}

/-- A morphism from a simplex of dimension at most one to the standard `2`-simplex misses a
vertex, so factors through a face. -/
theorem exists_eq_comp_δ_hypercoveringLocalLifts (x : SimplexCategory.Truncated 1)
    (m : x.obj ⟶ ⦋2⦌) :
    ∃ (j : Fin 3) (θ : x.obj ⟶ ⦋1⦌), m = θ ≫ SimplexCategory.δ j :=
  SimplexCategory.eq_comp_δ_of_not_surjective m fun hs => by
    have h := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at h
    have := x.property
    omega

variable (e) in
/-- The leg at `m` of the cone of a boundary: the face through which `m` factors, read along the
factorization. -/
def boundaryLegHypercoveringLocalLifts (x : SimplexCategory.Truncated 1) (m : x.obj ⟶ ⦋2⦌) :
    Z ⟶ K.obj (op x.obj) :=
  e (exists_eq_comp_δ_hypercoveringLocalLifts x m).choose ≫
    K.map (exists_eq_comp_δ_hypercoveringLocalLifts x m).choose_spec.choose.op

/-- The leg at `m` of the cone of a boundary is computed along any factorization
`m = θ ≫ δ j`. -/
theorem IsTriangleBoundary.boundaryLeg_eq (he : IsTriangleBoundary K e)
    (x : SimplexCategory.Truncated 1) (m : x.obj ⟶ ⦋2⦌)
    (j : Fin 3) (θ : x.obj ⟶ ⦋1⦌) (h : m = θ ≫ SimplexCategory.δ j) :
    boundaryLegHypercoveringLocalLifts e x m = e j ≫ K.map θ.op :=
  he.compat _ _ _ _
    ((exists_eq_comp_δ_hypercoveringLocalLifts x m).choose_spec.choose_spec.symm.trans h)

/-- The cone of a boundary over the diagram computing the matching object in degree two. -/
def IsTriangleBoundary.cone (he : IsTriangleBoundary K e) :
    Cone (StructuredArrow.proj (op ⦋2⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplicialObject.truncation 1).obj K) where
  pt := Z
  π :=
    { app := fun f => boundaryLegHypercoveringLocalLifts e f.right.unop f.hom.unop
      naturality := fun f f' φ => by
        have hφ : f'.hom.unop = φ.right.unop.hom ≫ f.hom.unop :=
          congrArg Quiver.Hom.unop (StructuredArrow.w φ).symm
        obtain ⟨j, θ, hθ⟩ := exists_eq_comp_δ_hypercoveringLocalLifts f.right.unop f.hom.unop
        change 𝟙 _ ≫ boundaryLegHypercoveringLocalLifts e f'.right.unop f'.hom.unop =
          boundaryLegHypercoveringLocalLifts e f.right.unop f.hom.unop ≫ K.map φ.right.unop.hom.op
        rw [Category.id_comp, he.boundaryLeg_eq _ _ j θ hθ,
          he.boundaryLeg_eq _ _ j (φ.right.unop.hom ≫ θ) (by rw [hφ, hθ, Category.assoc]),
          op_comp, CategoryTheory.Functor.map_comp, Category.assoc] }

/-- The leg at `m` of the cone of a pair of vertices `a`, `b`: the vertex `m` picks. -/
def pairLegHypercoveringLocalLifts (a b : Z ⟶ K _⦋0⦌) (x : SimplexCategory.Truncated 0)
    (m : x.obj ⟶ ⦋1⦌) :
    Z ⟶ K.obj (op x.obj) :=
  (if m.toOrderHom 0 = 0 then a else b) ≫ K.map (SimplexCategory.const x.obj ⦋0⦌ 0).op

/-- The cone of a pair of vertices over the diagram computing the matching object in degree
one. -/
def pairConeHypercoveringLocalLifts (a b : Z ⟶ K _⦋0⦌) :
    Cone (StructuredArrow.proj (op ⦋1⦌) (SimplexCategory.Truncated.inclusion 0).op ⋙
      (SimplicialObject.truncation 0).obj K) where
  pt := Z
  π :=
    { app := fun f => pairLegHypercoveringLocalLifts a b f.right.unop f.hom.unop
      naturality := fun f f' φ => by
        have hφ : f'.hom.unop = φ.right.unop.hom ≫ f.hom.unop :=
          congrArg Quiver.Hom.unop (StructuredArrow.w φ).symm
        have h0 : ∀ (x : SimplexCategory.Truncated 0) (p : Fin (x.obj.len + 1)), p = 0 :=
          fun x p => Fin.ext (by have := p.isLt; have := x.property; omega)
        change 𝟙 _ ≫ pairLegHypercoveringLocalLifts a b f'.right.unop f'.hom.unop =
          pairLegHypercoveringLocalLifts a b f.right.unop f.hom.unop ≫ K.map φ.right.unop.hom.op
        have hv : f'.hom.unop.toOrderHom 0 = f.hom.unop.toOrderHom 0 := by
          rw [hφ]
          exact congrArg f.hom.unop.toOrderHom (h0 _ _)
        have hc : SimplexCategory.const f'.right.unop.obj ⦋0⦌ 0 =
            φ.right.unop.hom ≫ SimplexCategory.const f.right.unop.obj ⦋0⦌ 0 := by
          ext p
          rfl
        rw [Category.id_comp, pairLegHypercoveringLocalLifts, pairLegHypercoveringLocalLifts,
          hv, hc, op_comp, CategoryTheory.Functor.map_comp,
          Category.assoc] }

/-- The morphism to the matching object in degree two cut out by a boundary. -/
def IsTriangleBoundary.matchingHom [∀ F : (SimplexCategory.Truncated 1)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion 1).op.HasPointwiseRightKanExtension F]
    (he : IsTriangleBoundary K e) :
    Z ⟶ ((SimplicialObject.cosk 1).obj K).obj (op ⦋2⦌) :=
  limit.lift _ he.cone ≫ ((SimplexCategory.Truncated.inclusion 1).op.ranObjObjIsoLimit
    ((SimplicialObject.truncation 1).obj K) (op ⦋2⦌)).inv

/-- A cone over the matching diagram, composed with the face maps of the coskeleton, recovers
its legs. -/
private theorem lift_comp_face_ranCounit (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (c : Cone (StructuredArrow.proj (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op ⋙
      (SimplicialObject.truncation n).obj K)) (i : Fin (n + 2)) :
    (limit.lift _ c ≫ ((SimplexCategory.Truncated.inclusion n).op.ranObjObjIsoLimit
      ((SimplicialObject.truncation n).obj K) (op ⦋n + 1⦌)).inv) ≫
      ((SimplicialObject.cosk n).obj K).map (SimplexCategory.δ i).op ≫
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
        ((SimplicialObject.truncation n).obj K)).app (op ⟨⦋n⦌, le_rfl⟩) =
      c.π.app (StructuredArrow.mk (Y := op (⟨⦋n⦌, le_rfl⟩ : SimplexCategory.Truncated n))
        (show op ⦋n + 1⦌ ⟶ op ⦋n⦌ from (SimplexCategory.δ i).op)) := by
  have key := (SimplexCategory.Truncated.inclusion n).op.ranObjObjIsoLimit_inv_π
    ((SimplicialObject.truncation n).obj K) (op ⦋n + 1⦌)
    (StructuredArrow.mk (Y := op (⟨⦋n⦌, le_rfl⟩ : SimplexCategory.Truncated n))
      (show op ⦋n + 1⦌ ⟶ op ⦋n⦌ from (SimplexCategory.δ i).op))
  refine (Category.assoc _ _ _).trans ((congrArg (limit.lift _ c ≫ ·) key).trans ?_)
  exact limit.lift_π _ _

/-- The faces of the morphism to the matching object of a boundary are the given edges. -/
theorem IsTriangleBoundary.matchingHom_face [∀ F : (SimplexCategory.Truncated 1)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion 1).op.HasPointwiseRightKanExtension F]
    (he : IsTriangleBoundary K e) (i : Fin 3) :
    he.matchingHom ≫ ((SimplicialObject.cosk 1).obj K).map (SimplexCategory.δ i).op ≫
      ((SimplexCategory.Truncated.inclusion 1).op.ranCounit.app
        ((SimplicialObject.truncation 1).obj K)).app (op ⟨⦋1⦌, le_rfl⟩) = e i := by
  refine (lift_comp_face_ranCounit 1 he.cone i).trans ?_
  exact (he.boundaryLeg_eq _ _ i (𝟙 _) (Category.id_comp _).symm).trans
    ((congrArg (e i ≫ ·) (K.map_id _)).trans (Category.comp_id _))

/-- The morphism to the matching object in degree one cut out by a pair of vertices. -/
def pairMatchingHomHypercoveringLocalLifts [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    (a b : Z ⟶ K _⦋0⦌) : Z ⟶ ((SimplicialObject.cosk 0).obj K).obj (op ⦋1⦌) :=
  limit.lift _ (pairConeHypercoveringLocalLifts a b) ≫
    ((SimplexCategory.Truncated.inclusion 0).op.ranObjObjIsoLimit
      ((SimplicialObject.truncation 0).obj K) (op ⦋1⦌)).inv

/-- The two faces of the morphism to the matching object of a pair of vertices. -/
theorem pairMatchingHom_face_hypercoveringLocalLifts [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    (a b : Z ⟶ K _⦋0⦌) (i : Fin 2) :
    pairMatchingHomHypercoveringLocalLifts a b ≫
      ((SimplicialObject.cosk 0).obj K).map (SimplexCategory.δ i).op ≫
      ((SimplexCategory.Truncated.inclusion 0).op.ranCounit.app
        ((SimplicialObject.truncation 0).obj K)).app (op ⟨⦋0⦌, le_rfl⟩) =
      if i = 0 then b else a := by
  refine (lift_comp_face_ranCounit 0 (pairConeHypercoveringLocalLifts a b) i).trans ?_
  change (if (SimplexCategory.δ i).toOrderHom 0 = 0 then a else b) ≫
    K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = _
  have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := by
    ext p
    fin_cases p
    rfl
  rw [hc, op_id, K.map_id, Category.comp_id]
  fin_cases i <;> rfl

/-- The faces of an `(n + 1)`-simplex are read off its image in the matching object. -/
theorem comp_δ_eq_of_unit_hypercoveringLocalLifts (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    {Y : A} (σ : Y ⟶ K _⦋n + 1⦌) (i : Fin (n + 2)) :
    σ ≫ K.δ i = σ ≫ ((SimplicialObject.coskAdj n).unit.app K).app (op ⦋n + 1⦌) ≫
      ((SimplicialObject.cosk n).obj K).map (SimplexCategory.δ i).op ≫
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
        ((SimplicialObject.truncation n).obj K)).app (op ⟨⦋n⦌, le_rfl⟩) := by
  have hnat := ((SimplicialObject.coskAdj n).unit.app K).naturality (SimplexCategory.δ i).op
  have htri :=
    (SimplexCategory.Truncated.inclusion n).op.ranCounit_app_app_ranAdjunction_unit_app_app
      (G := K) (X := op ⟨⦋n⦌, le_rfl⟩)
  have hnat' := congrArg (fun f => σ ≫ f ≫ ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
    ((SimplicialObject.truncation n).obj K)).app (op ⟨⦋n⦌, le_rfl⟩)) hnat
  refine ((Category.comp_id _).symm.trans (congrArg ((σ ≫ K.δ i) ≫ ·) htri.symm)).trans ?_
  refine Eq.trans ?_ (hnat'.trans ?_)
  · simp only [Category.assoc]
    rfl
  · simp only [Category.assoc]

end Matching

/-! ### Local edges and local triangles of a hypercovering -/

section Hypercovering

variable [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u, u} P)

/-- **Condition (2) of a hypercovering**: any two vertices are locally the two vertices of an
edge. -/
theorem hasLocalEdges_of_hypercovering_hypercoveringLocalLifts :
    HasLocalEdgesTotalSiteDescent P.toGrothendieck H.toSimplicialObject := by
  intro V a b
  obtain ⟨S, hS, hSl⟩ := exists_sieve_lift_pair P H V b a
  refine GrothendieckTopology.superset_covering _ ?_ hS
  intro V' g hg
  obtain ⟨ξ, h₀, h₁⟩ := hSl g hg
  exact ⟨ξ, h₁, h₀⟩

/-- **Condition (3) of a hypercovering in degree two**: any boundary of a triangle is locally the
boundary of a `2`-simplex. -/
theorem hasLocalTriangles_of_hypercovering_hypercoveringLocalLifts :
    HasLocalTrianglesTotalSiteDescent P.toGrothendieck H.toSimplicialObject := by
  intro V e₀₁ e₀₂ e₁₂ h₀ h₁ h₂
  let e : Fin 3 → ((FormalCoproduct.incl C).obj V ⟶ H.toSimplicialObject _⦋1⦌) :=
    ![e₁₂, e₀₂, e₀₁]
  have he : IsTriangleBoundary H.toSimplicialObject e := ⟨h₂.symm, h₁.symm, h₀.symm⟩
  let := hasPositiveCoskeleta.{u} (C := C) 1 le_rfl
  let t := (sectionEquiv _ V).symm he.matchingHom
  refine GrothendieckTopology.superset_covering _ ?_
    ((H.locallySurjective_succ 1 le_rfl).imageSieve_mem t)
  rintro V' g ⟨x, hx⟩
  have hσ : sectionEquiv _ V' x ≫
      ((SimplicialObject.coskAdj 1).unit.app H.toSimplicialObject).app (op ⦋2⦌) =
        (FormalCoproduct.incl C).map g ≫ he.matchingHom :=
    (sectionEquiv_map V' _ x).symm.trans ((congrArg (sectionEquiv _ V') hx).trans
      ((sectionEquiv_restrict _ g t).trans
        (congrArg ((FormalCoproduct.incl C).map g ≫ ·) (Equiv.apply_symm_apply _ _))))
  have hf : ∀ i : Fin 3, sectionEquiv _ V' x ≫ H.toSimplicialObject.δ i =
      (FormalCoproduct.incl C).map g ≫ e i := fun i =>
    (comp_δ_eq_of_unit_hypercoveringLocalLifts 1 _ i).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hσ).trans ((Category.assoc _ _ _).trans
        (congrArg ((FormalCoproduct.incl C).map g ≫ ·) (he.matchingHom_face i)))))
  exact ⟨sectionEquiv _ V' x, hf 2, hf 1, hf 0⟩

end Hypercovering

end CategoryTheory.SimplicialSemiRepresentable

end
