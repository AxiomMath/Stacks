module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.InverseImageCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TransitionCocycle

/-!
# Pairs with a cocycle isomorphism on a simplicial site

Let `S` be a simplicial-site situation. A cartesian sheaf of sets on its total site is
determined by its restriction `ℱ` to the degree-zero component together with the comparison
`α : (f_{δ¹₁})⁻¹ℱ ≅ (f_{δ¹₀})⁻¹ℱ` of the two inverse images of that restriction to the
degree-one component, and the comparisons that occur are exactly those satisfying the cocycle
condition `(f_{δ²₁})⁻¹α = (f_{δ²₀})⁻¹α ∘ (f_{δ²₂})⁻¹α` on the degree-two component.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.pasteIso`: the canonical identification
  `(f_φ)⁻¹(f_ψ)⁻¹ℱ ≅ (f_{ψ ≫ φ})⁻¹ℱ`, the inverse-image compositor of Stacks 09WF.
* `CategoryTheory.SimplicialSiteSituation.CartesianPair`: the category of pairs `(ℱ, α)`.
* `CategoryTheory.SimplicialSiteSituation.edgeTransport`: the comparison between the inverse
  images of `ℱ` along two vertices of a simplex joined by an edge, obtained from `α`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.edgeTransport_comp`: the comparisons attached to the
  edges of a simplex compose.
* `CategoryTheory.SimplicialSiteSituation.edgeTransport_naturality`: the comparisons are natural
  in the pair.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SimplexCategory

/-- A simplex map is monotone on vertices. -/
theorem hom_le {m n : SimplexCategory} (φ : m ⟶ n) {i j : Fin (m.len + 1)} (h : i ≤ j) :
    φ.toOrderHom i ≤ φ.toOrderHom j := φ.toOrderHom.monotone h

/-- The source vertex of the face `δ²₂` of `⦋2⦌` is the vertex `0`. -/
theorem delta_one_comp_delta_two : δ (1 : Fin 2) ≫ δ (2 : Fin 3) = const (mk 0) (mk 2) 0 := by
  apply Hom.ext_zero_left; rfl

/-- The source vertex of the face `δ²₁` of `⦋2⦌` is the vertex `0`. -/
theorem delta_one_comp_delta_one : δ (1 : Fin 2) ≫ δ (1 : Fin 3) = const (mk 0) (mk 2) 0 := by
  apply Hom.ext_zero_left; rfl

/-- The target vertex of the face `δ²₂` of `⦋2⦌` is the vertex `1`. -/
theorem delta_zero_comp_delta_two : δ (0 : Fin 2) ≫ δ (2 : Fin 3) = const (mk 0) (mk 2) 1 := by
  apply Hom.ext_zero_left; rfl

/-- The source vertex of the face `δ²₀` of `⦋2⦌` is the vertex `1`. -/
theorem delta_one_comp_delta_zero : δ (1 : Fin 2) ≫ δ (0 : Fin 3) = const (mk 0) (mk 2) 1 := by
  apply Hom.ext_zero_left; rfl

/-- The target vertex of the face `δ²₀` of `⦋2⦌` is the vertex `2`. -/
theorem delta_zero_comp_delta_zero : δ (0 : Fin 2) ≫ δ (0 : Fin 3) = const (mk 0) (mk 2) 2 := by
  apply Hom.ext_zero_left; rfl

/-- The target vertex of the face `δ²₁` of `⦋2⦌` is the vertex `2`. -/
theorem delta_zero_comp_delta_one : δ (0 : Fin 2) ≫ δ (1 : Fin 3) = const (mk 0) (mk 2) 2 := by
  apply Hom.ext_zero_left; rfl

/-- The first edge of `⦋2⦌` is its face `δ²₂`. -/
theorem edgeMap_two_zero_one_eq (h : (0 : Fin 3) ≤ 1) : mkOfLe 0 1 h = δ (2 : Fin 3) := by
  apply Hom.ext_one_left <;> rfl

/-- The long edge of `⦋2⦌` is its face `δ²₁`. -/
theorem edgeMap_two_zero_two_eq (h : (0 : Fin 3) ≤ 2) : mkOfLe 0 2 h = δ (1 : Fin 3) := by
  apply Hom.ext_one_left <;> rfl

/-- The second edge of `⦋2⦌` is its face `δ²₀`. -/
theorem edgeMap_two_one_two_eq (h : (1 : Fin 3) ≤ 2) : mkOfLe 1 2 h = δ (0 : Fin 3) := by
  apply Hom.ext_one_left <;> rfl

/-- The source of an edge is its vertex `i`. -/
theorem delta_one_comp_mkOfLe (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    δ (1 : Fin 2) ≫ mkOfLe i j h = const (mk 0) (mk n) i := by
  apply Hom.ext_zero_left; rfl

/-- The target of an edge is its vertex `j`. -/
theorem delta_zero_comp_mkOfLe (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    δ (0 : Fin 2) ≫ mkOfLe i j h = const (mk 0) (mk n) j := by
  apply Hom.ext_zero_left; rfl

/-- The face `δ²₂` of a triangle is its first edge. -/
theorem delta_two_comp_mkOfLeComp (n : ℕ) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    δ (2 : Fin 3) ≫ mkOfLeComp i j k hij hjk = mkOfLe i j hij := by
  apply Hom.ext_one_left <;> rfl

/-- The face `δ²₁` of a triangle is its long edge. -/
theorem delta_one_comp_mkOfLeComp (n : ℕ) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    δ (1 : Fin 3) ≫ mkOfLeComp i j k hij hjk = mkOfLe i k (hij.trans hjk) := by
  apply Hom.ext_one_left <;> rfl

/-- The face `δ²₀` of a triangle is its second edge. -/
theorem delta_zero_comp_mkOfLeComp (n : ℕ) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    δ (0 : Fin 3) ≫ mkOfLeComp i j k hij hjk = mkOfLe j k hjk := by
  apply Hom.ext_one_left <;> rfl

/-- The image of an edge under a simplex map is the edge between the images of its vertices. -/
theorem edgeMap_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1)) (h : i ≤ j) :
    mkOfLe i j h ≫ φ =
      mkOfLe (φ.toOrderHom i) (φ.toOrderHom j) (hom_le φ h) := by
  apply Hom.ext_one_left <;> rfl

/-- The image of a vertex under a simplex map is the image vertex. -/
theorem vertexMap_comp {m n : SimplexCategory} (φ : m ⟶ n) (i : Fin (m.len + 1)) :
    const (mk 0) (mk m.len) i ≫ φ = const (mk 0) (mk n.len) (φ.toOrderHom i) := const_comp _ _ _

/-- The only edge of `⦋1⦌` is its identity. -/
theorem edgeMap_one_zero_one (h : (0 : Fin 2) ≤ 1) : mkOfLe 0 1 h = 𝟙 ⦋1⦌ := by
  apply Hom.ext_one_left <;> rfl

/-- The only vertex of `⦋0⦌` is its identity. -/
theorem vertexMap_zero_zero : const (mk 0) (mk 0) 0 = 𝟙 ⦋0⦌ := by
  apply Hom.ext_zero_left; rfl

/-- The target vertex of `δ¹₀` is the last vertex of `⦋1⦌`. -/
theorem vertexMap_one_one : const (mk 0) (mk 1) 1 = δ (0 : Fin 2) := by
  apply Hom.ext_zero_left; rfl

/-- The source vertex of `δ¹₁` is the first vertex of `⦋1⦌`. -/
theorem vertexMap_one_zero : const (mk 0) (mk 1) 0 = δ (1 : Fin 2) := by
  apply Hom.ext_zero_left; rfl

end SimplexCategory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### The inverse-image compositor as an identification of objects -/

/-- The transport of an inverse image along an equality of simplex maps, read on an object. -/
theorem inverseImageCongr_hom_app {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ)
    (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.inverseImageCongr h).hom.app F =
      eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) h) := by
  subst h; simp [inverseImageCongr]

/-- The canonical identification `(f_φ)⁻¹(f_ψ)⁻¹ℱ ≅ (f_{ψ ≫ φ})⁻¹ℱ` given by the inverse-image
compositor of Stacks 09WF. -/
noncomputable def pasteIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology l) (Type u)) :
    (S.transitionMorphism φ).inverseImage.obj
        ((S.transitionMorphism ψ).inverseImage.obj F) ≅
      (S.transitionMorphism (ψ ≫ φ)).inverseImage.obj F :=
  ((canonicalCompositionComparison S ψ φ).app F).symm

/-- The compositor is natural in the sheaf. -/
theorem pasteIso_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    {F G : Sheaf (S.componentTopology l) (Type u)} (f : F ⟶ G) :
    (S.transitionMorphism φ).inverseImage.map
          ((S.transitionMorphism ψ).inverseImage.map f) ≫ (S.pasteIso ψ φ G).hom =
      (S.pasteIso ψ φ F).hom ≫ (S.transitionMorphism (ψ ≫ φ)).inverseImage.map f := by
  simpa [pasteIso] using (canonicalCompositionComparison S ψ φ).inv.naturality f

/-- The cocycle law for the compositor, read on an object. -/
theorem pasteIso_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology k) (Type u)) :
    (S.pasteIso ψ φ ((S.transitionMorphism χ).inverseImage.obj F)).hom ≫
        (S.pasteIso χ (ψ ≫ φ) F).hom =
      (S.transitionMorphism φ).inverseImage.map (S.pasteIso χ ψ F).hom ≫
        (S.pasteIso (χ ≫ ψ) φ F).hom ≫
          eqToHom (congrArg (fun t => (S.transitionMorphism t).inverseImage.obj F)
            (Category.assoc χ ψ φ)) := by
  simpa [pasteIso, inverseImageCongr_hom_app] using
    NatTrans.congr_app (congrArg Iso.hom (canonicalCompositionComparison_assoc S χ ψ φ)) F

/-- The compositor, written at a chosen factorization of a simplex map. -/
noncomputable def pasteIsoOfEq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (h : ψ ≫ φ = θ) (F : Sheaf (S.componentTopology l) (Type u)) :
    (S.transitionMorphism φ).inverseImage.obj
        ((S.transitionMorphism ψ).inverseImage.obj F) ≅
      (S.transitionMorphism θ).inverseImage.obj F :=
  S.pasteIso ψ φ F ≪≫
    eqToIso (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) h)

/-- The compositor at a factorization is natural in the sheaf. -/
theorem pasteIsoOfEq_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (h : ψ ≫ φ = θ) {F G : Sheaf (S.componentTopology l) (Type u)} (f : F ⟶ G) :
    (S.transitionMorphism φ).inverseImage.map
          ((S.transitionMorphism ψ).inverseImage.map f) ≫
        (S.pasteIsoOfEq ψ φ θ h G).hom =
      (S.pasteIsoOfEq ψ φ θ h F).hom ≫ (S.transitionMorphism θ).inverseImage.map f := by
  subst h
  simpa [pasteIsoOfEq] using S.pasteIso_naturality ψ φ f

/-- At the tautological factorization the compositor is the compositor. -/
theorem pasteIsoOfEq_rfl {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology l) (Type u)) :
    S.pasteIsoOfEq ψ φ (ψ ≫ φ) rfl F = S.pasteIso ψ φ F := by
  apply Iso.ext
  simp [pasteIsoOfEq]

/-- The cocycle law for the compositor at factorizations. -/
theorem pasteIsoOfEq_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (χψ : k ⟶ m) (ψφ : l ⟶ n) (χψφ : k ⟶ n) (h₁ : χ ≫ ψ = χψ) (h₂ : ψ ≫ φ = ψφ)
    (h₃ : χψ ≫ φ = χψφ) (h₄ : χ ≫ ψφ = χψφ) (F : Sheaf (S.componentTopology k) (Type u)) :
    (S.transitionMorphism φ).inverseImage.map (S.pasteIsoOfEq χ ψ χψ h₁ F).hom ≫
        (S.pasteIsoOfEq χψ φ χψφ h₃ F).hom =
      (S.pasteIsoOfEq ψ φ ψφ h₂ ((S.transitionMorphism χ).inverseImage.obj F)).hom ≫
        (S.pasteIsoOfEq χ ψφ χψφ h₄ F).hom := by
  subst h₁ h₂ h₃
  simp only [pasteIsoOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, S.pasteIso_assoc χ ψ φ F]
  simp

/-- The right unit law: the compositor at `φ ≫ 𝟙` is the canonical unit comparison. -/
theorem pasteIsoOfEq_comp_id {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.pasteIsoOfEq φ (𝟙 n) φ (Category.comp_id φ) F).hom =
      (canonicalIdentityComparison S n).hom.app
        ((S.transitionMorphism φ).inverseImage.obj F) := by
  simpa [pasteIsoOfEq, pasteIso, inverseImageCongr_hom_app] using
    NatTrans.congr_app (congrArg Iso.hom (canonicalCompositionComparison_comp_id S φ)) F

/-- The left unit law: the compositor at `𝟙 ≫ φ` is the inverse image of the canonical unit
comparison. -/
theorem pasteIsoOfEq_id_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.pasteIsoOfEq (𝟙 m) φ φ (Category.id_comp φ) F).hom =
      (S.transitionMorphism φ).inverseImage.map
        ((canonicalIdentityComparison S m).hom.app F) := by
  simpa [pasteIsoOfEq, pasteIso, inverseImageCongr_hom_app] using
    NatTrans.congr_app (congrArg Iso.hom (canonicalCompositionComparison_id_comp S φ)) F

/-- The right unit law, for a second factor presented as an identity and a composite presented
as the first factor. -/
theorem pasteIsoOfEq_comp_id' {m n : SimplexCategory} (φ θ : m ⟶ n) (h : φ ≫ 𝟙 n = θ)
    (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.pasteIsoOfEq φ (𝟙 n) θ h F).hom =
      (canonicalIdentityComparison S n).hom.app
          ((S.transitionMorphism φ).inverseImage.obj F) ≫
        eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F)
          ((Category.comp_id φ).symm.trans h)) := by
  obtain rfl : φ = θ := (Category.comp_id φ).symm.trans h
  simpa using S.pasteIsoOfEq_comp_id _ F

/-- The left unit law, for a first factor presented as a map equal to the identity and a
composite presented as a map equal to the second factor. -/
theorem pasteIsoOfEq_id_comp' {m n : SimplexCategory} (e : m ⟶ m) (he : e = 𝟙 m) (φ θ : m ⟶ n)
    (hθ : φ = θ) (h : e ≫ φ = θ) (F : Sheaf (S.componentTopology m) (Type u)) :
    (S.pasteIsoOfEq e φ θ h F).hom =
      (S.transitionMorphism φ).inverseImage.map
          (eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) he) ≫
            (canonicalIdentityComparison S m).hom.app F) ≫
        eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj F) hθ) := by
  subst he hθ
  simpa using S.pasteIsoOfEq_id_comp _ F

/-- The identification of the inverse images of a sheaf along two factorizations `ψ ≫ φ` and
`ψ' ≫ φ'` of one simplex map `v`, built from the inverse-image compositor at each. -/
noncomputable def glueOfEq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (F : Sheaf (S.componentTopology l) (Type u)) :
    (S.transitionMorphism φ).inverseImage.obj
        ((S.transitionMorphism ψ).inverseImage.obj F) ≅
      (S.transitionMorphism φ').inverseImage.obj
        ((S.transitionMorphism ψ').inverseImage.obj F) :=
  S.pasteIsoOfEq ψ φ v h F ≪≫ (S.pasteIsoOfEq ψ' φ' v h' F).symm

/-- The identification of two factorizations, written out. -/
theorem glueOfEq_hom {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (F : Sheaf (S.componentTopology l) (Type u)) :
    (S.glueOfEq ψ ψ' φ φ' v h h' F).hom =
      (S.pasteIsoOfEq ψ φ v h F).hom ≫ (S.pasteIsoOfEq ψ' φ' v h' F).inv := rfl

/-- The inverse of the identification of two factorizations, written out. -/
theorem glueOfEq_inv {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (F : Sheaf (S.componentTopology l) (Type u)) :
    (S.glueOfEq ψ ψ' φ φ' v h h' F).inv =
      (S.pasteIsoOfEq ψ' φ' v h' F).hom ≫ (S.pasteIsoOfEq ψ φ v h F).inv := rfl

/-! ### The canonical transitions of a sheaf on the total site -/

/-- The compositor carries the composite of two canonical transitions of a total-site sheaf to
the canonical transition of the composite simplex map. -/
theorem pasteIso_comp_fiberTransition (F : Sheaf S.totalTopology (Type u))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.pasteIso ψ φ ((S.restrict l).obj F)).hom ≫ (S.fiberTransition (ψ ≫ φ)).app F =
      (S.transitionMorphism φ).inverseImage.map ((S.fiberTransition ψ).app F) ≫
        (S.fiberTransition φ).app F := by
  rw [fiberTransition_comp S ψ φ F]
  simp [pasteIso]

/-- The canonical transitions are compatible with transport along an equality of simplex
maps. -/
theorem eqToHom_comp_fiberTransition (F : Sheaf S.totalTopology (Type u))
    {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    eqToHom (congrArg (fun k => (S.transitionMorphism k).inverseImage.obj
          ((S.restrict m).obj F)) h) ≫ (S.fiberTransition ψ).app F =
      (S.fiberTransition φ).app F := by
  subst h; simp

/-- The compositor at a factorization carries the composite of two canonical transitions to the
canonical transition of the factored map. -/
theorem pasteIsoOfEq_comp_fiberTransition (F : Sheaf S.totalTopology (Type u))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n) (h : ψ ≫ φ = θ) :
    (S.pasteIsoOfEq ψ φ θ h ((S.restrict l).obj F)).hom ≫ (S.fiberTransition θ).app F =
      (S.transitionMorphism φ).inverseImage.map ((S.fiberTransition ψ).app F) ≫
        (S.fiberTransition φ).app F := by
  rw [pasteIsoOfEq, Iso.trans_hom, eqToIso.hom, Category.assoc,
    S.eqToHom_comp_fiberTransition F h, S.pasteIso_comp_fiberTransition F ψ φ]

/-- The two composites of canonical transitions attached to two factorizations of one simplex
map agree under the identification `glueOfEq`. -/
theorem glueOfEq_comp_fiberTransition (F : Sheaf S.totalTopology (Type u))
    {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v)
    (h' : ψ' ≫ φ' = v) :
    (S.glueOfEq ψ ψ' φ φ' v h h' ((S.restrict l).obj F)).hom ≫
        ((S.transitionMorphism φ').inverseImage.map ((S.fiberTransition ψ').app F) ≫
          (S.fiberTransition φ').app F) =
      (S.transitionMorphism φ).inverseImage.map ((S.fiberTransition ψ).app F) ≫
        (S.fiberTransition φ).app F := by
  simp only [glueOfEq, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← S.pasteIsoOfEq_comp_fiberTransition F ψ' φ' v h', Iso.inv_hom_id_assoc,
    S.pasteIsoOfEq_comp_fiberTransition F ψ φ v h]

/-! ### The three identifications occurring in the cocycle condition -/

/-- The identification of the two inverse images of `(f_{δ¹₁})⁻¹ℱ` to degree two occurring in
the cocycle condition, along `δ¹₁ ≫ δ²₂ = δ¹₁ ≫ δ²₁`. -/
noncomputable def glueLeft (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism (SimplexCategory.δ (2 : Fin 3))).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F) ≅
      (S.transitionMorphism (SimplexCategory.δ (1 : Fin 3))).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F) :=
  S.glueOfEq _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one F

/-- The identification of `(f_{δ²₂})⁻¹(f_{δ¹₀})⁻¹ℱ` with `(f_{δ²₀})⁻¹(f_{δ¹₁})⁻¹ℱ`, along
`δ¹₀ ≫ δ²₂ = δ¹₁ ≫ δ²₀`. -/
noncomputable def glueMiddle (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism (SimplexCategory.δ (2 : Fin 3))).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F) ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 3))).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F) :=
  S.glueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero F

/-- The identification of the two inverse images of `(f_{δ¹₀})⁻¹ℱ` to degree two occurring in
the cocycle condition, along `δ¹₀ ≫ δ²₀ = δ¹₀ ≫ δ²₁`. -/
noncomputable def glueRight (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism (SimplexCategory.δ (0 : Fin 3))).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F) ≅
      (S.transitionMorphism (SimplexCategory.δ (1 : Fin 3))).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F) :=
  S.glueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one F

/-! ### The category of pairs -/

/-- A pair `(ℱ, α)`: a sheaf of sets on the degree-zero component of a simplicial-site situation
together with an isomorphism `α : (f_{δ¹₁})⁻¹ℱ ≅ (f_{δ¹₀})⁻¹ℱ` of sheaves on the degree-one
component satisfying the cocycle condition `(f_{δ²₁})⁻¹α = (f_{δ²₀})⁻¹α ∘ (f_{δ²₂})⁻¹α` on the
degree-two component. -/
structure CartesianPair (S : SimplicialSiteSituation.{u}) where
  /-- The sheaf of sets on the degree-zero component. -/
  sheaf : Sheaf (S.componentTopology ⦋0⦌) (Type u)
  /-- The comparison isomorphism between the two inverse images to degree one. -/
  iso : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj sheaf ≅
    (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj sheaf
  /-- The cocycle condition on the degree-two component. -/
  cocycle :
    (S.transitionMorphism (SimplexCategory.δ (1 : Fin 3))).inverseImage.map iso.hom =
      (S.glueLeft sheaf).inv ≫
        (S.transitionMorphism (SimplexCategory.δ (2 : Fin 3))).inverseImage.map iso.hom ≫
        (S.glueMiddle sheaf).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 3))).inverseImage.map iso.hom ≫
        (S.glueRight sheaf).hom

namespace CartesianPair

/-- A morphism of pairs is a morphism of the degree-zero sheaves commuting with the comparison
isomorphisms. -/
structure Hom (A B : CartesianPair S) where
  /-- The morphism of the degree-zero sheaves. -/
  map : A.sheaf ⟶ B.sheaf
  /-- Compatibility with the comparison isomorphisms. -/
  comm : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map map ≫
      B.iso.hom =
    A.iso.hom ≫ (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map map

/-- Pairs form a category, with composition that of the morphisms of degree-zero sheaves. -/
instance : Category (CartesianPair S) where
  Hom A B := Hom S A B
  id A := { map := 𝟙 A.sheaf, comm := by simp }
  comp f g :=
    { map := f.map ≫ g.map
      comm := by
        simp only [Functor.map_comp, Category.assoc, g.comm, reassoc_of% f.comm] }

/-- The identity morphism of pairs is the identity of the degree-zero sheaf. -/
@[simp] theorem id_map (A : CartesianPair S) : Hom.map (𝟙 A) = 𝟙 A.sheaf := rfl

/-- Composition of morphisms of pairs composes the morphisms of degree-zero sheaves. -/
@[simp] theorem comp_map {A B C : CartesianPair S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).map = f.map ≫ g.map := rfl

/-- A morphism of pairs is determined by its morphism of degree-zero sheaves. -/
theorem hom_ext {A B : CartesianPair S} {f g : A ⟶ B} (h : f.map = g.map) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  subst h
  rfl

/-- An isomorphism of degree-zero sheaves compatible with the comparison isomorphisms is an
isomorphism of pairs. -/
def isoMk {A B : CartesianPair S} (e : A.sheaf ≅ B.sheaf)
    (h : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map e.hom ≫
        B.iso.hom =
      A.iso.hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map e.hom) :
    A ≅ B where
  hom := ⟨e.hom, h⟩
  inv :=
    ⟨e.inv, by
      rw [← cancel_epi
          ((S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map e.hom),
        reassoc_of% h]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, e.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩
  hom_inv_id := hom_ext S (by simp)
  inv_hom_id := hom_ext S (by simp)

end CartesianPair

/-! ### Transport along the edges of a simplex -/

/-- The comparison between the inverse images of `ℱ` along the two ends of an edge `φ` of a
simplex, obtained from the inverse image of `α` along `φ`. -/
noncomputable def transportAlongIso (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (S.transitionMorphism v).inverseImage.obj F ≅
      (S.transitionMorphism w).inverseImage.obj F :=
  (S.pasteIsoOfEq _ φ v h₁ F).symm ≪≫
    (S.transitionMorphism φ).inverseImage.mapIso α ≪≫ S.pasteIsoOfEq _ φ w h₀ F

/-- Transport along an edge, as a morphism. -/
noncomputable def transportAlong (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (S.transitionMorphism v).inverseImage.obj F ⟶
      (S.transitionMorphism w).inverseImage.obj F :=
  (S.transportAlongIso F α φ v w h₁ h₀).hom

/-- Transport along an edge is invertible. -/
instance transportAlong_isIso (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    IsIso (S.transportAlong F α φ v w h₁ h₀) :=
  inferInstanceAs (IsIso (S.transportAlongIso F α φ v w h₁ h₀).hom)

/-- The comparison between the inverse images of `ℱ` along two vertices `i ≤ j` of `⦋n⦌`,
obtained from the inverse image of `α` along the edge joining them. -/
noncomputable def edgeTransportIso (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n) i)).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n) j)).inverseImage.obj F :=
  S.transportAlongIso F α (SimplexCategory.mkOfLe i j h) _ _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h)
    (SimplexCategory.delta_zero_comp_mkOfLe n i j h)

/-- Transport along an edge of `⦋n⦌`, as a morphism. -/
noncomputable def edgeTransport (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n) i)).inverseImage.obj F ⟶
      (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n) j)).inverseImage.obj F :=
  (S.edgeTransportIso F α i j h).hom

/-- Transport along an edge of `⦋n⦌` is invertible. -/
instance edgeTransport_isIso (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : IsIso (S.edgeTransport F α i j h) :=
  inferInstanceAs (IsIso (S.edgeTransportIso F α i j h).hom)

/-- Transport along an edge, written out. -/
theorem transportAlong_eq (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    S.transportAlong F α φ v w h₁ h₀ =
      (S.pasteIsoOfEq _ φ v h₁ F).inv ≫ (S.transitionMorphism φ).inverseImage.map α.hom ≫
        (S.pasteIsoOfEq _ φ w h₀ F).hom := rfl

/-- Transport along an edge of `⦋n⦌`, written out. -/
theorem edgeTransport_eq (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    S.edgeTransport F α i j h =
      (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe n i j h) F).inv ≫
        (S.transitionMorphism (SimplexCategory.mkOfLe i j h)).inverseImage.map α.hom ≫
        (S.pasteIsoOfEq (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe n i j h) F).hom := rfl

/-- The identification of the inverse image of `ℱ` along a vertex of `⦋m⦌`, pulled back along a
simplex map, with the inverse image along the image vertex. -/
noncomputable def vertexPaste {m n : SimplexCategory} (φ : m ⟶ n) (i : Fin (m.len + 1))
    (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism φ).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk m.len) i)).inverseImage.obj F) ≅
      (S.transitionMorphism
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len)
          (φ.toOrderHom i))).inverseImage.obj F :=
  S.pasteIsoOfEq _ φ _ (SimplexCategory.vertexMap_comp φ i) F

/-- The vertex identifications are compatible with composition of simplex maps. -/
theorem vertexPaste_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : Fin (l.len + 1)) (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism φ).inverseImage.map (S.vertexPaste ψ i F).hom ≫
        (S.vertexPaste φ (ψ.toOrderHom i) F).hom =
      (S.pasteIso ψ φ
          ((S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk l.len) i)).inverseImage.obj F)).hom ≫
        (S.vertexPaste (ψ ≫ φ) i F).hom := by
  have h := S.pasteIsoOfEq_assoc (SimplexCategory.const (SimplexCategory.mk 0)
    (SimplexCategory.mk l.len) i) ψ φ _
    (ψ ≫ φ) _
    (SimplexCategory.vertexMap_comp ψ i) rfl
    (SimplexCategory.vertexMap_comp φ (ψ.toOrderHom i))
    (SimplexCategory.vertexMap_comp (ψ ≫ φ) i) F
  rwa [S.pasteIsoOfEq_rfl ψ φ] at h

/-- Pulling back the source identification of an edge of `⦋m⦌` along a simplex map gives the
source identification of the image edge. -/
theorem edgePaste_one_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism φ).inverseImage.map
          (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.mkOfLe i j h) _
            (SimplexCategory.delta_one_comp_mkOfLe m.len i j h) F).hom ≫
        (S.vertexPaste φ i F).hom =
      (S.pasteIsoOfEq (SimplexCategory.mkOfLe i j h) φ _
            (SimplexCategory.edgeMap_comp φ i j h)
            ((S.transitionMorphism
              (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F)).hom ≫
        (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) _
          (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) F).hom :=
  S.pasteIsoOfEq_assoc (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) i)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h))
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len) (φ.toOrderHom i))
    (SimplexCategory.delta_one_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ i)
    (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) F

/-- Pulling back the target identification of an edge of `⦋m⦌` along a simplex map gives the
target identification of the image edge. -/
theorem edgePaste_zero_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) (F : Sheaf (S.componentTopology ⦋0⦌) (Type u)) :
    (S.transitionMorphism φ).inverseImage.map
          (S.pasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.mkOfLe i j h) _
            (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h) F).hom ≫
        (S.vertexPaste φ j F).hom =
      (S.pasteIsoOfEq (SimplexCategory.mkOfLe i j h) φ _
            (SimplexCategory.edgeMap_comp φ i j h)
            ((S.transitionMorphism
              (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)).hom ≫
        (S.pasteIsoOfEq (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) _
          (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) F).hom :=
  S.pasteIsoOfEq_assoc (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m.len) j)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h))
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n.len) (φ.toOrderHom j))
    (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ j)
    (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) F

/-- Edge transport preceded by the source identification of the edge is the inverse image of `α`
along the edge followed by the target identification. -/
theorem pasteIsoOfEq_comp_edgeTransport (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe n i j h) F).hom ≫
        S.edgeTransport F α i j h =
      (S.transitionMorphism (SimplexCategory.mkOfLe i j h)).inverseImage.map α.hom ≫
        (S.pasteIsoOfEq (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe n i j h) F).hom := by
  simp [S.edgeTransport_eq F α i j h]

/-- Edge transport is compatible with pulling back along a simplex map. -/
theorem edgeTransport_map {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    (i j : Fin (m.len + 1)) (h : i ≤ j) :
    (S.transitionMorphism φ).inverseImage.map (S.edgeTransport F α i j h) ≫
        (S.vertexPaste φ j F).hom =
      (S.vertexPaste φ i F).hom ≫
        S.edgeTransport F α (φ.toOrderHom i) (φ.toOrderHom j) (SimplexCategory.hom_le φ h) := by
  refine (cancel_epi ((S.transitionMorphism φ).inverseImage.map
    (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
      (SimplexCategory.delta_one_comp_mkOfLe m.len i j h) F).hom)).mp ?_
  rw [← Category.assoc, ← Functor.map_comp, S.pasteIsoOfEq_comp_edgeTransport F α i j h,
    Functor.map_comp, Category.assoc, S.edgePaste_zero_comp φ i j h F, ← Category.assoc,
    S.pasteIsoOfEq_naturality (SimplexCategory.mkOfLe i j h) φ _
      (SimplexCategory.edgeMap_comp φ i j h) α.hom, Category.assoc,
    ← Category.assoc _ (S.vertexPaste φ i F).hom, S.edgePaste_one_comp φ i j h F,
    Category.assoc, S.pasteIsoOfEq_comp_edgeTransport F α (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)]

/-- Edge transport read along any presentation of the edge as a simplex map. -/
theorem edgeTransport_eq_transportAlong (F : Sheaf (S.componentTopology ⦋0⦌) (Type u))
    (α : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj F ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj F)
    {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) (φ : ⦋1⦌ ⟶ ⦋n⦌)
    (hφ : SimplexCategory.mkOfLe i j h = φ)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j) :
    S.edgeTransport F α i j h = S.transportAlong F α φ _ _ h₁ h₀ := by
  subst hφ
  rfl

/-- The cocycle condition of a pair, read as composability of the transports along the three
edges of `⦋2⦌`. -/
theorem edgeTransport_cocycle_two (A : CartesianPair S) :
    S.edgeTransport A.sheaf A.iso (0 : Fin 3) 2 (by decide) =
      S.edgeTransport A.sheaf A.iso (0 : Fin 3) 1 (by decide) ≫
        S.edgeTransport A.sheaf A.iso (1 : Fin 3) 2 (by decide) := by
  rw [S.edgeTransport_eq_transportAlong (n := 2) A.sheaf A.iso 0 2 (by decide)
      (SimplexCategory.δ (1 : Fin 3)) (SimplexCategory.edgeMap_two_zero_two_eq _)
      SimplexCategory.delta_one_comp_delta_one SimplexCategory.delta_zero_comp_delta_one,
    S.edgeTransport_eq_transportAlong (n := 2) A.sheaf A.iso 0 1 (by decide)
      (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.edgeMap_two_zero_one_eq _)
      SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_zero_comp_delta_two,
    S.edgeTransport_eq_transportAlong (n := 2) A.sheaf A.iso 1 2 (by decide)
      (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.edgeMap_two_one_two_eq _)
      SimplexCategory.delta_one_comp_delta_zero SimplexCategory.delta_zero_comp_delta_zero]
  simp only [S.transportAlong_eq]
  rw [A.cocycle]
  simp only [glueLeft, glueMiddle, glueRight, S.glueOfEq_hom, S.glueOfEq_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Edge transports compose. -/
theorem edgeTransport_comp (A : CartesianPair S) {n : ℕ} (i j k : Fin (n + 1)) (hij : i ≤ j)
    (hjk : j ≤ k) :
    S.edgeTransport A.sheaf A.iso i k (hij.trans hjk) =
      S.edgeTransport A.sheaf A.iso i j hij ≫ S.edgeTransport A.sheaf A.iso j k hjk := by
  have h := congrArg
    (fun t => (S.transitionMorphism (SimplexCategory.mkOfLeComp i j k hij hjk)).inverseImage.map
        t ≫ (S.vertexPaste (SimplexCategory.mkOfLeComp i j k hij hjk) 2 A.sheaf).hom)
    (S.edgeTransport_cocycle_two A)
  simp only [Functor.map_comp, Category.assoc] at h
  rw [S.edgeTransport_map, S.edgeTransport_map, ← Category.assoc, S.edgeTransport_map,
    Category.assoc] at h
  exact (cancel_epi
    (S.vertexPaste (SimplexCategory.mkOfLeComp i j k hij hjk) 0 A.sheaf).hom).mp h

/-- Edge transport along a degenerate edge is the identity. -/
theorem edgeTransport_self (A : CartesianPair S) {n : ℕ} (i : Fin (n + 1)) :
    S.edgeTransport A.sheaf A.iso i i le_rfl = 𝟙 _ := by
  refine (cancel_epi (S.edgeTransport A.sheaf A.iso i i le_rfl)).mp ?_
  simpa using (S.edgeTransport_comp A i i i le_rfl le_rfl).symm

/-- Edge transport is natural in the pair. -/
theorem edgeTransport_naturality {A B : CartesianPair S} (f : A ⟶ B) {n : ℕ}
    (i j : Fin (n + 1)) (h : i ≤ j) :
    (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) i)).inverseImage.map f.map ≫
        S.edgeTransport B.sheaf B.iso i j h =
      S.edgeTransport A.sheaf A.iso i j h ≫
        (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) j)).inverseImage.map f.map := by
  have h₁ := S.pasteIsoOfEq_naturality (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.mkOfLe i j h) _ (SimplexCategory.delta_one_comp_mkOfLe n i j h) f.map
  have h₀ := S.pasteIsoOfEq_naturality (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.mkOfLe i j h) _ (SimplexCategory.delta_zero_comp_mkOfLe n i j h) f.map
  refine (cancel_epi (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.mkOfLe i j h) _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h) A.sheaf).hom).mp ?_
  rw [← Category.assoc, ← h₁, Category.assoc,
    S.pasteIsoOfEq_comp_edgeTransport B.sheaf B.iso i j h, ← Category.assoc,
    ← Functor.map_comp, f.comm, Functor.map_comp, Category.assoc, h₀,
    reassoc_of% (S.pasteIsoOfEq_comp_edgeTransport A.sheaf A.iso i j h)]

end CategoryTheory.SimplicialSiteSituation

end
