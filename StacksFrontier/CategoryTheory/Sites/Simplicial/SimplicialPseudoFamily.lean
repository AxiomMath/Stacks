module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPairEquivalence

/-!
# Pairs with a cocycle isomorphism for a pseudofunctorial family over the simplex category

A family of categories `C_n` indexed by the simplex category, with functors
`f_φ^* : C_m ⥤ C_n` for the simplex maps `φ : m ⟶ n`, a compositor
`f_φ^* f_ψ^* X ≅ f_{ψ ≫ φ}^* X` and a unit `f_𝟙^* X ≅ X` satisfying the cocycle law and the two
unit laws, is the shape shared by the inverse images of sheaves on the components of a simplicial
site and by the pullbacks of sheaves of modules along its transition morphisms of ringed topoi.

For such a family, a *pair* is an object `F` of `C_0` with an isomorphism
`α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` satisfying the cocycle condition
`f_{δ²₁}^* α = f_{δ²₀}^* α ∘ f_{δ²₂}^* α` on `C_2`, and a *cartesian system* is a family of
objects `N_n` with isomorphisms `f_φ^* N_m ≅ N_n` satisfying the unit and cocycle laws. This file
proves, for every such family, two facts about them used in Stacks 0D7I and Stacks 07TH:

* a pair determines a cartesian system, whose object in degree `n` is the pullback of `F` along
  the last vertex of `⦋n⦌`, whose object in degree zero is `F` and whose transitions along the two
  faces of `⦋1⦌` recover `α`;
* a morphism between the degree-zero objects of two cartesian systems which is compatible with
  the comparison isomorphisms in degree one extends to a family of morphisms compatible
  with every transition.

All names are in the namespace `CategoryTheory.SimplicialPseudoFamily`.

## Main definitions

* `CategoryTheory.SimplicialPseudoFamily`: the family, with its compositor, unit and laws.
* `IsCocycle`: the cocycle condition on a pair.
* `edgeTransport`: the comparison between the pullbacks of `F` along two vertices `i ≤ j` of
  `⦋n⦌`, obtained from the pullback of `α` along the edge joining them.
* `CartesianSystem`: a cartesian system.
* `pairSystem`: the cartesian system of a pair.
* `CartesianSystem.homAlong`: the morphism in degree `k` induced by a morphism in degree zero and
  a vertex of `k`.
* `CartesianSystem.homFamily`: the morphism in every degree induced by a morphism in degree zero,
  along the last vertex.

## Main results

* `edgeTransport_comp`, `edgeTransport_self` and `edgeTransport_map`: the edge transports
  compose, are the identity on a degenerate edge, and are compatible with pulling back along a
  simplex map.
* `pairTransition_face_zero` and `pairTransition_face_one`: the transitions of the system of a
  pair along the two faces of `⦋1⦌`.
* `CartesianSystem.homFamily_naturality` and `CartesianSystem.homFamily_zero`: the family induced
  by a compatible morphism in degree zero is compatible with every transition and is that
  morphism in degree zero.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe v u

namespace CategoryTheory

/-- A pseudofunctorial family of categories over the simplex category: categories `C_n`,
functors `f_φ^* : C_m ⥤ C_n` for the simplex maps `φ : m ⟶ n`, a natural compositor
`f_φ^* f_ψ^* X ≅ f_{ψ ≫ φ}^* X` and a natural unit `f_𝟙^* X ≅ X`, satisfying the cocycle law and
the two unit laws of a pseudofunctor. -/
structure SimplicialPseudoFamily where
  /-- The category in simplicial degree `n`. -/
  obj : SimplexCategory → Type u
  /-- The category structure in each degree. -/
  [category : ∀ n, Category.{v} (obj n)]
  /-- The functor `f_φ^*` attached to a simplex map. -/
  map : ∀ {m n : SimplexCategory}, (m ⟶ n) → obj m ⥤ obj n
  /-- The compositor `f_φ^* f_ψ^* X ≅ f_{ψ ≫ φ}^* X`. -/
  paste : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (X : obj l),
    (map φ).obj ((map ψ).obj X) ≅ (map (ψ ≫ φ)).obj X
  /-- The compositor is natural. -/
  paste_naturality : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) {X Y : obj l}
    (f : X ⟶ Y), (map φ).map ((map ψ).map f) ≫ (paste ψ φ Y).hom =
      (paste ψ φ X).hom ≫ (map (ψ ≫ φ)).map f
  /-- The unit `f_𝟙^* X ≅ X`. -/
  unit : ∀ (n : SimplexCategory) (X : obj n), (map (𝟙 n)).obj X ≅ X
  /-- The unit is natural. -/
  unit_naturality : ∀ (n : SimplexCategory) {X Y : obj n} (f : X ⟶ Y),
    (map (𝟙 n)).map f ≫ (unit n Y).hom = (unit n X).hom ≫ f
  /-- The cocycle law for the compositor. -/
  paste_assoc : ∀ {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n) (X : obj k),
    (paste ψ φ ((map χ).obj X)).hom ≫ (paste χ (ψ ≫ φ) X).hom =
      (map φ).map (paste χ ψ X).hom ≫ (paste (χ ≫ ψ) φ X).hom ≫
        eqToHom (congrArg (fun t => (map t).obj X) (Category.assoc χ ψ φ))
  /-- The right unit law: the compositor at `φ ≫ 𝟙` is the unit. -/
  paste_comp_id : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (X : obj m),
    (paste φ (𝟙 n) X).hom ≫ eqToHom (congrArg (fun k => (map k).obj X) (Category.comp_id φ)) =
      (unit n ((map φ).obj X)).hom
  /-- The left unit law: the compositor at `𝟙 ≫ φ` is the pullback of the unit. -/
  paste_id_comp : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (X : obj m),
    (paste (𝟙 m) φ X).hom ≫ eqToHom (congrArg (fun k => (map k).obj X) (Category.id_comp φ)) =
      (map φ).map (unit m X).hom

namespace SimplicialPseudoFamily

attribute [instance] SimplicialPseudoFamily.category

attribute [reassoc] SimplicialPseudoFamily.paste_naturality
  SimplicialPseudoFamily.unit_naturality SimplicialPseudoFamily.paste_assoc

variable (P : SimplicialPseudoFamily.{v, u})

/-! ### The compositor at a factorization -/

/-- The compositor, written at a chosen factorization `ψ ≫ φ = θ` of a simplex map. -/
def pasteOfEq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n) (h : ψ ≫ φ = θ)
    (X : P.obj l) : (P.map φ).obj ((P.map ψ).obj X) ≅ (P.map θ).obj X :=
  P.paste ψ φ X ≪≫ eqToIso (congrArg (fun k => (P.map k).obj X) h)

/-- The compositor at a factorization is natural. -/
theorem pasteOfEq_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (h : ψ ≫ φ = θ) {X Y : P.obj l} (f : X ⟶ Y) :
    (P.map φ).map ((P.map ψ).map f) ≫ (P.pasteOfEq ψ φ θ h Y).hom =
      (P.pasteOfEq ψ φ θ h X).hom ≫ (P.map θ).map f := by
  subst h
  simpa [pasteOfEq] using P.paste_naturality ψ φ f

/-- At the tautological factorization the compositor at a factorization is the compositor. -/
theorem pasteOfEq_rfl {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (X : P.obj l) :
    P.pasteOfEq ψ φ (ψ ≫ φ) rfl X = P.paste ψ φ X := by
  apply Iso.ext
  simp [pasteOfEq]

/-- The transport along an equation between two spellings of one simplex map is the identity. -/
theorem eqToHom_map_self {m n : SimplexCategory} {φ φ' : m ⟶ n} (h : φ = φ') (X : P.obj m)
    (h' : φ = φ') :
    eqToHom (congrArg (fun k => (P.map k).obj X) h) =
      eqToHom (congrArg (fun k => (P.map k).obj X) h') := rfl

/-- The cocycle law for the compositor at factorizations. -/
theorem pasteOfEq_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (χψ : k ⟶ m) (ψφ : l ⟶ n) (χψφ : k ⟶ n) (h₁ : χ ≫ ψ = χψ) (h₂ : ψ ≫ φ = ψφ)
    (h₃ : χψ ≫ φ = χψφ) (h₄ : χ ≫ ψφ = χψφ) (X : P.obj k) :
    (P.map φ).map (P.pasteOfEq χ ψ χψ h₁ X).hom ≫ (P.pasteOfEq χψ φ χψφ h₃ X).hom =
      (P.pasteOfEq ψ φ ψφ h₂ ((P.map χ).obj X)).hom ≫ (P.pasteOfEq χ ψφ χψφ h₄ X).hom := by
  subst h₁ h₂ h₃
  simp only [pasteOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, P.paste_assoc χ ψ φ X]
  simp

/-- The right unit law, for a composite presented as a map equal to the first factor. -/
theorem pasteOfEq_comp_id_eqToHom {m n : SimplexCategory} (φ θ : m ⟶ n) (h : φ ≫ 𝟙 n = θ)
    (hθ : θ = φ) (X : P.obj m) :
    (P.pasteOfEq φ (𝟙 n) θ h X).hom ≫ eqToHom (congrArg (fun k => (P.map k).obj X) hθ) =
      (P.unit n ((P.map φ).obj X)).hom := by
  subst hθ
  have := P.paste_comp_id θ X
  simp only [pasteOfEq, Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans] at this ⊢
  exact this

/-- The left unit law, for a first factor presented as a map equal to the identity and a
composite presented as a map equal to the second factor. -/
theorem pasteOfEq_id_comp_eqToHom {m n : SimplexCategory} (e : m ⟶ m) (he : e = 𝟙 m)
    (φ θ : m ⟶ n) (h : e ≫ φ = θ) (hθ : θ = φ) (X : P.obj m) :
    (P.pasteOfEq e φ θ h X).hom ≫ eqToHom (congrArg (fun k => (P.map k).obj X) hθ) =
      (P.map φ).map (eqToHom (congrArg (fun k => (P.map k).obj X) he) ≫ (P.unit m X).hom) := by
  subst he hθ
  have := P.paste_id_comp θ X
  simp only [pasteOfEq, Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_refl,
    Category.id_comp] at this ⊢
  rw [Category.comp_id]
  exact this

/-! ### The cocycle condition -/

/-- The identification of the pullbacks of an object along two factorizations of one simplex
map. -/
def glueOfEq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n) (v : l ⟶ n)
    (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) (X : P.obj l) :
    (P.map φ).obj ((P.map ψ).obj X) ≅ (P.map φ').obj ((P.map ψ').obj X) :=
  P.pasteOfEq ψ φ v h X ≪≫ (P.pasteOfEq ψ' φ' v h' X).symm

/-- The identification of the two pullbacks of `f_{δ¹₁}^* F` to degree two occurring in the
cocycle condition. -/
def glueLeft (F : P.obj ⦋0⦌) :
    (P.map (SimplexCategory.δ (2 : Fin 3))).obj ((P.map (SimplexCategory.δ (1 : Fin 2))).obj F) ≅
      (P.map (SimplexCategory.δ (1 : Fin 3))).obj
        ((P.map (SimplexCategory.δ (1 : Fin 2))).obj F) :=
  P.glueOfEq _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one F

/-- The identification of `f_{δ²₂}^* f_{δ¹₀}^* F` with `f_{δ²₀}^* f_{δ¹₁}^* F`. -/
def glueMiddle (F : P.obj ⦋0⦌) :
    (P.map (SimplexCategory.δ (2 : Fin 3))).obj ((P.map (SimplexCategory.δ (0 : Fin 2))).obj F) ≅
      (P.map (SimplexCategory.δ (0 : Fin 3))).obj
        ((P.map (SimplexCategory.δ (1 : Fin 2))).obj F) :=
  P.glueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero F

/-- The identification of the two pullbacks of `f_{δ¹₀}^* F` to degree two occurring in the
cocycle condition. -/
def glueRight (F : P.obj ⦋0⦌) :
    (P.map (SimplexCategory.δ (0 : Fin 3))).obj ((P.map (SimplexCategory.δ (0 : Fin 2))).obj F) ≅
      (P.map (SimplexCategory.δ (1 : Fin 3))).obj
        ((P.map (SimplexCategory.δ (0 : Fin 2))).obj F) :=
  P.glueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one F

/-- The cocycle condition `f_{δ²₁}^* α = f_{δ²₀}^* α ∘ f_{δ²₂}^* α` on an isomorphism
`α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F`, the three pullbacks being compared by the compositor. -/
def IsCocycle (F : P.obj ⦋0⦌)
    (α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj F) : Prop :=
  (P.map (SimplexCategory.δ (1 : Fin 3))).map α.hom =
    (P.glueLeft F).inv ≫ (P.map (SimplexCategory.δ (2 : Fin 3))).map α.hom ≫
      (P.glueMiddle F).hom ≫ (P.map (SimplexCategory.δ (0 : Fin 3))).map α.hom ≫
        (P.glueRight F).hom

/-! ### Transport along the edges of a simplex -/

section Transport

variable (F : P.obj ⦋0⦌)
  (α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
    (P.map (SimplexCategory.δ (0 : Fin 2))).obj F)

/-- The comparison between the pullbacks of `F` along the two ends of an edge `φ` of a simplex,
obtained from the pullback of `α` along `φ`. -/
def transportAlong {n : SimplexCategory} (φ : ⦋1⦌ ⟶ n) (v w : ⦋0⦌ ⟶ n)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = v) (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = w) :
    (P.map v).obj F ≅ (P.map w).obj F :=
  (P.pasteOfEq _ φ v h₁ F).symm ≪≫ (P.map φ).mapIso α ≪≫ P.pasteOfEq _ φ w h₀ F

/-- The comparison between the pullbacks of `F` along two vertices `i ≤ j` of `⦋n⦌`, obtained
from the pullback of `α` along the edge joining them. -/
def edgeTransport {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (P.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).obj F ≅
      (P.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)).obj F :=
  P.transportAlong F α (SimplexCategory.mkOfLe i j h) _ _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h)
    (SimplexCategory.delta_zero_comp_mkOfLe n i j h)

/-- Edge transport, written out. -/
theorem edgeTransport_hom {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (P.edgeTransport F α i j h).hom =
      (P.pasteOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe n i j h) F).inv ≫
        (P.map (SimplexCategory.mkOfLe i j h)).map α.hom ≫
        (P.pasteOfEq (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe n i j h) F).hom := rfl

/-- Edge transport read along any presentation of the edge as a simplex map. -/
theorem edgeTransport_eq_transportAlong {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j)
    (φ : ⦋1⦌ ⟶ ⦋n⦌) (hφ : SimplexCategory.mkOfLe i j h = φ)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ φ = SimplexCategory.const ⦋0⦌ ⦋n⦌ i)
    (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ φ = SimplexCategory.const ⦋0⦌ ⦋n⦌ j) :
    P.edgeTransport F α i j h = P.transportAlong F α φ _ _ h₁ h₀ := by
  subst hφ
  rfl

end Transport

/-- The identification of the pullback of `F` along a vertex of `⦋m⦌`, pulled back along a
simplex map, with the pullback along the image vertex. -/
def vertexPaste {m n : SimplexCategory} (φ : m ⟶ n) (i : Fin (m.len + 1)) (F : P.obj ⦋0⦌) :
    (P.map φ).obj ((P.map (SimplexCategory.const ⦋0⦌ ⦋m.len⦌ i)).obj F) ≅
      (P.map (SimplexCategory.const ⦋0⦌ ⦋n.len⦌ (φ.toOrderHom i))).obj F :=
  P.pasteOfEq _ φ _ (SimplexCategory.vertexMap_comp φ i) F

/-- The vertex identifications are compatible with composition of simplex maps. -/
theorem vertexPaste_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (i : Fin (l.len + 1)) (F : P.obj ⦋0⦌) :
    (P.map φ).map (P.vertexPaste ψ i F).hom ≫ (P.vertexPaste φ (ψ.toOrderHom i) F).hom =
      (P.paste ψ φ ((P.map (SimplexCategory.const ⦋0⦌ ⦋l.len⦌ i)).obj F)).hom ≫
        (P.vertexPaste (ψ ≫ φ) i F).hom := by
  have h := P.pasteOfEq_assoc (SimplexCategory.const ⦋0⦌ ⦋l.len⦌ i) ψ φ _ (ψ ≫ φ) _
    (SimplexCategory.vertexMap_comp ψ i) rfl
    (SimplexCategory.vertexMap_comp φ (ψ.toOrderHom i))
    (SimplexCategory.vertexMap_comp (ψ ≫ φ) i) F
  rw [P.pasteOfEq_rfl ψ φ] at h
  exact h

section Transport

variable (F : P.obj ⦋0⦌)
  (α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
    (P.map (SimplexCategory.δ (0 : Fin 2))).obj F)

/-- Pulling back the source identification of an edge of `⦋m⦌` along a simplex map gives the
source identification of the image edge. -/
theorem edgePaste_one_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) :
    (P.map φ).map (P.pasteOfEq (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe m.len i j h) F).hom ≫
        (P.vertexPaste φ i F).hom =
      (P.pasteOfEq (SimplexCategory.mkOfLe i j h) φ _ (SimplexCategory.edgeMap_comp φ i j h)
          ((P.map (SimplexCategory.δ (1 : Fin 2))).obj F)).hom ≫
        (P.pasteOfEq (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) _
          (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) F).hom :=
  P.pasteOfEq_assoc (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const ⦋0⦌ ⦋m.len⦌ i)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j) (SimplexCategory.hom_le φ h))
    (SimplexCategory.const ⦋0⦌ ⦋n.len⦌ (φ.toOrderHom i))
    (SimplexCategory.delta_one_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ i)
    (SimplexCategory.delta_one_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) F

/-- Pulling back the target identification of an edge of `⦋m⦌` along a simplex map gives the
target identification of the image edge. -/
theorem edgePaste_zero_comp {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) :
    (P.map φ).map (P.pasteOfEq (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h) F).hom ≫
        (P.vertexPaste φ j F).hom =
      (P.pasteOfEq (SimplexCategory.mkOfLe i j h) φ _ (SimplexCategory.edgeMap_comp φ i j h)
          ((P.map (SimplexCategory.δ (0 : Fin 2))).obj F)).hom ≫
        (P.pasteOfEq (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) _
          (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
            (SimplexCategory.hom_le φ h)) F).hom :=
  P.pasteOfEq_assoc (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) φ
    (SimplexCategory.const ⦋0⦌ ⦋m.len⦌ j)
    (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j) (SimplexCategory.hom_le φ h))
    (SimplexCategory.const ⦋0⦌ ⦋n.len⦌ (φ.toOrderHom j))
    (SimplexCategory.delta_zero_comp_mkOfLe m.len i j h)
    (SimplexCategory.edgeMap_comp φ i j h) (SimplexCategory.vertexMap_comp φ j)
    (SimplexCategory.delta_zero_comp_mkOfLe n.len (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)) F

/-- Composing edge transport with the source identification of the edge leaves the pullback of
`α` along the edge followed by the target identification. -/
theorem pasteOfEq_comp_edgeTransport {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (P.pasteOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_one_comp_mkOfLe n i j h) F).hom ≫
        (P.edgeTransport F α i j h).hom =
      (P.map (SimplexCategory.mkOfLe i j h)).map α.hom ≫
        (P.pasteOfEq (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
          (SimplexCategory.delta_zero_comp_mkOfLe n i j h) F).hom := by
  rw [P.edgeTransport_hom F α i j h, Iso.hom_inv_id_assoc]

/-- Edge transport is compatible with pulling back along a simplex map. -/
theorem edgeTransport_map {m n : SimplexCategory} (φ : m ⟶ n) (i j : Fin (m.len + 1))
    (h : i ≤ j) :
    (P.map φ).map (P.edgeTransport F α i j h).hom ≫ (P.vertexPaste φ j F).hom =
      (P.vertexPaste φ i F).hom ≫
        (P.edgeTransport F α (φ.toOrderHom i) (φ.toOrderHom j)
          (SimplexCategory.hom_le φ h)).hom := by
  refine (cancel_epi ((P.map φ).map
    (P.pasteOfEq (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.mkOfLe i j h) _
      (SimplexCategory.delta_one_comp_mkOfLe m.len i j h) F).hom)).mp ?_
  rw [← Category.assoc, ← Functor.map_comp, P.pasteOfEq_comp_edgeTransport F α i j h,
    Functor.map_comp, Category.assoc, P.edgePaste_zero_comp F φ i j h,
    ← Category.assoc, P.pasteOfEq_naturality (SimplexCategory.mkOfLe i j h) φ _
      (SimplexCategory.edgeMap_comp φ i j h) α.hom, Category.assoc,
    ← Category.assoc ((P.map φ).map _), P.edgePaste_one_comp F φ i j h, Category.assoc,
    P.pasteOfEq_comp_edgeTransport F α (φ.toOrderHom i) (φ.toOrderHom j)
      (SimplexCategory.hom_le φ h)]

/-- The cocycle condition, read as composability of the transports along the three edges of
`⦋2⦌`. -/
theorem edgeTransport_cocycle_two (hα : P.IsCocycle F α) :
    (P.edgeTransport F α (0 : Fin 3) 2 (by decide)).hom =
      (P.edgeTransport F α (0 : Fin 3) 1 (by decide)).hom ≫
        (P.edgeTransport F α (1 : Fin 3) 2 (by decide)).hom := by
  rw [P.edgeTransport_eq_transportAlong (n := 2) F α 0 2 (by decide)
      (SimplexCategory.δ (1 : Fin 3)) (SimplexCategory.edgeMap_two_zero_two_eq _)
      SimplexCategory.delta_one_comp_delta_one SimplexCategory.delta_zero_comp_delta_one,
    P.edgeTransport_eq_transportAlong (n := 2) F α 0 1 (by decide)
      (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.edgeMap_two_zero_one_eq _)
      SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_zero_comp_delta_two,
    P.edgeTransport_eq_transportAlong (n := 2) F α 1 2 (by decide)
      (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.edgeMap_two_one_two_eq _)
      SimplexCategory.delta_one_comp_delta_zero SimplexCategory.delta_zero_comp_delta_zero]
  have hα' : (P.map (SimplexCategory.δ (1 : Fin 3))).map α.hom =
      (P.glueLeft F).inv ≫ (P.map (SimplexCategory.δ (2 : Fin 3))).map α.hom ≫
        (P.glueMiddle F).hom ≫ (P.map (SimplexCategory.δ (0 : Fin 3))).map α.hom ≫
          (P.glueRight F).hom := hα
  simp only [transportAlong, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [hα']
  simp only [glueLeft, glueMiddle, glueRight, glueOfEq, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Edge transports compose. -/
theorem edgeTransport_comp (hα : P.IsCocycle F α) {n : ℕ} (i j k : Fin (n + 1)) (hij : i ≤ j)
    (hjk : j ≤ k) :
    (P.edgeTransport F α i k (hij.trans hjk)).hom =
      (P.edgeTransport F α i j hij).hom ≫ (P.edgeTransport F α j k hjk).hom := by
  have h := congrArg
    (fun t => (P.map (SimplexCategory.mkOfLeComp i j k hij hjk)).map t ≫
      (P.vertexPaste (SimplexCategory.mkOfLeComp i j k hij hjk) 2 F).hom)
    (P.edgeTransport_cocycle_two F α hα)
  simp only [Functor.map_comp, Category.assoc] at h
  rw [P.edgeTransport_map, P.edgeTransport_map, ← Category.assoc, P.edgeTransport_map,
    Category.assoc] at h
  exact (cancel_epi (P.vertexPaste (SimplexCategory.mkOfLeComp i j k hij hjk) 0 F).hom).mp h

/-- Edge transport along a degenerate edge is the identity. -/
theorem edgeTransport_self (hα : P.IsCocycle F α) {n : ℕ} (i : Fin (n + 1)) :
    (P.edgeTransport F α i i le_rfl).hom = 𝟙 _ := by
  refine (cancel_epi (P.edgeTransport F α i i le_rfl).hom).mp ?_
  simpa using (P.edgeTransport_comp F α hα i i i le_rfl le_rfl).symm

end Transport

/-! ### Cartesian systems -/

/-- A cartesian system: an object in every degree, with isomorphisms `f_φ^* N_m ≅ N_n`
satisfying the unit and cocycle laws. -/
structure CartesianSystem where
  /-- The object in degree `n`. -/
  obj : ∀ n : SimplexCategory, P.obj n
  /-- The transition isomorphism `f_φ^* N_m ≅ N_n`. -/
  trans : ∀ {m n : SimplexCategory} (φ : m ⟶ n), (P.map φ).obj (obj m) ≅ obj n
  /-- The unit law. -/
  trans_id : ∀ n : SimplexCategory, (trans (𝟙 n)).hom = (P.unit n (obj n)).hom
  /-- The cocycle law. -/
  trans_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    (P.paste ψ φ (obj l)).hom ≫ (trans (ψ ≫ φ)).hom =
      (P.map φ).map (trans ψ).hom ≫ (trans φ).hom

/-! ### The cartesian system of a pair -/

section PairSystem

variable (F : P.obj ⦋0⦌)
  (α : (P.map (SimplexCategory.δ (1 : Fin 2))).obj F ≅
    (P.map (SimplexCategory.δ (0 : Fin 2))).obj F)
  (hα : P.IsCocycle F α)

/-- The object in degree `n` of the system attached to a pair: the pullback of `F` along the
last vertex of `⦋n⦌`. -/
def pairObj (n : SimplexCategory) : P.obj n :=
  (P.map (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))).obj F

/-- The transition of the system attached to a pair: pull back to the image of the last vertex
and transport along the edge to the last vertex. -/
def pairTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (P.map φ).obj (P.pairObj F m) ≅ P.pairObj F n :=
  P.vertexPaste φ (Fin.last m.len) F ≪≫
    P.edgeTransport F α (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len) (Fin.le_last _)

include hα in
/-- The transitions of the system attached to a pair satisfy the cocycle law. -/
theorem pairTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (P.paste ψ φ (P.pairObj F l)).hom ≫ (P.pairTransition F α (ψ ≫ φ)).hom =
      (P.map φ).map (P.pairTransition F α ψ).hom ≫ (P.pairTransition F α φ).hom := by
  have hL : (P.paste ψ φ (P.pairObj F l)).hom ≫ (P.pairTransition F α (ψ ≫ φ)).hom =
      (P.paste ψ φ ((P.map
            (SimplexCategory.const ⦋0⦌ ⦋l.len⦌ (Fin.last l.len))).obj F)).hom ≫
        (P.vertexPaste (ψ ≫ φ) (Fin.last l.len) F).hom ≫
        (P.edgeTransport F α (φ.toOrderHom (ψ.toOrderHom (Fin.last l.len)))
          (Fin.last n.len) (Fin.le_last _)).hom := rfl
  have hR : (P.map φ).map (P.pairTransition F α ψ).hom ≫ (P.pairTransition F α φ).hom =
      (P.map φ).map
          ((P.vertexPaste ψ (Fin.last l.len) F).hom ≫
            (P.edgeTransport F α (ψ.toOrderHom (Fin.last l.len)) (Fin.last m.len)
              (Fin.le_last _)).hom) ≫
        (P.vertexPaste φ (Fin.last m.len) F).hom ≫
        (P.edgeTransport F α (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
          (Fin.le_last _)).hom := rfl
  rw [hL, hR, Functor.map_comp, Category.assoc,
    reassoc_of% (P.edgeTransport_map F α φ (ψ.toOrderHom (Fin.last l.len))
      (Fin.last m.len) (Fin.le_last _)),
    ← P.edgeTransport_comp F α hα, ← Category.assoc, P.vertexPaste_comp ψ φ]
  exact (Category.assoc _ _ _).symm

include hα in
/-- The transition of the system attached to a pair at an identity simplex map is the unit. -/
theorem pairTransition_id (n : SimplexCategory) :
    (P.pairTransition F α (𝟙 n)).hom = (P.unit n (P.pairObj F n)).hom := by
  have h : (P.pairTransition F α (𝟙 n)).hom =
      (P.pasteOfEq (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)) (𝟙 n)
          (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)) (Category.comp_id _) F).hom ≫
        (P.edgeTransport F α (Fin.last n.len) (Fin.last n.len) le_rfl).hom := rfl
  rw [h, P.edgeTransport_self F α hα, Category.comp_id]
  have := P.pasteOfEq_comp_id_eqToHom _ _
    (Category.comp_id (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))) rfl F
  rwa [eqToHom_refl, Category.comp_id] at this

include hα in
/-- **The cartesian system of a pair.** -/
def pairSystem : P.CartesianSystem where
  obj := P.pairObj F
  trans φ := P.pairTransition F α φ
  trans_id := P.pairTransition_id F α hα
  trans_comp ψ φ := P.pairTransition_comp F α hα ψ φ

/-- The object of the system of a pair in degree zero is the given object. -/
def pairZeroIso : P.pairObj F ⦋0⦌ ≅ F :=
  eqToIso (congrArg (fun k => (P.map k).obj F) SimplexCategory.vertexMap_zero_zero) ≪≫
    P.unit ⦋0⦌ F

/-- The pullback of `F` along the vertex `0` of `⦋1⦌` is its pullback along `δ¹₁`. -/
def vertexFaceIsoOne :
    (P.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)).obj F ≅
      (P.map (SimplexCategory.δ (1 : Fin 2))).obj F :=
  eqToIso (congrArg (fun k => (P.map k).obj F) SimplexCategory.vertexMap_one_zero)

/-- The pullback of `F` along the last vertex of `⦋1⦌` is its pullback along `δ¹₀`. -/
def vertexFaceIsoZero :
    (P.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)).obj F ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj F :=
  eqToIso (congrArg (fun k => (P.map k).obj F) SimplexCategory.vertexMap_one_one)

/-- Transport along a simplex map equal to the identity of `⦋1⦌`, read between the pullbacks of
`F` along the two faces, is `α`. -/
theorem transportAlong_eq_iso (e : ⦋1⦌ ⟶ ⦋1⦌) (he : e = 𝟙 ⦋1⦌) (v w : ⦋0⦌ ⟶ ⦋1⦌)
    (h₁ : SimplexCategory.δ (1 : Fin 2) ≫ e = v) (h₀ : SimplexCategory.δ (0 : Fin 2) ≫ e = w)
    (hv : v = SimplexCategory.δ (1 : Fin 2)) (hw : w = SimplexCategory.δ (0 : Fin 2)) :
    (P.transportAlong F α e v w h₁ h₀).hom ≫
        eqToHom (congrArg (fun k => (P.map k).obj F) hw) =
      eqToHom (congrArg (fun k => (P.map k).obj F) hv) ≫ α.hom := by
  subst he hv hw
  have key : (P.transportAlong F α (𝟙 ⦋1⦌) _ _ h₁ h₀).hom = α.hom := by
    have e₁ := P.pasteOfEq_comp_id_eqToHom (SimplexCategory.δ (1 : Fin 2)) _ h₁ rfl F
    have e₀ := P.pasteOfEq_comp_id_eqToHom (SimplexCategory.δ (0 : Fin 2)) _ h₀ rfl F
    simp only [eqToHom_refl, Category.comp_id] at e₁ e₀
    simp only [transportAlong, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, e₀,
      Iso.inv_comp_eq, e₁]
    exact P.unit_naturality ⦋1⦌ α.hom
  exact (Category.comp_id _).trans (key.trans (Category.id_comp _).symm)

/-- The edge transport across the whole of `⦋1⦌` is `α`. -/
theorem edgeTransport_one :
    (P.edgeTransport F α (0 : Fin 2) 1 (by decide)).hom ≫ (P.vertexFaceIsoZero F).hom =
      (P.vertexFaceIsoOne F).hom ≫ α.hom := by
  rw [P.edgeTransport_eq_transportAlong (n := 1) F α 0 1 (by decide) (𝟙 ⦋1⦌)
      (SimplexCategory.edgeMap_one_zero_one _)
      ((Category.comp_id _).trans SimplexCategory.vertexMap_one_zero.symm)
      ((Category.comp_id _).trans SimplexCategory.vertexMap_one_one.symm)]
  exact P.transportAlong_eq_iso F α (𝟙 ⦋1⦌) rfl _ _ _ _
    SimplexCategory.vertexMap_one_zero SimplexCategory.vertexMap_one_one

/-- The compositor at the factorization of the vertex `0` of `⦋1⦌` through `δ¹₁`, followed by
the identification of that vertex with `δ¹₁`, is the pullback of the degree-zero
identification. -/
theorem vertexPaste_comp_vertexFaceIsoOne :
    (P.pasteOfEq (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) SimplexCategory.vertexMap_zero_comp_delta_one F).hom ≫
        (P.vertexFaceIsoOne F).hom =
      (P.map (SimplexCategory.δ (1 : Fin 2))).map (P.pairZeroIso F).hom :=
  P.pasteOfEq_id_comp_eqToHom _ SimplexCategory.vertexMap_zero_zero _ _ _
    SimplexCategory.vertexMap_one_zero F

/-- The compositor at the factorization of the last vertex of `⦋1⦌` through `δ¹₀`, followed by
the identification of that vertex with `δ¹₀`, is the pullback of the degree-zero
identification. -/
theorem vertexPaste_comp_vertexFaceIsoZero :
    (P.pasteOfEq (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) SimplexCategory.vertexMap_zero_comp_delta_zero F).hom ≫
        (P.vertexFaceIsoZero F).hom =
      (P.map (SimplexCategory.δ (0 : Fin 2))).map (P.pairZeroIso F).hom :=
  P.pasteOfEq_id_comp_eqToHom _ SimplexCategory.vertexMap_zero_zero _ _ _
    SimplexCategory.vertexMap_one_one F

include hα in
/-- The transition of the system of a pair along `δ¹₀` is the pullback of the degree-zero
identification. -/
theorem pairTransition_face_zero :
    (P.pairTransition F α (SimplexCategory.δ (0 : Fin 2))).hom ≫ (P.vertexFaceIsoZero F).hom =
      (P.map (SimplexCategory.δ (0 : Fin 2))).map (P.pairZeroIso F).hom := by
  have h : (P.pairTransition F α (SimplexCategory.δ (0 : Fin 2))).hom =
      (P.pasteOfEq (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
          SimplexCategory.vertexMap_zero_comp_delta_zero F).hom ≫
        (P.edgeTransport F α (1 : Fin 2) 1 le_rfl).hom := rfl
  rw [h, P.edgeTransport_self F α hα, Category.comp_id]
  exact P.vertexPaste_comp_vertexFaceIsoZero F

/-- The transition of the system of a pair along `δ¹₁` is the pullback of the degree-zero
identification followed by `α`. -/
theorem pairTransition_face_one :
    (P.pairTransition F α (SimplexCategory.δ (1 : Fin 2))).hom ≫ (P.vertexFaceIsoZero F).hom =
      (P.map (SimplexCategory.δ (1 : Fin 2))).map (P.pairZeroIso F).hom ≫ α.hom := by
  have h : (P.pairTransition F α (SimplexCategory.δ (1 : Fin 2))).hom =
      (P.pasteOfEq (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)
          SimplexCategory.vertexMap_zero_comp_delta_one F).hom ≫
        (P.edgeTransport F α (0 : Fin 2) 1 (by decide)).hom := rfl
  rw [h]
  exact ((Category.assoc _ _ _).trans (_ ≫= P.edgeTransport_one F α)).trans
    ((Category.assoc _ _ _).symm.trans (P.vertexPaste_comp_vertexFaceIsoOne F =≫ α.hom))

/-- The object in degree one of the system of a pair is the pullback of `F` along `δ¹₀`. -/
def pairOneIso : P.pairObj F ⦋0 + 1⦌ ≅ (P.map (SimplexCategory.δ (0 : Fin 2))).obj F :=
  P.vertexFaceIsoZero F

include hα in
/-- The transition of the system of a pair along `δ¹₀`, followed by the identification in degree
one, is the pullback of the identification in degree zero. -/
theorem pairTransition_face_zero' :
    (P.pairTransition F α (SimplexCategory.δ (0 : Fin 2))).hom ≫ (P.pairOneIso F).hom =
      (P.map (SimplexCategory.δ (0 : Fin 2))).map (P.pairZeroIso F).hom :=
  P.pairTransition_face_zero F α hα

/-- The transition of the system of a pair along `δ¹₁`, followed by the identification in degree
one, is the pullback of the identification in degree zero followed by `α`. -/
theorem pairTransition_face_one' :
    (P.pairTransition F α (SimplexCategory.δ (1 : Fin 2))).hom ≫ (P.pairOneIso F).hom =
      (P.map (SimplexCategory.δ (1 : Fin 2))).map (P.pairZeroIso F).hom ≫ α.hom :=
  P.pairTransition_face_one F α

/-- A cartesian system whose objects are identified, compatibly with the transitions, with those
of the system of a pair has that pair as its pair: the identification in degree zero, followed
by the identification of the object of the system of the pair in degree zero, intertwines the
comparison `f_{δ¹₁}^* N_0 ≅ N_1 ≅ f_{δ¹₀}^* N_0` of the system with `α`. -/
theorem comm_of_iso_pairSystem (hα : P.IsCocycle F α) (N : P.CartesianSystem)
    (e : ∀ n, N.obj n ≅ P.pairObj F n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (N.trans φ).hom ≫ (e n).hom = (P.map φ).map (e m).hom ≫ (P.pairTransition F α φ).hom) :
    (P.map (SimplexCategory.δ (1 : Fin 2))).map ((e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom) ≫ α.hom =
      ((N.trans (SimplexCategory.δ (1 : Fin 2))).hom ≫
        (N.trans (SimplexCategory.δ (0 : Fin 2))).inv) ≫
        (P.map (SimplexCategory.δ (0 : Fin 2))).map ((e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom) := by
  have l : (P.map (SimplexCategory.δ (1 : Fin 2))).map ((e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom) ≫
      α.hom = (N.trans (SimplexCategory.δ (1 : Fin 2))).hom ≫ (e ⦋0 + 1⦌).hom ≫
        (P.vertexFaceIsoZero F).hom :=
    ((Functor.map_comp _ _ _) =≫ _).trans ((Category.assoc _ _ _).trans
      ((_ ≫= (P.pairTransition_face_one F α).symm).trans ((Category.assoc _ _ _).symm.trans
        (((he (SimplexCategory.δ (1 : Fin 2))).symm =≫ _).trans (Category.assoc _ _ _)))))
  have r : (P.map (SimplexCategory.δ (0 : Fin 2))).map ((e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom) =
      (N.trans (SimplexCategory.δ (0 : Fin 2))).hom ≫ (e ⦋0 + 1⦌).hom ≫
        (P.vertexFaceIsoZero F).hom :=
    (Functor.map_comp _ _ _).trans ((_ ≫= (P.pairTransition_face_zero F α hα).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (((he (SimplexCategory.δ (0 : Fin 2))).symm =≫ _).trans (Category.assoc _ _ _))))
  rw [l, r, Category.assoc, Iso.inv_hom_id_assoc]

/-- `comm_of_iso_pairSystem`, with the objects and transitions of the system of the pair read
through `pairSystem`. -/
theorem comm_of_iso_pairSystem' (hα : P.IsCocycle F α) (N : P.CartesianSystem)
    (e : ∀ n, N.obj n ≅ (P.pairSystem F α hα).obj n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (N.trans φ).hom ≫ (e n).hom = (P.map φ).map (e m).hom ≫ ((P.pairSystem F α hα).trans φ).hom) :
    (P.map (SimplexCategory.δ (1 : Fin 2))).map ((e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom) ≫ α.hom =
      ((N.trans (SimplexCategory.δ (1 : Fin 2))).hom ≫
        (N.trans (SimplexCategory.δ (0 : Fin 2))).inv) ≫
        (P.map (SimplexCategory.δ (0 : Fin 2))).map ((e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom) :=
  P.comm_of_iso_pairSystem F α hα N e he

/-- `comm_of_iso_pairSystem`, for an isomorphism `E : N_0 ≅ F` and an isomorphism
`c : f_{δ¹₁}^* N_0 ≅ f_{δ¹₀}^* N_0` given by the identification in degree zero and the comparison
of the two transitions of `N` to degree one. -/
theorem comm_of_iso_pairSystem_of_eq (hα : P.IsCocycle F α) (N : P.CartesianSystem)
    (e : ∀ n, N.obj n ≅ (P.pairSystem F α hα).obj n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (N.trans φ).hom ≫ (e n).hom = (P.map φ).map (e m).hom ≫ ((P.pairSystem F α hα).trans φ).hom)
    (E : N.obj ⦋0⦌ ≅ F) (hE : E.hom = (e ⦋0⦌).hom ≫ (P.pairZeroIso F).hom)
    (c : (P.map (SimplexCategory.δ (1 : Fin 2))).obj (N.obj ⦋0⦌) ≅
      (P.map (SimplexCategory.δ (0 : Fin 2))).obj (N.obj ⦋0⦌))
    (hc : c.hom = (N.trans (SimplexCategory.δ (1 : Fin 2))).hom ≫
      (N.trans (SimplexCategory.δ (0 : Fin 2))).inv) :
    (P.map (SimplexCategory.δ (1 : Fin 2))).map E.hom ≫ α.hom =
      c.hom ≫ (P.map (SimplexCategory.δ (0 : Fin 2))).map E.hom := by
  rw [hE, hc]
  exact P.comm_of_iso_pairSystem' F α hα N e he

end PairSystem

/-! ### Extending a morphism in degree zero -/

namespace CartesianSystem

variable {P} (N N' : P.CartesianSystem) (h : N.obj ⦋0⦌ ⟶ N'.obj ⦋0⦌)

/-- The morphism in degree `k` induced by a morphism in degree zero and a vertex `μ` of `k`:
transport to the pullback along `μ`, apply the pullback of the morphism, and transport back. -/
def homAlong {k : SimplexCategory} (μ : ⦋0⦌ ⟶ k) : N.obj k ⟶ N'.obj k :=
  (N.trans μ).inv ≫ (P.map μ).map h ≫ (N'.trans μ).hom

/-- The morphism along a vertex, pulled back along a simplex map and conjugated by the
transitions, is the morphism along the image vertex. -/
theorem homAlong_comp {k n : SimplexCategory} (μ : ⦋0⦌ ⟶ k) (χ : k ⟶ n) (ν : ⦋0⦌ ⟶ n)
    (hν : μ ≫ χ = ν) :
    (P.map χ).map (N.homAlong N' h μ) ≫ (N'.trans χ).hom =
      (N.trans χ).hom ≫ N.homAlong N' h ν := by
  subst hν
  rw [← cancel_epi ((P.map χ).map (N.trans μ).hom)]
  simp only [homAlong, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
    ← N'.trans_comp μ χ, ← reassoc_of% (N.trans_comp μ χ), Iso.hom_inv_id_assoc,
    ← P.paste_naturality_assoc]

/-- The condition on a morphism in degree zero: it is compatible with the comparison
isomorphisms `f_{δ¹₁}^* N_0 ≅ N_1 ≅ f_{δ¹₀}^* N_0` of the two systems. -/
def IsCompatible : Prop :=
  N.homAlong N' h (SimplexCategory.δ (1 : Fin 2)) = N.homAlong N' h (SimplexCategory.δ (0 : Fin 2))

variable {N N' h}

/-- A morphism in degree zero commuting with the comparison isomorphisms
`f_{δ¹₁}^* N_0 ≅ N_1 ≅ f_{δ¹₀}^* N_0` of the two systems is compatible. -/
theorem isCompatible_of_comm
    (hc : (P.map (SimplexCategory.δ (1 : Fin 2))).map h ≫
        (N'.trans (SimplexCategory.δ (1 : Fin 2)) ≪≫
          (N'.trans (SimplexCategory.δ (0 : Fin 2))).symm).hom =
      (N.trans (SimplexCategory.δ (1 : Fin 2)) ≪≫
          (N.trans (SimplexCategory.δ (0 : Fin 2))).symm).hom ≫
        (P.map (SimplexCategory.δ (0 : Fin 2))).map h) :
    IsCompatible N N' h := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at hc
  unfold IsCompatible homAlong
  rw [Iso.inv_comp_eq, ← cancel_mono (N'.trans (SimplexCategory.δ (0 : Fin 2))).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hc

/-- For a compatible morphism, the morphism along a vertex does not depend on the vertex. -/
theorem homAlong_eq (hh : IsCompatible N N' h) {n : ℕ} (μ ν : ⦋0⦌ ⟶ ⦋n⦌) :
    N.homAlong N' h μ = N.homAlong N' h ν := by
  have key : ∀ i j : Fin (n + 1), i ≤ j →
      N.homAlong N' h (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) =
        N.homAlong N' h (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) := by
    intro i j hij
    have h₁ := N.homAlong_comp N' h _ (SimplexCategory.mkOfLe i j hij) _
      (SimplexCategory.delta_one_comp_mkOfLe n i j hij)
    have h₀ := N.homAlong_comp N' h _ (SimplexCategory.mkOfLe i j hij) _
      (SimplexCategory.delta_zero_comp_mkOfLe n i j hij)
    rw [hh] at h₁
    exact (cancel_epi (N.trans (SimplexCategory.mkOfLe i j hij)).hom).mp (h₁.symm.trans h₀)
  obtain ⟨i, rfl⟩ := SimplexCategory.exists_eq_const_of_zero μ
  obtain ⟨j, rfl⟩ := SimplexCategory.exists_eq_const_of_zero ν
  rcases le_total i j with hle | hle
  · exact key _ _ hle
  · exact (key _ _ hle).symm

/-- The family of morphisms induced by a compatible morphism in degree zero: the morphism along
the last vertex in every degree. -/
def homFamily (n : SimplexCategory) : N.obj n ⟶ N'.obj n :=
  N.homAlong N' h (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))

/-- The family induced by a compatible morphism in degree zero is compatible with every
transition. -/
theorem homFamily_naturality (hh : IsCompatible N N' h) {m n : SimplexCategory} (φ : m ⟶ n) :
    (P.map φ).map (homFamily (N := N) (N' := N') (h := h) m) ≫ (N'.trans φ).hom =
      (N.trans φ).hom ≫ homFamily (N := N) (N' := N') (h := h) n := by
  rw [homFamily, N.homAlong_comp N' h _ φ _ rfl, homFamily]
  exact congrArg _ (homAlong_eq hh (n := n.len) _ _)

/-- The family induced by a morphism in degree zero is that morphism in degree zero. -/
theorem homFamily_zero : homFamily (N := N) (N' := N') (h := h) ⦋0⦌ = h := by
  rw [homFamily, show N.homAlong N' h (SimplexCategory.const ⦋0⦌ ⦋0⦌
      (Fin.last (SimplexCategory.len ⦋0⦌))) = N.homAlong N' h (𝟙 ⦋0⦌) from
      congrArg _ SimplexCategory.const_eq_id,
    homAlong, Iso.inv_comp_eq, N'.trans_id, N.trans_id]
  exact P.unit_naturality ⦋0⦌ h

end CartesianSystem

end SimplicialPseudoFamily

end CategoryTheory
