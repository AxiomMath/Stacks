module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import StacksFrontier.RingTheory.MvPolynomial.TruncatedChart

/-!
# One-truncated simplicial objects from a reflexive graph

A one-truncated simplicial object in a category `C` is the same thing as a reflexive graph in
`C`: an object of vertices, an object of edges, the two restrictions of an edge to its
vertices, and a degeneracy from vertices to edges which is a section of both restrictions.
This file packages that data and builds the corresponding functor on
`(SimplexCategory.Truncated 1)ᵒᵖ`.

## Main definitions

* `CategoryTheory.SimplicialObject.OneTruncatedData`: the reflexive-graph data.
* `CategoryTheory.SimplicialObject.OneTruncatedData.objOfLen` and
  `CategoryTheory.SimplicialObject.OneTruncatedData.mapOfLen`: the object and morphism
  assignments, indexed by the lengths of the simplices involved.
* `CategoryTheory.SimplicialObject.OneTruncatedData.toTruncated`: the resulting one-truncated
  simplicial object.

## Main results

* `CategoryTheory.SimplicialObject.OneTruncatedData.mapOfLen_id` and
  `CategoryTheory.SimplicialObject.OneTruncatedData.mapOfLen_comp`: functoriality of
  `mapOfLen` in the range of lengths that a one-truncated object sees.
* `CategoryTheory.SimplicialObject.OneTruncatedData.toTruncated_obj_zero`,
  `toTruncated_obj_one`, `toTruncated_map_δ` and `toTruncated_map_σ`: the values of the
  resulting functor on the generating objects and morphisms.

## Implementation notes

The morphism assignment is a function of the *lengths* `m`, `n` of the two simplices and of the
underlying monotone map `Fin (n + 1) →o Fin (m + 1)`, rather than of a morphism of
`SimplexCategory.Truncated 1`. Writing it this way means the case distinction is a structural
match on two natural numbers, so the object assignment reduces definitionally in every branch
and no transport appears in the definition. Functoriality is then a statement about monotone
maps between `Fin 1` and `Fin 2`, which is proved by elementary case analysis. Assembling the
truncated object by case analysis on the morphisms of `(SimplexCategory.Truncated 1)ᵒᵖ`
directly, with a transport along `Δ.len = 0` in the object assignment, produces an elaboration
problem several orders of magnitude more expensive.

The assignments are total on all of `ℕ`, taking junk values outside the range `m, n ≤ 1`; the
functoriality lemmas carry that range as a hypothesis.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

/-- A reflexive graph in `C`: two objects, the two restrictions of an edge to its vertices, and
a common section of those restrictions. This is exactly the data of a one-truncated simplicial
object in `C`. -/
structure OneTruncatedData (C : Type u) [Category.{v} C] where
  /-- The object of vertices, in degree zero. -/
  vertex : C
  /-- The object of edges, in degree one. -/
  edge : C
  /-- The restriction of an edge to each of its two vertices. -/
  restrict : Fin 2 → (edge ⟶ vertex)
  /-- The degeneracy from vertices to edges. -/
  degeneracy : vertex ⟶ edge
  /-- The degeneracy is a section of both restrictions. -/
  degeneracy_comp_restrict (i : Fin 2) : degeneracy ≫ restrict i = 𝟙 vertex

namespace OneTruncatedData

variable {C : Type u} [Category.{v} C] (D : OneTruncatedData C)

/-- The object attached to a simplex of length `n`: the vertices in degree zero and the edges
in every positive degree. -/
@[implicit_reducible]
def objOfLen : ℕ → C
  | 0 => D.vertex
  | _ + 1 => D.edge

/-- In degree zero the object is the object of vertices. -/
@[simp] lemma objOfLen_zero : D.objOfLen 0 = D.vertex := rfl

/-- In every positive degree the object is the object of edges. -/
@[simp] lemma objOfLen_succ (n : ℕ) : D.objOfLen (n + 1) = D.edge := rfl

/-- The morphism attached to a monotone map `Fin (n + 1) →o Fin (m + 1)`, viewed as a simplicial
operator from degree `m` to degree `n`. The value is the identity, a restriction to a vertex,
the degeneracy, or a degenerate edge, according to the two lengths and the two values of the
monotone map. -/
def mapOfLen : (m n : ℕ) → (Fin (n + 1) →o Fin (m + 1)) → (D.objOfLen m ⟶ D.objOfLen n)
  | 0, 0, _ => 𝟙 _
  | 0, _ + 1, _ => D.degeneracy
  | 1, 0, g => D.restrict (g 0)
  | 1, 1, g => if g 0 = g 1 then D.restrict (g 0) ≫ D.degeneracy else 𝟙 _
  | 1, _ + 2, _ => 𝟙 _
  | _ + 2, 0, _ => D.restrict 0
  | _ + 2, _ + 1, _ => 𝟙 _

/-- From degree zero to degree zero `mapOfLen` is the identity. -/
@[simp] lemma mapOfLen_zero_zero (g : Fin 1 →o Fin 1) : D.mapOfLen 0 0 g = 𝟙 D.vertex := rfl

/-- From degree zero to a positive degree `mapOfLen` is the degeneracy. -/
@[simp] lemma mapOfLen_zero_succ (n : ℕ) (g : Fin (n + 2) →o Fin 1) :
    D.mapOfLen 0 (n + 1) g = D.degeneracy := rfl

/-- From degree one to degree zero `mapOfLen` is the restriction to the vertex `g 0`. -/
@[simp] lemma mapOfLen_one_zero (g : Fin 1 →o Fin 2) :
    D.mapOfLen 1 0 g = D.restrict (g 0) := rfl

/-- From degree one to degree one `mapOfLen` is the degenerate edge at `g 0` if `g`
identifies the two points, and the identity otherwise. -/
@[simp] lemma mapOfLen_one_one (g : Fin 2 →o Fin 2) :
    D.mapOfLen 1 1 g = if g 0 = g 1 then D.restrict (g 0) ≫ D.degeneracy else 𝟙 D.edge := rfl

section Fin

/-- If `g` identifies the two points, `mapOfLen 1 1 g` is the degenerate edge at `g 0`. -/
private lemma mapOfLen_one_one_of_eq {g : Fin 2 →o Fin 2} (h : g 0 = g 1) :
    D.mapOfLen 1 1 g = D.restrict (g 0) ≫ D.degeneracy := ite_eq_left h

/-- If `g` separates the two points, `mapOfLen 1 1 g` is the identity. -/
private lemma mapOfLen_one_one_of_ne {g : Fin 2 →o Fin 2} (h : g 0 ≠ g 1) :
    D.mapOfLen 1 1 g = 𝟙 D.edge := ite_eq_right h

/-- The only point of `Fin 1`. -/
private lemma fin_one_cases (i : Fin 1) : i = 0 := Fin.ext (by omega)

/-- The two points of `Fin 2`. -/
private alias fin_two_cases := Stacks.TruncatedChart.eq_zero_or_eq_one

/-- A monotone self-map of `Fin 2` which separates the two points is the identity. -/
private lemma apply_eq_self_of_apply_ne {f : Fin 2 →o Fin 2} (h : f 0 ≠ f 1) (j : Fin 2) :
    f j = j := by
  have hmono : (f 0).val ≤ (f 1).val := f.monotone (by decide)
  have hne : (f 0).val ≠ (f 1).val := fun he => h (Fin.ext he)
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  rcases fin_two_cases j with rfl | rfl
  · exact Fin.ext (by simpa using by omega : (f 0).val = 0)
  · exact Fin.ext (by simpa using by omega : (f 1).val = 1)

/-- A monotone self-map of `Fin 2` which identifies the two points is constant. -/
private lemma apply_eq_of_apply_eq {f : Fin 2 →o Fin 2} (h : f 0 = f 1) (j : Fin 2) :
    f j = f 0 := by
  rcases fin_two_cases j with rfl | rfl
  · rfl
  · exact h.symm

end Fin

/-- `mapOfLen` takes the identity monotone map to the identity morphism. -/
lemma mapOfLen_id (m : ℕ) (hm : m ≤ 1) :
    D.mapOfLen m m (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) = 𝟙 (D.objOfLen m) := by
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · rfl
  · exact D.mapOfLen_one_one_of_ne (by decide)

section Comp

/-- Functoriality of `mapOfLen` from degree zero to degree zero. -/
private lemma mapOfLen_comp_zero_zero_zero (f g : Fin 1 →o Fin 1) :
    D.mapOfLen 0 0 (f.comp g) = D.mapOfLen 0 0 f ≫ D.mapOfLen 0 0 g := by
  change 𝟙 D.vertex = 𝟙 D.vertex ≫ 𝟙 D.vertex
  rw [Category.comp_id]

/-- Functoriality of `mapOfLen` for a degeneracy preceded by an identity. -/
private lemma mapOfLen_comp_zero_zero_one (f : Fin 1 →o Fin 1) (g : Fin 2 →o Fin 1) :
    D.mapOfLen 0 1 (f.comp g) = D.mapOfLen 0 0 f ≫ D.mapOfLen 0 1 g := by
  change D.degeneracy = 𝟙 D.vertex ≫ D.degeneracy
  rw [Category.id_comp]

/-- Functoriality of `mapOfLen` for a restriction following a degeneracy: the first simplicial
identity. -/
private lemma mapOfLen_comp_zero_one_zero (f : Fin 2 →o Fin 1) (g : Fin 1 →o Fin 2) :
    D.mapOfLen 0 0 (f.comp g) = D.mapOfLen 0 1 f ≫ D.mapOfLen 1 0 g := by
  change 𝟙 D.vertex = D.degeneracy ≫ D.restrict (g 0)
  rw [D.degeneracy_comp_restrict]

/-- The degeneracy followed by `mapOfLen 1 1 g` is the degeneracy. -/
private lemma degeneracy_comp_mapOfLen_one_one (g : Fin 2 →o Fin 2) :
    D.degeneracy ≫ D.mapOfLen 1 1 g = D.degeneracy := by
  by_cases h : g 0 = g 1
  · rw [D.mapOfLen_one_one_of_eq h, ← Category.assoc, D.degeneracy_comp_restrict, Category.id_comp]
  · rw [D.mapOfLen_one_one_of_ne h]
    exact Category.comp_id _

/-- Functoriality of `mapOfLen` for an edge following a degeneracy. -/
private lemma mapOfLen_comp_zero_one_one (f : Fin 2 →o Fin 1) (g : Fin 2 →o Fin 2) :
    D.mapOfLen 0 1 (f.comp g) = D.mapOfLen 0 1 f ≫ D.mapOfLen 1 1 g :=
  (D.degeneracy_comp_mapOfLen_one_one g).symm

/-- Functoriality of `mapOfLen` for a restriction followed by an identity. -/
private lemma mapOfLen_comp_one_zero_zero (f : Fin 1 →o Fin 2) (g : Fin 1 →o Fin 1) :
    D.mapOfLen 1 0 (f.comp g) = D.mapOfLen 1 0 f ≫ D.mapOfLen 0 0 g := by
  change D.restrict (f (g 0)) = D.restrict (f 0) ≫ 𝟙 D.vertex
  rw [Category.comp_id, fin_one_cases (g 0)]

/-- Functoriality of `mapOfLen` for a degeneracy following a restriction: the resulting edge is
degenerate at the chosen vertex. -/
private lemma mapOfLen_comp_one_zero_one (f : Fin 1 →o Fin 2) (g : Fin 2 →o Fin 1) :
    D.mapOfLen 1 1 (f.comp g) = D.mapOfLen 1 0 f ≫ D.mapOfLen 0 1 g := by
  change (if f (g 0) = f (g 1) then D.restrict (f (g 0)) ≫ D.degeneracy else 𝟙 D.edge) =
    D.restrict (f 0) ≫ D.degeneracy
  rw [fin_one_cases (g 0), fin_one_cases (g 1), ite_eq_left rfl]

/-- Functoriality of `mapOfLen` for a restriction of an edge: the second simplicial identity in
the degenerate case, and a plain restriction in the other case. -/
private lemma mapOfLen_comp_one_one_zero (f : Fin 2 →o Fin 2) (g : Fin 1 →o Fin 2) :
    D.mapOfLen 1 0 (f.comp g) = D.mapOfLen 1 1 f ≫ D.mapOfLen 1 0 g := by
  by_cases h : f 0 = f 1
  · rw [D.mapOfLen_one_one_of_eq h, D.mapOfLen_one_zero, D.mapOfLen_one_zero, Category.assoc,
      D.degeneracy_comp_restrict, Category.comp_id]
    exact congrArg D.restrict (apply_eq_of_apply_eq h (g 0))
  · rw [D.mapOfLen_one_one_of_ne h]
    erw [Category.id_comp]
    exact congrArg D.restrict (apply_eq_self_of_apply_ne h (g 0))

/-- Functoriality of `mapOfLen` for two composed edges: the composite is degenerate exactly
when one of the two factors is. -/
private lemma mapOfLen_comp_one_one_one (f g : Fin 2 →o Fin 2) :
    D.mapOfLen 1 1 (f.comp g) = D.mapOfLen 1 1 f ≫ D.mapOfLen 1 1 g := by
  by_cases hf : f 0 = f 1
  · rw [D.mapOfLen_one_one_of_eq hf, D.mapOfLen_one_one_of_eq ((apply_eq_of_apply_eq hf (g 0)).trans
      (apply_eq_of_apply_eq hf (g 1)).symm), Category.assoc, D.degeneracy_comp_mapOfLen_one_one]
    exact congrArg (fun x => D.restrict x ≫ D.degeneracy) (apply_eq_of_apply_eq hf (g 0))
  · rw [D.mapOfLen_one_one_of_ne hf]
    erw [Category.id_comp]
    exact congrArg (D.mapOfLen 1 1)
      (OrderHom.ext _ _ (funext fun j => apply_eq_self_of_apply_ne hf (g j)))

/-- `mapOfLen` is compatible with composition, for the lengths a one-truncated object sees. The
composite order homomorphism goes the other way round, since a simplicial operator from degree
`m` to degree `n` is a map of simplices from `⦋n⦌` to `⦋m⦌`. -/
lemma mapOfLen_comp (m n k : ℕ) (hm : m ≤ 1) (hn : n ≤ 1) (hk : k ≤ 1)
    (f : Fin (n + 1) →o Fin (m + 1)) (g : Fin (k + 1) →o Fin (n + 1)) :
    D.mapOfLen m k (f.comp g) = D.mapOfLen m n f ≫ D.mapOfLen n k g := by
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;>
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;>
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact D.mapOfLen_comp_zero_zero_zero f g
  · exact D.mapOfLen_comp_zero_zero_one f g
  · exact D.mapOfLen_comp_zero_one_zero f g
  · exact D.mapOfLen_comp_zero_one_one f g
  · exact D.mapOfLen_comp_one_zero_zero f g
  · exact D.mapOfLen_comp_one_zero_one f g
  · exact D.mapOfLen_comp_one_one_zero f g
  · exact D.mapOfLen_comp_one_one_one f g

end Comp

/-- The one-truncated simplicial object determined by a reflexive graph. -/
@[implicit_reducible]
def toTruncated : SimplicialObject.Truncated C 1 where
  obj X := D.objOfLen (unop X).obj.len
  map f := D.mapOfLen _ _ f.unop.hom.toOrderHom
  map_id X := D.mapOfLen_id _ (unop X).property
  map_comp {X Y Z} f g :=
    D.mapOfLen_comp _ _ _ (unop X).property (unop Y).property (unop Z).property
      f.unop.hom.toOrderHom g.unop.hom.toOrderHom

/-- The object of `toTruncated` at a simplex is `objOfLen` of its length. -/
@[simp] lemma toTruncated_obj (X : (SimplexCategory.Truncated 1)ᵒᵖ) :
    D.toTruncated.obj X = D.objOfLen (unop X).obj.len := rfl

/-- The morphism of `toTruncated` at a simplicial operator is `mapOfLen` of its monotone map. -/
@[simp] lemma toTruncated_map {X Y : (SimplexCategory.Truncated 1)ᵒᵖ} (f : X ⟶ Y) :
    D.toTruncated.map f = D.mapOfLen _ _ f.unop.hom.toOrderHom := rfl

/-- The object of `toTruncated` in degree zero is the object of vertices. -/
@[simp] lemma toTruncated_obj_zero (h : (⦋0⦌ : SimplexCategory).len ≤ 1) :
    D.toTruncated.obj (op ⟨⦋0⦌, h⟩) = D.vertex := rfl

/-- The object of `toTruncated` in degree one is the object of edges. -/
@[simp] lemma toTruncated_obj_one (h : (⦋1⦌ : SimplexCategory).len ≤ 1) :
    D.toTruncated.obj (op ⟨⦋1⦌, h⟩) = D.edge := rfl

/-- The `i`-th face map of the one-truncated object restricts an edge to the vertex opposite
to `i`: the face `δ i` omits the vertex `i`, so for an edge it keeps the vertex `i.rev`. -/
lemma toTruncated_map_δ (i : Fin 2) (h₀ : (⦋0⦌ : SimplexCategory).len ≤ 1)
    (h₁ : (⦋1⦌ : SimplexCategory).len ≤ 1) :
    D.toTruncated.map
        (SimplexCategory.Truncated.Hom.tr (n := 1) (SimplexCategory.δ i) h₀ h₁).op =
      D.restrict i.rev := by
  change D.mapOfLen 1 0 (SimplexCategory.δ i).toOrderHom = _
  rw [D.mapOfLen_one_zero]
  congr 1
  revert i
  decide

/-- The degeneracy of the one-truncated object is the given one. -/
lemma toTruncated_map_σ (h₁ : (⦋1⦌ : SimplexCategory).len ≤ 1)
    (h₀ : (⦋0⦌ : SimplexCategory).len ≤ 1) :
    D.toTruncated.map
        (SimplexCategory.Truncated.Hom.tr (n := 1) (SimplexCategory.σ (0 : Fin 1)) h₁ h₀).op =
      D.degeneracy := by
  change D.mapOfLen 0 1 (SimplexCategory.σ (0 : Fin 1)).toOrderHom = _
  rw [D.mapOfLen_zero_succ]

end OneTruncatedData

end CategoryTheory.SimplicialObject

end
