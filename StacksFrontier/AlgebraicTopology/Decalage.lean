module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The décalage of a simplicial object

The *décalage* of a simplicial object `X` is the simplicial object `dec X` with
`(dec X) _⦋n⦌ = X _⦋n + 1⦌`, obtained by precomposing `X` with the functor
`SimplexCategory.shift` which adds a new initial vertex. It is augmented over `X _⦋0⦌` by
restriction along the new vertex, and that augmentation carries an extra degeneracy, namely the
zeroth degeneracy `σ 0` of `X`: the décalage is a contractible simplicial object over `X`, and
the zeroth face of `X` is a morphism `dec X ⟶ X`.

## Main definitions

* `SimplexCategory.shift`: the functor `⦋n⦌ ↦ ⦋n + 1⦌` adding a new initial vertex.
* `CategoryTheory.SimplicialObject.dec`: the décalage of a simplicial object.
* `CategoryTheory.SimplicialObject.decAugmented`: the décalage, augmented over `X _⦋0⦌`.
* `CategoryTheory.SimplicialObject.decExtraDegeneracy`: its extra degeneracy.
* `CategoryTheory.SimplicialObject.decδ₀`: the morphism `dec X ⟶ X` given by the zeroth face.

## Implementation notes

`SimplexCategory.shift` sends a monotone map `f` to the map which fixes the new vertex `0` and
is `f` shifted by one elsewhere; it therefore sends `δ i` to `δ i.succ` and `σ i` to `σ i.succ`,
which is why the faces and degeneracies of `dec X` are those of `X` with their index shifted,
and why `σ 0` of `X`, which no index shift reaches, is available as an extra degeneracy.
-/

@[expose] public section

open CategoryTheory Opposite

open scoped Simplicial

universe v u

namespace SimplexCategory

/-- The functor `⦋n⦌ ↦ ⦋n + 1⦌` which adds a new initial vertex: a monotone map `f` is sent to
the monotone map fixing the new vertex `0` and acting by `f`, shifted by one, elsewhere. -/
public def shift : SimplexCategory ⥤ SimplexCategory where
  obj n := .mk (n.len + 1)
  map {n m} f := Hom.mk
    { toFun := Fin.cases 0 fun i => (f.toOrderHom i).succ
      monotone' := by
        intro i j hij
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
        · simp
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
          · exact absurd (Fin.le_zero_iff.mp hij) (Fin.succ_ne_zero a)
          · simpa using Fin.succ_le_succ_iff.mpr
              (f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij)) }
  map_id n := by
    ext i : 3
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩ <;> simp
  map_comp f g := by
    ext i : 3
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩ <;> simp

@[simp]
public lemma shift_map_apply_zero {n m : SimplexCategory} (f : n ⟶ m) :
    (shift.map f).toOrderHom 0 = 0 := rfl

@[simp]
public lemma shift_map_apply_succ {n m : SimplexCategory} (f : n ⟶ m)
    (i : Fin (n.len + 1)) :
    (shift.map f).toOrderHom i.succ = (f.toOrderHom i).succ := rfl

private lemma δ_toOrderHom_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (δ i).toOrderHom j = i.succAbove j := rfl

private lemma σ_toOrderHom_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (σ i).toOrderHom j = i.predAbove j := rfl

/-- A map `shift.obj n ⟶ shift.obj m` fixing `0` and acting by `f`, shifted by one, elsewhere
is `shift.map f`. -/
private lemma shift_map_eq_of_apply {n m : SimplexCategory} (f : n ⟶ m)
    (g : shift.obj n ⟶ shift.obj m) (h₀ : g.toOrderHom 0 = 0)
    (h : ∀ a, g.toOrderHom a.succ = (f.toOrderHom a).succ) : shift.map f = g := by
  ext j : 3
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨a, rfl⟩
  · exact h₀.symm
  · exact (h a).symm

public lemma shift_map_δ {n : ℕ} (i : Fin (n + 2)) : shift.map (δ i) = δ i.succ :=
  shift_map_eq_of_apply _ _ (Fin.succ_succAbove_zero i)
    (Fin.succ_succAbove_succ i)

public lemma shift_map_σ {n : ℕ} (i : Fin (n + 1)) : shift.map (σ i) = σ i.succ :=
  shift_map_eq_of_apply _ _ (Fin.predAbove_right_zero (i := i.succ))
    (Fin.succ_predAbove_succ i)

/-- The zeroth face as a morphism `n ⟶ shift.obj n`, for an arbitrary object. -/
public abbrev δ₀ (n : SimplexCategory) : n ⟶ shift.obj n := δ (n := n.len) 0

public lemma δ₀_toOrderHom_apply (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (δ₀ n).toOrderHom i = i.succ :=
  Fin.zero_succAbove i

/-- The zeroth face is a natural transformation from the identity to `shift`. -/
public lemma δ₀_comp_shift_map {n m : SimplexCategory} (f : n ⟶ m) :
    δ₀ n ≫ shift.map f = f ≫ δ₀ m := by
  ext i : 3
  change (shift.map f).toOrderHom ((δ₀ n).toOrderHom i) = (δ₀ m).toOrderHom (f.toOrderHom i)
  rw [δ₀_toOrderHom_apply, shift_map_apply_succ, δ₀_toOrderHom_apply]

/-- The new initial vertex is a natural transformation from the constant functor `⦋0⦌`
to `shift`. -/
public lemma const_zero_comp_shift_map {n m : SimplexCategory} (f : n ⟶ m) :
    const ⦋0⦌ (shift.obj n) 0 ≫ shift.map f = const ⦋0⦌ (shift.obj m) 0 := by
  rw [const_comp, shift_map_apply_zero]

/-- Precomposing a constant morphism with anything is constant. -/
public lemma comp_const {x y z : SimplexCategory} (f : x ⟶ y) (i : Fin (z.len + 1)) :
    f ≫ const y z i = const x z i := by
  ext j : 3
  simp

public lemma const_zero_eq_δ_one : const ⦋0⦌ ⦋1⦌ 0 = δ 1 := by
  apply Hom.ext_zero_left
  simp [δ]

public lemma const_one_eq_δ_zero : const ⦋0⦌ ⦋1⦌ 1 = δ 0 := by
  apply Hom.ext_zero_left
  simp [δ]

end SimplexCategory

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The décalage of a simplicial object: `(dec X) _⦋n⦌ = X _⦋n + 1⦌`. -/
public def dec (X : SimplicialObject C) : SimplicialObject C := SimplexCategory.shift.op ⋙ X

public lemma dec_map (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (dec X).map f = X.map (SimplexCategory.shift.map f.unop).op := rfl

public lemma dec_δ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    (dec X).δ i = X.δ i.succ := by
  change X.map (SimplexCategory.shift.map (SimplexCategory.δ i)).op = _
  rw [SimplexCategory.shift_map_δ]
  rfl

public lemma dec_σ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    (dec X).σ i = X.σ i.succ := by
  change X.map (SimplexCategory.shift.map (SimplexCategory.σ i)).op = _
  rw [SimplexCategory.shift_map_σ]
  rfl

/-- The augmentation of the décalage over `X _⦋0⦌`, restriction along the new initial vertex. -/
public def decAug (X : SimplicialObject C) : dec X ⟶ (const C).obj (X _⦋0⦌) where
  app n := X.map (SimplexCategory.const ⦋0⦌ (SimplexCategory.shift.obj n.unop) 0).op
  naturality n m f := by
    dsimp only [dec, Functor.comp_map, Functor.op_map]
    rw [← X.map_comp, ← op_comp, SimplexCategory.const_zero_comp_shift_map f.unop]
    simp

public lemma decAug_app (X : SimplicialObject C) (n : ℕ) :
    (decAug X).app (op ⦋n⦌) =
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op := rfl

public lemma decAug_app_zero (X : SimplicialObject C) :
    (decAug X).app (op ⦋0⦌) = X.δ 1 := by
  rw [decAug_app, SimplexCategory.const_zero_eq_δ_one]
  rfl

/-- The décalage as an augmented simplicial object over `X _⦋0⦌`. -/
public def decAugmented (X : SimplicialObject C) : SimplicialObject.Augmented C where
  left := dec X
  right := X _⦋0⦌
  hom := decAug X

/-- The extra degeneracy of the décalage: the zeroth degeneracy of `X`, which the index shift
of the décalage leaves free. -/
public def decExtraDegeneracy (X : SimplicialObject C) :
    SimplicialObject.Augmented.ExtraDegeneracy (decAugmented X) where
  s' := X.σ 0
  s _ := X.σ 0
  s'_comp_ε := by
    change X.σ 0 ≫ (decAug X).app (op ⦋0⦌) = _
    rw [decAug_app_zero]
    exact X.δ_comp_σ_succ' (by simp)
  s₀_comp_δ₁ := by
    change X.σ 0 ≫ (dec X).δ 1 = (decAug X).app (op ⦋0⦌) ≫ X.σ 0
    rw [dec_δ, decAug_app_zero]
    exact X.δ_comp_σ_of_gt (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide)
  s_comp_δ₀ n := by
    change X.σ 0 ≫ (dec X).δ 0 = _
    rw [dec_δ]
    exact X.δ_comp_σ_succ' (by simp)
  s_comp_δ n i := by
    change X.σ 0 ≫ (dec X).δ i.succ = (dec X).δ i ≫ X.σ 0
    rw [dec_δ, dec_δ]
    exact X.δ_comp_σ_of_gt (i := i.succ) (j := 0) (Fin.succ_pos i)
  s_comp_σ n i := by
    change X.σ 0 ≫ (dec X).σ i.succ = (dec X).σ i ≫ X.σ 0
    rw [dec_σ, dec_σ]
    exact (X.σ_comp_σ (i := 0) (j := i.succ) (Fin.zero_le _)).symm

/-- The zeroth face of `X` as a morphism `dec X ⟶ X`. -/
public def decδ₀ (X : SimplicialObject C) : dec X ⟶ X where
  app n := X.map (SimplexCategory.δ₀ n.unop).op
  naturality n m f := by
    change X.map (SimplexCategory.shift.map f.unop).op ≫ X.map (SimplexCategory.δ₀ m.unop).op =
      X.map (SimplexCategory.δ₀ n.unop).op ≫ X.map f.unop.op
    rw [← X.map_comp, ← X.map_comp, ← op_comp, ← op_comp,
      SimplexCategory.δ₀_comp_shift_map f.unop]

public lemma decδ₀_app (X : SimplicialObject C) (n : ℕ) :
    (decδ₀ X).app (op ⦋n⦌) = X.δ 0 := rfl

end CategoryTheory.SimplicialObject

end
