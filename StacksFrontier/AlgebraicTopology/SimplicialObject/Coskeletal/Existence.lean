module

public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Existence of coskeleta by induction on the truncation level

The inductive construction of coskeleta: faces and degeneracies of a one-step extension in
coordinates, the inductive step, and the existence of coskeleta without assuming all finite limits.
-/

/-!
## Faces and degeneracies of a one-step extension, in coordinates

Let `C` be a category, let `U` be an `(n + 1)`-truncated simplicial object of `C`, and suppose the
functor of matching families of `U` in degree `n + 2` is represented by an object `Y` with
universal matching family `f = (f_0, …, f_{n + 2})`, as in [Stacks, Tag 0187]. The extension `Ũ`
produced there has `Ũ_{n + 2} = Y`, and its faces and degeneracies in degree `n + 2` admit the
following description on `T`-valued points. The faces are the projections,
`d_i (g_0, …, g_{n + 2}) = g_i`, which is the identification of `Ũ_{n + 2}` with `Y`. The
degeneracies `s_j : Ũ_{n + 1} ⟶ Ũ_{n + 2}` are then computed by
`g ↦ (s_{j - 1} d_0 g, …, s_{j - 1} d_{j - 1} g, g, g, s_j d_{j + 1} g, …, s_j d_{n + 1} g)`, the
components being taken in `U` itself. Since the components of a morphism to `Y` determine it, that
description characterises the degeneracies.

### Main results

* `CategoryTheory.SimplicialObject.Truncated.eq_σ_comp_iff_of_matchingFamily`: a family `s` of
  morphisms `Ũ_{n + 1} ⟶ Y` records the degeneracies `s_j : Ũ_{n + 1} ⟶ Ũ_{n + 2}` of the one-step
  extension, in the coordinates given by the universal matching family, if and only if the
  components `s j ≫ f i` are the displayed composites of a face and a degeneracy of `U`: the
  identity (transported along `α`) for `i = j` and `i = j + 1`, `s_{j - 1} ∘ d_i` for `i < j`, and
  `s_j ∘ d_{i - 1}` for `i > j + 1`.

### References

* [Stacks, Tag 0188](https://stacks.math.columbia.edu/tag/0188)
-/

section

open CategoryTheory Opposite Simplicial
open scoped SimplexCategory.Truncated CategoryTheory.SimplicialObject.Truncated

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

section Helpers

variable {n : ℕ}

section SimplicialIdentities

variable {m : ℕ}

/-- The identity `δ_i ≫ σ_i = id` in the `m`-truncated simplex category. -/
private theorem δ_comp_σ_self {i : Fin (n + 1)} {h : n + 1 ≤ m} :
    SimplexCategory.Truncated.δ m i.castSucc (by trunc) h ≫
      SimplexCategory.Truncated.σ m i h (by trunc) = 𝟙 _ :=
  ObjectProperty.hom_ext _ SimplexCategory.δ_comp_σ_self

/-- The identity `δ_{i + 1} ≫ σ_i = id` in the `m`-truncated simplex category. -/
private theorem δ_comp_σ_succ {i : Fin (n + 1)} {h : n + 1 ≤ m} :
    SimplexCategory.Truncated.δ m i.succ (by trunc) h ≫
      SimplexCategory.Truncated.σ m i h (by trunc) = 𝟙 _ :=
  ObjectProperty.hom_ext _ SimplexCategory.δ_comp_σ_succ

/-- The identity `δ_i ≫ σ_{j + 1} = σ_j ≫ δ_i` for `i ≤ j` in the `m`-truncated simplex category.
-/
private theorem δ_comp_σ_of_le {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc)
    {h : n + 2 ≤ m} :
    SimplexCategory.Truncated.δ m i.castSucc (by trunc) h ≫
        SimplexCategory.Truncated.σ m j.succ h (by trunc) =
      SimplexCategory.Truncated.σ m j (by trunc) (by trunc) ≫
        SimplexCategory.Truncated.δ m i (by trunc) (by trunc) :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_le H)

/-- The identity `δ_{i + 1} ≫ σ_j = σ_j ≫ δ_i` for `j < i` in the `m`-truncated simplex category.
-/
private theorem δ_comp_σ_of_gt {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i)
    {h : n + 2 ≤ m} :
    SimplexCategory.Truncated.δ m i.succ (by trunc) h ≫
        SimplexCategory.Truncated.σ m j.castSucc h (by trunc) =
      SimplexCategory.Truncated.σ m j (by trunc) (by trunc) ≫
        SimplexCategory.Truncated.δ m i (by trunc) (by trunc) :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_gt H)

/-- The four cases of the fourth simplicial identity, as an elimination principle: a component
index `i : Fin (n + 3)` and a degeneracy index `j : Fin (n + 2)` fall into one of the four cases of
`δ_comp_σ_self`, `δ_comp_σ_succ`, `δ_comp_σ_of_le` and `δ_comp_σ_of_gt`, namely `i = j.castSucc`,
`i = j.succ`, `i = i'.castSucc` with `j = j'.succ` and `i' ≤ j'.castSucc`, or `i = i'.succ` with
`j = j'.castSucc` and `j'.castSucc < i'`. -/
private theorem δ_comp_σ_cases {p : Prop} (i : Fin (n + 3)) (j : Fin (n + 2))
    (self : i = j.castSucc → p) (succ : i = j.succ → p)
    (of_le : ∀ (i' : Fin (n + 2)) (j' : Fin (n + 1)), i' ≤ j'.castSucc →
      i = i'.castSucc → j = j'.succ → p)
    (of_gt : ∀ (i' : Fin (n + 2)) (j' : Fin (n + 1)), j'.castSucc < i' →
      i = i'.succ → j = j'.castSucc → p) : p := by
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · exact of_le ⟨i, by omega⟩ ⟨(j : ℕ) - 1, by omega⟩
      (by simp only [Fin.le_def, Fin.val_castSucc]; omega)
      (Fin.ext rfl)
      (Fin.ext (by simp only [Fin.val_succ]; omega))
  · exact self (Fin.ext (by simpa only [Fin.val_castSucc] using h))
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · exact succ (Fin.ext (by simp only [Fin.val_succ]; omega))
    · exact of_gt ⟨(i : ℕ) - 1, by omega⟩ ⟨j, by omega⟩
        (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
        (Fin.ext (by simp only [Fin.val_succ]; omega))
        (Fin.ext rfl)

end SimplicialIdentities

section Components

variable {U : SimplicialObject.Truncated C (n + 1)} {Ũ : SimplicialObject.Truncated C (n + 2)}
  {Y : C} (f : Fin (n + 3) → (Y ⟶ U _⦋n + 1⦌ₙ₊₁)) (e : Ũ _⦋n + 2⦌ₙ₊₂ ≅ Y)
  (a : Ũ _⦋n + 1⦌ₙ₊₂ ⟶ U _⦋n + 1⦌ₙ₊₁)
  (he : ∀ i : Fin (n + 3), e.hom ≫ f i =
    Ũ.map (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc)).op ≫ a)
  (ha : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)),
    Ũ.map (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc)).op ≫
        Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ a =
      a ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op ≫
        U.map (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op)

include he in
/-- The `i`-th component of the `j`-th degeneracy of `Ũ`, in the coordinates given by the universal
matching family `f`, is `Ũ` applied to the composite `δ_i ≫ σ_j`. -/
private theorem map_σ_comp_hom_comp_f (j : Fin (n + 2)) (i : Fin (n + 3)) :
    (Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ e.hom) ≫ f i =
      Ũ.map (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc) ≫
        SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ a := by
  rw [Category.assoc, he i, op_comp, Ũ.map_comp, Category.assoc]

include he in
/-- A component of the `j`-th degeneracy of `Ũ` whose index makes `δ_i ≫ σ_j` the identity is `a`.
-/
private theorem map_σ_comp_hom_comp_f_of_eq_id {i : Fin (n + 3)} {j : Fin (n + 2)}
    (hij : SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc) ≫
      SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc) = 𝟙 _) :
    (Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ e.hom) ≫ f i =
      a := by
  rw [map_σ_comp_hom_comp_f f e a he, hij, op_id, Ũ.map_id, Category.id_comp]

include he ha in
/-- A component of the `j`-th degeneracy of `Ũ` whose index makes `δ_i ≫ σ_j` factor as
`σ_{j'} ≫ δ_{i'}` through degree `n`, hence through the truncation, is the composite
`s_{j'} d_{i'}` computed in `U`. -/
private theorem map_σ_comp_hom_comp_f_of_eq_comp {i : Fin (n + 3)} {j : Fin (n + 2)}
    {i' : Fin (n + 2)} {j' : Fin (n + 1)}
    (hij : SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc) ≫
        SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc) =
      SimplexCategory.Truncated.σ (n + 2) j' (by trunc) (by trunc) ≫
        SimplexCategory.Truncated.δ (n + 2) i' (by trunc) (by trunc)) :
    (Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ e.hom) ≫ f i =
      a ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i' (by trunc) (by trunc)).op ≫
        U.map (SimplexCategory.Truncated.σ (n + 1) j' (by trunc) (by trunc)).op := by
  rw [map_σ_comp_hom_comp_f f e a he, hij, op_comp, Ũ.map_comp, Category.assoc, ha i' j']

include he ha in
/-- A family `s` of morphisms `Ũ_{n + 1} ⟶ Y` whose components along the universal matching family
`f` are the four displayed cases has, in every component, the same value as the `j`-th degeneracy
of `Ũ` read in the coordinates `f`. -/
private theorem map_σ_comp_hom_comp_f_eq_of_components {s : Fin (n + 2) → (Ũ _⦋n + 1⦌ₙ₊₂ ⟶ Y)}
    (h₁ : ∀ j : Fin (n + 2), s j ≫ f j.castSucc = a)
    (h₂ : ∀ j : Fin (n + 2), s j ≫ f j.succ = a)
    (h₃ : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)), i ≤ j.castSucc →
      s j.succ ≫ f i.castSucc =
        a ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op ≫
          U.map (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op)
    (h₄ : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)), j.castSucc < i →
      s j.castSucc ≫ f i.succ =
        a ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op ≫
          U.map (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op)
    (j : Fin (n + 2)) (i : Fin (n + 3)) :
    (Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ e.hom) ≫ f i =
      s j ≫ f i := by
  refine δ_comp_σ_cases i j (fun hi => ?_) (fun hi => ?_) (fun i' j' hij hi hj => ?_)
    (fun i' j' hij hi hj => ?_)
  · subst hi
    rw [h₁ j]
    exact map_σ_comp_hom_comp_f_of_eq_id f e a he δ_comp_σ_self
  · subst hi
    rw [h₂ j]
    exact map_σ_comp_hom_comp_f_of_eq_id f e a he δ_comp_σ_succ
  · subst hi hj
    rw [h₃ i' j' hij]
    exact map_σ_comp_hom_comp_f_of_eq_comp f e a he ha (δ_comp_σ_of_le hij)
  · subst hi hj
    rw [h₄ i' j' hij]
    exact map_σ_comp_hom_comp_f_of_eq_comp f e a he ha (δ_comp_σ_of_gt hij)

end Components

/-- A degeneracy after a face of `Ũ`, both in degrees `≤ n + 1`, is carried by the comparison
morphism `α : sk_{n + 1} Ũ ⟶ U` to the same composite in `U`. -/
private theorem map_δ_comp_map_σ_comp_app {U : SimplicialObject.Truncated C (n + 1)}
    {Ũ : SimplicialObject.Truncated C (n + 2)}
    (α : (SimplicialObject.Truncated.trunc C (n + 2) (n + 1)).obj Ũ ⟶ U)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    Ũ.map (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc)).op ≫
        Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫
          α.app (op ⦋n + 1⦌ₙ₊₁) =
      α.app (op ⦋n + 1⦌ₙ₊₁) ≫
        U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op ≫
          U.map (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op := by
  have hσ := α.naturality (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op
  have hδ := α.naturality (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op
  dsimp [SimplicialObject.Truncated.trunc] at hσ hδ
  rw [hσ, reassoc_of% hδ]
  rfl

/-- A universal matching family is jointly monomorphic: two morphisms to an object representing the
functor of matching families of `U` in degree `n + 2` which have the same components along the
universal family `f` are equal. -/
private theorem hom_ext_of_matchingFamily {U : SimplicialObject.Truncated C (n + 1)} {Y : C}
    (f : Fin (n + 3) → (Y ⟶ U _⦋n + 1⦌ₙ₊₁))
    (hf : ∀ i j : Fin (n + 2), i ≤ j →
      f i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
        f j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op)
    (huniv : ∀ (T : C) (g : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌ₙ₊₁)),
      (∀ i j : Fin (n + 2), i ≤ j →
        g i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
          g j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op) →
      ∃! h : T ⟶ Y, ∀ i, h ≫ f i = g i)
    {T : C} {b c : T ⟶ Y} (hbc : ∀ i, b ≫ f i = c ≫ f i) : b = c :=
  (huniv T (fun i => b ≫ f i) fun i j hij => by simp [hf i j hij]).unique
    (fun _ => rfl) fun i => (hbc i).symm

end Helpers

/-- Let `U` be an `(n + 1)`-truncated simplicial object of `C` whose functor of matching families in
degree `n + 2` is represented by `Y` with universal matching family `f` ([Stacks, Tag 0187]), let
`Ũ` be an `(n + 2)`-truncated object with a comparison morphism `α : sk_{n + 1} Ũ ⟶ U` and an
identification `e : Ũ_{n + 2} ≅ Y` under which the faces `d_i : Ũ_{n + 2} ⟶ Ũ_{n + 1}` become the
projections `f_i`. Then a family `s` of morphisms `Ũ_{n + 1} ⟶ Y` records the degeneracies
`s_j : Ũ_{n + 1} ⟶ Ũ_{n + 2}` of `Ũ` if and only if, componentwise, `s_j` sends `g` to
`(s_{j - 1} d_0 g, …, s_{j - 1} d_{j - 1} g, g, g, s_j d_{j + 1} g, …, s_j d_{n + 1} g)`. -/
@[stacks 0188 "the description of the faces is the identification `he` of Lemma 0187; the \
  description of the degeneracies is stated as a characterisation of them by their components, \
  which the representability of the functor of matching families makes possible"]
public theorem eq_σ_comp_iff_of_matchingFamily {n : ℕ}
    {U : SimplicialObject.Truncated C (n + 1)} {Ũ : SimplicialObject.Truncated C (n + 2)}
    (α : (SimplicialObject.Truncated.trunc C (n + 2) (n + 1)).obj Ũ ⟶ U) {Y : C}
    (f : Fin (n + 3) → (Y ⟶ U _⦋n + 1⦌ₙ₊₁))
    (hf : ∀ i j : Fin (n + 2), i ≤ j →
      f i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
        f j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op)
    (huniv : ∀ (T : C) (g : Fin (n + 3) → (T ⟶ U _⦋n + 1⦌ₙ₊₁)),
      (∀ i j : Fin (n + 2), i ≤ j →
        g i.castSucc ≫ U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
          g j.succ ≫ U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op) →
      ∃! h : T ⟶ Y, ∀ i, h ≫ f i = g i)
    (e : Ũ _⦋n + 2⦌ₙ₊₂ ≅ Y)
    (he : ∀ i : Fin (n + 3), e.hom ≫ f i =
      Ũ.map (SimplexCategory.Truncated.δ (n + 2) i (by trunc) (by trunc)).op ≫
        α.app (op ⦋n + 1⦌ₙ₊₁))
    (s : Fin (n + 2) → (Ũ _⦋n + 1⦌ₙ₊₂ ⟶ Y)) :
    (∀ j : Fin (n + 2),
        Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op = s j ≫ e.inv) ↔
      (∀ j : Fin (n + 2), s j ≫ f j.castSucc = α.app (op ⦋n + 1⦌ₙ₊₁)) ∧
      (∀ j : Fin (n + 2), s j ≫ f j.succ = α.app (op ⦋n + 1⦌ₙ₊₁)) ∧
      (∀ (i : Fin (n + 2)) (j : Fin (n + 1)), i ≤ j.castSucc →
        s j.succ ≫ f i.castSucc = α.app (op ⦋n + 1⦌ₙ₊₁) ≫
          U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op ≫
            U.map (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op) ∧
      (∀ (i : Fin (n + 2)) (j : Fin (n + 1)), j.castSucc < i →
        s j.castSucc ≫ f i.succ = α.app (op ⦋n + 1⦌ₙ₊₁) ≫
          U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op ≫
            U.map (SimplexCategory.Truncated.σ (n + 1) j (by trunc) (by trunc)).op) := by
  have ha := map_δ_comp_map_σ_comp_app α
  constructor
  · intro hs
    have hsj : ∀ j : Fin (n + 2), s j =
        Ũ.map (SimplexCategory.Truncated.σ (n + 2) j (by trunc) (by trunc)).op ≫ e.hom :=
      fun j => (e.eq_comp_inv.mp (hs j)).symm
    refine ⟨fun j => ?_, fun j => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [hsj j]
      exact map_σ_comp_hom_comp_f_of_eq_id f e _ he δ_comp_σ_self
    · rw [hsj j]
      exact map_σ_comp_hom_comp_f_of_eq_id f e _ he δ_comp_σ_succ
    · rw [hsj j.succ]
      exact map_σ_comp_hom_comp_f_of_eq_comp f e _ he ha (δ_comp_σ_of_le hij)
    · rw [hsj j.castSucc]
      exact map_σ_comp_hom_comp_f_of_eq_comp f e _ he ha (δ_comp_σ_of_gt hij)
  · rintro ⟨h₁, h₂, h₃, h₄⟩ j
    exact e.eq_comp_inv.mpr (hom_ext_of_matchingFamily f hf huniv
      (map_σ_comp_hom_comp_f_eq_of_components f e _ he ha h₁ h₂ h₃ h₄ j))

end CategoryTheory.SimplicialObject.Truncated

end

/-!
## Inductive construction of coskeleta

Let `C` be a category, let `m : ℕ` and let `U` be an `m`-truncated simplicial object of `C`, i.e. a
functor `(Δ_{≤m})ᵒᵖ ⥤ C` where `Δ_{≤m}` is the full subcategory of the simplex category `Δ` on the
objects `⦋i⦌` with `i ≤ m`. The coskeleton `cosk_m U` is the simplicial object characterised by
`Mor_{Simp(C)}(V, cosk_m U) = Mor_{Simp_m(C)}(sk_m V, U)`, that is, the right Kan extension of `U`
along `(Δ_{≤m})ᵒᵖ ⥤ Δᵒᵖ`. It can be built one degree at a time. Writing `U^n` for the `n`-truncated
object characterised by `Mor_{Simp_n(C)}(V, U^n) = Mor_{Simp_m(C)}(sk_m V, U)`, the source's
construction is `U^m = U` and `U^{n + 1} = Ũ^n`, the one-degree extension of [Stacks, Tag 0187];
since that construction leaves the `n`-skeleton unchanged the terms `U^n_n` are compatible and
`(cosk_m U)_n = U^n_n`. So the whole tower, and `cosk_m` itself, exist as soon as each single
degree can be added.

### Main results

* `CategoryTheory.SimplicialObject.Truncated.hasPointwiseRightKanExtension_of_incl_succ`: if every
  `k`-truncated simplicial object of `C` extends by one degree, for every `k ≥ m` — i.e. admits a
  pointwise right Kan extension along `(Δ_{≤k} ⊆ Δ_{≤k+1})ᵒᵖ` — then every `m`-truncated `F` admits
  a pointwise right Kan extension along `(Δ_{≤m} ⊆ Δ_{≤n})ᵒᵖ` for every `n ≥ m` and along
  `(Δ_{≤m} ⊆ Δ)ᵒᵖ`, and the `n`-truncation of the latter is the former.

### References

* [Stacks, Tag 018A](https://stacks.math.columbia.edu/tag/018A)
-/

section

open CategoryTheory Opposite Limits

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

section Helpers

section KanExtension

variable {J₁ J₂ J₃ K : Type*} [Category J₁] [Category J₂] [Category J₃] [Category K]

/-- A pointwise right Kan extension of `G` along a fully faithful functor `L` exists at every
object in the image of `L`. -/
private lemma hasPointwiseRightKanExtensionAt_obj {L : J₁ ⥤ J₂} [L.Full] [L.Faithful]
    (G : J₁ ⥤ K) (X : J₁) : L.HasPointwiseRightKanExtensionAt G (L.obj X) :=
  HasLimit.mk ⟨_, limitOfDiagramInitial StructuredArrow.mkIdInitial _⟩

variable {L₁ : J₁ ⥤ J₂} {L₂ : J₂ ⥤ J₃} {G : J₁ ⥤ K} {G₁ : J₂ ⥤ K} {G₂ : J₃ ⥤ K}

/-- The legs of the cone `Functor.RightExtension.coneAt` at `Y` of the right extension of `G` along
`L` given by `G'` and `α : L ⋙ G' ⟶ G`, as a cone with apex `G'.obj Y`. -/
private def extπ {L : J₁ ⥤ J₂} {G' : J₂ ⥤ K} (α : L ⋙ G' ⟶ G) (Y : J₂) :
    (Functor.const (StructuredArrow Y L)).obj (G'.obj Y) ⟶ StructuredArrow.proj Y L ⋙ G :=
  ((Functor.RightExtension.mk G' α).coneAt Y).π

/-- The leg of `extπ α Y` at `e` is `G'.map e.hom ≫ α.app e.right`. -/
private lemma extπ_app {L : J₁ ⥤ J₂} {G' : J₂ ⥤ K} (α : L ⋙ G' ⟶ G) (Y : J₂)
    (e : StructuredArrow Y L) : (extπ α Y).app e = G'.map e.hom ≫ α.app e.right := rfl

/-- A pointwise right Kan extension at `Y`, restated as a limit of the cone `extπ α Y` with apex
`G'.obj Y`. -/
private def isLimit_extπ {L : J₁ ⥤ J₂} {G' : J₂ ⥤ K} (α : L ⋙ G' ⟶ G) (Y : J₂)
    (h : (Functor.RightExtension.mk G' α).IsPointwiseRightKanExtensionAt Y) :
    IsLimit (Cone.mk (G'.obj Y) (extπ α Y)) := h

/-- A cone over `StructuredArrow Y (L₁ ⋙ L₂)` restricts, for each `d : StructuredArrow Y L₂`, to a
cone over `StructuredArrow d.right L₁`: the leg at `e` is the leg at `d.hom ≫ L₂.map e.hom`. -/
private def innerπ {Y : J₃} (c : Cone (StructuredArrow.proj Y (L₁ ⋙ L₂) ⋙ G))
    (d : StructuredArrow Y L₂) :
    (Functor.const (StructuredArrow d.right L₁)).obj c.pt ⟶
      StructuredArrow.proj d.right L₁ ⋙ G where
  app e := c.π.app (StructuredArrow.mk (d.hom ≫ L₂.map e.hom))
  naturality e e' φ := by
    have h := c.π.naturality
      (show (StructuredArrow.mk (d.hom ≫ L₂.map e.hom) : StructuredArrow Y (L₁ ⋙ L₂)) ⟶
          StructuredArrow.mk (d.hom ≫ L₂.map e'.hom) from
        StructuredArrow.homMk φ.right (by simp [← L₂.map_comp]))
    simpa using h

/-- The leg of `innerπ c d` at `e` is the leg of `c` at `d.hom ≫ L₂.map e.hom`. -/
private lemma innerπ_app {Y : J₃} (c : Cone (StructuredArrow.proj Y (L₁ ⋙ L₂) ⋙ G))
    (d : StructuredArrow Y L₂) (e : StructuredArrow d.right L₁) :
    (innerπ c d).app e = c.π.app (StructuredArrow.mk (d.hom ≫ L₂.map e.hom)) := rfl

/-- Given a pointwise right Kan extension `(G₁, α₁)` of `G` along `L₁`, a cone over
`StructuredArrow Y (L₁ ⋙ L₂)` induces a cone over `StructuredArrow Y L₂` with values in `G₁`, whose
leg at `d` is the map into the limit `G₁.obj d.right` given by `innerπ`. -/
private def outerπ (α₁ : L₁ ⋙ G₁ ⟶ G)
    (h₁ : ∀ X, IsLimit (Cone.mk (G₁.obj X) (extπ α₁ X))) {Y : J₃}
    (c : Cone (StructuredArrow.proj Y (L₁ ⋙ L₂) ⋙ G)) :
    (Functor.const (StructuredArrow Y L₂)).obj c.pt ⟶ StructuredArrow.proj Y L₂ ⋙ G₁ where
  app d := (h₁ d.right).lift (Cone.mk c.pt (innerπ c d))
  naturality d d' ψ := by
    refine (h₁ d'.right).hom_ext fun e => ?_
    have hfac' := (h₁ d'.right).fac (Cone.mk c.pt (innerπ c d')) e
    have hfac := (h₁ d.right).fac (Cone.mk c.pt (innerπ c d))
      (StructuredArrow.mk (ψ.right ≫ e.hom))
    have hd : d.hom ≫ L₂.map (ψ.right ≫ e.hom) = d'.hom ≫ L₂.map e.hom := by
      simp [L₂.map_comp]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
      StructuredArrow.proj_obj, Functor.comp_map, StructuredArrow.proj_map, Category.id_comp,
      Category.assoc, extπ_app, innerπ_app, StructuredArrow.mk_right,
      StructuredArrow.mk_hom_eq_self] at hfac hfac' ⊢
    rwa [← Functor.map_comp_assoc, hfac, hd]

/-- The leg of `outerπ α₁ h₁ c` at `d` is the map into the limit `G₁.obj d.right` induced by the
cone `innerπ c d`. -/
private lemma outerπ_app (α₁ : L₁ ⋙ G₁ ⟶ G)
    (h₁ : ∀ X, IsLimit (Cone.mk (G₁.obj X) (extπ α₁ X))) {Y : J₃}
    (c : Cone (StructuredArrow.proj Y (L₁ ⋙ L₂) ⋙ G)) (d : StructuredArrow Y L₂) :
    (outerπ α₁ h₁ c).app d = (h₁ d.right).lift (Cone.mk c.pt (innerπ c d)) := rfl

/-- Pointwise right Kan extensions compose: if `(G₁, α₁)` is a pointwise right Kan extension of `G`
along `L₁` and `(G₂, α₂)` is a pointwise right Kan extension of `G₁` along `L₂` at `Y`, then `G₂`,
with the pasted structure map, is a pointwise right Kan extension of `G` along `L₁ ⋙ L₂` at `Y`. -/
private def isLimitExtπComp (α₁ : L₁ ⋙ G₁ ⟶ G) (α₂ : L₂ ⋙ G₂ ⟶ G₁)
    (h₁ : ∀ X, IsLimit (Cone.mk (G₁.obj X) (extπ α₁ X))) {Y : J₃}
    (h₂ : IsLimit (Cone.mk (G₂.obj Y) (extπ α₂ Y))) :
    IsLimit (Cone.mk (G₂.obj Y)
      (extπ (L := L₁ ⋙ L₂) (Functor.whiskerLeft L₁ α₂ ≫ α₁) Y)) where
  lift c := h₂.lift (Cone.mk c.pt (outerπ α₁ h₁ c))
  fac c g := by
    have hg : c.π.app (StructuredArrow.mk (g.hom ≫ L₂.map (𝟙 (L₁.obj g.right))) :
        StructuredArrow Y (L₁ ⋙ L₂)) = c.π.app g := by
      simpa using (c.π.naturality
        (show (StructuredArrow.mk (g.hom ≫ L₂.map (𝟙 (L₁.obj g.right))) :
            StructuredArrow Y (L₁ ⋙ L₂)) ⟶ g from
          StructuredArrow.homMk (𝟙 g.right) (by simp))).symm
    have h2 := h₂.fac (Cone.mk c.pt (outerπ α₁ h₁ c))
      (StructuredArrow.mk g.hom : StructuredArrow Y L₂)
    have h1 := (h₁ (L₁.obj g.right)).fac
      (Cone.mk c.pt (innerπ c (StructuredArrow.mk g.hom : StructuredArrow Y L₂)))
      (StructuredArrow.mk (𝟙 (L₁.obj g.right)))
    simp only [extπ_app, outerπ_app, innerπ_app, StructuredArrow.mk_right,
      StructuredArrow.mk_hom_eq_self, NatTrans.comp_app,
      Functor.whiskerLeft_app] at h1 h2 ⊢
    rw [reassoc_of% h2]
    simpa [hg] using h1
  uniq c f hf := by
    refine h₂.uniq (Cone.mk c.pt (outerπ α₁ h₁ c)) f fun d => ?_
    refine (h₁ d.right).hom_ext fun e => ?_
    have h1 := (h₁ d.right).fac (Cone.mk c.pt (innerπ c d)) e
    have hfe := hf (StructuredArrow.mk (d.hom ≫ L₂.map e.hom) : StructuredArrow Y (L₁ ⋙ L₂))
    have hnat := α₂.naturality e.hom
    simp only [extπ_app, outerπ_app, innerπ_app, StructuredArrow.mk_right,
      StructuredArrow.mk_hom_eq_self, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.comp_map, Functor.map_comp, Category.assoc] at h1 hfe hnat ⊢
    rwa [h1, ← reassoc_of% hnat]

/-- If `L₂` is fully faithful, the restriction `L₂ ⋙ E.left` of a pointwise right Kan extension of
`G` along `L₁ ⋙ L₂` is a pointwise right Kan extension of `G` along `L₁`. -/
public noncomputable def restrictIsPointwiseRightKanExtensionAt [L₂.Full] [L₂.Faithful]
    (E : Functor.RightExtension (L₁ ⋙ L₂) G) (Y : J₂)
    (hE : E.IsPointwiseRightKanExtensionAt (L₂.obj Y)) :
    (Functor.RightExtension.mk (L := L₁) (F := G) (L₂ ⋙ E.left)
      E.hom).IsPointwiseRightKanExtensionAt Y := by
  refine IsLimit.ofIsoLimit (hE.whiskerEquivalence
    (StructuredArrow.post Y L₁ L₂).asEquivalence) (Cone.ext (Iso.refl _) ?_)
  intro j
  simp [Functor.asEquivalence, StructuredArrow.post]

end KanExtension

end Helpers

variable {C : Type u} [Category.{v} C]

/-- Let `C` be a category, let `m : ℕ` and let `F` be an `m`-truncated simplicial object of `C`.
Assume that every `k`-truncated simplicial object of `C`, for `k ≥ m`, can be extended by one
degree, i.e. admits a pointwise right Kan extension along the inclusion `(Δ_{≤k} ⊆ Δ_{≤k+1})ᵒᵖ` —
the one-degree step of [Stacks, Tag 0187]. Then:

* for every `n ≥ m` the `n`-truncated object `U^n` extending `F` exists, as a pointwise right Kan
  extension of `F` along `(Δ_{≤m} ⊆ Δ_{≤n})ᵒᵖ`; its universal property is the source's
  `Mor_{Simp_n(C)}(V, U^n) = Mor_{Simp_m(C)}(sk_m V, F)`;
* the coskeleton `cosk_m F` exists, as a pointwise right Kan extension of `F` along
  `(Δ_{≤m} ⊆ Δ)ᵒᵖ`; its universal property is the source's
  `Mor_{Simp(C)}(V, cosk_m F) = Mor_{Simp_m(C)}(sk_m V, F)`;
* the tower is compatible: the `n`-truncation of any right Kan extension `X` of `F` along
  `(Δ_{≤m} ⊆ Δ)ᵒᵖ` is again a right Kan extension of `F` along `(Δ_{≤m} ⊆ Δ_{≤n})ᵒᵖ`, which is the
  source's `(cosk_m F)_n = U^n_n`. -/
@[stacks 018A "the source's three displayed assertions, with each `Mor` formula stated as the \
  universal property of the right Kan extension it is; the hypothesis is the one-degree step of \
  Lemma 0187 rather than finite limits in the ambient category"]
public theorem hasPointwiseRightKanExtension_of_incl_succ {m : ℕ}
    (H : ∀ (k : ℕ), m ≤ k → ∀ G : SimplicialObject.Truncated C k,
      (SimplexCategory.Truncated.incl k (k + 1)).op.HasPointwiseRightKanExtension G)
    (F : SimplicialObject.Truncated C m) :
    (∀ (n : ℕ) (h : m ≤ n),
        (SimplexCategory.Truncated.incl m n h).op.HasPointwiseRightKanExtension F) ∧
      (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F ∧
      ∀ (n : ℕ) (h : m ≤ n) (X : SimplicialObject C) (β : (truncation m).obj X ⟶ F),
        X.IsRightKanExtension β →
          ((truncation n).obj X).IsRightKanExtension
            (((truncationCompTrunc (C := C) h).app X).hom ≫ β) := by
  have tower : ∀ (n : ℕ) (h : m ≤ n),
      (SimplexCategory.Truncated.incl m n h).op.HasPointwiseRightKanExtension F := by
    intro n h
    induction n, h using Nat.le_induction with
    | base => exact fun Y => hasPointwiseRightKanExtensionAt_obj F Y
    | succ n hn IH =>
      have hp1 := (SimplexCategory.Truncated.incl m n
        hn).op.pointwiseRightKanExtensionIsPointwiseRightKanExtension F
      have hstep := H n hn ((SimplexCategory.Truncated.incl m n hn).op.pointwiseRightKanExtension F)
      have hp2 := (SimplexCategory.Truncated.incl n (n + 1)
        (Nat.le_succ n)).op.pointwiseRightKanExtensionIsPointwiseRightKanExtension
        ((SimplexCategory.Truncated.incl m n hn).op.pointwiseRightKanExtension F)
      exact fun Y => HasLimit.mk
        ⟨_, isLimitExtπComp _ _ (fun X => isLimit_extπ _ _ (hp1 X)) (isLimit_extπ _ _ (hp2 Y))⟩
  have cosk : (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F := by
    rintro ⟨W⟩
    have hmn : m ≤ max m W.len := le_max_left _ _
    have hW : W.len ≤ max m W.len := le_max_right _ _
    exact (hasLimit_equivalence_comp_iff (StructuredArrow.post
      (op (⟨W, hW⟩ : SimplexCategory.Truncated (max m W.len)))
      (SimplexCategory.Truncated.incl m (max m W.len) hmn).op
      (SimplexCategory.Truncated.inclusion (max m W.len)).op).asEquivalence).mp
      (tower (max m W.len) hmn (op ⟨W, hW⟩))
  refine ⟨tower, cosk, ?_⟩
  intro n h X β hβ
  refine Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := Functor.RightExtension.mk (L := (SimplexCategory.Truncated.incl m n h).op)
      ((SimplicialObject.truncation n).obj X)
      (((SimplicialObject.truncationCompTrunc (C := C) h).app X).hom ≫ β)) fun Y => ?_
  refine IsLimit.ofIsoLimit (restrictIsPointwiseRightKanExtensionAt
    (L₁ := (SimplexCategory.Truncated.incl m n h).op)
    (L₂ := (SimplexCategory.Truncated.inclusion n).op)
    (Functor.RightExtension.mk X β) Y
    (Functor.isPointwiseRightKanExtensionOfIsRightKanExtension X β _))
    (Cone.ext (Iso.refl _) fun j => ?_)
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact congrArg (X.map j.hom.unop.hom.op ≫ ·) (Category.id_comp (β.app j.right)).symm

end CategoryTheory.SimplicialObject.Truncated

end

/-!
## Coskeleta exist without all finite limits

Let `C` be a category and `k : ℕ`. The coskeleton functor `cosk_k`, right adjoint to
`sk_k : Simp(C) ⥤ Simp_k(C)`, exists as soon as `C` has finite limits ([Stacks, Tag 0183]), because
`(cosk_k U)_n` is then the limit of `U` over the finite category `((Δ/⦋n⦌)_{≤k})ᵒᵖ`. Finite limits
are more than is needed, and less suffices, level by level:

* for `k = 0` the categories `(Δ/⦋n⦌)_{≤0}` are discrete on the `n + 1` vertices of `⦋n⦌`, so
  `(cosk_0 U)_n` is the product of `n + 1` copies of `U_0` and products of pairs of objects are
  enough ([Stacks, Example 0182]);
* for `k ≥ 1` the categories `(Δ/⦋n⦌)_{≤k}` are connected — any `α : ⦋j⦌ → ⦋n⦌` receives a vertex
  `⦋0⦌ → ⦋n⦌`, and the two vertices of an edge `⦋1⦌ → ⦋n⦌` both map to it, so any two vertices are
  joined, the edge being an object because `k ≥ 1` — so finite connected limits are enough. For
  `n ≤ k` nothing at all is needed, the identity of `⦋n⦌` being a final object
  ([Stacks, Lemma 0184], and hence [Stacks, Lemma 0185]).

### Main results

* `hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits`, in the
  namespace `CategoryTheory.SimplicialObject.Truncated`: if `C` has products of pairs then every
  `0`-truncated simplicial object of `C` admits a pointwise right Kan extension along
  `(Δ_{≤0} ⊆ Δ)ᵒᵖ`, and if `C` has finite connected limits then, for every `k ≥ 1`, so does every
  `k`-truncated simplicial object.

### References

* [Stacks, Remark 09VS](https://stacks.math.columbia.edu/tag/09VS)
* [Stacks, Lemma 0183](https://stacks.math.columbia.edu/tag/0183)
* [Stacks, Example 0182](https://stacks.math.columbia.edu/tag/0182)
* [Stacks, Lemma 0184](https://stacks.math.columbia.edu/tag/0184)
-/

section

open CategoryTheory Opposite Limits

universe w w' v u

namespace CategoryTheory.SimplicialObject.Truncated

section Helpers

open Simplicial

section Discrete

variable {C : Type u} [Category.{v} C]

/-- If `A` is a discrete category then so is `StructuredArrow Y L`, for every `L : A ⥤ T` and every
`Y : T`. -/
private theorem isDiscrete_structuredArrow {A : Type*} [Category A] {T : Type*} [Category T]
    [IsDiscrete A] (L : A ⥤ T) (Y : T) : IsDiscrete (StructuredArrow Y L) where
  subsingleton X X' := ⟨fun f g => StructuredArrow.ext f g (Subsingleton.elim _ _)⟩
  eq_of_hom {X X'} f := by
    have hr : X.right = X'.right := obj_ext_of_isDiscrete f.right
    refine StructuredArrow.obj_ext _ _ hr ?_
    rw [Subsingleton.elim (eqToHom hr) f.right]
    exact StructuredArrow.w f

/-- A discrete category is equivalent to the discrete category on its objects. -/
private def equivalenceDiscrete (J : Type w) [Category.{w'} J] [IsDiscrete J] : J ≌ Discrete J where
  functor :=
    { obj := Discrete.mk
      map := fun f => Discrete.eqToHom (obj_ext_of_isDiscrete f)
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  inverse := Discrete.functor id
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp := fun _ => Subsingleton.elim _ _

/-- Products of nonempty finite families of objects exist as soon as products of pairs do. -/
private theorem hasProduct_fin_succ [HasBinaryProducts C] (n : ℕ) :
    ∀ f : Fin (n + 1) → C, HasProduct f := by
  induction n with
  | zero =>
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    exact fun _ => inferInstance
  | succ n ih =>
    intro f
    have := ih (fun i => f i.succ)
    exact HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

/-- A category with products of pairs of objects has limits of every shape that is finite, nonempty
and discrete. -/
private theorem hasLimitsOfShape_of_isDiscrete (J : Type w) [Category.{w'} J] [Finite J]
    [Nonempty J] [IsDiscrete J] [HasBinaryProducts C] : HasLimitsOfShape J C := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  obtain _ | m := m
  · exact (e (Classical.arbitrary J)).elim0
  have : HasProductsOfShape (Fin (m + 1)) C := ⟨fun K => by
    rw [← hasLimit_iff_of_iso (Discrete.natIso (F := Discrete.functor fun i => K.obj ⟨i⟩)
      (G := K) fun ⟨_⟩ => Iso.refl _)]
    exact hasProduct_fin_succ m _⟩
  have : HasProductsOfShape J C := hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
  exact hasLimitsOfShape_of_equivalence (equivalenceDiscrete J).symm

end Discrete

section Finiteness

/-- A morphism of an opposite category is a morphism of the category, so opposite hom types inherit
finiteness. -/
public theorem finite_hom_op {C : Type*} [Category C] (a b : Cᵒᵖ)
    [Finite (b.unop ⟶ a.unop)] : Finite (a ⟶ b) :=
  .of_equiv _ (opEquiv a b).symm

/-- A morphism of a full subcategory is a morphism of the category, so hom types of a full
subcategory inherit finiteness. -/
public theorem finite_hom_fullSubcategory {C : Type*} [Category C] {P : ObjectProperty C}
    (a b : P.FullSubcategory) [Finite (a.obj ⟶ b.obj)] : Finite (a ⟶ b) :=
  .of_injective (fun f => f.hom) fun _ _ h => InducedCategory.hom_ext h

/-- If `A` is finite and each `Y ⟶ L.obj X` is finite, then the structured arrow category
`StructuredArrow Y L` has finitely many objects: an object is a pair consisting of an object `X` of
`A` and a morphism `Y ⟶ L.obj X`. -/
private theorem finite_structuredArrow {A : Type*} [Category A] {T : Type*} [Category T]
    (L : A ⥤ T) (Y : T) [Finite A] [∀ X : A, Finite (Y ⟶ L.obj X)] :
    Finite (StructuredArrow Y L) := by
  refine Finite.of_injective (fun f => (⟨f.right, f.hom⟩ : (X : A) × (Y ⟶ L.obj X))) ?_
  rintro ⟨l₁, r₁, w₁⟩ ⟨l₂, r₂, w₂⟩ h
  obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h'
  cases l₁
  cases l₂
  rfl

/-- A morphism of `StructuredArrow Y L` is determined by its component in `A`, so the hom types of
`StructuredArrow Y L` inherit finiteness from those of `A`. -/
private theorem finite_hom_structuredArrow {A : Type*} [Category A] {T : Type*} [Category T]
    (L : A ⥤ T) (Y : T) (X X' : StructuredArrow Y L) [Finite (X.right ⟶ X'.right)] :
    Finite (X ⟶ X') :=
  .of_injective CommaMorphism.right fun _ _ h => StructuredArrow.hom_ext _ _ h

/-- There are only finitely many `k`-truncated simplices, since `⦋j⦌ ↦ j` is injective on them with
values in `{0, …, k}`. -/
public theorem finite_truncated (k : ℕ) : Finite (SimplexCategory.Truncated k) :=
  .of_injective (fun X => (⟨X.obj.len, Nat.lt_succ_of_le X.2⟩ : Fin (k + 1)))
    fun X Y h => by
      obtain ⟨⟨x⟩, hx⟩ := X
      obtain ⟨⟨y⟩, hy⟩ := Y
      simp_all

/-- The shape `(Δ/⦋n⦌)_{≤k}ᵒᵖ = StructuredArrow Y (Δ_{≤k} ⊆ Δ)ᵒᵖ` of the limit formula of
[Stacks, Lemma 0183] is a finite category: its objects are the morphisms `⦋j⦌ ⟶ ⦋n⦌` with `j ≤ k`,
of which there are finitely many, and a morphism between two of them is a morphism of simplices. -/
@[instance_reducible]
private noncomputable def finCategoryStructuredArrow (k : ℕ) (Y : SimplexCategoryᵒᵖ) :
    FinCategory (StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op) :=
  have := finite_truncated k
  have : Finite (SimplexCategory.Truncated k)ᵒᵖ := .of_equiv _ equivToOpposite
  have : ∀ X : (SimplexCategory.Truncated k)ᵒᵖ,
      Finite (Y ⟶ (SimplexCategory.Truncated.inclusion k).op.obj X) := fun _ => finite_hom_op _ _
  have : ∀ a b : (SimplexCategory.Truncated k)ᵒᵖ, Finite (a ⟶ b) := fun a b =>
    have := finite_hom_fullSubcategory b.unop a.unop
    finite_hom_op a b
  { fintypeObj := @Fintype.ofFinite _ (finite_structuredArrow _ Y)
    fintypeHom := fun X X' => @Fintype.ofFinite _ (finite_hom_structuredArrow _ Y X X') }

/-- Every vertex of `⦋n⦌` is an object of `(Δ/⦋n⦌)_{≤k}`, so that category is nonempty. -/
private theorem nonempty_structuredArrow (k : ℕ) (Y : SimplexCategoryᵒᵖ) :
    Nonempty (StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op) :=
  ⟨StructuredArrow.mk (Y := op (⟨⦋0⦌, by simp⟩ : SimplexCategory.Truncated k))
    (SimplexCategory.const ⦋0⦌ Y.unop 0).op⟩

end Finiteness

section Zero

/-- The only `0`-truncated simplex is `⦋0⦌`. -/
private theorem obj_eq_zero (X : SimplexCategory.Truncated 0) : X.obj = ⦋0⦌ := by
  rw [← SimplexCategory.mk_len X.obj, Nat.le_zero.mp X.2]

/-- `Δ_{≤0}` is the terminal category, hence discrete: `⦋0⦌` is its only object, and a morphism of
`Δ` with target `⦋0⦌` is unique. -/
private theorem isDiscrete_truncated_zero : IsDiscrete (SimplexCategory.Truncated 0) := by
  have : Subsingleton (SimplexCategory.Truncated 0) :=
    ⟨fun a b => ObjectProperty.FullSubcategory.ext (by rw [obj_eq_zero a, obj_eq_zero b])⟩
  have : Quiver.IsThin (SimplexCategory.Truncated 0) := fun a b => by
    obtain ⟨b, hb⟩ := b
    obtain rfl : b = ⦋0⦌ := obj_eq_zero ⟨b, hb⟩
    exact ⟨fun f g => InducedCategory.hom_ext (Subsingleton.elim _ _)⟩
  infer_instance

end Zero

variable {C : Type u} [Category.{v} C]

/-- For every `⦋n⦌` the shape `(Δ/⦋n⦌)_{≤0}ᵒᵖ` of the limit formula of [Stacks, Lemma 0183] is
finite, nonempty and discrete — discrete because `Δ_{≤0}` is the terminal category — so a category
with products of pairs of objects has the limits of that shape ([Stacks, Example 0182]). -/
private theorem hasLimitsOfShape_structuredArrow_inclusion_zero [HasBinaryProducts C]
    (Y : SimplexCategoryᵒᵖ) :
    HasLimitsOfShape (StructuredArrow Y (SimplexCategory.Truncated.inclusion 0).op) C :=
  have := finCategoryStructuredArrow 0 Y
  have := nonempty_structuredArrow 0 Y
  have := isDiscrete_truncated_zero
  have := isDiscrete_structuredArrow (SimplexCategory.Truncated.inclusion 0).op Y
  hasLimitsOfShape_of_isDiscrete _

/-- For every `⦋n⦌` the shape `(Δ/⦋n⦌)_{≤k}ᵒᵖ` of the limit formula of [Stacks, Lemma 0183] is a
finite category, and it is connected because `Δ_{≤k} ⊆ Δ` is initial for `k ≥ 1`. -/
private theorem hasLimitsOfShape_structuredArrow_inclusion
    (H : ∀ (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C)
    (k : ℕ) [NeZero k] (Y : SimplexCategoryᵒᵖ) :
    HasLimitsOfShape (StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op) C :=
  have := finCategoryStructuredArrow k Y
  have : IsConnected (StructuredArrow Y (SimplexCategory.Truncated.inclusion k).op) :=
    Functor.Final.out Y
  H _

end Helpers

variable {C : Type u} [Category.{v} C]

/-- Let `C` be a category.

* If `C` has products of pairs of objects, then every `0`-truncated simplicial object `F` of `C`
  admits a pointwise right Kan extension along `(Δ_{≤0} ⊆ Δ)ᵒᵖ`; equivalently `cosk_0` exists, as
  the right adjoint `Truncated.cosk 0` of `sk_0` ([Stacks, Example 0182]).
* If `C` has finite connected limits, then for every `k ≥ 1` every `k`-truncated simplicial object
  `F` of `C` admits a pointwise right Kan extension along `(Δ_{≤k} ⊆ Δ)ᵒᵖ`; equivalently `cosk_k`
  exists. -/
@[stacks 09VS "the two items of the remark, as the two conjuncts; \"cosk_k exists\" is spelled \
  as the existence of the pointwise right Kan extensions along `(Δ_{≤k} ⊆ Δ)ᵒᵖ` that define \
  `Truncated.cosk k`, and each hypothesis is an antecedent of its own item so that item (1) \
  stays a claim about categories with products of pairs alone", sga "4 Vbis 3.0.1" "more general"]
public theorem hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits :
    (HasBinaryProducts C → ∀ F : SimplicialObject.Truncated C 0,
        (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F) ∧
      ((∀ (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C) →
        ∀ (k : ℕ), 0 < k → ∀ F : SimplicialObject.Truncated C k,
          (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F) := by
  refine ⟨fun _ F Y => ?_, fun H k hk F Y => ?_⟩
  · have := hasLimitsOfShape_structuredArrow_inclusion_zero (C := C) Y
    infer_instance
  · have : NeZero k := ⟨hk.ne'⟩
    have := hasLimitsOfShape_structuredArrow_inclusion H k Y
    infer_instance

/-- If `C` has finite limits, every truncated simplicial object has the pointwise right Kan
extension along `( Δ_{≤ k} ⊆ Δ )ᵒᵖ` which defines its `k`-coskeleton. Pointwiseness says that its
value at `[n]` is the limit over the finite structured-arrow category `((Δ/[n])_{≤ k})ᵒᵖ`, and
functoriality supplies the maps induced by `[n] → [n']`. -/
@[stacks 0183 "existence and the displayed limit formula; the formula is the defining universal \
  property of `HasPointwiseRightKanExtension` at each simplex", sga "4 Vbis 3.0.1"]
public theorem hasPointwiseRightKanExtension_of_hasFiniteLimits [HasFiniteLimits C]
    (k : ℕ) (F : SimplicialObject.Truncated C k) :
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F := by
  obtain rfl | k := k
  · exact hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits.1
      inferInstance F
  · exact hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits.2
      (fun _ _ _ _ ↦ inferInstance) (k + 1) (Nat.zero_lt_succ k) F

/-- Let `C` be a category with finite limits and let `U` be an `n`-truncated simplicial object
of `C`. Then the morphism `sk_n cosk_n U → U` is an isomorphism. Here `sk_n` is the truncation
functor `truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n`, its right adjoint
`cosk_n` is the right Kan extension along `(Δ_{≤n} ⊆ Δ)ᵒᵖ`, which exists by [Stacks, Lemma 0183]
(`hasPointwiseRightKanExtension_of_hasFiniteLimits`), and the morphism is the counit at `U` of the
adjunction `ranAdjunction` between them. -/
@[stacks 0185 "`sk_n` is the truncation `truncation n` and the morphism is the counit at `U` of \
  `ranAdjunction`, truncation ⊣ `cosk_n`, whose right Kan extensions exist by Lemma 0183"]
public theorem isIso_ranAdjunction_counit_app_of_hasFiniteLimits [HasFiniteLimits C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) :
    haveI := hasPointwiseRightKanExtension_of_hasFiniteLimits (C := C) n
    IsIso (((SimplexCategory.Truncated.inclusion n).op.ranAdjunction C).counit.app U) :=
  have := hasPointwiseRightKanExtension_of_hasFiniteLimits (C := C) n
  inferInstance

end CategoryTheory.SimplicialObject.Truncated

end
