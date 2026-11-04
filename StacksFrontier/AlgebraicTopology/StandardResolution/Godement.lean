module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Basic

/-!
# Preparation for standard resolutions

Let `C` be a category, let `Y : C ⥤ C` be an endofunctor and suppose given transformations of
functors `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`, subject to no compatibility whatsoever. Writing `Y^n`
for the `n`-fold composite, put `X_n = Y^{n+1}` for `n ≥ 0` and `X_{-1} = Y^0 = 𝟭 C`. Whiskering
`d`, resp. `s`, into the `j`-th factor of `X_n`, counted from the left, produces
`d^n_j = 1_{X_{j-1}} ⋆ d ⋆ 1_{X_{n-j-1}} : X_n ⟶ X_{n-1}` and
`s^n_j = 1_{X_{j-1}} ⋆ s ⋆ 1_{X_{n-j-1}} : X_n ⟶ X_{n+1}` for `0 ≤ j ≤ n`, where `⋆` is horizontal
composition. These are the faces and degeneracies of Godement's system.

As soon as `d` and `s` satisfy the counit identities `1_Y = (d ⋆ 1_Y) ∘ s = (1_Y ⋆ d) ∘ s` and
coassociativity `(s ⋆ 1_Y) ∘ s = (1_Y ⋆ s) ∘ s` — that is, as soon as `(Y, d, s)` is a comonad on
`C` — the system `(X_n, d^n_j, s^n_j)` is a simplicial object of the category `C ⥤ C` of
endofunctors of `C`, augmented over the constant simplicial object `𝟭 C` by `d : X_0 = Y ⟶ 𝟭 C`.
Applying `G ∘ - ∘ F` termwise, for functors `F : A ⥤ C` and `G : C ⥤ B`, gives the augmented
simplicial object `G ∘ X ∘ F` of `A ⥤ B` over `G ∘ F`.

Two homotopy statements about that system follow. First, an augmentation split in degree `0` is
split: a morphism `h₀ : X.right ⟶ X_0` with `ε_0 ∘ h₀ = 1` extends, in exactly one way, to a
morphism of simplicial objects `h : const X.right ⟶ X.left` with `ε ∘ h = 1`, necessarily
`h_n = u_n ∘ h₀` for `u_n : X_0 ⟶ X_n` the image of the unique morphism `⦋n⦌ ⟶ ⦋0⦌`. Second, for
two morphisms `(a_n) : G ∘ X ⟶ G' ∘ X` and `(b_n) : X ∘ F ⟶ X ∘ F'` of simplicial objects
compatible via the augmentations with `a : G ⟶ G'` and `b : F ⟶ F'`, the two horizontal composites
`a ⋆ (b_n)` and `(a_n) ⋆ b` are homotopic, by the family `h_{n, i} = a_{i-1} ⋆ b_{n-i}`; the
special case of the two whiskerings of an endomorphism `f : 𝟭 C ⟶ 𝟭 C` of the identity functor onto
`X` is recorded separately.

## Main definitions

* `CategoryTheory.Functor.iterate`: the `n`-fold composite `Y.iterate n = Y ∘ … ∘ Y` of an
  endofunctor with itself, with `Y.iterate 0 = 𝟭 C`. The `X_n` above is `Y.iterate (n + 1)` and
  `X_{-1}` is `Y.iterate 0`.
* `CategoryTheory.Godement.face`: the transformation `face d n j = d^n_j : X_n ⟶ X_{n-1}`, for
  `n ≥ 0` and `j : Fin (n + 1)`, i.e. `0 ≤ j ≤ n`.
* `CategoryTheory.Godement.degeneracy`: the transformation
  `degeneracy s n j = s^n_j : X_n ⟶ X_{n+1}`, for `n ≥ 0` and `j : Fin (n + 1)`.

## Main results

* `CategoryTheory.Functor.iterate_add_of_rec`: additivity, `X (m + n) = X m ⋙ X n`, of any family
  `X : ℕ → C ⥤ C` presented by the recursion `X 0 = 𝟭 C` and `X (n + 1) = X n ⋙ Y`.
* `CategoryTheory.Functor.iterate_add`: the observation `X_{n+m+1} = X_n ∘ X_m`, in the form
  `Y.iterate (m + n) = Y.iterate m ⋙ Y.iterate n`.
* `CategoryTheory.Godement.exists_augmented_standardResolution`: under the counit and
  coassociativity identities there is an augmented simplicial object of `C ⥤ C` whose terms are
  the powers `Y.iterate (n + 1)`, whose faces and degeneracies are `Godement.face d` and
  `Godement.degeneracy s`, and whose augmentation is `d`.
* `CategoryTheory.Godement.exists_augmented_standardResolution_whisker`: the same for the
  conjugated powers `F ⋙ Y.iterate (n + 1) ⋙ G`, augmented over `F ⋙ G`.
* `CategoryTheory.SimplicialObject.Augmented.exists_section_of_comp_hom_app_zero_eq_id`: a
  morphism `h₀ : X.right ⟶ X.left _⦋0⦌` with `h₀ ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right` extends to a
  morphism of simplicial objects `h : (SimplicialObject.const D).obj X.right ⟶ X.left` with
  `h.app (op ⦋0⦌) = h₀` and `h ≫ X.hom = 𝟙`.

The two horizontal composites of maps into and out of this resolution, and the two whiskerings of
an endomorphism of the identity functor, are in
`StacksFrontier.AlgebraicTopology.StandardResolution.Whiskering`.

## References

* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
* [Stacks Project, Tag 0G5N](https://stacks.math.columbia.edu/tag/0G5N)
* [Stacks Project, Tag 0G5P](https://stacks.math.columbia.edu/tag/0G5P)
* [Stacks Project, Tag 0G5Q](https://stacks.math.columbia.edu/tag/0G5Q)
* [Stacks Project, Tag 003D](https://stacks.math.columbia.edu/tag/003D)
* [Stacks Project, Tag 003F](https://stacks.math.columbia.edu/tag/003F)
* [Stacks Project, Tag 016B](https://stacks.math.columbia.edu/tag/016B)
* [Stacks Project, Tag 019L](https://stacks.math.columbia.edu/tag/019L)
* [Stacks Project, Tag 019M](https://stacks.math.columbia.edu/tag/019M)
* [Godement, *Topologie algébrique et théorie des faisceaux*, Appendice 1]
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v' u' v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- **Stacks 0G5M**.
The `n`-fold composite `Y ∘ … ∘ Y` of an endofunctor `Y : C ⥤ C` with itself, with
`Y.iterate 0 = 𝟭 C` and `Y.iterate (n + 1) = Y.iterate n ⋙ Y`, so that the copy of `Y` added at
each step is the outermost one. On objects it is the `n`-fold iterate of `Y.obj`, whence the name.
Godement's `X_n`, a composite of `n + 1` copies of `Y`, is `Y.iterate (n + 1)`, and his `X_{-1}` is
`Y.iterate 0`. -/
@[stacks 0G5M]
public def iterate (Y : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => Y.iterate n ⋙ Y

attribute [implicit_reducible] iterate

/-- A family of endofunctors presented by the recursion `X 0 = 𝟭 C` and `X (n + 1) = X n ⋙ Y` is
additive: `X (m + n) = X m ⋙ X n`. The powers of `Y` are such a family, and for them this is the
observation `X_{n+m+1} = X_n ∘ X_m`; nothing about `X` beyond the two clauses of the recursion is
used. -/
public theorem iterate_add_of_rec (Y : C ⥤ C) (X : ℕ → C ⥤ C) (h0 : X 0 = 𝟭 C)
    (hs : ∀ n, X (n + 1) = X n ⋙ Y) (m n : ℕ) :
    X (m + n) = X m ⋙ X n := by
  induction n with
  | zero => rw [Nat.add_zero, h0, Functor.comp_id]
  | succ n ih =>
      rw [← Nat.add_assoc, hs (m + n), ih, hs n, Functor.assoc]

/-- **Stacks 0G5M**.
The powers of an endofunctor are additive: `Y^{m+n} = Y^m ∘ Y^n` in `⋙`-order, i.e.
`Y.iterate (m + n) = Y.iterate m ⋙ Y.iterate n`. This is the observation `X_{n+m+1} = X_n ∘ X_m`,
where `X_n = Y.iterate (n + 1)`. -/
@[stacks 0G5M]
public theorem iterate_add (Y : C ⥤ C) (m n : ℕ) :
    Y.iterate (m + n) = Y.iterate m ⋙ Y.iterate n :=
  iterate_add_of_rec Y Y.iterate rfl (fun _ => rfl) m n

end CategoryTheory.Functor

namespace CategoryTheory.Godement

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- **Stacks 0G5M**.
The face `d^n_j : X_n ⟶ X_{n-1}` attached to a transformation `d : Y ⟶ 𝟭 C`, for `n ≥ 0` and
`0 ≤ j ≤ n`: it whiskers `d` into the `j`-th of the `n + 1` copies of `Y` in
`X_n = Y.iterate (n + 1)`, counted from the left, i.e. from the outside, so that
`d^n_j = 1_{X_{j-1}} ⋆ d ⋆ 1_{X_{n-j-1}}`. It is defined by the recursion `d^n_0 = d ⋆ 1_{X_{n-1}}`
and `d^{n+1}_{j+1} = 1_Y ⋆ d^n_j`; in particular `face d 0 0 = d : X_0 = Y ⟶ 𝟭 C` is the
augmentation. No compatibility between `d` and a comultiplication is assumed. -/
@[stacks 0G5M]
public def face (d : Y ⟶ 𝟭 C) :
    (n : ℕ) → Fin (n + 1) → (Y.iterate (n + 1) ⟶ Y.iterate n)
  | 0, _ => Functor.whiskerLeft (Y.iterate 0) d
  | n + 1, j =>
      Fin.cases (Functor.whiskerLeft (Y.iterate (n + 1)) d)
        (fun i => Functor.whiskerRight (face d n i) Y) j

/-- **Stacks 0G5M**.
The degeneracy `s^n_j : X_n ⟶ X_{n+1}` attached to a transformation `s : Y ⟶ Y ⋙ Y`, for `n ≥ 0`
and `0 ≤ j ≤ n`: it whiskers `s` into the `j`-th of the `n + 1` copies of `Y` in
`X_n = Y.iterate (n + 1)`, counted from the left, i.e. from the outside, so that
`s^n_j = 1_{X_{j-1}} ⋆ s ⋆ 1_{X_{n-j-1}}`. It is defined by the recursion `s^n_0 = s ⋆ 1_{X_{n-1}}`
and `s^{n+1}_{j+1} = 1_Y ⋆ s^n_j`. No compatibility between `s` and a counit is assumed. -/
@[stacks 0G5M]
public def degeneracy (s : Y ⟶ Y ⋙ Y) :
    (n : ℕ) → Fin (n + 1) → (Y.iterate (n + 1) ⟶ Y.iterate (n + 2))
  | 0, _ => Functor.whiskerLeft (Y.iterate 0) s
  | n + 1, j =>
      Fin.cases (Functor.whiskerLeft (Y.iterate (n + 1)) s)
        (fun i => Functor.whiskerRight (degeneracy s n i) Y) j

end CategoryTheory.Godement

open Simplicial

/-! ### The defining clauses of the faces and degeneracies -/

section Clauses

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- The first defining clause of `Godement.face`: `d^n_0` whiskers `d` into the outermost factor of
`X_n = Y^{n+1}`. -/
public lemma CategoryTheory.Godement.Prep.face_zero (d : Y ⟶ 𝟭 C) (n : ℕ) :
    Godement.face d n 0 = Functor.whiskerLeft (Y.iterate n) d := by
  cases n <;> rfl

/-- The second defining clause of `Godement.face`: `d^{n+1}_{j+1}` is `d^n_j` whiskered with `Y` on
the outside. -/
public lemma CategoryTheory.Godement.Prep.face_succ (d : Y ⟶ 𝟭 C) (n : ℕ) (j : Fin (n + 1)) :
    Godement.face d (n + 1) j.succ = Functor.whiskerRight (Godement.face d n j) Y :=
  rfl

/-- The first defining clause of `Godement.degeneracy`. -/
public lemma CategoryTheory.Godement.Prep.degeneracy_zero (s : Y ⟶ Y ⋙ Y) (n : ℕ) :
    Godement.degeneracy s n 0 = Functor.whiskerLeft (Y.iterate n) s := by
  cases n <;> rfl

/-- The second defining clause of `Godement.degeneracy`. -/
public lemma CategoryTheory.Godement.Prep.degeneracy_succ (s : Y ⟶ Y ⋙ Y) (n : ℕ)
    (j : Fin (n + 1)) :
    Godement.degeneracy s (n + 1) j.succ = Functor.whiskerRight (Godement.degeneracy s n j) Y :=
  rfl

/-- Two composites of transformations whiskered with `Y` on the outside agree as soon as the
composites do. -/
public lemma CategoryTheory.Godement.Prep.whiskerRight_comp_congr {F G H G' : C ⥤ C}
    {a : F ⟶ G} {b : G ⟶ H} {a' : F ⟶ G'}
    {b' : G' ⟶ H} (h : a ≫ b = a' ≫ b') :
    Functor.whiskerRight a Y ≫ Functor.whiskerRight b Y
      = Functor.whiskerRight a' Y ≫ Functor.whiskerRight b' Y := by
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, h]

end Clauses

/-! ### Transport along a functor, and homotopies from the relations of a family -/

section Generalities

/-- A functor preserves pinning: if `g` is pinned to `f` by `eqToHom` on both sides, then `W.map g`
is pinned to `W.map f` by the `W.obj`-images of the same two equalities. -/
public theorem CategoryTheory.Godement.Prep.map_eq_eqToHom_comp {D : Type*} [Category D]
    {E : Type*} [Category E]
    (W : D ⥤ E) {x y z w : D} {g : x ⟶ w} {h₁ : x = y} {f : y ⟶ z} {h₂ : z = w}
    (hg : g = eqToHom h₁ ≫ f ≫ eqToHom h₂) :
    W.map g = eqToHom (congrArg W.obj h₁) ≫ W.map f ≫ eqToHom (congrArg W.obj h₂) := by
  subst hg; subst h₁; subst h₂; simp

variable {D : Type u'} [Category.{v'} D] {Z W : SimplicialObject D}

/-- A family `Hb n i : Z_n ⟶ W_n`, `i = 0, …, n + 1`, whose ends are the two given morphisms and
which satisfies the five relations of a simplicial homotopy, is a simplicial homotopy from `a` to
`b`. Mathlib's datum is the family `h_{n + 1, i + 1} ∘ s^n_i : Z_n ⟶ W_{n + 1}`. -/
public def CategoryTheory.Godement.Prep.homotopyOfRel (a b : Z ⟶ W)
    (Hb : (n : ℕ) → Fin (n + 2) → (Z.obj (op ⦋n⦌) ⟶ W.obj (op ⦋n⦌)))
    (r_zero : ∀ n : ℕ, Hb n 0 = b.app (op ⦋n⦌))
    (r_last : ∀ n : ℕ, Hb n (Fin.last (n + 1)) = a.app (op ⦋n⦌))
    (r_face_gt : ∀ (n : ℕ) (j i : Fin (n + 2)), j ≤ i →
      Hb (n + 1) i.succ ≫ W.δ j = Z.δ j ≫ Hb n i)
    (r_face_le : ∀ (n : ℕ) (j i : Fin (n + 2)), i ≤ j →
      Hb (n + 1) i.castSucc ≫ W.δ j = Z.δ j ≫ Hb n i)
    (r_deg_gt : ∀ (n : ℕ) (j i : Fin (n + 1)), j ≤ i →
      Hb n i.succ ≫ W.σ j = Z.σ j ≫ Hb (n + 1) i.succ.succ)
    (r_deg_le : ∀ (n : ℕ) (j i : Fin (n + 1)), i ≤ j →
      Hb n i.castSucc ≫ W.σ j = Z.σ j ≫ Hb (n + 1) i.castSucc.castSucc) :
    SimplicialObject.Homotopy a b where
  h {n} i := Z.σ i ≫ Hb (n + 1) i.castSucc.succ
  h_zero_comp_δ_zero n := by
    have h2 : Z.σ (0 : Fin (n + 1)) ≫ Z.δ 0 = 𝟙 _ := by
      simpa using Z.δ_comp_σ_self (i := (0 : Fin (n + 1)))
    rw [Fin.castSucc_zero, Category.assoc, r_face_gt n 0 0 le_rfl, ← Category.assoc, h2,
      Category.id_comp, r_zero]
  h_last_comp_δ_last n := by
    have h2 : Z.σ (Fin.last n) ≫ Z.δ (Fin.last (n + 1)) = 𝟙 _ := by
      simpa using Z.δ_comp_σ_succ (i := Fin.last n)
    rw [Fin.succ_castSucc, Fin.succ_last, Category.assoc,
      r_face_le n (Fin.last (n + 1)) (Fin.last (n + 1)) le_rfl, ← Category.assoc, h2,
      Category.id_comp, r_last]
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    rw [Category.assoc, r_face_gt (n + 1) i.castSucc j.succ.castSucc
        (by grind),
      ← Category.assoc, Z.δ_comp_σ_of_le hij, Category.assoc, Fin.succ_castSucc]
  h_succ_comp_δ_castSucc_succ {n} j := by
    have h3 : Z.σ j.succ ≫ Z.δ j.castSucc.succ = 𝟙 _ := by
      rw [Fin.succ_castSucc]; exact Z.δ_comp_σ_self
    rw [Category.assoc, r_face_gt (n + 1) j.castSucc.succ j.succ.castSucc
        (le_of_eq (Fin.succ_castSucc j)), ← Category.assoc, h3, Category.id_comp,
      Category.assoc, Fin.succ_castSucc j.castSucc,
      r_face_le (n + 1) j.castSucc.succ j.castSucc.succ le_rfl, ← Category.assoc,
      Z.δ_comp_σ_succ, Category.id_comp, Fin.succ_castSucc]
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    rw [Category.assoc, Fin.succ_castSucc j.castSucc, r_face_le (n + 1) i.succ j.castSucc.succ
        (by grind),
      ← Category.assoc, Z.δ_comp_σ_of_gt hji, Category.assoc]
  h_comp_σ_castSucc_of_le {n} i j hij := by
    rw [Category.assoc, r_deg_gt (n + 1) i.castSucc j.castSucc
        (by simpa only [Fin.le_def, Fin.val_castSucc] using hij),
      ← Category.assoc, Z.σ_comp_σ hij, Category.assoc, Fin.succ_castSucc]
  h_comp_σ_succ_of_lt {n} i j hji := by
    rw [Category.assoc, Fin.succ_castSucc, r_deg_le (n + 1) i.succ j.succ
        (by grind),
      ← Category.assoc, ← Z.σ_comp_σ hji, Category.assoc,
      Fin.succ_castSucc j.castSucc, Fin.succ_castSucc j]

end Generalities

open CategoryTheory.Godement.Prep

/-! ### Godement's system of powers is an augmented simplicial endofunctor -/

section Simplicial

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- The recursion defining `Godement.face` and `Godement.degeneracy`, as an induction principle: a
property of a degree `n` and an index `i : Fin (n + 1)` which holds when `i = 0` and passes from
`(n, i)` to `(n + 1, i.succ)` holds always. It is `Fin.succRec` reindexed, so that `i` is an index
of `Godement.face _ n`. -/
private theorem succ_induction {P : (n : ℕ) → Fin (n + 1) → Prop} (h0 : ∀ n, P n 0)
    (hs : ∀ n i, P n i → P (n + 1) i.succ) (n : ℕ) (i : Fin (n + 1)) : P n i := by
  induction n with
  | zero => exact Fin.cases (h0 0) (fun i => i.elim0) i
  | succ n ih => exact Fin.cases (h0 (n + 1)) (fun i => hs n i (ih i)) i

/-- The same induction for an index `i : Fin (n + 2)`, one degree higher: there the index can be a
successor already in degree `0`, so that case is a hypothesis of its own. -/
private theorem succ_induction' {P : (n : ℕ) → Fin (n + 2) → Prop} (h0 : ∀ n, P n 0)
    (h1 : ∀ i : Fin 1, P 0 i.succ) (hs : ∀ n i, P n i → P (n + 1) i.succ)
    (n : ℕ) (i : Fin (n + 2)) : P n i := by
  induction n with
  | zero => exact Fin.cases (h0 0) h1 i
  | succ n ih => exact Fin.cases (h0 (n + 1)) (fun i => hs n i (ih i)) i

/-- A composite which is the identity stays the identity after whiskering with `Y`. -/
private lemma whiskerRight_comp_eq_id {F G : C ⥤ C} {a : F ⟶ G} {b : G ⟶ F} (h : a ≫ b = 𝟙 F) :
    Functor.whiskerRight a Y ≫ Functor.whiskerRight b Y = 𝟙 (F ⋙ Y) := by
  rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_id']

variable (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)

/-- The outermost face commutes past any transformation whiskered into the inner factors: this is
the interchange law for `d`. -/
private lemma whiskerRight_comp_face_zero {m n : ℕ} (α : Y.iterate m ⟶ Y.iterate n) :
    Functor.whiskerRight α Y ≫ Godement.face d n 0 = Godement.face d m 0 ≫ α := by
  rw [face_zero, face_zero]
  exact (Functor.whiskerLeft_comp_whiskerRight α d).symm

/-- The outermost degeneracy commutes past any transformation whiskered into the inner factors: the
interchange law for `s`. -/
private lemma whiskerRight_comp_degeneracy_zero {m n : ℕ} (α : Y.iterate m ⟶ Y.iterate n) :
    Functor.whiskerRight α Y ≫ Godement.degeneracy s n 0
      = Godement.degeneracy s m 0 ≫ Functor.whiskerRight (Functor.whiskerRight α Y) Y := by
  rw [degeneracy_zero, degeneracy_zero]
  exact (Functor.whiskerLeft_comp_whiskerRight α s).symm

variable {d s}

/-- The counit identities, whiskered with a power of `Y` on the inside, give the identity. -/
private lemma whiskerLeft_comp_eq_id (K : C ⥤ C) {F G : C ⥤ C} {a : F ⟶ G} {b : G ⟶ F}
    (h : a ≫ b = 𝟙 F) : Functor.whiskerLeft K a ≫ Functor.whiskerLeft K b = 𝟙 (K ⋙ F) := by
  rw [← Functor.whiskerLeft_comp, h, Functor.whiskerLeft_id']

/-- The first counit identity, whiskered with a power of `Y`: `d^{n+1}_0 ∘ s^n_0 = id`. -/
private lemma degeneracy_zero_comp_face_zero (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
    (n : ℕ) : Godement.degeneracy s n 0 ≫ Godement.face d (n + 1) 0 = 𝟙 (Y.iterate (n + 1)) := by
  rw [degeneracy_zero, face_zero]
  exact whiskerLeft_comp_eq_id _ left_counit

/-- The second counit identity, whiskered with a power of `Y`: `d^{n+1}_1 ∘ s^n_0 = id`. -/
private lemma degeneracy_zero_comp_face_one (right_counit : s ≫ Functor.whiskerRight d Y = 𝟙 Y)
    (n : ℕ) : Godement.degeneracy s n 0 ≫ Godement.face d (n + 1) (0 : Fin (n + 1)).succ
      = 𝟙 (Y.iterate (n + 1)) := by
  rw [degeneracy_zero, face_succ, face_zero]
  exact whiskerLeft_comp_eq_id _ right_counit

variable (d s)

/-- The first simplicial identity for Godement's system: it holds for arbitrary `d`. -/
private lemma face_comp_face (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    Godement.face d (n + 1) j.succ ≫ Godement.face d n i
      = Godement.face d (n + 1) i.castSucc ≫ Godement.face d n j := by
  induction n, i using succ_induction with
  | h0 n => rw [face_succ, Fin.castSucc_zero]; exact whiskerRight_comp_face_zero d _
  | hs n i ih =>
      cases j using Fin.cases with
      | zero => simp at h
      | succ j => exact whiskerRight_comp_congr (ih j (by simpa using h))

/-- The mixed simplicial identity for an index below the degeneracy: it holds for arbitrary `d` and
`s`. -/
private lemma degeneracy_comp_face_of_le (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) :
    Godement.degeneracy s (n + 1) j.succ ≫ Godement.face d (n + 2) i.castSucc
      = Godement.face d (n + 1) i ≫ Godement.degeneracy s n j := by
  induction n, i using succ_induction' with
  | h0 n => rw [degeneracy_succ, Fin.castSucc_zero]; exact whiskerRight_comp_face_zero d _
  | h1 i => grind
  | hs n i ih =>
      cases j using Fin.cases with
      | zero => simp at h
      | succ j =>
          refine whiskerRight_comp_congr (ih j ?_)
          grind

/-- A face cancels the degeneracy of the same index: this is the first counit identity, whiskered
up. -/
private lemma degeneracy_comp_face_self (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
    (n : ℕ) (i : Fin (n + 1)) :
    Godement.degeneracy s n i ≫ Godement.face d (n + 1) i.castSucc = 𝟙 (Y.iterate (n + 1)) := by
  induction n, i using succ_induction with
  | h0 n => rw [Fin.castSucc_zero]; exact degeneracy_zero_comp_face_zero left_counit n
  | hs n i ih => exact whiskerRight_comp_eq_id ih

/-- A face cancels the degeneracy of the preceding index: this is the second counit identity,
whiskered up. -/
private lemma degeneracy_comp_face_succ (right_counit : s ≫ Functor.whiskerRight d Y = 𝟙 Y)
    (n : ℕ) (i : Fin (n + 1)) :
    Godement.degeneracy s n i ≫ Godement.face d (n + 1) i.succ = 𝟙 (Y.iterate (n + 1)) := by
  induction n, i using succ_induction with
  | h0 n => exact degeneracy_zero_comp_face_one right_counit n
  | hs n i ih => exact whiskerRight_comp_eq_id ih

/-- The mixed simplicial identity for an index above the degeneracy: it holds for arbitrary `d` and
`s`. -/
private lemma degeneracy_comp_face_of_gt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) :
    Godement.degeneracy s (n + 1) j.castSucc ≫ Godement.face d (n + 2) i.succ
      = Godement.face d (n + 1) i ≫ Godement.degeneracy s n j := by
  induction n, j using succ_induction with
  | h0 n =>
      cases i using Fin.cases with
      | zero => simp at h
      | succ i =>
          rw [Fin.castSucc_zero, face_succ, face_succ]
          exact (whiskerRight_comp_degeneracy_zero s (Godement.face d n i)).symm
  | hs n j ih =>
      cases i using Fin.cases with
      | zero => simp at h
      | succ i =>
          refine whiskerRight_comp_congr (ih i ?_)
          grind

/-- The degeneracy identity when the smaller index is `0`: the relation is coassociativity
whiskered with a power of `Y` when both indices vanish, and the interchange law for `s`
otherwise. -/
private lemma degeneracy_comp_degeneracy_zero
    (coassoc : s ≫ Functor.whiskerLeft Y s = s ≫ Functor.whiskerRight s Y) (n : ℕ)
    (j : Fin (n + 1)) :
    Godement.degeneracy s n j ≫ Godement.degeneracy s (n + 1) 0
      = Godement.degeneracy s n 0 ≫ Godement.degeneracy s (n + 1) j.succ := by
  induction n, j using succ_induction with
  | h0 n =>
      have e : Functor.whiskerLeft (Y.iterate n) s
            ≫ Functor.whiskerLeft (Y.iterate n) (Functor.whiskerLeft Y s)
          = Functor.whiskerLeft (Y.iterate n) s
            ≫ Functor.whiskerLeft (Y.iterate n) (Functor.whiskerRight s Y) := by
        rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, coassoc]
      rw [degeneracy_zero, degeneracy_zero, degeneracy_succ, degeneracy_zero]
      exact e
  | hs n j _ =>
      rw [degeneracy_succ]
      exact whiskerRight_comp_degeneracy_zero s (Godement.degeneracy s n j)

/-- The degeneracy identity. -/
private lemma degeneracy_comp_degeneracy
    (coassoc : s ≫ Functor.whiskerLeft Y s = s ≫ Functor.whiskerRight s Y) (n : ℕ)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    Godement.degeneracy s n j ≫ Godement.degeneracy s (n + 1) i.castSucc
      = Godement.degeneracy s n i ≫ Godement.degeneracy s (n + 1) j.succ := by
  induction n, i using succ_induction with
  | h0 n => rw [Fin.castSucc_zero]; exact degeneracy_comp_degeneracy_zero s coassoc n j
  | hs n i ih =>
      cases j using Fin.cases with
      | zero => simp at h
      | succ j => exact whiskerRight_comp_congr (ih j (by simpa using h))

end Simplicial

section Augmentation

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- The `n`-fold horizontal power `aug d n = d ⋆ … ⋆ d : Y^n ⟶ 𝟭 C` of `d : Y ⟶ 𝟭 C`, defined by
`aug d 0 = 𝟙` and `aug d (n + 1) = d^n_0 ∘ aug d n`, so that it is the outermost face which
shortens it. The augmentation of `X_n = Y^{n+1}` is `aug d (n + 1)`. -/
private def aug (d : Y ⟶ 𝟭 C) : (n : ℕ) → (Y.iterate n ⟶ 𝟭 C) :=
  Nat.rec (motive := fun n => Y.iterate n ⟶ 𝟭 C) (𝟙 (𝟭 C))
    fun n a => Godement.face d n 0 ≫ a

variable (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)

/-- The empty power is the identity. -/
private lemma aug_zero : aug d 0 = 𝟙 (𝟭 C) := rfl

/-- The outermost face shortens the augmentation. -/
private lemma aug_succ (n : ℕ) : aug d (n + 1) = Godement.face d n 0 ≫ aug d n := rfl

/-- A transformation whiskered with `Y` on the outside is compatible with the augmentation as soon
as it is compatible one degree lower. -/
private lemma whiskerRight_comp_aug {m n : ℕ} (α : Y.iterate m ⟶ Y.iterate n)
    (h : α ≫ aug d n = aug d m) :
    Functor.whiskerRight α Y ≫ aug d (n + 1) = aug d (m + 1) := by
  have key : (Functor.whiskerRight α Y ≫ Godement.face d n 0) ≫ aug d n = aug d (m + 1) :=
    (congrArg (· ≫ aug d n) (whiskerRight_comp_face_zero d α)).trans
      ((Category.assoc _ _ _).trans (congrArg (Godement.face d m 0 ≫ ·) h))
  exact (Category.assoc _ _ _).symm.trans key

/-- Every face is compatible with the augmentation: `(d ⋆ … ⋆ d) ∘ d^n_i = d ⋆ … ⋆ d`. -/
private lemma face_comp_aug (n : ℕ) (i : Fin (n + 1)) :
    Godement.face d n i ≫ aug d n = aug d (n + 1) := by
  induction n, i using succ_induction with
  | h0 n => exact (aug_succ d n).symm
  | hs n i ih => exact whiskerRight_comp_aug d _ ih

variable {d s}

/-- Every degeneracy is compatible with the augmentation: `(d ⋆ … ⋆ d) ∘ s^n_i = d ⋆ … ⋆ d`. In the
outermost degree this is the first counit identity. -/
private lemma degeneracy_comp_aug (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
    (n : ℕ) (i : Fin (n + 1)) : Godement.degeneracy s n i ≫ aug d (n + 2) = aug d (n + 1) := by
  induction n, i using succ_induction with
  | h0 n =>
      rw [aug_succ, ← Category.assoc, degeneracy_zero_comp_face_zero left_counit,
        Category.id_comp]
  | hs n i ih => exact whiskerRight_comp_aug d _ ih

end Augmentation

section Presentation

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
  (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
  (right_counit : s ≫ Functor.whiskerRight d Y = 𝟙 Y)
  (coassoc : s ≫ Functor.whiskerLeft Y s = s ≫ Functor.whiskerRight s Y)

/-- The lift of a prefunctor to the path category, on a generator. -/
private lemma lift_of_map {V : Type*} [Quiver V] {D : Type*} [Category D] (φ : V ⥤q D)
    {a b : V} (f : a ⟶ b) : (Paths.lift φ).map ((Paths.of V).map f) = φ.map f :=
  Paths.lift_toPath φ f

/-- The lift of a prefunctor to the path category, on a two-step path. -/
private lemma lift_of_map_comp {V : Type*} [Quiver V] {D : Type*} [Category D] (φ : V ⥤q D)
    {a b c : V} (f : a ⟶ b) (g : b ⟶ c) :
    (Paths.lift φ).map ((Paths.of V).map f ≫ (Paths.of V).map g) = φ.map f ≫ φ.map g := by
  rw [Functor.map_comp, lift_of_map, lift_of_map]
  rfl

/-- Godement's system as a prefunctor on the quiver of generators of the simplex category, in the
category of structured arrows over the constant `𝟭 C`: the object at `n` is `X_n = Y^{n+1}`
together with its augmentation `d ⋆ … ⋆ d`, the generator `δ i` acts by `d^n_i` and the generator
`σ i` by `s^n_i`. -/
private def augPrefunctor :
    FreeSimplexQuiver ⥤q StructuredArrow (op (𝟭 C)) (𝟭 ((C ⥤ C)ᵒᵖ)) where
  obj n := StructuredArrow.mk (aug d (n.len + 1)).op
  map {a b} f :=
    match f with
    | FreeSimplexQuiver.Hom.δ (n := n) i =>
        StructuredArrow.homMk (Godement.face d (n + 1) i).op
          (congrArg Quiver.Hom.op (face_comp_aug d (n + 1) i))
    | FreeSimplexQuiver.Hom.σ (n := n) i =>
        StructuredArrow.homMk (Godement.degeneracy s n i).op
          (congrArg Quiver.Hom.op (degeneracy_comp_aug left_counit n i))

/-- Godement's system as a functor out of the category presented by the generators `δ i`, `σ i` and
the simplicial identities, in the category of structured arrows over the constant `𝟭 C`. -/
private def augFunctor :
    SimplexCategoryGenRel ⥤ StructuredArrow (op (𝟭 C)) (𝟭 ((C ⥤ C)ᵒᵖ)) :=
  CategoryTheory.Quotient.lift _ (Paths.lift (augPrefunctor d s left_counit)) (by
    have ext {x y : StructuredArrow (op (𝟭 C)) (𝟭 ((C ⥤ C)ᵒᵖ))} {f g : x ⟶ y}
        (h : f.right.unop = g.right.unop) : f = g :=
      StructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj h)
    intro a b f₁ f₂ hr
    cases hr with
    | δ_comp_δ H =>
        rw [lift_of_map_comp, lift_of_map_comp]
        exact ext (face_comp_face d _ _ _ H)
    | δ_comp_σ_of_le H =>
        rw [lift_of_map_comp, lift_of_map_comp]
        exact ext (degeneracy_comp_face_of_le d s _ _ _ H)
    | δ_comp_σ_self =>
        rw [lift_of_map_comp, CategoryTheory.Functor.map_id]
        exact ext (degeneracy_comp_face_self d s left_counit _ _)
    | δ_comp_σ_succ =>
        rw [lift_of_map_comp, CategoryTheory.Functor.map_id]
        exact ext (degeneracy_comp_face_succ d s right_counit _ _)
    | δ_comp_σ_of_gt H =>
        rw [lift_of_map_comp, lift_of_map_comp]
        exact ext (degeneracy_comp_face_of_gt d s _ _ _ H)
    | σ_comp_σ H =>
        rw [lift_of_map_comp, lift_of_map_comp]
        exact ext (degeneracy_comp_degeneracy s coassoc _ _ _ H))

/-- Godement's system as a functor out of the presented category. -/
private def stdFunctor : SimplexCategoryGenRel ⥤ (C ⥤ C)ᵒᵖ :=
  augFunctor d s left_counit right_counit coassoc ⋙
    StructuredArrow.proj (op (𝟭 C)) (𝟭 ((C ⥤ C)ᵒᵖ))

private lemma stdFunctor_map_δ (n : ℕ) (i : Fin (n + 2)) :
    (stdFunctor d s left_counit right_counit coassoc).map (SimplexCategoryGenRel.δ i)
      = (Godement.face d (n + 1) i).op :=
  congrArg CommaMorphism.right
    (lift_of_map (augPrefunctor d s left_counit) (FreeSimplexQuiver.Hom.δ i))

private lemma stdFunctor_map_σ (n : ℕ) (i : Fin (n + 1)) :
    (stdFunctor d s left_counit right_counit coassoc).map (SimplexCategoryGenRel.σ i)
      = (Godement.degeneracy s n i).op :=
  congrArg CommaMorphism.right
    (lift_of_map (augPrefunctor d s left_counit) (FreeSimplexQuiver.Hom.σ i))

private lemma stdFunctor_leftOp_map_δ (n : ℕ) (i : Fin (n + 2)) :
    (stdFunctor d s left_counit right_counit coassoc).leftOp.map (SimplexCategoryGenRel.δ i).op
      = Godement.face d (n + 1) i :=
  congrArg Quiver.Hom.unop (stdFunctor_map_δ d s left_counit right_counit coassoc n i)

private lemma stdFunctor_leftOp_map_σ (n : ℕ) (i : Fin (n + 1)) :
    (stdFunctor d s left_counit right_counit coassoc).leftOp.map (SimplexCategoryGenRel.σ i).op
      = Godement.degeneracy s n i :=
  congrArg Quiver.Hom.unop (stdFunctor_map_σ d s left_counit right_counit coassoc n i)

/-- The augmentation of Godement's system, as a transformation from the constant functor. -/
private def augTrans :
    (Functor.const SimplexCategoryGenRel).obj (op (𝟭 C)) ⟶
      stdFunctor d s left_counit right_counit coassoc where
  app x := ((augFunctor d s left_counit right_counit coassoc).obj x).hom
  naturality _ _ f :=
    (Category.id_comp _).trans
      (StructuredArrow.w ((augFunctor d s left_counit right_counit coassoc).map f)).symm

private lemma augTrans_leftOp_app (n : ℕ) :
    (augTrans d s left_counit right_counit coassoc).leftOp.app
        (op (SimplexCategoryGenRel.mk n)) = aug d (n + 1) := rfl

end Presentation

namespace CategoryTheory.Godement

/-- **Stacks 0G5N**.
Let `Y : C ⥤ C` be an endofunctor with transformations `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y` satisfying
the counit identities `1_Y = (d ⋆ 1_Y) ∘ s = (1_Y ⋆ d) ∘ s` and coassociativity
`(s ⋆ 1_Y) ∘ s = (1_Y ⋆ s) ∘ s`, i.e. let `(Y, d, s)` be a comonad on `C`. Then the powers
`X_n = Y.iterate (n + 1)`, with the faces `Godement.face d` and the degeneracies
`Godement.degeneracy s`, are a simplicial object of the category `C ⥤ C` of endofunctors of `C`,
augmented over `X_{-1} = Y.iterate 0 = 𝟭 C` by `face d 0 0 = d : X_0 = Y ⟶ 𝟭 C`. -/
@[stacks 0G5N]
public theorem exists_augmented_standardResolution {C : Type u} [Category.{v} C] {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
    (right_counit : s ≫ Functor.whiskerRight d Y = 𝟙 Y)
    (coassoc : s ≫ Functor.whiskerLeft Y s = s ≫ Functor.whiskerRight s Y) :
    ∃ (X : SimplicialObject.Augmented (C ⥤ C))
      (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = Y.iterate (n + 1)) (hX : X.right = 𝟭 C),
      (∀ (n : ℕ) (j : Fin (n + 2)),
        X.left.δ j = eqToHom (h (n + 1)) ≫ face d (n + 1) j ≫ eqToHom (h n).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)),
        X.left.σ j = eqToHom (h n) ≫ degeneracy s n j ≫ eqToHom (h (n + 1)).symm) ∧
      X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ face d 0 0 ≫ eqToHom hX.symm := by
  obtain ⟨hobj, hmor⟩ :=
    SimplicialObject.bijective_comp_toSimplexCategory_op_and_whiskerLeft (C ⥤ C)
  obtain ⟨X₁, hX₁⟩ :=
    hobj.surjective (stdFunctor d s left_counit right_counit coassoc).leftOp
  have h : ∀ n : ℕ, X₁.obj (op ⦋n⦌) = Y.iterate (n + 1) := fun n =>
    Functor.congr_obj hX₁ (op (SimplexCategoryGenRel.mk n))
  obtain ⟨a, ha⟩ := (hmor X₁ ((SimplicialObject.const (C ⥤ C)).obj (𝟭 C))).surjective
    (eqToHom hX₁ ≫ (augTrans d s left_counit right_counit coassoc).leftOp)
  refine ⟨⟨X₁, 𝟭 C, a⟩, h, rfl, ?_, ?_, ?_⟩
  · intro n j
    refine (Functor.congr_hom hX₁ (SimplexCategoryGenRel.δ j).op).trans ?_
    rw [stdFunctor_leftOp_map_δ]
    rfl
  · intro n j
    refine (Functor.congr_hom hX₁ (SimplexCategoryGenRel.σ j).op).trans ?_
    rw [stdFunctor_leftOp_map_σ]
    rfl
  · refine (NatTrans.congr_app ha (op (SimplexCategoryGenRel.mk 0))).trans ?_
    rw [NatTrans.comp_app, eqToHom_app, augTrans_leftOp_app]
    rfl

end CategoryTheory.Godement

/-! ### Conjugation by a pair of functors -/

section Conjugation

open CategoryTheory.Godement

/-- The augmentation of the image of an augmented simplicial object under a functor `W` is the
`W`-image of its augmentation. -/
private theorem whiskeringObj_obj_hom_app {D : Type*} [Category D] {E : Type*} [Category E]
    (W : D ⥤ E) (X : SimplicialObject.Augmented D) (k : SimplexCategoryᵒᵖ) :
    ((SimplicialObject.Augmented.whiskeringObj D E W).obj X).hom.app k = W.map (X.hom.app k) :=
  Category.comp_id _

/-- The image of Godement's augmented simplicial endofunctor under a functor. Let `Y`, `d`, `s`
satisfy the counit and coassociativity identities and let `W : (C ⥤ C) ⥤ D` be any functor. Then
the images `W (X_n)` of the powers `X_n = Y.iterate (n + 1)`, with the faces `W (d^n_j)` and the
degeneracies `W (s^n_j)`, are a simplicial object of `D`, augmented over `W (𝟭 C)` by `W (d)`. -/
private theorem exists_augmented_map_standardResolution {C : Type u} [Category.{v} C]
    {D : Type*} [Category D] {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (W : (C ⥤ C) ⥤ D)
    (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
    (right_counit : s ≫ Functor.whiskerRight d Y = 𝟙 Y)
    (coassoc : s ≫ Functor.whiskerLeft Y s = s ≫ Functor.whiskerRight s Y) :
    ∃ (X : SimplicialObject.Augmented D)
      (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = W.obj (Y.iterate (n + 1)))
      (hX : X.right = W.obj (𝟭 C)),
      (∀ (n : ℕ) (j : Fin (n + 2)),
        X.left.δ j = eqToHom (h (n + 1)) ≫ W.map (face d (n + 1) j) ≫ eqToHom (h n).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)),
        X.left.σ j = eqToHom (h n) ≫ W.map (degeneracy s n j) ≫ eqToHom (h (n + 1)).symm) ∧
      X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ W.map (face d 0 0) ≫ eqToHom hX.symm := by
  obtain ⟨X, h, hX, hδ, hσ, hhom⟩ :=
    exists_augmented_standardResolution d s left_counit right_counit coassoc
  exact ⟨(SimplicialObject.Augmented.whiskeringObj _ _ W).obj X,
    fun n => congrArg W.obj (h n), congrArg W.obj hX,
    fun n j => map_eq_eqToHom_comp W (hδ n j),
    fun n j => map_eq_eqToHom_comp W (hσ n j),
    (whiskeringObj_obj_hom_app W X _).trans (map_eq_eqToHom_comp W hhom)⟩

end Conjugation

namespace CategoryTheory.Godement

/-- **Stacks 0G5P**.
Let `Y : C ⥤ C` be an endofunctor with transformations `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y` satisfying
the counit identities `1_Y = (d ⋆ 1_Y) ∘ s = (1_Y ⋆ d) ∘ s` and coassociativity
`(s ⋆ 1_Y) ∘ s = (1_Y ⋆ s) ∘ s`, i.e. let `(Y, d, s)` be a comonad on `C`, and let `F : A ⥤ C` and
`G : C ⥤ B` be functors. Then the conjugated powers `G ∘ X_n ∘ F = F ⋙ Y.iterate (n+1) ⋙ G`, with
the faces `1_G ⋆ d^n_j ⋆ 1_F` and degeneracies `1_G ⋆ s^n_j ⋆ 1_F` obtained from `Godement.face d`
and `Godement.degeneracy s` by whiskering with `F` and `G`, are a simplicial object of the category
`A ⥤ B` of functors from `A` to `B`, augmented over `G ∘ F = F ⋙ G` by `1_G ⋆ d ⋆ 1_F`. -/
@[stacks 0G5P]
public theorem exists_augmented_standardResolution_whisker
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u} [Category.{v} C] {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (F : A ⥤ C) (G : C ⥤ B)
    (left_counit : s ≫ Functor.whiskerLeft Y d = 𝟙 Y)
    (right_counit : s ≫ Functor.whiskerRight d Y = 𝟙 Y)
    (coassoc : s ≫ Functor.whiskerLeft Y s = s ≫ Functor.whiskerRight s Y) :
    ∃ (X : SimplicialObject.Augmented (A ⥤ B))
      (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = F ⋙ Y.iterate (n + 1) ⋙ G)
      (hX : X.right = F ⋙ G),
      (∀ (n : ℕ) (j : Fin (n + 2)),
        X.left.δ j = eqToHom (h (n + 1)) ≫
          Functor.whiskerRight (Functor.whiskerLeft F (face d (n + 1) j)) G ≫
            eqToHom (h n).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)),
        X.left.σ j = eqToHom (h n) ≫
          Functor.whiskerRight (Functor.whiskerLeft F (degeneracy s n j)) G ≫
            eqToHom (h (n + 1)).symm) ∧
      X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫
        Functor.whiskerRight (Functor.whiskerLeft F (face d 0 0)) G ≫ eqToHom hX.symm :=
  exists_augmented_map_standardResolution d s
    ((Functor.whiskeringLeft A C C).obj F ⋙ (Functor.whiskeringRight A C B).obj G)
    left_counit right_counit coassoc

end CategoryTheory.Godement

/-! ### A degree-zero splitting of an augmentation extends to a section -/

section Section

variable {D : Type u} [Category.{v} D]

attribute [local simp ←] CategoryTheory.Functor.map_comp in
/-- The canonical morphism of simplicial objects from the constant simplicial object on the
`0`-simplices of `Y` to `Y`, whose degree `n` component is the map `u_n : Y_0 ⟶ Y_n` induced by the
unique morphism `⦋n⦌ ⟶ ⦋0⦌` of `SimplexCategory`. It is the counit of the adjunction between
`SimplicialObject.const` and evaluation in degree `0`. -/
private def constZeroSection (Y : SimplicialObject D) :
    (SimplicialObject.const D).obj (Y _⦋0⦌) ⟶ Y where
  app n := Y.map (SimplexCategory.isTerminalZero.from _).op

@[local simp]
private lemma constZeroSection_app (Y : SimplicialObject D) (n : SimplexCategoryᵒᵖ) :
    (constZeroSection Y).app n = Y.map (SimplexCategory.isTerminalZero.from (unop n)).op :=
  rfl

private lemma constZeroSection_app_zero (Y : SimplicialObject D) :
    (constZeroSection Y).app (op ⦋0⦌) = 𝟙 _ := by
  simp

/-- Composing `constZeroSection Y` with an augmentation `ε : Y ⟶ const R` gives the image under
`const` of the degree-`0` component of `ε`: naturality of `ε` along the unique `⦋n⦌ ⟶ ⦋0⦌` says
that `ε_n ∘ u_n = ε_0`. -/
private lemma constZeroSection_comp {Y : SimplicialObject D} {R : D}
    (ε : Y ⟶ (SimplicialObject.const D).obj R) :
    constZeroSection Y ≫ ε = (SimplicialObject.const D).map (ε.app (op ⦋0⦌)) := by
  ext n
  simp

end Section

namespace CategoryTheory.SimplicialObject.Augmented

/-- **Stacks 0G5Q**.
Let `X` be an augmented simplicial object of `D`, with augmentation
`ε = X.hom : X.left ⟶ const X.right`, and let `h₀ : X.right ⟶ X_0` satisfy `ε_0 ∘ h₀ = 1`. Then
there is a morphism of simplicial objects `h : const X.right ⟶ X.left` restricting to `h₀` in
degree `0` and satisfying `ε ∘ h = 1`; necessarily `h_n = u_n ∘ h₀` with `u_n : X_0 ⟶ X_n` induced
by the unique morphism `⦋n⦌ ⟶ ⦋0⦌`. -/
@[stacks 0G5Q]
public theorem exists_section_of_comp_hom_app_zero_eq_id {D : Type u} [Category.{v} D]
    (X : SimplicialObject.Augmented D) (h₀ : X.right ⟶ X.left.obj (op ⦋0⦌))
    (hh₀ : h₀ ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right) :
    ∃ h : (SimplicialObject.const D).obj X.right ⟶ X.left,
      h.app (op ⦋0⦌) = h₀ ∧ h ≫ X.hom = 𝟙 ((SimplicialObject.const D).obj X.right) := by
  refine ⟨(SimplicialObject.const D).map h₀ ≫ constZeroSection X.left,
    by simp [constZeroSection_app_zero], ?_⟩
  rw [Category.assoc, constZeroSection_comp, ← Functor.map_comp, hh₀,
    CategoryTheory.Functor.map_id]

end CategoryTheory.SimplicialObject.Augmented

end
