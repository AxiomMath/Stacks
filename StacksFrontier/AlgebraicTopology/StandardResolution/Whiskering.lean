module

public import StacksFrontier.AlgebraicTopology.StandardResolution.Godement

/-!
# Homotopies between the composites of Godement's standard resolution

Let `C` be a category, let `Y : C ⥤ C` be an endofunctor and let `d : Y ⟶ 𝟭 C` and
`s : Y ⟶ Y ⋙ Y` make `(Y, d, s)` a comonad, so that the powers `X_n = Y.iterate (n + 1)` form an
augmented simplicial endofunctor as constructed in
`StacksFrontier.AlgebraicTopology.StandardResolution.Godement`.

Given functors `F F' : A ⥤ C` and `G G' : C ⥤ B` with transformations `a : G ⟶ G'` and
`b : F ⟶ F'`, together with degreewise families `(a_n) : G ∘ X ⟶ G' ∘ X` and
`(b_n) : X ∘ F ⟶ X ∘ F'` compatible with the faces, the degeneracies and the augmentations, the two
horizontal composites `(a_n) ⋆ b` and `a ⋆ (b_n)` are morphisms of augmented simplicial objects
with the same component `a ⋆ b` over the augmentations, and they are simplicially homotopic. The
special case `F = F' = G = G' = 𝟭 C` is the pair of whiskerings of an endomorphism `f : 𝟭 C ⟶ 𝟭 C`
of the identity functor.

## Main results

* `CategoryTheory.Godement.exists_homotopy_hcomp_hcomp`: the two horizontal composites `a ⋆ (b_n)`
  and `(a_n) ⋆ b` are morphisms of augmented simplicial objects with component `a ⋆ b` over the
  augmentations, and there is a simplicial homotopy from the second to the first.
* `CategoryTheory.Godement.exists_homotopy_whiskerLeft_whiskerRight`: the two whiskerings of an
  endomorphism `f` of `𝟭 C` are endomorphisms of the augmented simplicial object with component
  `f` over `𝟭 C`, and there is a simplicial homotopy from the inner one to the outer one.

## References

* [Stacks, Tag 0G5R](https://stacks.math.columbia.edu/tag/0G5R)
* [Stacks, Tag 0G5S](https://stacks.math.columbia.edu/tag/0G5S)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open CategoryTheory.Godement.Prep

universe v₁ u₁ v₂ u₂ v' u' v u

/-! ### The two horizontal composites of maps into and out of Godement's resolution -/

section Horizontal

-- The pinnings of this section cross the definitional boundary between `conj F G |>.obj V` and
-- `F ⋙ V ⋙ G`; without this the `rw`s below are rejected for a motive that is ill-typed at
-- `implicit` transparency only.

open CategoryTheory.Godement

/-! #### Generalities on powers, faces and degeneracies -/

section Powers

variable {C : Type u} [Category.{v} C]

/-- Additivity of the powers, along an equality of exponents. -/
private theorem iterate_eq_comp {Y : C ⥤ C} {m q p : ℕ} (h : m = q + p) :
    Y.iterate m = Y.iterate q ⋙ Y.iterate p := by
  subst h; exact Functor.iterate_add Y q p

/-- Sandwiching a morphism by `eqToHom`s of definitionally equal objects changes nothing. -/
private theorem eqToHom_comp_eqToHom_eq {D : Type*} [Category D] {X Z : D} (h₁ : X = X)
    (h₂ : Z = Z) (f : X ⟶ Z) : eqToHom h₁ ≫ f ≫ eqToHom h₂ = f := by simp

variable {Y : C ⥤ C}

/-- Transporting the functor a transformation is whiskered by. -/
private theorem whiskerLeft_eqToHom {V W T T' : C ⥤ C} (h : V = W) (α : T ⟶ T') :
    Functor.whiskerLeft V α = eqToHom (congrArg (· ⋙ T) h) ≫ Functor.whiskerLeft W α ≫
      eqToHom (congrArg (· ⋙ T') h).symm := by
  subst h; simp

/-- `d^n_j = 1_k ⋆ d^p_j`: a face of index `j ≤ p` in degree `k + p` whiskers the face `d^p_j` of
the outer `p + 1` factors by the inner `k` factors. -/
private theorem face_add_left (d : Y ⟶ 𝟭 C) (k : ℕ) : ∀ (p : ℕ) (j : Fin (p + 1)),
    face d (k + p) (Fin.castLE (by omega) j) =
      eqToHom (iterate_eq_comp (Y := Y) (show k + p + 1 = k + (p + 1) by omega)) ≫
        Functor.whiskerLeft (Y.iterate k) (face d p j) ≫
          eqToHom (iterate_eq_comp (Y := Y) (show k + p = k + p from rfl)).symm := by
  intro p
  induction p with
  | zero =>
    intro j
    obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    refine (face_zero d (k + 0)).trans ?_
    exact (eqToHom_comp_eqToHom_eq _ _ _).symm
  | succ p ih =>
    refine Fin.cases ?_ (fun i => ?_)
    · refine (face_zero d (k + (p + 1))).trans ?_
      rw [face_zero]
      exact whiskerLeft_eqToHom (Functor.iterate_add Y k (p + 1)) d
    · exact map_eq_eqToHom_comp ((Functor.whiskeringRight C C C).obj Y) (ih i)

/-- `s^n_j = 1_k ⋆ s^p_j`, the degeneracy analogue of `face_add_left`. -/
private theorem degeneracy_add_left (s : Y ⟶ Y ⋙ Y) (k : ℕ) : ∀ (p : ℕ) (j : Fin (p + 1)),
    degeneracy s (k + p) (Fin.castLE (by omega) j) =
      eqToHom (iterate_eq_comp (Y := Y) (show k + p + 1 = k + (p + 1) by omega)) ≫
        Functor.whiskerLeft (Y.iterate k) (degeneracy s p j) ≫
          eqToHom (iterate_eq_comp (Y := Y) (show k + p + 2 = k + (p + 2) by omega)).symm := by
  intro p
  induction p with
  | zero =>
    intro j
    obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    refine (degeneracy_zero s (k + 0)).trans ?_
    exact (eqToHom_comp_eqToHom_eq _ _ _).symm
  | succ p ih =>
    refine Fin.cases ?_ (fun i => ?_)
    · refine (degeneracy_zero s (k + (p + 1))).trans ?_
      rw [degeneracy_zero]
      exact whiskerLeft_eqToHom (Functor.iterate_add Y k (p + 1)) s
    · exact map_eq_eqToHom_comp ((Functor.whiskeringRight C C C).obj Y) (ih i)

/-- `d^n_{j + p} = d^q_j ⋆ 1_p`: a face of index `≥ p` in degree `q + p` whiskers the face `d^q_j`
of the inner `q + 1` factors by the outer `p` factors, which it leaves untouched. -/
private theorem face_add_right (d : Y ⟶ 𝟭 C) (q : ℕ) (j : Fin (q + 1)) : ∀ p : ℕ,
    face d (q + p) ⟨(j : ℕ) + p, by omega⟩ =
      eqToHom (iterate_eq_comp (Y := Y) (show q + p + 1 = q + 1 + p by omega)) ≫
        Functor.whiskerRight (face d q j) (Y.iterate p) ≫
          eqToHom (iterate_eq_comp (Y := Y) (show q + p = q + p from rfl)).symm := by
  intro p
  induction p with
  | zero =>
    exact (eqToHom_comp_eqToHom_eq _ _ _).symm
  | succ p ih => exact map_eq_eqToHom_comp ((Functor.whiskeringRight C C C).obj Y) ih

/-- The degeneracy analogue of `face_add_right`. -/
private theorem degeneracy_add_right (s : Y ⟶ Y ⋙ Y) (q : ℕ) (j : Fin (q + 1)) : ∀ p : ℕ,
    degeneracy s (q + p) ⟨(j : ℕ) + p, by omega⟩ =
      eqToHom (iterate_eq_comp (Y := Y) (show q + p + 1 = q + 1 + p by omega)) ≫
        Functor.whiskerRight (degeneracy s q j) (Y.iterate p) ≫
          eqToHom (iterate_eq_comp (Y := Y) (show q + p + 2 = q + 2 + p by omega)).symm := by
  intro p
  induction p with
  | zero =>
    exact (eqToHom_comp_eqToHom_eq _ _ _).symm
  | succ p ih => exact map_eq_eqToHom_comp ((Functor.whiskeringRight C C C).obj Y) ih

/-- A face whose index lies in the outer `p + 1` factors of a splitting, with the degree and the
index given by equalities rather than by their shape. -/
private theorem face_eq_whiskerLeft (d : Y ⟶ 𝟭 C) {m q p : ℕ} (hm : m = q + p) (j : Fin (p + 1))
    (j₀ : Fin (m + 1)) (hj : (j₀ : ℕ) = (j : ℕ)) :
    face d m j₀ = eqToHom (iterate_eq_comp (Y := Y) (show m + 1 = q + (p + 1) by omega)) ≫
      Functor.whiskerLeft (Y.iterate q) (face d p j) ≫
        eqToHom (iterate_eq_comp (Y := Y) hm).symm := by
  subst hm
  rw [show j₀ = Fin.castLE (by omega) j from Fin.ext hj]
  exact face_add_left d q p j

/-- A degeneracy whose index lies in the outer `p + 1` factors of a splitting. -/
private theorem degeneracy_eq_whiskerLeft (s : Y ⟶ Y ⋙ Y) {m q p : ℕ} (hm : m = q + p)
    (j : Fin (p + 1)) (j₀ : Fin (m + 1)) (hj : (j₀ : ℕ) = (j : ℕ)) :
    degeneracy s m j₀ = eqToHom (iterate_eq_comp (Y := Y) (show m + 1 = q + (p + 1) by omega)) ≫
      Functor.whiskerLeft (Y.iterate q) (degeneracy s p j) ≫
        eqToHom (iterate_eq_comp (Y := Y) (show m + 2 = q + (p + 2) by omega)).symm := by
  subst hm
  rw [show j₀ = Fin.castLE (by omega) j from Fin.ext hj]
  exact degeneracy_add_left s q p j

/-- A face whose index lies in the inner `q + 1` factors of a splitting. -/
private theorem face_eq_whiskerRight (d : Y ⟶ 𝟭 C) {m q p : ℕ} (hm : m = q + p) (j : Fin (q + 1))
    (j₀ : Fin (m + 1)) (hj : (j₀ : ℕ) = (j : ℕ) + p) :
    face d m j₀ = eqToHom (iterate_eq_comp (Y := Y) (show m + 1 = q + 1 + p by omega)) ≫
      Functor.whiskerRight (face d q j) (Y.iterate p) ≫
        eqToHom (iterate_eq_comp (Y := Y) hm).symm := by
  subst hm
  rw [show j₀ = (⟨(j : ℕ) + p, by omega⟩ : Fin (q + p + 1)) from Fin.ext hj]
  exact face_add_right d q j p

/-- A degeneracy whose index lies in the inner `q + 1` factors of a splitting. -/
private theorem degeneracy_eq_whiskerRight (s : Y ⟶ Y ⋙ Y) {m q p : ℕ} (hm : m = q + p)
    (j : Fin (q + 1)) (j₀ : Fin (m + 1)) (hj : (j₀ : ℕ) = (j : ℕ) + p) :
    degeneracy s m j₀ = eqToHom (iterate_eq_comp (Y := Y) (show m + 1 = q + 1 + p by omega)) ≫
      Functor.whiskerRight (degeneracy s q j) (Y.iterate p) ≫
        eqToHom (iterate_eq_comp (Y := Y) (show m + 2 = q + 2 + p by omega)).symm := by
  subst hm
  rw [show j₀ = (⟨(j : ℕ) + p, by omega⟩ : Fin (q + p + 1)) from Fin.ext hj]
  exact degeneracy_add_right s q j p

end Powers

/-! #### Interchange -/

section Interchange

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u} [Category.{v} C]

/-- Interchange: post-composing a horizontal composite with a left whiskering. -/
private theorem hcomp_comp_whiskerLeft {P P' : A ⥤ C} {Q Q' Q'' : C ⥤ B} (α : P ⟶ P')
    (β : Q ⟶ Q') (γ : Q' ⟶ Q'') :
    NatTrans.hcomp α β ≫ Functor.whiskerLeft P' γ = NatTrans.hcomp α (β ≫ γ) := by
  ext X; simp [γ.naturality]

/-- Interchange: pre-composing a horizontal composite with a left whiskering. -/
private theorem whiskerLeft_comp_hcomp {P P' : A ⥤ C} {Q₀ Q Q' : C ⥤ B} (α : P ⟶ P')
    (β : Q ⟶ Q') (γ : Q₀ ⟶ Q) :
    Functor.whiskerLeft P γ ≫ NatTrans.hcomp α β = NatTrans.hcomp α (γ ≫ β) := by
  ext X; simp

/-- Interchange: post-composing a horizontal composite with a right whiskering. -/
private theorem hcomp_comp_whiskerRight {P P' P'' : A ⥤ C} {Q Q' : C ⥤ B} (α : P ⟶ P')
    (β : Q ⟶ Q') (δ : P' ⟶ P'') :
    NatTrans.hcomp α β ≫ Functor.whiskerRight δ Q' = NatTrans.hcomp (α ≫ δ) β := by
  ext X; simp

/-- Interchange: pre-composing a horizontal composite with a right whiskering. -/
private theorem whiskerRight_comp_hcomp {P₀ P P' : A ⥤ C} {Q Q' : C ⥤ B} (α : P ⟶ P')
    (β : Q ⟶ Q') (δ : P₀ ⟶ P) :
    Functor.whiskerRight δ Q ≫ NatTrans.hcomp α β = NatTrans.hcomp (δ ≫ α) β := by
  ext X; simp

end Interchange

/-! #### Transport of a commuting square along pinnings -/

section Pinned

/-- A square commutes as soon as the square of its pinned representatives does: if `u`, `f'`, `f`,
`v` are conjugates of `U`, `U'`, `W`, `W'` by `eqToHom`s of a common set of pinnings, then
`U ≫ U' = W ≫ W'` implies `u ≫ f' = f ≫ v`. -/
private theorem pinned_comm {D : Type*} [Category D] {O₁ O₂ O₃ O₄ P₁ P₂ P₃ P₄ : D}
    (e₁ : O₁ = P₁) (e₂ : O₂ = P₂) (e₃ : O₃ = P₃) (e₄ : O₄ = P₄)
    {u : O₁ ⟶ O₂} {U : P₁ ⟶ P₂} (hu : u = eqToHom e₁ ≫ U ≫ eqToHom e₂.symm)
    {f' : O₂ ⟶ O₄} {U' : P₂ ⟶ P₄} (hf' : f' = eqToHom e₂ ≫ U' ≫ eqToHom e₄.symm)
    {f : O₁ ⟶ O₃} {W : P₁ ⟶ P₃} (hf : f = eqToHom e₁ ≫ W ≫ eqToHom e₃.symm)
    {v : O₃ ⟶ O₄} {W' : P₃ ⟶ P₄} (hv : v = eqToHom e₃ ≫ W' ≫ eqToHom e₄.symm)
    (h : U ≫ U' = W ≫ W') : u ≫ f' = f ≫ v := by
  subst e₁; subst e₂; subst e₃; subst e₄
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hu hf' hf hv
  rw [hu, hf', hf, hv, h]

end Pinned

/-! #### The conjugation functor and the core relations -/

section Core

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u} [Category.{v} C]

/-- Conjugation `V ↦ F ∘ V ∘ G`, as a functor `(C ⥤ C) ⥤ (A ⥤ B)`. -/
private abbrev conj (F : A ⥤ C) (G : C ⥤ B) : (C ⥤ C) ⥤ (A ⥤ B) :=
  (Functor.whiskeringLeft A C C).obj F ⋙ (Functor.whiskeringRight A C B).obj G

private theorem conj_obj (F : A ⥤ C) (G : C ⥤ B) (V : C ⥤ C) :
    (conj F G).obj V = F ⋙ V ⋙ G := rfl

private theorem conj_map (F : A ⥤ C) (G : C ⥤ B) {V W : C ⥤ C} (α : V ⟶ W) :
    (conj F G).map α = Functor.whiskerRight (Functor.whiskerLeft F α) G := rfl

variable {Y : C ⥤ C} {F F' : A ⥤ C} {G G' : C ⥤ B} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
  (AA : (p : ℕ) → (Y.iterate p ⋙ G ⟶ Y.iterate p ⋙ G'))
  (BB : (q : ℕ) → (F ⋙ Y.iterate q ⟶ F' ⋙ Y.iterate q))

/-- The interpolating `a_{p - 1} ⋆ b_{q - 1}`, for the splitting of `Y^{q + p}` as `Y^q ∘ Y^p`. -/
private def hstar (q p : ℕ) :
    (F ⋙ Y.iterate q) ⋙ (Y.iterate p ⋙ G) ⟶ (F' ⋙ Y.iterate q) ⋙ (Y.iterate p ⋙ G') :=
  NatTrans.hcomp (BB q) (AA p)

private theorem hstar_def (q p : ℕ) : hstar AA BB q p = NatTrans.hcomp (BB q) (AA p) := rfl

/-- A transformation `α` of the powers, whiskered into the outer, `AA`-side factors, commutes with
the interpolating `hstar` as soon as it commutes with `AA`. -/
private theorem hstar_comm_whiskerLeft {p p' : ℕ} (α : Y.iterate p ⟶ Y.iterate p')
    (hA : AA p ≫ Functor.whiskerRight α G' = Functor.whiskerRight α G ≫ AA p') (q : ℕ) :
    hstar AA BB q p ≫ (conj F' G').map (Functor.whiskerLeft (Y.iterate q) α) =
      (conj F G).map (Functor.whiskerLeft (Y.iterate q) α) ≫ hstar AA BB q p' := by
  rw [show (conj F' G').map (Functor.whiskerLeft (Y.iterate q) α) =
        Functor.whiskerLeft (F' ⋙ Y.iterate q) (Functor.whiskerRight α G') from rfl,
    show (conj F G).map (Functor.whiskerLeft (Y.iterate q) α) =
        Functor.whiskerLeft (F ⋙ Y.iterate q) (Functor.whiskerRight α G) from rfl,
    hstar_def, hstar_def, hcomp_comp_whiskerLeft, hA, ← whiskerLeft_comp_hcomp]

/-- A transformation `α` of the powers, whiskered into the inner, `BB`-side factors, commutes with
the interpolating `hstar` as soon as it commutes with `BB`. -/
private theorem hstar_comm_whiskerRight {q q' : ℕ} (α : Y.iterate q ⟶ Y.iterate q')
    (hB : BB q ≫ Functor.whiskerLeft F' α = Functor.whiskerLeft F α ≫ BB q') (p : ℕ) :
    hstar AA BB q p ≫ (conj F' G').map (Functor.whiskerRight α (Y.iterate p)) =
      (conj F G).map (Functor.whiskerRight α (Y.iterate p)) ≫ hstar AA BB q' p := by
  rw [show (conj F' G').map (Functor.whiskerRight α (Y.iterate p)) =
        Functor.whiskerRight (Functor.whiskerLeft F' α) (Y.iterate p ⋙ G') from rfl,
    show (conj F G).map (Functor.whiskerRight α (Y.iterate p)) =
        Functor.whiskerRight (Functor.whiskerLeft F α) (Y.iterate p ⋙ G) from rfl,
    hstar_def, hstar_def, hcomp_comp_whiskerRight, hB, ← whiskerRight_comp_hcomp]


/-! #### The same relations between the conjugated powers -/

/-- The interpolating `a_{p - 1} ⋆ b_{q - 1}`, as a morphism between the conjugated powers
`F ∘ Y^{n + 1} ∘ G` and `F' ∘ Y^{n + 1} ∘ G'`, for a splitting `q + p = n + 1`. -/
private def hcen (n q p : ℕ) (hn : q + p = n + 1) :
    (conj F G).obj (Y.iterate (n + 1)) ⟶ (conj F' G').obj (Y.iterate (n + 1)) :=
  eqToHom (congrArg (conj F G).obj (iterate_eq_comp hn.symm)) ≫ hstar AA BB q p ≫
    eqToHom (congrArg (conj F' G').obj (iterate_eq_comp hn.symm)).symm

private theorem hcen_def (n q p : ℕ) (hn : q + p = n + 1) :
    hcen AA BB n q p hn =
      eqToHom (congrArg (conj F G).obj (iterate_eq_comp hn.symm)) ≫ hstar AA BB q p ≫
        eqToHom (congrArg (conj F' G').obj (iterate_eq_comp hn.symm)).symm := rfl

/-- `hcen` depends on the splitting only through its two numbers. -/
private theorem hcen_congr (n q p q' p' : ℕ) (hn : q + p = n + 1) (hn' : q' + p' = n + 1)
    (hq : q = q') (hp : p = p') : hcen AA BB n q p hn = hcen AA BB n q' p' hn' := by
  subst hq; subst hp; rfl

/-- At the end `p = 0` no transport is left: `h_{n, 0} = a ⋆ b_n`. -/
private theorem hcen_p_zero (n : ℕ) (hn : n + 1 + 0 = n + 1) :
    hcen AA BB n (n + 1) 0 hn = hstar AA BB (n + 1) 0 := by
  rw [hcen_def]
  exact eqToHom_comp_eqToHom_eq _ _ _

/-- At the end `q = 0` no transport is left: `h_{n, n + 1} = a_n ⋆ b`. -/
private theorem hcen_q_zero (n : ℕ) (hn : 0 + (n + 1) = n + 1) :
    hcen AA BB n 0 (n + 1) hn = hstar AA BB 0 (n + 1) := by
  rw [hcen_def]
  exact eqToHom_comp_eqToHom_eq _ _ _

/-- The first homotopy relation between the conjugated powers. -/
private theorem hcen_face_left
    (hAf : ∀ (m : ℕ) (j : Fin (m + 1)), AA (m + 1) ≫ Functor.whiskerRight (face d m j) G' =
      Functor.whiskerRight (face d m j) G ≫ AA m)
    {n q p : ℕ} (hn : q + p = n + 1) (j : Fin (p + 1)) (j₀ : Fin (n + 2))
    (hj : (j₀ : ℕ) = (j : ℕ)) :
    hcen AA BB (n + 1) q (p + 1) (by omega) ≫ (conj F' G').map (face d (n + 1) j₀) =
      (conj F G).map (face d (n + 1) j₀) ≫ hcen AA BB n q p hn := by
  have hf := face_eq_whiskerLeft d (show n + 1 = q + p by omega) j j₀ hj
  exact pinned_comm _ _ _ (congrArg (conj F' G').obj (iterate_eq_comp hn.symm))
    (hcen_def AA BB (n + 1) q (p + 1) (by omega))
    (map_eq_eqToHom_comp (conj F' G') hf) (map_eq_eqToHom_comp (conj F G) hf)
    (hcen_def AA BB n q p hn) (hstar_comm_whiskerLeft AA BB _ (hAf p j) q)

/-- The second homotopy relation between the conjugated powers. -/
private theorem hcen_face_right
    (hBf : ∀ (m : ℕ) (j : Fin (m + 1)), BB (m + 1) ≫ Functor.whiskerLeft F' (face d m j) =
      Functor.whiskerLeft F (face d m j) ≫ BB m)
    {n q p : ℕ} (hn : q + p = n + 1) (j : Fin (q + 1)) (j₀ : Fin (n + 2))
    (hj : (j₀ : ℕ) = (j : ℕ) + p) :
    hcen AA BB (n + 1) (q + 1) p (by omega) ≫ (conj F' G').map (face d (n + 1) j₀) =
      (conj F G).map (face d (n + 1) j₀) ≫ hcen AA BB n q p hn := by
  have hf := face_eq_whiskerRight d (show n + 1 = q + p by omega) j j₀ hj
  exact pinned_comm _ _ _ (congrArg (conj F' G').obj (iterate_eq_comp hn.symm))
    (hcen_def AA BB (n + 1) (q + 1) p (by omega))
    (map_eq_eqToHom_comp (conj F' G') hf) (map_eq_eqToHom_comp (conj F G) hf)
    (hcen_def AA BB n q p hn) (hstar_comm_whiskerRight AA BB _ (hBf q j) p)

/-- The third homotopy relation between the conjugated powers. -/
private theorem hcen_degeneracy_left
    (hAs : ∀ (m : ℕ) (j : Fin (m + 1)), AA (m + 1) ≫ Functor.whiskerRight (degeneracy s m j) G' =
      Functor.whiskerRight (degeneracy s m j) G ≫ AA (m + 2))
    {n q p : ℕ} (hn : q + (p + 1) = n + 1) (j : Fin (p + 1)) (j₀ : Fin (n + 1))
    (hj : (j₀ : ℕ) = (j : ℕ)) :
    hcen AA BB n q (p + 1) hn ≫ (conj F' G').map (degeneracy s n j₀) =
      (conj F G).map (degeneracy s n j₀) ≫ hcen AA BB (n + 1) q (p + 2) (by omega) := by
  have hf := degeneracy_eq_whiskerLeft s (show n = q + p by omega) j j₀ hj
  exact pinned_comm _ _ _
      (congrArg (conj F' G').obj (iterate_eq_comp (show n + 2 = q + (p + 2) by omega)))
    (hcen_def AA BB n q (p + 1) hn)
    (map_eq_eqToHom_comp (conj F' G') hf) (map_eq_eqToHom_comp (conj F G) hf)
    (hcen_def AA BB (n + 1) q (p + 2) (by omega)) (hstar_comm_whiskerLeft AA BB _ (hAs p j) q)

/-- The fourth homotopy relation between the conjugated powers. -/
private theorem hcen_degeneracy_right
    (hBs : ∀ (m : ℕ) (j : Fin (m + 1)), BB (m + 1) ≫ Functor.whiskerLeft F' (degeneracy s m j) =
      Functor.whiskerLeft F (degeneracy s m j) ≫ BB (m + 2))
    {n q p : ℕ} (hn : q + 1 + p = n + 1) (j : Fin (q + 1)) (j₀ : Fin (n + 1))
    (hj : (j₀ : ℕ) = (j : ℕ) + p) :
    hcen AA BB n (q + 1) p hn ≫ (conj F' G').map (degeneracy s n j₀) =
      (conj F G).map (degeneracy s n j₀) ≫ hcen AA BB (n + 1) (q + 2) p (by omega) := by
  have hf := degeneracy_eq_whiskerRight s (show n = q + p by omega) j j₀ hj
  exact pinned_comm _ _ _
      (congrArg (conj F' G').obj (iterate_eq_comp (show n + 2 = q + 2 + p by omega)))
    (hcen_def AA BB n (q + 1) p hn)
    (map_eq_eqToHom_comp (conj F' G') hf) (map_eq_eqToHom_comp (conj F G) hf)
    (hcen_def AA BB (n + 1) (q + 2) p (by omega)) (hstar_comm_whiskerRight AA BB _ (hBs q j) p)

end Core

/-! #### Morphisms of simplicial objects from degreewise data -/

section Degreewise

variable {D : Type u₁} [Category.{v₁} D] {U U' : SimplicialObject D}
  (h : ∀ n : ℕ, U.obj (op ⦋n⦌) ⟶ U'.obj (op ⦋n⦌))

/-- A family of morphisms commuting with the faces and the degeneracies is a morphism of simplicial
objects, the faces and the degeneracies generating `Δ`. -/
private def homMk (hδ : ∀ (n : ℕ) (i : Fin (n + 2)), U.δ i ≫ h n = h (n + 1) ≫ U'.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), U.σ i ≫ h (n + 1) = h n ≫ U'.σ i) : U ⟶ U' where
  app x := h x.unop.len
  naturality _ _ g := SimplicialObject.naturality_of_δ_σ h hδ hσ g.unop

private theorem homMk_app
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)), U.δ i ≫ h n = h (n + 1) ≫ U'.δ i)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), U.σ i ≫ h (n + 1) = h n ≫ U'.σ i) (n : ℕ) :
    (homMk h hδ hσ).app (op ⦋n⦌) = h n := rfl

/-- A morphism of augmented simplicial objects is a morphism of the underlying simplicial objects
together with one of the augmentations, compatible in degree `0`: the compatibility in every degree
follows, every object of `Δ` receiving a morphism from `⦋0⦌`. -/
private def augmentedHomMk {Z Z' : SimplicialObject.Augmented D} (f : Z.left ⟶ Z'.left)
    (g : Z.right ⟶ Z'.right)
    (h₀ : f.app (op ⦋0⦌) ≫ Z'.hom.app (op ⦋0⦌) = Z.hom.app (op ⦋0⦌) ≫ g) : Z ⟶ Z' where
  left := f
  right := g
  w := by
    ext n
    have key : ∀ W : SimplicialObject.Augmented D,
        W.hom.app n = W.left.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫
          W.hom.app (op ⦋0⦌) := fun W => by
      simp
    simp only [Functor.id_map, NatTrans.comp_app, Functor.const_map_app]
    rw [key Z, key Z', ← Category.assoc, ← f.naturality, Category.assoc, h₀, Category.assoc]

private theorem augmentedHomMk_left {Z Z' : SimplicialObject.Augmented D} (f : Z.left ⟶ Z'.left)
    (g : Z.right ⟶ Z'.right)
    (h₀ : f.app (op ⦋0⦌) ≫ Z'.hom.app (op ⦋0⦌) = Z.hom.app (op ⦋0⦌) ≫ g) :
    (augmentedHomMk f g h₀).left = f := rfl

private theorem augmentedHomMk_right {Z Z' : SimplicialObject.Augmented D} (f : Z.left ⟶ Z'.left)
    (g : Z.right ⟶ Z'.right)
    (h₀ : f.app (op ⦋0⦌) ≫ Z'.hom.app (op ⦋0⦌) = Z.hom.app (op ⦋0⦌) ≫ g) :
    (augmentedHomMk f g h₀).right = g := rfl

end Degreewise

/-! #### The two families, extended by the augmentations -/

section Families

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u} [Category.{v} C] {Y : C ⥤ C} {F F' : A ⥤ C} {G G' : C ⥤ B} (d : Y ⟶ 𝟭 C)
  (s : Y ⟶ Y ⋙ Y)

/-- The family `(a_n)` extended by the convention `a_{-1} = a`: the value at `0` is `a`. -/
private def aFam (a : G ⟶ G') (an : (n : ℕ) → (Y.iterate (n + 1) ⋙ G ⟶ Y.iterate (n + 1) ⋙ G')) :
    (p : ℕ) → (Y.iterate p ⋙ G ⟶ Y.iterate p ⋙ G') :=
  Nat.rec (motive := fun p => (Y.iterate p ⋙ G ⟶ Y.iterate p ⋙ G')) a fun n _ => an n

/-- The family `(b_n)` extended by the convention `b_{-1} = b`. -/
private def bFam (b : F ⟶ F') (bn : (n : ℕ) → (F ⋙ Y.iterate (n + 1) ⟶ F' ⋙ Y.iterate (n + 1))) :
    (q : ℕ) → (F ⋙ Y.iterate q ⟶ F' ⋙ Y.iterate q) :=
  Nat.rec (motive := fun q => (F ⋙ Y.iterate q ⟶ F' ⋙ Y.iterate q)) b fun n _ => bn n

variable (a : G ⟶ G') (b : F ⟶ F')
  (an : (n : ℕ) → (Y.iterate (n + 1) ⋙ G ⟶ Y.iterate (n + 1) ⋙ G'))
  (bn : (n : ℕ) → (F ⋙ Y.iterate (n + 1) ⟶ F' ⋙ Y.iterate (n + 1)))

/-- Commutation of the extended family `(a_n)` with the faces, the case `m = 0` being the
compatibility with the augmentations. -/
private theorem aFam_face
    (han_face : ∀ (n : ℕ) (j : Fin (n + 2)),
      an (n + 1) ≫ Functor.whiskerRight (face d (n + 1) j) G' =
        Functor.whiskerRight (face d (n + 1) j) G ≫ an n)
    (han_aug : an 0 ≫ Functor.whiskerRight (face d 0 0) G' =
      Functor.whiskerRight (face d 0 0) G ≫ a) (m : ℕ) (j : Fin (m + 1)) :
    aFam a an (m + 1) ≫ Functor.whiskerRight (face d m j) G' =
      Functor.whiskerRight (face d m j) G ≫ aFam a an m := by
  cases m with
  | zero => obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt); exact han_aug
  | succ m => exact han_face m j

/-- Commutation of the extended family `(a_n)` with the degeneracies. -/
private theorem aFam_degeneracy
    (han_degeneracy : ∀ (n : ℕ) (j : Fin (n + 1)),
      an n ≫ Functor.whiskerRight (degeneracy s n j) G' =
        Functor.whiskerRight (degeneracy s n j) G ≫ an (n + 1)) (m : ℕ) (j : Fin (m + 1)) :
    aFam a an (m + 1) ≫ Functor.whiskerRight (degeneracy s m j) G' =
      Functor.whiskerRight (degeneracy s m j) G ≫ aFam a an (m + 2) :=
  han_degeneracy m j

/-- Commutation of the extended family `(b_n)` with the faces. -/
private theorem bFam_face
    (hbn_face : ∀ (n : ℕ) (j : Fin (n + 2)),
      bn (n + 1) ≫ Functor.whiskerLeft F' (face d (n + 1) j) =
        Functor.whiskerLeft F (face d (n + 1) j) ≫ bn n)
    (hbn_aug : bn 0 ≫ Functor.whiskerLeft F' (face d 0 0) =
      Functor.whiskerLeft F (face d 0 0) ≫ b) (m : ℕ) (j : Fin (m + 1)) :
    bFam b bn (m + 1) ≫ Functor.whiskerLeft F' (face d m j) =
      Functor.whiskerLeft F (face d m j) ≫ bFam b bn m := by
  cases m with
  | zero => obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt); exact hbn_aug
  | succ m => exact hbn_face m j

/-- Commutation of the extended family `(b_n)` with the degeneracies. -/
private theorem bFam_degeneracy
    (hbn_degeneracy : ∀ (n : ℕ) (j : Fin (n + 1)),
      bn n ≫ Functor.whiskerLeft F' (degeneracy s n j) =
        Functor.whiskerLeft F (degeneracy s n j) ≫ bn (n + 1)) (m : ℕ) (j : Fin (m + 1)) :
    bFam b bn (m + 1) ≫ Functor.whiskerLeft F' (degeneracy s m j) =
      Functor.whiskerLeft F (degeneracy s m j) ≫ bFam b bn (m + 2) :=
  hbn_degeneracy m j

end Families

/-! #### The interpolating family between the terms of `Z` and `Z'` -/

section Assembly

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u} [Category.{v} C] {Y : C ⥤ C} {F F' : A ⥤ C} {G G' : C ⥤ B} (d : Y ⟶ 𝟭 C)
  (s : Y ⟶ Y ⋙ Y)
  (AA : (p : ℕ) → (Y.iterate p ⋙ G ⟶ Y.iterate p ⋙ G'))
  (BB : (q : ℕ) → (F ⋙ Y.iterate q ⟶ F' ⋙ Y.iterate q))
  {Z Z' : SimplicialObject.Augmented (A ⥤ B)}
  (hZ : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = F ⋙ Y.iterate (n + 1) ⋙ G)
  (hZ' : ∀ n : ℕ, Z'.left.obj (op ⦋n⦌) = F' ⋙ Y.iterate (n + 1) ⋙ G')

/-- The interpolating `h_{n, i} = a_{i - 1} ⋆ b_{n - i}` as a morphism `Z_n ⟶ Z'_n`, for the
splitting `n + 1 = (n + 1 - i) + i`. -/
private def hpin (n : ℕ) (i : Fin (n + 2)) : Z.left.obj (op ⦋n⦌) ⟶ Z'.left.obj (op ⦋n⦌) :=
  eqToHom (hZ n) ≫ hcen AA BB n (n + 1 - (i : ℕ)) (i : ℕ) (Nat.sub_add_cancel i.is_le) ≫
    eqToHom (hZ' n).symm

private theorem hpin_def (n : ℕ) (i : Fin (n + 2)) :
    hpin AA BB hZ hZ' n i = eqToHom (hZ n) ≫
      hcen AA BB n (n + 1 - (i : ℕ)) (i : ℕ) (Nat.sub_add_cancel i.is_le) ≫
        eqToHom (hZ' n).symm := rfl

/-- `hpin` computed from any splitting with the same two numbers. -/
private theorem hpin_eq (n : ℕ) (i : Fin (n + 2)) (q p : ℕ) (hn : q + p = n + 1)
    (hp : (i : ℕ) = p) :
    hpin AA BB hZ hZ' n i = eqToHom (hZ n) ≫ hcen AA BB n q p hn ≫ eqToHom (hZ' n).symm := by
  rw [hpin_def, hcen_congr AA BB n (n + 1 - (i : ℕ)) (i : ℕ) q p _ hn (by omega) hp]

/-- The end `i = 0` of the family is `a ⋆ b_n`. -/
private theorem hpin_zero (n : ℕ) :
    hpin AA BB hZ hZ' n 0 = eqToHom (hZ n) ≫ hstar AA BB (n + 1) 0 ≫ eqToHom (hZ' n).symm := by
  rw [hpin_eq AA BB hZ hZ' n 0 (n + 1) 0 (by omega) (by simp), hcen_p_zero]

/-- The end `i = n + 1` of the family is `a_n ⋆ b`. -/
private theorem hpin_last (n : ℕ) :
    hpin AA BB hZ hZ' n (Fin.last (n + 1)) =
      eqToHom (hZ n) ≫ hstar AA BB 0 (n + 1) ≫ eqToHom (hZ' n).symm := by
  rw [hpin_eq AA BB hZ hZ' n (Fin.last (n + 1)) 0 (n + 1) (by omega) (by simp), hcen_q_zero]

/-- The first homotopy relation for `Z` and `Z'`. -/
private theorem hpin_face_gt
    (hAf : ∀ (m : ℕ) (j : Fin (m + 1)), AA (m + 1) ≫ Functor.whiskerRight (face d m j) G' =
      Functor.whiskerRight (face d m j) G ≫ AA m)
    (hZδ : ∀ (n : ℕ) (j : Fin (n + 2)), Z.left.δ j = eqToHom (hZ (n + 1)) ≫
      (conj F G).map (face d (n + 1) j) ≫ eqToHom (hZ n).symm)
    (hZδ' : ∀ (n : ℕ) (j : Fin (n + 2)), Z'.left.δ j = eqToHom (hZ' (n + 1)) ≫
      (conj F' G').map (face d (n + 1) j) ≫ eqToHom (hZ' n).symm)
    (n : ℕ) (j i : Fin (n + 2)) (hji : j ≤ i) :
    hpin AA BB hZ hZ' (n + 1) i.succ ≫ Z'.left.δ j = Z.left.δ j ≫ hpin AA BB hZ hZ' n i := by
  have hji' : (j : ℕ) ≤ (i : ℕ) := hji
  have hi : (i : ℕ) ≤ n + 1 := i.is_le
  rw [hpin_eq AA BB hZ hZ' (n + 1) i.succ (n + 1 - (i : ℕ)) ((i : ℕ) + 1) (by omega) (by simp),
    hpin_eq AA BB hZ hZ' n i (n + 1 - (i : ℕ)) (i : ℕ) (by omega) rfl]
  exact pinned_comm _ _ _ (hZ' n) rfl (hZδ' n j) (hZδ n j) rfl
    (hcen_face_left d AA BB hAf (by omega) ⟨(j : ℕ), by omega⟩ j rfl)

/-- The second homotopy relation for `Z` and `Z'`. -/
private theorem hpin_face_le
    (hBf : ∀ (m : ℕ) (j : Fin (m + 1)), BB (m + 1) ≫ Functor.whiskerLeft F' (face d m j) =
      Functor.whiskerLeft F (face d m j) ≫ BB m)
    (hZδ : ∀ (n : ℕ) (j : Fin (n + 2)), Z.left.δ j = eqToHom (hZ (n + 1)) ≫
      (conj F G).map (face d (n + 1) j) ≫ eqToHom (hZ n).symm)
    (hZδ' : ∀ (n : ℕ) (j : Fin (n + 2)), Z'.left.δ j = eqToHom (hZ' (n + 1)) ≫
      (conj F' G').map (face d (n + 1) j) ≫ eqToHom (hZ' n).symm)
    (n : ℕ) (j i : Fin (n + 2)) (hij : i ≤ j) :
    hpin AA BB hZ hZ' (n + 1) i.castSucc ≫ Z'.left.δ j =
      Z.left.δ j ≫ hpin AA BB hZ hZ' n i := by
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  have hj : (j : ℕ) ≤ n + 1 := j.is_le
  rw [hpin_eq AA BB hZ hZ' (n + 1) i.castSucc (n + 1 - (i : ℕ) + 1) (i : ℕ) (by omega) (by simp),
    hpin_eq AA BB hZ hZ' n i (n + 1 - (i : ℕ)) (i : ℕ) (by omega) rfl]
  exact pinned_comm _ _ _ (hZ' n) rfl (hZδ' n j) (hZδ n j) rfl
    (hcen_face_right d AA BB hBf (by omega) ⟨(j : ℕ) - (i : ℕ), by omega⟩ j
      (show (j : ℕ) = ((j : ℕ) - (i : ℕ)) + (i : ℕ) by omega))

/-- The third homotopy relation for `Z` and `Z'`. -/
private theorem hpin_degeneracy_gt
    (hAs : ∀ (m : ℕ) (j : Fin (m + 1)), AA (m + 1) ≫ Functor.whiskerRight (degeneracy s m j) G' =
      Functor.whiskerRight (degeneracy s m j) G ≫ AA (m + 2))
    (hZσ : ∀ (n : ℕ) (j : Fin (n + 1)), Z.left.σ j = eqToHom (hZ n) ≫
      (conj F G).map (degeneracy s n j) ≫ eqToHom (hZ (n + 1)).symm)
    (hZσ' : ∀ (n : ℕ) (j : Fin (n + 1)), Z'.left.σ j = eqToHom (hZ' n) ≫
      (conj F' G').map (degeneracy s n j) ≫ eqToHom (hZ' (n + 1)).symm)
    (n : ℕ) (j i : Fin (n + 1)) (hji : j ≤ i) :
    hpin AA BB hZ hZ' n i.succ ≫ Z'.left.σ j =
      Z.left.σ j ≫ hpin AA BB hZ hZ' (n + 1) i.succ.succ := by
  have hji' : (j : ℕ) ≤ (i : ℕ) := hji
  have hi : (i : ℕ) ≤ n := i.is_le
  rw [hpin_eq AA BB hZ hZ' n i.succ (n - (i : ℕ)) ((i : ℕ) + 1) (by omega) (by simp),
    hpin_eq AA BB hZ hZ' (n + 1) i.succ.succ (n - (i : ℕ)) ((i : ℕ) + 2) (by omega) (by simp)]
  exact pinned_comm _ _ _ (hZ' (n + 1)) rfl (hZσ' n j) (hZσ n j) rfl
    (hcen_degeneracy_left s AA BB hAs (by omega) ⟨(j : ℕ), by omega⟩ j rfl)

/-- The fourth homotopy relation for `Z` and `Z'`. -/
private theorem hpin_degeneracy_le
    (hBs : ∀ (m : ℕ) (j : Fin (m + 1)), BB (m + 1) ≫ Functor.whiskerLeft F' (degeneracy s m j) =
      Functor.whiskerLeft F (degeneracy s m j) ≫ BB (m + 2))
    (hZσ : ∀ (n : ℕ) (j : Fin (n + 1)), Z.left.σ j = eqToHom (hZ n) ≫
      (conj F G).map (degeneracy s n j) ≫ eqToHom (hZ (n + 1)).symm)
    (hZσ' : ∀ (n : ℕ) (j : Fin (n + 1)), Z'.left.σ j = eqToHom (hZ' n) ≫
      (conj F' G').map (degeneracy s n j) ≫ eqToHom (hZ' (n + 1)).symm)
    (n : ℕ) (j i : Fin (n + 1)) (hij : i ≤ j) :
    hpin AA BB hZ hZ' n i.castSucc ≫ Z'.left.σ j =
      Z.left.σ j ≫ hpin AA BB hZ hZ' (n + 1) i.castSucc.castSucc := by
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  have hj : (j : ℕ) ≤ n := j.is_le
  rw [hpin_eq AA BB hZ hZ' n i.castSucc (n - (i : ℕ) + 1) (i : ℕ) (by omega) (by simp),
    hpin_eq AA BB hZ hZ' (n + 1) i.castSucc.castSucc (n - (i : ℕ) + 2) (i : ℕ) (by omega)
      (by simp)]
  exact pinned_comm _ _ _ (hZ' (n + 1)) rfl (hZσ' n j) (hZσ n j) rfl
    (hcen_degeneracy_right s AA BB hBs (by omega) ⟨(j : ℕ) - (i : ℕ), by omega⟩ j
      (show (j : ℕ) = ((j : ℕ) - (i : ℕ)) + (i : ℕ) by omega))

variable (hZr : Z.right = F ⋙ G) (hZr' : Z'.right = F' ⋙ G')

/-- Compatibility of the end `i = 0` with the augmentations. -/
private theorem hpin_zero_comp_hom
    (hBf : BB 1 ≫ Functor.whiskerLeft F' (face d 0 0) =
      Functor.whiskerLeft F (face d 0 0) ≫ BB 0)
    (hZhom : Z.hom.app (op ⦋0⦌) = eqToHom (hZ 0) ≫ (conj F G).map (face d 0 0) ≫
      eqToHom hZr.symm)
    (hZhom' : Z'.hom.app (op ⦋0⦌) = eqToHom (hZ' 0) ≫ (conj F' G').map (face d 0 0) ≫
      eqToHom hZr'.symm) :
    hpin AA BB hZ hZ' 0 0 ≫ Z'.hom.app (op ⦋0⦌) =
      Z.hom.app (op ⦋0⦌) ≫ (eqToHom hZr ≫ hstar AA BB 0 0 ≫ eqToHom hZr'.symm) :=
  pinned_comm _ _ _ hZr' (hpin_zero AA BB hZ hZ' 0) hZhom' hZhom rfl
    (hstar_comm_whiskerRight AA BB _ hBf 0)

/-- Compatibility of the end `i = n + 1` with the augmentations. -/
private theorem hpin_last_comp_hom
    (hAf : AA 1 ≫ Functor.whiskerRight (face d 0 0) G' =
      Functor.whiskerRight (face d 0 0) G ≫ AA 0)
    (hZhom : Z.hom.app (op ⦋0⦌) = eqToHom (hZ 0) ≫ (conj F G).map (face d 0 0) ≫
      eqToHom hZr.symm)
    (hZhom' : Z'.hom.app (op ⦋0⦌) = eqToHom (hZ' 0) ≫ (conj F' G').map (face d 0 0) ≫
      eqToHom hZr'.symm) :
    hpin AA BB hZ hZ' 0 (Fin.last 1) ≫ Z'.hom.app (op ⦋0⦌) =
      Z.hom.app (op ⦋0⦌) ≫ (eqToHom hZr ≫ hstar AA BB 0 0 ≫ eqToHom hZr'.symm) :=
  pinned_comm _ _ _ hZr' (hpin_last AA BB hZ hZ' 0) hZhom' hZhom rfl
    (hstar_comm_whiskerLeft AA BB _ hAf 0)

end Assembly

namespace CategoryTheory.Godement

/-- **Stacks 0G5R**.
Let `Y : C ⥤ C` be an endofunctor with transformations `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`, let `F`,
`F' : A ⥤ C` and `G`, `G' : C ⥤ B` be functors, and let `Z`, `Z'` be the augmented simplicial
objects `G ∘ X ∘ F` and `G' ∘ X ∘ F'` of `A ⥤ B` obtained by conjugating the powers
`X_n = Y.iterate (n + 1)`. Let `(a_n) : G ∘ X ⟶ G' ∘ X` and `(b_n) : X ∘ F ⟶ X ∘ F'` be morphisms
of simplicial objects, i.e. families commuting with the faces `Godement.face d` and degeneracies
`Godement.degeneracy s`, compatible via the augmentations with `a : G ⟶ G'` and `b : F ⟶ F'`. Then
the two horizontal composites `a ⋆ (b_n)` and `(a_n) ⋆ b` are morphisms `Z ⟶ Z'` of augmented
simplicial objects with component `a ⋆ b` over the augmentations, and they are homotopic: there is
a simplicial homotopy from `(a_n) ⋆ b` to `a ⋆ (b_n)`, given by `h_{n, i} = a_{i-1} ⋆ b_{n-i}`. -/
@[stacks 0G5R]
public theorem exists_homotopy_hcomp_hcomp
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u} [Category.{v} C] {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (F F' : A ⥤ C) (G G' : C ⥤ B)
    (a : G ⟶ G') (b : F ⟶ F')
    (an : (n : ℕ) → (Y.iterate (n + 1) ⋙ G ⟶ Y.iterate (n + 1) ⋙ G'))
    (bn : (n : ℕ) → (F ⋙ Y.iterate (n + 1) ⟶ F' ⋙ Y.iterate (n + 1)))
    (han_face : ∀ (n : ℕ) (j : Fin (n + 2)),
      an (n + 1) ≫ Functor.whiskerRight (face d (n + 1) j) G' =
        Functor.whiskerRight (face d (n + 1) j) G ≫ an n)
    (han_degeneracy : ∀ (n : ℕ) (j : Fin (n + 1)),
      an n ≫ Functor.whiskerRight (degeneracy s n j) G' =
        Functor.whiskerRight (degeneracy s n j) G ≫ an (n + 1))
    (han_aug : an 0 ≫ Functor.whiskerRight (face d 0 0) G' =
      Functor.whiskerRight (face d 0 0) G ≫ a)
    (hbn_face : ∀ (n : ℕ) (j : Fin (n + 2)),
      bn (n + 1) ≫ Functor.whiskerLeft F' (face d (n + 1) j) =
        Functor.whiskerLeft F (face d (n + 1) j) ≫ bn n)
    (hbn_degeneracy : ∀ (n : ℕ) (j : Fin (n + 1)),
      bn n ≫ Functor.whiskerLeft F' (degeneracy s n j) =
        Functor.whiskerLeft F (degeneracy s n j) ≫ bn (n + 1))
    (hbn_aug : bn 0 ≫ Functor.whiskerLeft F' (face d 0 0) =
      Functor.whiskerLeft F (face d 0 0) ≫ b)
    (Z Z' : SimplicialObject.Augmented (A ⥤ B))
    (hZ : ∀ n : ℕ, Z.left.obj (op ⦋n⦌) = F ⋙ Y.iterate (n + 1) ⋙ G)
    (hZr : Z.right = F ⋙ G)
    (hZδ : ∀ (n : ℕ) (j : Fin (n + 2)), Z.left.δ j = eqToHom (hZ (n + 1)) ≫
      Functor.whiskerRight (Functor.whiskerLeft F (face d (n + 1) j)) G ≫ eqToHom (hZ n).symm)
    (hZσ : ∀ (n : ℕ) (j : Fin (n + 1)), Z.left.σ j = eqToHom (hZ n) ≫
      Functor.whiskerRight (Functor.whiskerLeft F (degeneracy s n j)) G ≫
        eqToHom (hZ (n + 1)).symm)
    (hZhom : Z.hom.app (op ⦋0⦌) = eqToHom (hZ 0) ≫
      Functor.whiskerRight (Functor.whiskerLeft F (face d 0 0)) G ≫ eqToHom hZr.symm)
    (hZ' : ∀ n : ℕ, Z'.left.obj (op ⦋n⦌) = F' ⋙ Y.iterate (n + 1) ⋙ G')
    (hZr' : Z'.right = F' ⋙ G')
    (hZδ' : ∀ (n : ℕ) (j : Fin (n + 2)), Z'.left.δ j = eqToHom (hZ' (n + 1)) ≫
      Functor.whiskerRight (Functor.whiskerLeft F' (face d (n + 1) j)) G' ≫ eqToHom (hZ' n).symm)
    (hZσ' : ∀ (n : ℕ) (j : Fin (n + 1)), Z'.left.σ j = eqToHom (hZ' n) ≫
      Functor.whiskerRight (Functor.whiskerLeft F' (degeneracy s n j)) G' ≫
        eqToHom (hZ' (n + 1)).symm)
    (hZhom' : Z'.hom.app (op ⦋0⦌) = eqToHom (hZ' 0) ≫
      Functor.whiskerRight (Functor.whiskerLeft F' (face d 0 0)) G' ≫ eqToHom hZr'.symm) :
    ∃ α β : Z ⟶ Z',
      (∀ n : ℕ, α.left.app (op ⦋n⦌) = eqToHom (hZ n) ≫
        NatTrans.hcomp (F := F ⋙ Y.iterate (n + 1)) (bn n) a ≫ eqToHom (hZ' n).symm) ∧
      (∀ n : ℕ, β.left.app (op ⦋n⦌) = eqToHom (hZ n) ≫
        NatTrans.hcomp b (an n) ≫ eqToHom (hZ' n).symm) ∧
      α.right = eqToHom hZr ≫ NatTrans.hcomp b a ≫ eqToHom hZr'.symm ∧
      β.right = eqToHom hZr ≫ NatTrans.hcomp b a ≫ eqToHom hZr'.symm ∧
      Nonempty (SimplicialObject.Homotopy β.left α.left) := by
  have hAf := aFam_face d a an han_face han_aug
  have hAs := aFam_degeneracy s a an han_degeneracy
  have hBf := bFam_face d b bn hbn_face hbn_aug
  have hBs := bFam_degeneracy s b bn hbn_degeneracy
  refine ⟨augmentedHomMk (homMk (fun n => hpin (aFam a an) (bFam b bn) hZ hZ' n 0) ?_ ?_)
      (eqToHom hZr ≫ NatTrans.hcomp b a ≫ eqToHom hZr'.symm) ?_,
    augmentedHomMk
      (homMk (fun n => hpin (aFam a an) (bFam b bn) hZ hZ' n (Fin.last (n + 1))) ?_ ?_)
      (eqToHom hZr ≫ NatTrans.hcomp b a ≫ eqToHom hZr'.symm) ?_,
    fun n => ?_, fun n => ?_, rfl, rfl,
    ⟨homotopyOfRel _ _ (fun n i => hpin (aFam a an) (bFam b bn) hZ hZ' n i) (fun n => rfl)
      (fun n => rfl)
      (fun n j i hji => hpin_face_gt d _ _ hZ hZ' hAf hZδ hZδ' n j i hji)
      (fun n j i hij => hpin_face_le d _ _ hZ hZ' hBf hZδ hZδ' n j i hij)
      (fun n j i hji => hpin_degeneracy_gt s _ _ hZ hZ' hAs hZσ hZσ' n j i hji)
      (fun n j i hij => hpin_degeneracy_le s _ _ hZ hZ' hBs hZσ hZσ' n j i hij)⟩⟩
  · exact fun n i =>
      (by simpa using (hpin_face_le d _ _ hZ hZ' hBf hZδ hZδ' n i 0 (Fin.zero_le _)).symm)
  · exact fun n i =>
      (by simpa using (hpin_degeneracy_le s _ _ hZ hZ' hBs hZσ hZσ' n i 0 (Fin.zero_le _)).symm)
  · exact hpin_zero_comp_hom d _ _ hZ hZ' hZr hZr' (hBf 0 0) hZhom hZhom'
  · exact fun n i =>
      (by simpa using (hpin_face_gt d _ _ hZ hZ' hAf hZδ hZδ' n i (Fin.last (n + 1))
        (Fin.le_last i)).symm)
  · exact fun n i =>
      (by simpa using (hpin_degeneracy_gt s _ _ hZ hZ' hAs hZσ hZσ' n i (Fin.last n)
        (Fin.le_last i)).symm)
  · exact hpin_last_comp_hom d _ _ hZ hZ' hZr hZr' (hAf 0 0) hZhom hZhom'
  · exact hpin_zero (aFam a an) (bFam b bn) hZ hZ' n
  · exact hpin_last (aFam a an) (bFam b bn) hZ hZ' n

end CategoryTheory.Godement

end Horizontal

/-! ### The two whiskerings of an endomorphism of the identity functor -/

section Whiskerings

/-! #### Endomorphisms of the identity functor are central -/

section Central

variable {C : Type u} [Category.{v} C]

/-- The outer whiskering `F ↦ f ⋆ 1_F` of an endomorphism `f` of the identity functor of `C`, as an
endomorphism of the identity functor of the category `C ⥤ C` of endofunctors of `C`. Naturality is
the identity `a ∘ (f ⋆ 1_F) = (f ⋆ 1_G) ∘ a`, i.e. the naturality of `f` at the components of
`a`. -/
private def centerWhiskerLeft (f : 𝟭 C ⟶ 𝟭 C) : 𝟭 (C ⥤ C) ⟶ 𝟭 (C ⥤ C) where
  app F := Functor.whiskerLeft F f
  naturality _ _ a := by ext c; exact f.naturality (a.app c)

/-- The inner whiskering `F ↦ 1_F ⋆ f` of an endomorphism `f` of the identity functor of `C`, as an
endomorphism of the identity functor of `C ⥤ C`. Naturality is the naturality of the transformation
being whiskered at the components of `f`. -/
private def centerWhiskerRight (f : 𝟭 C ⟶ 𝟭 C) : 𝟭 (C ⥤ C) ⟶ 𝟭 (C ⥤ C) where
  app F := Functor.whiskerRight f F
  naturality _ _ a := by ext c; exact (a.naturality (f.app c)).symm

variable (f : 𝟭 C ⟶ 𝟭 C)

private lemma centerWhiskerLeft_app (F : C ⥤ C) :
    (centerWhiskerLeft f).app F = Functor.whiskerLeft F f := rfl

private lemma centerWhiskerRight_app (F : C ⥤ C) :
    (centerWhiskerRight f).app F = Functor.whiskerRight f F := rfl

private lemma centerWhiskerLeft_app_id : (centerWhiskerLeft f).app (𝟭 C) = f := rfl

private lemma centerWhiskerRight_app_id : (centerWhiskerRight f).app (𝟭 C) = f := rfl

/-- The identity `a ∘ (f ⋆ 1_F) = f ⋆ a = (f ⋆ 1_G) ∘ a`: the outer whiskerings of an endomorphism
of the identity functor commute with every transformation of endofunctors. -/
private lemma whiskerLeft_id_naturality {F G : C ⥤ C} (a : F ⟶ G) :
    Functor.whiskerLeft F f ≫ a = a ≫ Functor.whiskerLeft G f :=
  ((centerWhiskerLeft f).naturality a).symm

end Central

section Augmented

variable {D : Type u'} [Category.{v'} D]

/-- Conjugating the component of an endomorphism of the identity functor along an equality of
objects does nothing. -/
private lemma eqToHom_comp_app_comp_eqToHom (η : 𝟭 D ⟶ 𝟭 D) {A B : D} (e : A = B) :
    eqToHom e ≫ η.app B ≫ eqToHom e.symm = η.app A := by
  subst e; simp

/-- Conjugating a commuting square of the form `p ≫ q = q ≫ p'` along equalities of objects
produces a commuting square of the conjugates. -/
private lemma conj_comp_conj {A B A' B' : D} (eA : A = A') (eB : B = B') {p : A' ⟶ A'}
    {q : A' ⟶ B'} {p' : B' ⟶ B'} (hpq : p ≫ q = q ≫ p') :
    (eqToHom eA ≫ p ≫ eqToHom eA.symm) ≫ eqToHom eA ≫ q ≫ eqToHom eB.symm
      = (eqToHom eA ≫ q ≫ eqToHom eB.symm) ≫ eqToHom eB ≫ p' ≫ eqToHom eB.symm := by
  subst eA; subst eB; simpa using hpq

/-- An endomorphism `η` of the identity functor of `D` induces an endomorphism of every augmented
simplicial object of `D`: `η.app` in every degree and `η.app X.right` over the augmentation. All
three commutations — with the faces, the degeneracies and the augmentation — are instances of the
naturality of `η`. -/
private def augmentedEndo (η : 𝟭 D ⟶ 𝟭 D) (X : SimplicialObject.Augmented D) : X ⟶ X where
  left :=
    { app := fun n => η.app (X.left.obj n)
      naturality := fun _ _ g => η.naturality (X.left.map g) }
  right := η.app X.right
  w := by ext n; exact (η.naturality (X.hom.app n)).symm

private lemma augmentedEndo_left_app (η : 𝟭 D ⟶ 𝟭 D) (X : SimplicialObject.Augmented D)
    (n : SimplexCategoryᵒᵖ) : (augmentedEndo η X).left.app n = η.app (X.left.obj n) := rfl

private lemma augmentedEndo_right (η : 𝟭 D ⟶ 𝟭 D) (X : SimplicialObject.Augmented D) :
    (augmentedEndo η X).right = η.app X.right := rfl

end Augmented

/-! #### The interpolating family `h_{n, i} = 1_i ⋆ f ⋆ 1_{n + 1 - i}` -/

section Family

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- The family `1_i ⋆ f ⋆ 1_{n - i} : Y^n ⟶ Y^n` interpolating between `f ⋆ 1_{Y^n}` and
`1_{Y^n} ⋆ f`, whiskering `f` into the `i`-th of the `n` copies of `Y` in `Y^n` counted from the
outside. It is defined by the recursion `hFam f n 0 = f ⋆ 1_{Y^n}` and
`hFam f (n + 1) (i + 1) = (hFam f n i) ⋆ 1_Y`; the interpolating `h_{n, i}` is
`hFam f (n + 1) i`. -/
private def hFam (f : 𝟭 C ⟶ 𝟭 C) :
    (n : ℕ) → Fin (n + 1) → (Y.iterate n ⟶ Y.iterate n) :=
  Nat.rec (motive := fun n => Fin (n + 1) → (Y.iterate n ⟶ Y.iterate n))
    (fun _ => Functor.whiskerLeft (Y.iterate 0) f)
    (fun n ih i => Fin.cases (Functor.whiskerLeft (Y.iterate (n + 1)) f)
      (fun j => Functor.whiskerRight (ih j) Y) i)

variable (f : 𝟭 C ⟶ 𝟭 C)

/-- The first defining clause: the outermost member of the family is the outer whiskering. -/
private lemma hFam_zero (n : ℕ) :
    hFam f n 0 = Functor.whiskerLeft (Y.iterate n) f := by
  cases n <;> rfl

/-- The second defining clause. -/
private lemma hFam_succ (n : ℕ) (j : Fin (n + 1)) :
    hFam f (n + 1) j.succ = Functor.whiskerRight (hFam f n j) Y := rfl

/-- The innermost member of the family is the inner whiskering. -/
private lemma hFam_last (n : ℕ) :
    hFam f n (Fin.last n) = Functor.whiskerRight f (Y.iterate n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Fin.succ_last, hFam_succ, ih]; rfl

end Family

/-! #### The four relations involving a face or a degeneracy -/

section Relations

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C}

/-- The recursion defining `Godement.face`, `Godement.degeneracy` and `hFam`, as an induction
principle for the pairs of indices the homotopy relations are indexed by: a property of a degree
`n` and two indices `j ≤ i` which holds at `j = 0` and passes from `(n, j, i)` to
`(n + 1, j.succ, i.succ)` holds always. The case `i = 0` never arises, `j ≤ i` forcing `j = 0`
there. -/
private theorem succ_induction_le {P : (n : ℕ) → Fin (n + 1) → Fin (n + 1) → Prop}
    (h0 : ∀ n i, P n 0 i) (hs : ∀ n j i, P n j i → P (n + 1) j.succ i.succ) :
    ∀ (n : ℕ) (j i : Fin (n + 1)), j ≤ i → P n j i := by
  intro n
  induction n with
  | zero => exact fun j i _ => Fin.cases (h0 0 i) (fun j => j.elim0) j
  | succ n ih =>
      intro j i hji
      cases j using Fin.cases with
      | zero => exact h0 _ i
      | succ j =>
          cases i using Fin.cases with
          | zero => simp at hji
          | succ i =>
              exact hs n j i (ih j i (by grind))

/-- The mirror image of `succ_induction_le`, for a pair of indices `i ≤ j`: a property which holds
at `i = 0` and passes from `(n, j, i)` to `(n + 1, j.succ, i.succ)` holds always. -/
private theorem succ_induction_ge {P : (n : ℕ) → Fin (n + 1) → Fin (n + 1) → Prop}
    (h0 : ∀ n j, P n j 0) (hs : ∀ n j i, P n j i → P (n + 1) j.succ i.succ) (n : ℕ)
    (j i : Fin (n + 1)) (hij : i ≤ j) : P n j i :=
  succ_induction_le (P := fun n j i => P n i j) h0 (fun n j i => hs n i j) n i j hij

variable (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (f : 𝟭 C ⟶ 𝟭 C)

/-- The first homotopy relation for the family `hFam`: for `i > j` the face `d^n_j` carries
`h_{n, i}` to `h_{n - 1, i - 1}`. -/
private lemma hFam_succ_comp_face (n : ℕ) (j i : Fin (n + 1)) (hji : j ≤ i) :
    hFam f (n + 1) i.succ ≫ Godement.face d n j
      = Godement.face d n j ≫ hFam f n i :=
  succ_induction_le (P := fun n j i => hFam f (n + 1) i.succ ≫ Godement.face d n j
      = Godement.face d n j ≫ hFam f n i)
    (fun n i => by
      rw [face_zero]; exact (Functor.whiskerLeft_comp_whiskerRight (hFam f n i) d).symm)
    (fun _ _ _ ih => whiskerRight_comp_congr ih) n j i hji

/-- The second homotopy relation for the family `hFam`: for `i ≤ j` the face `d^n_j` carries
`h_{n, i}` to `h_{n - 1, i}`. -/
private lemma hFam_castSucc_comp_face (n : ℕ) (j i : Fin (n + 1)) (hij : i ≤ j) :
    hFam f (n + 1) i.castSucc ≫ Godement.face d n j
      = Godement.face d n j ≫ hFam f n i :=
  succ_induction_ge (P := fun n j i => hFam f (n + 1) i.castSucc ≫ Godement.face d n j
      = Godement.face d n j ≫ hFam f n i)
    (fun n j => by
      simp only [Fin.castSucc_zero, hFam_zero]
      exact whiskerLeft_id_naturality f (Godement.face d n j))
    (fun _ _ _ ih => whiskerRight_comp_congr ih) n j i hij

/-- The third homotopy relation for the family `hFam`: for `i > j` the degeneracy `s^n_j` carries
`h_{n, i}` to `h_{n + 1, i + 1}`. -/
private lemma hFam_succ_comp_degeneracy (n : ℕ) (j i : Fin (n + 1)) (hji : j ≤ i) :
    hFam f (n + 1) i.succ ≫ Godement.degeneracy s n j
      = Godement.degeneracy s n j ≫ hFam f (n + 2) i.succ.succ :=
  succ_induction_le (P := fun n j i => hFam f (n + 1) i.succ ≫ Godement.degeneracy s n j
      = Godement.degeneracy s n j ≫ hFam f (n + 2) i.succ.succ)
    (fun n i => by
      rw [degeneracy_zero]; exact (Functor.whiskerLeft_comp_whiskerRight (hFam f n i) s).symm)
    (fun _ _ _ ih => whiskerRight_comp_congr ih) n j i hji

/-- The fourth homotopy relation for the family `hFam`: for `i ≤ j` the degeneracy `s^n_j` carries
`h_{n, i}` to `h_{n + 1, i}`. -/
private lemma hFam_castSucc_comp_degeneracy (n : ℕ) (j i : Fin (n + 1)) (hij : i ≤ j) :
    hFam f (n + 1) i.castSucc ≫ Godement.degeneracy s n j
      = Godement.degeneracy s n j ≫ hFam f (n + 2) i.castSucc.castSucc :=
  succ_induction_ge (P := fun n j i => hFam f (n + 1) i.castSucc ≫ Godement.degeneracy s n j
      = Godement.degeneracy s n j ≫ hFam f (n + 2) i.castSucc.castSucc)
    (fun n j => by
      simp only [Fin.castSucc_zero, hFam_zero]
      exact whiskerLeft_id_naturality f (Godement.degeneracy s n j))
    (fun _ _ _ ih => whiskerRight_comp_congr ih) n j i hij

end Relations

namespace CategoryTheory.Godement

/-- **Stacks 0G5S**.
Let `Y : C ⥤ C` be an endofunctor with transformations `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`, and let
`X` be an augmented simplicial object of the category `C ⥤ C` of endofunctors of `C` whose terms
are the powers `X_n = Y.iterate (n + 1)`, whose faces and degeneracies are `Godement.face d` and
`Godement.degeneracy s`, and whose augmentation has target `𝟭 C`. Let `f : 𝟭 C ⟶ 𝟭 C` be an
endomorphism of the identity functor. Then the two whiskerings `f ⋆ 1_{X_n}` and `1_{X_n} ⋆ f` of
`f` onto the terms of `X` are morphisms of simplicial objects, compatible with `f` through the
augmentation `ε : X ⟶ 𝟭 C`, i.e. they are endomorphisms of `X` in the category of augmented
simplicial objects with component `f` over `𝟭 C`. Moreover they are homotopic: there is a
simplicial homotopy from `1_X ⋆ f` to `f ⋆ 1_X`, given by `h_{n, i} = 1_i ⋆ f ⋆ 1_{n + 1 - i}`. -/
@[stacks 0G5S]
public theorem exists_homotopy_whiskerLeft_whiskerRight {C : Type u} [Category.{v} C]
    {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (f : 𝟭 C ⟶ 𝟭 C)
    (X : SimplicialObject.Augmented (C ⥤ C))
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = Y.iterate (n + 1)) (hX : X.right = 𝟭 C)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)),
      X.left.δ j = eqToHom (h (n + 1)) ≫ face d (n + 1) j ≫ eqToHom (h n).symm)
    (hσ : ∀ (n : ℕ) (j : Fin (n + 1)),
      X.left.σ j = eqToHom (h n) ≫ degeneracy s n j ≫ eqToHom (h (n + 1)).symm) :
    ∃ α β : X ⟶ X,
      (∀ n : ℕ, α.left.app (op ⦋n⦌) =
        eqToHom (h n) ≫ Functor.whiskerLeft (Y.iterate (n + 1)) f ≫ eqToHom (h n).symm) ∧
      (∀ n : ℕ, β.left.app (op ⦋n⦌) =
        eqToHom (h n) ≫ Functor.whiskerRight f (Y.iterate (n + 1)) ≫ eqToHom (h n).symm) ∧
      α.right = eqToHom hX ≫ f ≫ eqToHom hX.symm ∧
      β.right = eqToHom hX ≫ f ≫ eqToHom hX.symm ∧
      Nonempty (SimplicialObject.Homotopy β.left α.left) := by
  refine ⟨augmentedEndo (centerWhiskerLeft f) X, augmentedEndo (centerWhiskerRight f) X,
    fun n => ?_, fun n => ?_, ?_, ?_, ⟨?_⟩⟩
  · rw [augmentedEndo_left_app, ← eqToHom_comp_app_comp_eqToHom (centerWhiskerLeft f) (h n),
      centerWhiskerLeft_app]
  · rw [augmentedEndo_left_app, ← eqToHom_comp_app_comp_eqToHom (centerWhiskerRight f) (h n),
      centerWhiskerRight_app]
  · rw [augmentedEndo_right, ← eqToHom_comp_app_comp_eqToHom (centerWhiskerLeft f) hX,
      centerWhiskerLeft_app_id]
  · rw [augmentedEndo_right, ← eqToHom_comp_app_comp_eqToHom (centerWhiskerRight f) hX,
      centerWhiskerRight_app_id]
  · refine homotopyOfRel _ _
      (fun n i => eqToHom (h n) ≫ hFam f (n + 1) i ≫ eqToHom (h n).symm)
      (fun n => ?_) (fun n => ?_) (fun n j i hji => ?_) (fun n j i hij => ?_)
      (fun n j i hji => ?_) (fun n j i hij => ?_)
    · rw [hFam_zero]
      exact eqToHom_comp_app_comp_eqToHom (centerWhiskerLeft f) (h n)
    · rw [hFam_last]
      exact eqToHom_comp_app_comp_eqToHom (centerWhiskerRight f) (h n)
    · rw [hδ n j]
      exact conj_comp_conj (h (n + 1)) (h n) (hFam_succ_comp_face d f (n + 1) j i hji)
    · rw [hδ n j]
      exact conj_comp_conj (h (n + 1)) (h n) (hFam_castSucc_comp_face d f (n + 1) j i hij)
    · rw [hσ n j]
      exact conj_comp_conj (h n) (h (n + 1)) (hFam_succ_comp_degeneracy s f n j i hji)
    · rw [hσ n j]
      exact conj_comp_conj (h n) (h (n + 1)) (hFam_castSucc_comp_degeneracy s f n j i hij)

end CategoryTheory.Godement

end Whiskerings

end
