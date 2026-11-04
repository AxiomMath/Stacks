module

public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# Lifting isomorphisms along a directed system over a base

Let `P` be a coherent pullback pseudofunctor datum and `S` a directed system over a base `b` with
a cone.  When `Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)` for all four
pairs taken from two objects `X`, `Y` of the fibre over `b`, every isomorphism `k^*X ≅ k^*Y` at
the vertex is the image of an isomorphism `k_j^*X ≅ k_j^*Y` at some stage.  This is the form in
which full faithfulness of the comparison out of a colimit of categories is used to descend
isomorphisms.  The file also records that the colimit statement may be checked on the stages
beyond a given one.

## Main definitions

* `CategoryTheory.PullbackData.LimitSystem.restrictIndex`: the stages beyond a given one.

## Main results

* `CategoryTheory.PullbackData.factorHom_comp_hom` and `factorHom_id_hom`: the map attached to a
  factorisation respects composition and identities of morphisms.
* `CategoryTheory.PullbackData.LimitSystem.IsColim.exists_iso`: the lifting of isomorphisms.
* `CategoryTheory.PullbackData.LimitSystem.isColim_of_restrictIndex`: the colimit statement on
  the stages beyond a given one gives it on all stages.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D)

/-- The map of morphism sets attached to a factorisation respects composition. -/
theorem factorHom_comp_hom {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k)
    {X Y Z : D c} (φ : (P.pull g).obj X ⟶ (P.pull g).obj Y)
    (ψ : (P.pull g).obj Y ⟶ (P.pull g).obj Z) :
    P.factorHom h (φ ≫ ψ) = P.factorHom h φ ≫ P.factorHom h ψ := by
  simp [factorHom, Functor.conjHom]

/-- The map of morphism sets attached to a factorisation sends identities to identities. -/
theorem factorHom_id_hom {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k)
    (X : D c) : P.factorHom h (𝟙 ((P.pull g).obj X)) = 𝟙 _ := by
  simp [factorHom, Functor.conjHom]

/-- Two maps of morphism sets attached to a factorisation compose to the identity iff the
factorisation of their composite is the factorisation of the identity. -/
private theorem factorHom_comp_eq_id_iff {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    {h : f ≫ g = k} {X Y : D c} {x : (P.pull g).obj X ⟶ (P.pull g).obj Y}
    {y : (P.pull g).obj Y ⟶ (P.pull g).obj X} :
    P.factorHom h (x ≫ y) = P.factorHom h (𝟙 _) ↔ P.factorHom h x ≫ P.factorHom h y = 𝟙 _ := by
  rw [factorHom_comp_hom, factorHom_id_hom]

namespace LimitSystem

variable {P} {b : A} {J : Type w} [Preorder J] {S : LimitSystem (A := A) b J}

/-- **Lifting isomorphisms.**  If the colimit statement holds for the four pairs of objects taken
from `X` and `Y`, every isomorphism `k^*X ≅ k^*Y` at the vertex is the image of an isomorphism
`k_j^*X ≅ k_j^*Y` at some stage. -/
theorem IsColim.exists_iso (hP : P.IsCoherent) [IsDirected J (· ≤ ·)] {X Y : D b}
    (hXY : S.IsColim P X Y) (hYX : S.IsColim P Y X) (hXX : S.IsColim P X X)
    (hYY : S.IsColim P Y Y) (φ : (P.pull S.limitToBase).obj X ≅ (P.pull S.limitToBase).obj Y) :
    ∃ (j : J) (c : (P.pull (S.toBase j)).obj X ≅ (P.pull (S.toBase j)).obj Y),
      S.projHom P X Y j c.hom = φ.hom := by
  obtain ⟨i₁, a, ha⟩ := hXY.exists_stage φ.hom
  obtain ⟨i₂, a', ha'⟩ := hYX.exists_stage φ.inv
  obtain ⟨k, h₁, h₂⟩ := directed_of (· ≤ ·) i₁ i₂
  set x := S.trans P X Y i₁ k h₁ a
  set y := S.trans P Y X i₂ k h₂ a'
  have hx : S.projHom P X Y k x = φ.hom := (projHom_trans hP X Y h₁ a).trans ha
  have hy : S.projHom P Y X k y = φ.inv := (projHom_trans hP Y X h₂ a').trans ha'
  have hxy : S.projHom P X X k (x ≫ y) = S.projHom P X X k (𝟙 _) :=
    P.factorHom_comp_eq_id_iff.2 ((congrArg₂ (· ≫ ·) hx hy).trans φ.hom_inv_id)
  have hyx : S.projHom P Y Y k (y ≫ x) = S.projHom P Y Y k (𝟙 _) :=
    P.factorHom_comp_eq_id_iff.2 ((congrArg₂ (· ≫ ·) hy hx).trans φ.inv_hom_id)
  obtain ⟨m₁, hm₁, e₁⟩ := hXX.exists_trans_eq k _ _ hxy
  obtain ⟨m₂, hm₂, e₂⟩ := hYY.exists_trans_eq k _ _ hyx
  obtain ⟨m, hm₁m, hm₂m⟩ := directed_of (· ≤ ·) m₁ m₂
  have e₁' : S.trans P X X k m (hm₁.trans hm₁m) (x ≫ y) =
      S.trans P X X k m (hm₁.trans hm₁m) (𝟙 _) := by
    rw [← trans_trans hP X X hm₁ hm₁m, e₁, trans_trans hP]
  have e₂' : S.trans P Y Y k m (hm₂.trans hm₂m) (y ≫ x) =
      S.trans P Y Y k m (hm₂.trans hm₂m) (𝟙 _) := by
    rw [← trans_trans hP Y Y hm₂ hm₂m, e₂, trans_trans hP]
  refine ⟨m, ⟨S.trans P X Y k m (hm₁.trans hm₁m) x, S.trans P Y X k m (hm₁.trans hm₁m) y,
    P.factorHom_comp_eq_id_iff.1 e₁', P.factorHom_comp_eq_id_iff.1 e₂'⟩, ?_⟩
  exact (projHom_trans hP X Y _ x).trans hx

/-! ### The stages beyond a given one -/

/-- **The stages of a system beyond a given one**, as a system over the same base. -/
def restrictIndex (S : LimitSystem (A := A) b J) (j₀ : J) :
    LimitSystem (A := A) b {j // j₀ ≤ j} where
  stage j := S.stage j.1
  toBase j := S.toBase j.1
  transition h := S.transition h
  transition_toBase h := S.transition_toBase h
  transition_comp h h' := S.transition_comp h h'
  limit := S.limit
  limitToBase := S.limitToBase
  proj j := S.proj j.1
  proj_toBase j := S.proj_toBase j.1
  proj_transition h := S.proj_transition h

/-- **The colimit statement on the stages beyond a given one gives it on all stages**, the index
being directed. -/
theorem isColim_of_restrictIndex (hP : P.IsCoherent) [IsDirected J (· ≤ ·)] (j₀ : J) {X Y : D b}
    (h : (S.restrictIndex j₀).IsColim P X Y) : S.IsColim P X Y where
  ι_trans i j hij φ := projHom_trans hP X Y hij φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := h.exists_stage ψ
    exact ⟨i.1, φ, hφ⟩
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨m, hm₀, hmi⟩ := directed_of (· ≤ ·) j₀ i
    have hm : S.projHom P X Y m (S.trans P X Y i m hmi φ) =
        S.projHom P X Y m (S.trans P X Y i m hmi φ') := by
      rw [projHom_trans hP, projHom_trans hP]
      exact hφ
    obtain ⟨n, hn, hnm⟩ := h.exists_trans_eq ⟨m, hm₀⟩ _ _ hm
    refine ⟨n.1, hmi.trans hn, ?_⟩
    have e := hnm
    change S.trans P X Y m n.1 hn (S.trans P X Y i m hmi φ) =
      S.trans P X Y m n.1 hn (S.trans P X Y i m hmi φ') at e
    rwa [trans_trans hP, trans_trans hP] at e

end LimitSystem

end CategoryTheory.PullbackData

end
