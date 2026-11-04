module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Tactic.Ring

/-!
# Extra degeneracies at the last face

Mathlib's `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy` records a contraction of an
augmented simplicial object which is split off by the *zeroth* face: its data is a section `s'` of
the augmentation together with maps `s n : X_n ⟶ X_{n+1}` satisfying `s n ≫ δ 0 = 𝟙` and
`s (n + 1) ≫ δ i.succ = δ i ≫ s n`.

This file records the mirror-image notion, `ExtraDegeneracyLast`, where the new degeneracy is
split off by the *last* face: `s n ≫ δ (Fin.last (n + 1)) = 𝟙` and
`s (n + 1) ≫ δ i.castSucc = δ i ≫ s n`. The two notions are exchanged degreewise by the covariant
involution `SimplicialObject.opFunctor`, which Mathlib builds from `SimplexCategory.rev`
(`SimplexCategory.rev_map_δ : rev.map (δ i) = δ i.rev`). What Mathlib does *not* have is a
comparison of the alternating face map complexes along that involution — the differential acquires
the sign `(-1) ^ n` — so the homotopy equivalence below cannot be obtained by transporting
`ExtraDegeneracy.homotopyEquiv`, and the contracting homotopy is built directly instead.

The mirror-image notion is the one that occurs for the Godement (bar) resolution of a free object.
If `G = U ∘ V` is the comonad of an adjunction `U ⊣ V` and `B = U E` is a free object, then
`θ = U η_E : B ⟶ G B` is a coalgebra structure map, and in the standard resolution
`X_n = G^{n+1} B` — whose faces `δ i` insert the counit into the `i`-th factor counted *from the
outside* — the maps `s n = G^{n+1} θ` insert a new *innermost* factor. These satisfy
`δ (Fin.last (n + 1)) ∘ s n = G^{n+1}(ε_B ∘ θ) = 𝟙` by the triangle identity and
`δ i ∘ s (n + 1) = s n ∘ δ i` for the remaining faces by naturality: an `ExtraDegeneracyLast`,
never an `ExtraDegeneracy`.

## Main definitions

* `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracyLast`: the structure.
* `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracyLast.map`: transport along a functor.

## Main results

* `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracyLast.homotopyEquiv`: in a preadditive
  category with a zero object, the augmentation on the alternating face map complex of an
  augmented simplicial object carrying an `ExtraDegeneracyLast` is a homotopy equivalence onto the
  augmentation point in degree `0`.

## Implementation notes

The contracting homotopy has components `(-1) ^ n • s n`, where Mathlib's zeroth-face version has
`-s n`: the sign depends on the degree because the face which cancels `s n` is `δ (n + 1)` rather
than `δ 0`, and so contributes `(-1) ^ (n + 1)` rather than `1` to the alternating sum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe v v' u u'

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- The datum of an extra degeneracy *at the last face* of an augmented simplicial object `X`:
morphisms `s'` and `s n` which formally behave like extra degeneracies inserted next to the
augmentation point, so that it is the last face `δ (n + 1)`, rather than the zeroth face, which
cancels them. This is the structure carried by the Godement resolution of a free object. -/
@[ext]
public structure ExtraDegeneracyLast (X : SimplicialObject.Augmented C) where
  /-- a section of the augmentation in dimension `0` -/
  s' : X.right ⟶ X.left _⦋0⦌
  /-- the extra degeneracy -/
  s : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌
  /-- `s'` is a section of the augmentation -/
  s'_comp_ε : s' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right := by cat_disch
  /-- the zeroth face of `s 0` is the idempotent cut out by the augmentation -/
  s₀_comp_δ₀ : s 0 ≫ X.left.δ 0 = X.hom.app (op ⦋0⦌) ≫ s' := by cat_disch
  /-- the last face cancels the extra degeneracy -/
  s_comp_δ_last : ∀ n : ℕ, s n ≫ X.left.δ (Fin.last (n + 1)) = 𝟙 _ := by cat_disch
  /-- the remaining faces commute past the extra degeneracy -/
  s_comp_δ : ∀ (n : ℕ) (i : Fin (n + 2)),
    s (n + 1) ≫ X.left.δ i.castSucc = X.left.δ i ≫ s n := by cat_disch

namespace ExtraDegeneracyLast

attribute [reassoc] s₀_comp_δ₀ s_comp_δ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ_last

/-- The augmentation of the image of an augmented simplicial object under a functor is the image
of its augmentation. -/
private lemma whiskering_obj_obj_hom_app {D : Type u'} [Category.{v'} D]
    (X : SimplicialObject.Augmented C) (F : C ⥤ D) (n : SimplexCategoryᵒᵖ) :
    (((whiskering C D).obj F).obj X).hom.app n = F.map (X.hom.app n) := by
  dsimp [whiskering, whiskeringObj]
  simp

/-- The faces of the image of an augmented simplicial object under a functor are the images of
its faces. -/
private lemma whiskering_obj_obj_left_δ {D : Type u'} [Category.{v'} D]
    (X : SimplicialObject.Augmented C) (F : C ⥤ D) {n : ℕ} (i : Fin (n + 2)) :
    (((whiskering C D).obj F).obj X).left.δ i = F.map (X.left.δ i) := rfl

/-- If `ed` is an extra degeneracy at the last face for `X : SimplicialObject.Augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy at the last face for the
augmented simplicial object in `D` obtained by applying `F` to `X`. -/
public def map {D : Type u'} [Category.{v'} D] {X : SimplicialObject.Augmented C}
    (ed : ExtraDegeneracyLast X) (F : C ⥤ D) :
    ExtraDegeneracyLast (((whiskering C D).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := by
    have h := congrArg F.map ed.s'_comp_ε
    rw [F.map_comp, F.map_id] at h
    rw [whiskering_obj_obj_hom_app]
    exact h
  s₀_comp_δ₀ := by
    have h := congrArg F.map ed.s₀_comp_δ₀
    rw [F.map_comp, F.map_comp] at h
    rw [whiskering_obj_obj_hom_app, whiskering_obj_obj_left_δ]
    exact h
  s_comp_δ_last n := by
    have h := congrArg F.map (ed.s_comp_δ_last n)
    rw [F.map_comp, F.map_id] at h
    rw [whiskering_obj_obj_left_δ]
    exact h
  s_comp_δ n i := by
    have h := congrArg F.map (ed.s_comp_δ n i)
    rw [F.map_comp, F.map_comp] at h
    rw [whiskering_obj_obj_left_δ, whiskering_obj_obj_left_δ]
    exact h

variable [Preadditive C] [HasZeroObject C]

/-- If `C` is a preadditive category with a zero object and `X` is an augmented simplicial object
in `C` that has an extra degeneracy at the last face, then the augmentation on the alternating
face map complex of `X` is a homotopy equivalence. -/
public noncomputable def homotopyEquiv {X : SimplicialObject.Augmented C}
    (ed : ExtraDegeneracyLast X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj X))
      ((ChainComplex.single₀ C).obj (point.obj X)) where
  hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')
  homotopyInvHomId := Homotopy.ofEq (by
    ext
    simp [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := AlternatingFaceMapComplex.obj X.left)])
  homotopyHomInvId :=
    { hom i := Pi.single (i + 1) ((-1 : ℤ) ^ i • ed.s i)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          have h₁ : ed.s 0 ≫ X.left.δ 1 = 𝟙 _ := by
            simpa using ed.s_comp_δ_last 0
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
          simp [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C := AlternatingFaceMapComplex.obj X.left),
            Fin.sum_univ_two, ed.s₀_comp_δ₀, h₁]
        | succ i =>
          have h₂ : ((-1 : ℤ) ^ i * (-1 : ℤ) ^ (i + 2)) = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow ⟨i + 1, by omega⟩
          have h₃ : ∀ x : ℕ, ((-1 : ℤ) ^ x * (-1 : ℤ) ^ (i + 1))
              = -((-1 : ℤ) ^ i * (-1 : ℤ) ^ x) := by
            intro x
            rw [pow_succ]
            ring
          rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
          simp [Fin.sum_univ_castSucc (n := i + 2), Preadditive.sum_comp,
            Preadditive.comp_sum, ed.s_comp_δ, ed.s_comp_δ_last, smul_smul,
            Finset.smul_sum, h₂, h₃] }

end ExtraDegeneracyLast

end CategoryTheory.SimplicialObject.Augmented

end
