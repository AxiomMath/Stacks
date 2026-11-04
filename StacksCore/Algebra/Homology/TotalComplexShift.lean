module

public import Mathlib.Algebra.Homology.TotalComplexShift
import StacksCore.Tactic.StacksAttribute

/-! ## The total complex and the shifts of a double complex

Stacks 0FLG shifts a double complex by `[a, b]`: `(A[a, b])^{p, q} = A^{p + a, q + b}` with the
differentials `(-1)^a d₁` and `(-1)^b d₂`, and gives an isomorphism
`γ : Tot(A)[a + b] → Tot(A[a, b])` which is `(-1)^{pb}` on the summand `A^{p, q}`.

Mathlib has the two elementary shifts: `HomologicalComplex₂.shiftFunctor₁ C a` is `[a, 0]` and
`HomologicalComplex₂.shiftFunctor₂ C b` is `[0, b]`, so Stacks' `A[a, b]` is
`(shiftFunctor₂ C b ⋙ shiftFunctor₁ C a).obj K` on the nose: its terms and its two
differentials agree with the tag's by `rfl`. Mathlib's comparison isomorphisms `totalShift₁Iso`
and `totalShift₂Iso` run in the opposite direction to `γ`, from `Tot(A[a, 0])` and
`Tot(A[0, b])` to `Tot(A)[a]` and `Tot(A)[b]`; the first has no sign, the second is `(-1)^{pb}`
on the summand `A^{p, q}`.

`totalShift₁₂Iso` below is the composite for a general `[a, b]`, hence the inverse of `γ`, and
`ι_totalShift₁₂Iso_inv_f` is `γ` itself with the tag's sign. The order of composition matters:
applying `totalShift₁Iso a` to `A[0, b]` and then `totalShift₂Iso b` to `A` produces `(-1)^{pb}`
with `p` the first index in `A`, which is the tag's choice; the other order is off by `(-1)^{ab}`,
which is Mathlib's `totalShift₁Iso_trans_totalShift₂Iso`.

The first points of Stacks 0G6A and 0G6B are the special cases `[0, 1]` and `[1, 0]`: the shift of
a double complex regarded as a complex of rows, respectively of columns, and the functorial
compatibility of `Tot` with it. These are `totalShift₂Iso`/`totalShift₁Iso` at `1` together with
their naturality lemmas, attributed below.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape

add_to_stacks 0FLG "the shift `[a, 0]`: `A^{p + a, q}` with the sign `(-1)^a` on `d₁`"
  HomologicalComplex₂.shiftFunctor₁
add_to_stacks 0FLG "the shift `[0, b]`: `A^{p, q + b}` with the sign `(-1)^b` on `d₂`"
  HomologicalComplex₂.shiftFunctor₂
add_to_stacks 0FLG "`γ⁻¹` for `[a, 0]`, without signs" HomologicalComplex₂.totalShift₁Iso
add_to_stacks 0FLG "`γ⁻¹` for `[0, b]`, the sign `(-1)^{pb}` on the summand `A^{p, q}`"
  HomologicalComplex₂.totalShift₂Iso
add_to_stacks 0FLG "combining `[a, 0]` and `[0, b]` in the other order costs the sign `(-1)^{ab}`"
  HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso

add_to_stacks 0G6B "point 1: the shift of `A` as a complex of columns is `[1, 0]`"
  HomologicalComplex₂.shiftFunctor₁
add_to_stacks 0G6B "point 1: `Tot` is compatible with the shift `[1, 0]`; the tag's `γ`, inverted"
  HomologicalComplex₂.totalShift₁Iso
add_to_stacks 0G6B "point 1: the compatibility isomorphism is functorial"
  HomologicalComplex₂.totalShift₁Iso_hom_naturality
add_to_stacks 0G6A "point 1: the shift of `A` as a complex of rows is `[0, 1]`"
  HomologicalComplex₂.shiftFunctor₂
add_to_stacks 0G6A "point 1: `Tot` is compatible with the shift `[0, 1]`; the tag's `γ`, inverted"
  HomologicalComplex₂.totalShift₂Iso
add_to_stacks 0G6A "point 1: the compatibility isomorphism is functorial"
  HomologicalComplex₂.totalShift₂Iso_hom_naturality

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (x y : ℤ) [K.HasTotal (up ℤ)]

/-- **Stacks 0FLG**, the inverse of the tag's `γ : Tot(A)[a + b] → Tot(A[a, b])`: the composite
of Mathlib's `totalShift₁Iso a` on `A[0, b]` and `totalShift₂Iso b` on `A`. On the summand
`A^{p, q}` it is `(-1)^{pb}`, the tag's sign; see `ι_totalShift₁₂Iso_hom_f`. -/
@[stacks 0FLG "the tag's `γ` for a general `[a, b]`, inverted to run in Mathlib's direction"]
noncomputable def totalShift₁₂Iso :
    ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x + y⟧ :=
  ((shiftFunctor₂ C y).obj K).totalShift₁Iso x ≪≫
    (shiftFunctor (CochainComplex C ℤ) x).mapIso (K.totalShift₂Iso y) ≪≫
      ((shiftFunctorAdd' (CochainComplex C ℤ) y x (x + y) (add_comm y x)).app
        (K.total (up ℤ))).symm

/-- **Stacks 0FLG**, the sign of `γ⁻¹`: on the summand `A^{p, q}` of `Tot(A[a, b])`, which is
the summand `A^{p + a, q + b}` of `A`, it is `(-1)^{(p + a) b}`. -/
@[reassoc, stacks 0FLG "the sign of `γ⁻¹`: `(-1)^{pb}` on the summand `A^{p, q}` of `Tot(A)`"]
lemma ι_totalShift₁₂Iso_hom_f (p q n : ℤ) (h : p + q = n) (p' : ℤ) (hp' : p' = p + x)
    (q' : ℤ) (hq' : q' = q + y) (n' : ℤ) (hn' : n' = n + (x + y)) :
    ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).ιTotal (up ℤ) p q n h ≫
        (K.totalShift₁₂Iso x y).hom.f n =
      (p' * y).negOnePow • (((shiftFunctor₂ C y).obj K).shiftFunctor₁XXIso p x p' hp' q).hom ≫
        (K.shiftFunctor₂XXIso p' q y q' hq').hom ≫ K.ιTotal (up ℤ) p' q' n' (by dsimp; lia) ≫
          (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) (x + y) n n' hn').inv := by
  subst hp' hq' hn'
  dsimp [totalShift₁₂Iso]
  rw [ι_totalShift₁Iso_hom_f_assoc _ x p q n h _ rfl _ rfl]
  dsimp
  simp only [id_comp, comp_id]
  rw [ι_totalShift₂Iso_hom_f_assoc _ y (p + x) q (n + x) (by lia) _ rfl (n + (x + y)) (by lia),
    CochainComplex.shiftFunctorAdd'_inv_app_f']
  dsimp
  simp only [id_comp, comp_id, Category.assoc, Iso.inv_hom_id, Linear.units_smul_comp]

/-- **Stacks 0FLG**, the tag's `γ : Tot(A)[a + b] → Tot(A[a, b])` itself: on the summand
`A^{p', q'}` of `Tot(A)[a + b]` it is `(-1)^{p' b}` times the identification of `A^{p', q'}` with
the summand `(A[a, b])^{p, q}`, where `p' = p + a` and `q' = q + b`. -/
@[reassoc, stacks 0FLG "the tag's `γ`: `ε(p, q, a, b) = (-1)^{pb}` on the summand `A^{p, q}`"]
lemma ι_totalShift₁₂Iso_inv_f (p q n : ℤ) (h : p + q = n) (p' : ℤ) (hp' : p' = p + x)
    (q' : ℤ) (hq' : q' = q + y) (n' : ℤ) (hn' : n' = n + (x + y)) :
    K.ιTotal (up ℤ) p' q' n' (by dsimp; lia) ≫
        (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) (x + y) n n' hn').inv ≫
          (K.totalShift₁₂Iso x y).inv.f n =
      (p' * y).negOnePow • (K.shiftFunctor₂XXIso p' q y q' hq').inv ≫
        (((shiftFunctor₂ C y).obj K).shiftFunctor₁XXIso p x p' hp' q).inv ≫
          ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).ιTotal (up ℤ) p q n h := by
  rw [← cancel_mono ((K.totalShift₁₂Iso x y).hom.f n), Category.assoc, Category.assoc,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f, Linear.units_smul_comp,
    Category.assoc, Category.assoc, ι_totalShift₁₂Iso_hom_f K x y p q n h p' hp' q' hq' n' hn']
  simp [Linear.comp_units_smul, smul_smul]

end HomologicalComplex₂
