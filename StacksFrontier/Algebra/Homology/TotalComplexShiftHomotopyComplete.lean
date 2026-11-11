module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.TotalComplexShift
public import StacksCore.Algebra.Homology.HomotopyCategory.HomComplexShift
public import StacksCore.Algebra.Homology.TotalComplexHomotopy

/-! # The total complex of a double complex regarded as a complex of columns

Stacks 0G6B regards a double complex `A^{•, •}` as the complex of complexes
`… → A^{-1, •} → A^{0, •} → A^{1, •} → …`, which is Mathlib's
`HomologicalComplex₂ C (up ℤ) (up ℤ) = CochainComplex (CochainComplex C ℤ) ℤ`, and shows that
`Tot` is compatible with four structures on complexes.

1. The shift of complexes of complexes is `[1, 0]` (`shiftFunctor₁ C 1` is `shiftFunctor _ 1` by
   definition), and `γ : Tot(A)[1] → Tot(A[1, 0])` is a functorial isomorphism without signs:
   it is the inverse of Mathlib's `totalShift₁Iso`, natural by `totalShift₁Iso_hom_naturality`,
   identity on summands by `ι_totalShift₁Iso_hom_f`.
2. A homotopy `h` between `f, g : A → B` gives the homotopy `h'` between `Tot(f)` and `Tot(g)`
   which is `h^{p, q}` on the summand `A^{p, q}`: this is `totalMapHomotopy₁`, and
   `ιTotal_totalMapHomotopy₁_hom_up` is the tag's formula, with the sign `ε₁ = 1`.
3. For `f = g`, the morphism `Tot(A) → Tot(B)[-1]` attached to `h'` by Stacks 011I
   (`Homotopy.equivHomShiftSelf`) is `γ⁻¹ ∘ Tot(h)`, where `h` is viewed as a morphism
   `A → B[-1, 0]` by 011I: `equivHomShiftSelf_totalMapHomotopy₁`.
4. A complex `0 → A → B → C → 0` of double complexes with splittings `s^p`, `π^p` of complexes in
   each column gives the complex `0 → Tot(A) → Tot(B) → Tot(C) → 0` (`totalShortComplex`), which
   is termwise split by the maps `(s')ⁿ`, `(π')ⁿ` with components `s^{p, q}`, `π^{p, q}`
   (`totalSplitting`), and the connecting morphism `δ'` of 011J for these splittings is
   `γ⁻¹ ∘ Tot(δ)`, `δ : C → A[1, 0]` that of the columns:
   `homOfDegreewiseSplit_totalShortComplex`.

The tag writes `δ : C^{•, •} → A^{•, •}[0, 1]` in point 4; the procedure of 011J applied to
complexes of columns gives a map to the shift `A[1]` of complexes of complexes, which point 1
identifies with `A^{•, •}[1, 0]`, and that is also the source of `Tot(δ)` in the tag's next
display. The statements here use `[1, 0]`.

`total_shift_homotopy_degreewiseSplit` collects the four points in one statement.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]

section homotopy

variable {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]

/-- **Stacks 0G6B**, point 2: the homotopy `h'` between `Tot(f)` and `Tot(g)` induced by a homotopy
`h` between maps of complexes of columns is `h^{p, q} : A^{p, q} → B^{p - 1, q}` on the summand
`A^{p, q}`, with no sign. -/
@[reassoc, stacks 0G6B "point 2: the tag's `h'` is `h^{p, q}` on the summand `A^{p, q}`, unsigned"]
lemma ιTotal_totalMapHomotopy₁_hom_up {f g : K ⟶ L} (h : Homotopy f g) (p q n : ℤ)
    (hpq : p + q = n) :
    K.ιTotal (up ℤ) p q n hpq ≫ (totalMapHomotopy₁ h (up ℤ)).hom n (n - 1) =
      (h.hom p (p - 1)).f q ≫ L.ιTotal (up ℤ) (p - 1) q (n - 1) (by dsimp; omega) := by
  rw [ιTotal_totalMapHomotopy₁_hom h (up ℤ) (p - 1) p q n (n - 1) hpq
    ((up ℤ).prev_eq' (by simp)), ιTotalOrZero_eq _ _ _ _ _ (by dsimp; omega)]
  exact one_smul _ _

/-- **Stacks 0G6B**, point 3: for a homotopy `h` from `f` to itself, viewed by Stacks 011I as a
morphism `A → B[-1, 0]`, the morphism `Tot(A) → Tot(B)[-1]` attached by 011I to the induced
homotopy `h'` from `Tot(f)` to itself is `Tot(h)` followed by `γ⁻¹ : Tot(B[-1, 0]) → Tot(B)[-1]`,
Mathlib's `totalShift₁Iso`. -/
@[stacks 0G6B "point 3: `h ↦ h'` is compatible with the identification of 011I, via `γ⁻¹`"]
theorem equivHomShiftSelf_totalMapHomotopy₁ {f : K ⟶ L} (h : Homotopy f f) :
    Homotopy.equivHomShiftSelf (total.map f (up ℤ)) (totalMapHomotopy₁ h (up ℤ)) =
      total.map (Homotopy.equivHomShiftSelf f h) (up ℤ) ≫ (L.totalShift₁Iso (-1)).hom := by
  ext n p q hpq
  rw [HomologicalComplex.comp_f, ιTotal_map_assoc, Homotopy.equivHomShiftSelf,
    Homotopy.equivHomShiftSelf, Homotopy.equivHomShift_f, Homotopy.equivHomShift_f,
    L.ι_totalShift₁Iso_hom_f (-1) p q n hpq (p + -1) rfl (n + -1) rfl]
  have := ιTotal_totalMapHomotopy₁_hom h (up ℤ) (p + -1) p q n (n + -1) hpq
    ((up ℤ).prev_eq' (by simp))
  have e : ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (p + -1, q) = 1 := rfl
  rw [ιTotalOrZero_eq _ _ _ _ _ (by dsimp at hpq ⊢; omega), e, one_smul] at this
  simp only [Homotopy.refl_hom, sub_zero, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Iso.refl_hom, shiftFunctor₁XXIso,
    eqToIso_refl, comp_id, id_comp]
  exact this

end homotopy

section split

variable (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))
  [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)]

/-- **Stacks 0G6B**, point 4: `Tot` applied to a complex `0 → A → B → C → 0` of double complexes
is a complex `0 → Tot(A) → Tot(B) → Tot(C) → 0`. -/
@[stacks 0G6B "point 4: `Tot` of a complex `0 → A → B → C → 0` of double complexes"]
noncomputable abbrev totalShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (total.map S.f (up ℤ)) (total.map S.g (up ℤ)) (by
    rw [← total.map_comp, S.zero]
    ext n p q hpq
    simp)

variable (σ : ∀ p, (S.map (HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) p)).Splitting)

namespace totalSplitting

variable {S}

omit [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)] in
lemma f_r (p q : ℤ) : (S.f.f p).f q ≫ (σ p).r.f q = 𝟙 _ := by
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ q) (σ p).f_r
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at this
  exact this

omit [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)] in
lemma s_g (p q : ℤ) : (σ p).s.f q ≫ (S.g.f p).f q = 𝟙 _ := by
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ q) (σ p).s_g
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at this
  exact this

omit [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)] in
lemma id (p q : ℤ) :
    ((σ p).r.f q ≫ (S.f.f p).f q : (S.X₂.X p).X q ⟶ (S.X₂.X p).X q) +
      ((S.g.f p).f q ≫ (σ p).s.f q : (S.X₂.X p).X q ⟶ (S.X₂.X p).X q) = 𝟙 _ := by
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ q) (σ p).id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.add_f_apply] at this
  exact this

omit [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)] in
lemma s_r (p q : ℤ) : (σ p).s.f q ≫ (σ p).r.f q = 0 := by
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ q) (σ p).s_r
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at this
  exact this

end totalSplitting

/-- **Stacks 0G6B**, point 4: the complex `0 → Tot(A) → Tot(B) → Tot(C) → 0` is termwise split,
by the maps `(s')ⁿ` and `(π')ⁿ` whose components are `s^{p, q}` and `π^{p, q}` for `p + q = n`. -/
@[stacks 0G6B "point 4: `Tot` of the sequence is termwise split by `s'`, `π'`"]
noncomputable def totalSplitting (n : ℤ) :
    ((totalShortComplex S).map (HomologicalComplex.eval C (up ℤ) n)).Splitting where
  r := S.X₂.totalDesc (fun p q hpq => (σ p).r.f q ≫ S.X₁.ιTotal (up ℤ) p q n hpq)
  s := S.X₃.totalDesc (fun p q hpq => (σ p).s.f q ≫ S.X₂.ιTotal (up ℤ) p q n hpq)
  f_r := by
    refine total.hom_ext (up ℤ) (fun p q hpq => ?_)
    simp [HomologicalComplex.eval_map, reassoc_of% (totalSplitting.f_r σ p q)]
  s_g := by
    refine total.hom_ext (up ℤ) (fun p q hpq => ?_)
    simp [HomologicalComplex.eval_map, reassoc_of% (totalSplitting.s_g σ p q)]
  id := by
    refine total.hom_ext (up ℤ) (fun p q hpq => ?_)
    simp only [ShortComplex.map_X₂, HomologicalComplex.eval_obj, ShortComplex.map_X₁,
      ShortComplex.map_f, HomologicalComplex.eval_map, ShortComplex.map_X₃,
      ShortComplex.map_g, Preadditive.comp_add, ι_totalDesc_assoc, Category.assoc,
      ιTotal_map, ιTotal_map_assoc, ι_totalDesc, comp_id]
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, totalSplitting.id σ p q,
      id_comp]

/-- The section `(s')ⁿ` of `totalSplitting` is `s^{p, q}` on the summand `C^{p, q}`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalSplitting_s (n p q : ℤ) (hpq : p + q = n) :
    S.X₃.ιTotal (up ℤ) p q n hpq ≫ (totalSplitting S σ n).s =
      (σ p).s.f q ≫ S.X₂.ιTotal (up ℤ) p q n hpq :=
  by simp [totalSplitting]

/-- The retraction `(π')ⁿ` of `totalSplitting` is `π^{p, q}` on the summand `B^{p, q}`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalSplitting_r (n p q : ℤ) (hpq : p + q = n) :
    S.X₂.ιTotal (up ℤ) p q n hpq ≫ (totalSplitting S σ n).r =
      (σ p).r.f q ≫ S.X₁.ιTotal (up ℤ) p q n hpq :=
  by simp [totalSplitting]

/-- **Stacks 0G6B**, point 4: the connecting morphism `δ' : Tot(C) → Tot(A)[1]` of Stacks 011J for
the splittings `s'`, `π'` of the total complexes is `Tot(δ)` followed by
`γ⁻¹ : Tot(A[1, 0]) → Tot(A)[1]`, where `δ : C → A[1, 0]` is the connecting morphism of 011J for
the splittings `s^p`, `π^p` of the complexes of columns. -/
@[stacks 0G6B "point 4: `δ' = γ⁻¹ ∘ Tot(δ)` for the connecting morphisms of 011J"]
theorem homOfDegreewiseSplit_totalShortComplex :
    CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (totalSplitting S σ) =
      total.map (CochainComplex.homOfDegreewiseSplit S σ) (up ℤ) ≫
        (S.X₁.totalShift₁Iso 1).hom := by
  ext n : 1
  refine total.hom_ext (up ℤ) (fun p q hpq => ?_)
  rw [HomologicalComplex.comp_f, ιTotal_map_assoc, CochainComplex.homOfDegreewiseSplit_f,
    CochainComplex.homOfDegreewiseSplit_f,
    S.X₁.ι_totalShift₁Iso_hom_f 1 p q n hpq (p + 1) rfl (n + 1) rfl]
  have hd₂ : (σ p).s.f q ≫ (S.X₂.X p).d q (q + 1) ≫ (σ p).r.f (q + 1) = 0 := by
    refine ((σ p).s.comm_assoc q (q + 1) ((σ p).r.f (q + 1))).trans ?_
    rw [totalSplitting.s_r, comp_zero]
  have e : ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (p, q) = 1 := rfl
  simp only [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v, ShortComplex.map_X₂, HomologicalComplex.eval_obj,
    ιTotal_totalSplitting_s_assoc, total_d, Preadditive.add_comp,
    Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc,
    S.X₂.d₁_eq (up ℤ) (show (up ℤ).Rel p (p + 1) by simp) q (n + 1) (by dsimp at hpq ⊢; omega),
    S.X₂.d₂_eq (up ℤ) p (show (up ℤ).Rel q (q + 1) by simp) (n + 1) (by dsimp at hpq ⊢; omega),
    Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc, ιTotal_totalSplitting_r,
    reassoc_of% hd₂, zero_comp,
    smul_zero, add_zero, HomologicalComplex.comp_f, shiftFunctor₁XXIso, eqToIso_refl,
    Iso.refl_hom, CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, comp_id, id_comp, e, one_smul]

end split

/-- **Stacks 0G6B**: taking the total complex of double complexes regarded as complexes of columns
is compatible with the shift `[1, 0]`, with homotopies, with the identification of self-homotopies
with morphisms to the shift (011I), and with the connecting morphisms of termwise split sequences
(011J). In order: `γ⁻¹ = totalShift₁Iso` is natural and has no signs on summands; `h'` is
`h^{p, q}` on `A^{p, q}`; the third point; and the fourth point, with the splittings of the total
complexes given by `s^{p, q}`, `π^{p, q}` on summands. -/
@[stacks 0G6B "the whole remark: points 1 to 4"]
theorem total_shift_homotopy_degreewiseSplit :
    (∀ (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
        (φ : K ⟶ L),
        total.map ((shiftFunctor₁ C 1).map φ) (up ℤ) ≫ (L.totalShift₁Iso 1).hom =
          (K.totalShift₁Iso 1).hom ≫ (total.map φ (up ℤ))⟦(1 : ℤ)⟧') ∧
    (∀ (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (p q n : ℤ)
        (hpq : p + q = n),
        ((shiftFunctor₁ C 1).obj K).ιTotal (up ℤ) p q n hpq ≫ (K.totalShift₁Iso 1).hom.f n =
          K.ιTotal (up ℤ) (p + 1) q (n + 1) (by dsimp; omega) ≫
            (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) 1 n (n + 1) rfl).inv) ∧
    (∀ (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
        (f g : K ⟶ L) (h : Homotopy f g) (p q n : ℤ) (hpq : p + q = n),
        K.ιTotal (up ℤ) p q n hpq ≫ (totalMapHomotopy₁ h (up ℤ)).hom n (n - 1) =
          (h.hom p (p - 1)).f q ≫ L.ιTotal (up ℤ) (p - 1) q (n - 1) (by dsimp; omega)) ∧
    (∀ (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
        (f : K ⟶ L) (h : Homotopy f f),
        Homotopy.equivHomShiftSelf (total.map f (up ℤ)) (totalMapHomotopy₁ h (up ℤ)) =
          total.map (Homotopy.equivHomShiftSelf f h) (up ℤ) ≫ (L.totalShift₁Iso (-1)).hom) ∧
    (∀ (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))
        [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)]
        (σ : ∀ p, (S.map (HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) p)).Splitting),
        (∀ (p q n : ℤ) (hpq : p + q = n),
          S.X₃.ιTotal (up ℤ) p q n hpq ≫ (totalSplitting S σ n).s =
            (σ p).s.f q ≫ S.X₂.ιTotal (up ℤ) p q n hpq) ∧
        (∀ (p q n : ℤ) (hpq : p + q = n),
          S.X₂.ιTotal (up ℤ) p q n hpq ≫ (totalSplitting S σ n).r =
            (σ p).r.f q ≫ S.X₁.ιTotal (up ℤ) p q n hpq) ∧
        CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (totalSplitting S σ) =
          total.map (CochainComplex.homOfDegreewiseSplit S σ) (up ℤ) ≫
            (S.X₁.totalShift₁Iso 1).hom) := by
  refine ⟨fun K L _ _ φ => totalShift₁Iso_hom_naturality φ 1,
    fun K _ p q n hpq => ?_,
    fun K L _ _ f g h p q n hpq => ιTotal_totalMapHomotopy₁_hom_up h p q n hpq,
    fun K L _ _ f h => equivHomShiftSelf_totalMapHomotopy₁ h,
    fun S _ _ _ σ => ⟨fun p q n hpq => ιTotal_totalSplitting_s S σ n p q hpq,
      fun p q n hpq => ιTotal_totalSplitting_r S σ n p q hpq,
      homOfDegreewiseSplit_totalShortComplex S σ⟩⟩
  rw [K.ι_totalShift₁Iso_hom_f 1 p q n hpq (p + 1) rfl (n + 1) rfl]
  simp [shiftFunctor₁XXIso]

end HomologicalComplex₂
