module

public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksCore.Algebra.Homology.TotalComplexHomotopy
public import StacksCore.Algebra.Homology.HomotopyCategory.HomComplexShift
public import StacksFrontier.Algebra.Homology.TricomplexRotation
public import StacksFrontier.Algebra.Homology.TotalComplexShiftHomotopyComplete
import StacksCore.Tactic.StacksAttribute

/-! # The total complex of a double complex regarded as a complex of rows

Stacks 0G6A regards a double complex `A^{•, •}` as the complex of complexes
`… → A^{•, -1} → A^{•, 0} → A^{•, 1} → …`, which is Mathlib's `A.flip`, and shows that `Tot` is
compatible with four structures on complexes. The first two are in the library already: the
compatibility with the shift `[0, 1]` is Mathlib's `HomologicalComplex₂.totalShift₂Iso` (the
tag's `γ`, inverted) with its naturality `totalShift₂Iso_hom_naturality`, and a homotopy between
the flipped maps induces the homotopy `HomologicalComplex₂.totalMapHomotopy₂` between the total
maps. This file proves the last two, for double complexes indexed by `ℤ × ℤ` in a preadditive
category, under the sole assumption that the total complexes involved exist (the tag's countable
direct sums provide them):

* point 3, `equivHomShiftSelf_totalMapHomotopy₂`: for a self-homotopy `h` of `f` (the case
  `f = g`), the morphism of complexes attached by Stacks 011I to `h' = totalMapHomotopy₂ h` is
  `γ⁻¹ ∘ Tot(h)`, where `h` is viewed through 011I as a morphism `A ⟶ B[0, -1]`;
* point 4, `homOfDegreewiseSplit_totalSplittingOfFlip`: for a complex `0 → A → B → C → 0` of
  double complexes (`rowShortComplex` regards it as a complex of complexes of rows) with splittings
  `s^q, π^q` of its rows as complexes (with differential `d₁`), the
  connecting morphism `δ'` of 011J of the termwise split sequence of total complexes, split by
  the components `s^{p, q}, π^{p, q}`, is `γ⁻¹ ∘ Tot(δ)`, `δ : C ⟶ A[0, 1]` being the connecting
  morphism of 011J of the rows.

A morphism `A.flip ⟶ B.flip⟦y⟧` of complexes of rows is read as a morphism `A ⟶ B[0, y]` of
double complexes by `homShiftOfFlip`; `B[0, y]` is Mathlib's `(shiftFunctor₂ C y).obj B`, whose
terms are those of `B.flip⟦y⟧` on the nose.

The complex `0 → Tot(A) → Tot(B) → Tot(C) → 0` is `totalShortComplex`, shared with the mirror
remark 0G6B for complexes of columns; only its splitting differs here (`totalSplittingOfFlip`,
built from splittings of the rows rather than of the columns).
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

section homShiftOfFlip

variable {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (y : ℤ)

/-- A morphism `K.flip ⟶ L.flip⟦y⟧` of complexes of rows, read as a morphism of double complexes
`K ⟶ L[0, y]`: both have the component `(φ.f q).f p : K^{p, q} ⟶ L^{p, q + y}`. -/
@[simps]
def homShiftOfFlip
    (φ : (flipFunctor C (up ℤ) (up ℤ)).obj K ⟶ ((flipFunctor C (up ℤ) (up ℤ)).obj L)⟦y⟧) :
    K ⟶ (shiftFunctor₂ C y).obj L where
  f p :=
    { f := fun q => (φ.f q).f p
      comm' := by
        intro q q' _
        exact congrArg (fun ψ => ψ.f p) (φ.comm q q') }
  comm' := by
    intro p p' _
    ext q
    exact (φ.f q).comm p p'

end homShiftOfFlip

section point3

variable {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} {f : K ⟶ L}
  (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f) ((flipFunctor C (up ℤ) (up ℤ)).map f))

/-- The components of the morphism `A ⟶ B[0, -1]` attached by Stacks 011I to a self-homotopy `h`
of the rows are the components `h^{p, q} : A^{p, q} ⟶ B^{p, q - 1}` of `h`. -/
lemma homShiftOfFlip_equivHomShiftSelf_f_f (p q : ℤ) :
    ((homShiftOfFlip (-1) (Homotopy.equivHomShiftSelf _ h)).f p).f q =
      totalMapHomotopy.rowHom h q (q + -1) p := by
  refine (congrArg (fun φ => φ.f p) (Homotopy.equivHomShift_f (Homotopy.refl _) h q)).trans ?_
  simp [Homotopy.refl, Homotopy.ofEq, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, totalMapHomotopy.rowHom]

/-- **Stacks 0G6A**, point 3: for a self-homotopy `h` of `f`, regarded as complexes of rows, the
assignment `h ↦ h'` of point 2 (`totalMapHomotopy₂`) is compatible with the identification of
self-homotopies with morphisms to the shift by `-1` of Stacks 011I (`Homotopy.equivHomShiftSelf`):
the morphism attached to `h'` is the composite of `Tot(h) : Tot(A) ⟶ Tot(B[0, -1])`, with `h`
viewed as `A ⟶ B[0, -1]` via 011I, and `γ⁻¹ : Tot(B[0, -1]) ⟶ Tot(B)[-1]` (`totalShift₂Iso`). -/
@[stacks 0G6A "point 3: `h ↦ h'` is compatible with the identification of 011I, through `γ⁻¹`"]
theorem equivHomShiftSelf_totalMapHomotopy₂ [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] :
    Homotopy.equivHomShiftSelf (total.map f (up ℤ)) (totalMapHomotopy₂ h (up ℤ)) =
      total.map (homShiftOfFlip (-1) (Homotopy.equivHomShiftSelf _ h)) (up ℤ) ≫
        (L.totalShift₂Iso (-1)).hom := by
  ext n : 1
  refine total.hom_ext _ fun p q hpq => ?_
  dsimp at hpq
  have hprev : (up ℤ).prev q = q + -1 := (up ℤ).prev_eq' (by simp)
  rw [HomologicalComplex.comp_f, ιTotal_map_assoc, homShiftOfFlip_equivHomShiftSelf_f_f,
    L.ι_totalShift₂Iso_hom_f (-1) p q n hpq (q + -1) rfl (n + -1) rfl,
    Homotopy.equivHomShiftSelf, Homotopy.equivHomShift_f]
  simp only [totalMapHomotopy₂, Homotopy.refl, Homotopy.ofEq, Pi.zero_apply, sub_zero]
  rw [totalMapHomotopy.ιTotal_hom₂_assoc h (up ℤ) p (q + -1) q n (n + -1) hpq hprev,
    L.ιTotalOrZero_eq (up ℤ) p (q + -1) (n + -1) (by dsimp; lia)]
  simp [shiftFunctor₂XXIso, Int.negOnePow_neg]

end point3

section point4

variable (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))

/-- A complex `0 → A → B → C → 0` of double complexes, regarded as a complex
`0 → A.flip → B.flip → C.flip → 0` of complexes of rows. -/
abbrev rowShortComplex : ShortComplex (CochainComplex (CochainComplex C ℤ) ℤ) :=
  ShortComplex.mk ((flipFunctor C (up ℤ) (up ℤ)).map S.f) ((flipFunctor C (up ℤ) (up ℤ)).map S.g)
    (by rw [← Functor.map_comp, S.zero, Functor.map_zero])

variable (σ : ∀ q, ((rowShortComplex S).map
  (HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).Splitting)

namespace totalSplittingOfFlip

variable {S}

/-- The component `π^{p, q} : B^{p, q} ⟶ A^{p, q}` of the retraction `π^q` of the row `q`. -/
def rowR (p q : ℤ) : (S.X₂.X p).X q ⟶ (S.X₁.X p).X q := (σ q).r.f p

/-- The component `s^{p, q} : C^{p, q} ⟶ B^{p, q}` of the section `s^q` of the row `q`. -/
def rowS (p q : ℤ) : (S.X₃.X p).X q ⟶ (S.X₂.X p).X q := (σ q).s.f p

lemma f_rowR (p q : ℤ) : (S.f.f p).f q ≫ rowR σ p q = 𝟙 _ :=
  congrArg (fun φ => φ.f p) (σ q).f_r

lemma rowS_g (p q : ℤ) : rowS σ p q ≫ (S.g.f p).f q = 𝟙 _ :=
  congrArg (fun φ => φ.f p) (σ q).s_g

lemma rowR_f_add_g_rowS (p q : ℤ) :
    rowR σ p q ≫ (S.f.f p).f q + (S.g.f p).f q ≫ rowS σ p q = 𝟙 _ :=
  (HomologicalComplex.add_f_apply _ _ p).symm.trans (congrArg (fun φ => φ.f p) (σ q).id)

lemma rowS_rowR (p q : ℤ) : rowS σ p q ≫ rowR σ p q = 0 :=
  (HomologicalComplex.comp_f _ _ p).symm.trans (congrArg (fun φ => φ.f p) (σ q).s_r)

lemma rowS_d₁ (p p' q : ℤ) :
    rowS σ p q ≫ (S.X₂.d p p').f q = (S.X₃.d p p').f q ≫ rowS σ p' q :=
  (σ q).s.comm p p'

end totalSplittingOfFlip

open totalSplittingOfFlip in
/-- The components of the connecting morphism `δ : C ⟶ A[0, 1]` of Stacks 011J of the rows:
`δ^{p, q} = π^{p, q + 1} ∘ d_2^{p, q} ∘ s^{p, q}`. -/
lemma homShiftOfFlip_homOfDegreewiseSplit_f_f (p q : ℤ) :
    ((homShiftOfFlip 1 (CochainComplex.homOfDegreewiseSplit (rowShortComplex S) σ)).f p).f q =
        rowS σ p q ≫ (S.X₂.X p).d q (q + 1) ≫ rowR σ p (q + 1) := by
  rw [homShiftOfFlip_f_f]
  refine (congrArg (fun φ => φ.f p)
    (CochainComplex.homOfDegreewiseSplit_f (rowShortComplex S) σ q)).trans ?_
  simp only [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v]
  rfl

variable [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)]

namespace totalSplittingOfFlip

variable {S}

/-- The retraction `(π')^n : Tot^n(B) ⟶ Tot^n(A)`, with components `π^{p, q}`. -/
noncomputable def totR (n : ℤ) : (S.X₂.total (up ℤ)).X n ⟶ (S.X₁.total (up ℤ)).X n :=
  S.X₂.totalDesc fun p q h => rowR σ p q ≫ S.X₁.ιTotal (up ℤ) p q n h

/-- The section `(s')^n : Tot^n(C) ⟶ Tot^n(B)`, with components `s^{p, q}`. -/
noncomputable def totS (n : ℤ) : (S.X₃.total (up ℤ)).X n ⟶ (S.X₂.total (up ℤ)).X n :=
  S.X₃.totalDesc fun p q h => rowS σ p q ≫ S.X₂.ιTotal (up ℤ) p q n h

omit [S.X₃.HasTotal (up ℤ)] in
@[reassoc (attr := simp)]
lemma ι_totR (p q n : ℤ) (h : p + q = n) :
    S.X₂.ιTotal (up ℤ) p q n h ≫ totR σ n = rowR σ p q ≫ S.X₁.ιTotal (up ℤ) p q n h := by
  simp [totR]

omit [S.X₁.HasTotal (up ℤ)] in
@[reassoc (attr := simp)]
lemma ι_totS (p q n : ℤ) (h : p + q = n) :
    S.X₃.ιTotal (up ℤ) p q n h ≫ totS σ n = rowS σ p q ≫ S.X₂.ιTotal (up ℤ) p q n h := by
  simp [totS]

omit [S.X₃.HasTotal (up ℤ)] in
lemma f_totR (n : ℤ) : (total.map S.f (up ℤ)).f n ≫ totR σ n = 𝟙 _ := by
  refine total.hom_ext _ fun p q h => ?_
  rw [ιTotal_map_assoc, ι_totR, ← Category.assoc, f_rowR, Category.id_comp, Category.comp_id]

omit [S.X₁.HasTotal (up ℤ)] in
lemma totS_g (n : ℤ) : totS σ n ≫ (total.map S.g (up ℤ)).f n = 𝟙 _ := by
  refine total.hom_ext _ fun p q h => ?_
  rw [ι_totS_assoc, ιTotal_map, ← Category.assoc, rowS_g, Category.id_comp, Category.comp_id]

lemma totR_f_add_g_totS (n : ℤ) :
    totR σ n ≫ (total.map S.f (up ℤ)).f n + (total.map S.g (up ℤ)).f n ≫ totS σ n = 𝟙 _ := by
  refine total.hom_ext _ fun p q h => ?_
  rw [Preadditive.comp_add, ι_totR_assoc, ιTotal_map_assoc, ιTotal_map, ι_totS, Category.comp_id,
    ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, rowR_f_add_g_rowS,
    Category.id_comp]

end totalSplittingOfFlip

open totalSplittingOfFlip in
/-- The splittings `(s')^n, (π')^n` of `0 → Tot(A) → Tot(B) → Tot(C) → 0` in degree `n` used in
Stacks 0G6A, point 4: their components on the summands `C^{p, q}` and `B^{p, q}` are the
components `s^{p, q}` and `π^{p, q}` of the splittings `s^q, π^q` of the rows. -/
noncomputable def totalSplittingOfFlip (n : ℤ) :
    ((totalShortComplex S).map (HomologicalComplex.eval C (up ℤ) n)).Splitting where
  r := totR σ n
  s := totS σ n
  f_r := f_totR σ n
  s_g := totS_g σ n
  id := totR_f_add_g_totS σ n

open totalSplittingOfFlip in
/-- The components of the connecting morphism `δ'` of Stacks 011J of the total complexes:
`(δ')^n = (π')^{n + 1} ∘ d_{Tot(B)}^n ∘ (s')^n`. -/
lemma homOfDegreewiseSplit_totalSplittingOfFlip_f (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (totalSplittingOfFlip S σ)).f n =
      totS σ n ≫ (S.X₂.total (up ℤ)).d n (n + 1) ≫ totR σ (n + 1) := by
  rw [CochainComplex.homOfDegreewiseSplit_f]
  simp only [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v]
  rfl

open totalSplittingOfFlip in
/-- **Stacks 0G6A**, point 4: let `0 → A → B → C → 0` be a complex of double complexes with
splittings `s^q, π^q` of its rows `0 → A^{•, q} → B^{•, q} → C^{•, q} → 0` as complexes. The
connecting morphism `δ' : Tot(C) ⟶ Tot(A)[1]` of Stacks 011J of the termwise split sequence of
total complexes, split by `totalSplittingOfFlip`, is the composite of `Tot(δ)`, for the connecting
morphism `δ : C ⟶ A[0, 1]` of 011J of the rows, and `γ⁻¹ : Tot(A[0, 1]) ⟶ Tot(A)[1]`
(`totalShift₂Iso`). -/
@[stacks 0G6A "point 4: the connecting morphism of `Tot` of a row-wise split sequence is
  `γ⁻¹ ∘ Tot(δ)`"]
theorem homOfDegreewiseSplit_totalSplittingOfFlip :
    CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (totalSplittingOfFlip S σ) =
      total.map (homShiftOfFlip 1
        (CochainComplex.homOfDegreewiseSplit (rowShortComplex S) σ)) (up ℤ) ≫
        (S.X₁.totalShift₂Iso 1).hom := by
  ext n : 1
  rw [homOfDegreewiseSplit_totalSplittingOfFlip_f, HomologicalComplex.comp_f]
  refine total.hom_ext _ fun p q hpq => ?_
  dsimp at hpq
  have hcomm : rowS σ p q ≫ (S.X₂.d p (p + 1)).f q ≫ rowR σ (p + 1) q = 0 := by
    rw [← Category.assoc, rowS_d₁, Category.assoc, rowS_rowR, comp_zero]
  rw [ιTotal_map_assoc, homShiftOfFlip_homOfDegreewiseSplit_f_f,
    S.X₁.ι_totalShift₂Iso_hom_f 1 p q n hpq (q + 1) rfl (n + 1) rfl, ι_totS_assoc, total_d]
  simp only [Preadditive.add_comp, Preadditive.comp_add]
  rw [ι_D₁_assoc, ι_D₂_assoc,
    S.X₂.d₁_eq (up ℤ) (show (up ℤ).Rel p (p + 1) by simp) q (n + 1) (by dsimp; lia),
    S.X₂.d₂_eq (up ℤ) p (show (up ℤ).Rel q (q + 1) by simp) (n + 1) (by dsimp; lia),
    Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc, ι_totR,
    ι_totR, Linear.comp_units_smul, Linear.comp_units_smul, reassoc_of% hcomm]
  simp [shiftFunctor₂XXIso, CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

end point4

open totalSplittingOfFlip in
/-- **Stacks 0G6A**: taking the total complex of double complexes regarded as complexes of rows is
compatible with the shift `[0, 1]`, with homotopies, with the identification of self-homotopies
with morphisms to the shift (011I), and with the connecting morphisms of termwise split sequences
(011J). In order: `γ⁻¹ = totalShift₂Iso` is natural and is `(-1)^p` on the summand `A^{p, q + 1}`;
`h' = totalMapHomotopy₂ h` is `(-1)^p h^{p, q}` on `A^{p, q}`; the third point; and the fourth
point, with the splittings of the total complexes given by `s^{p, q}`, `π^{p, q}` on summands. -/
@[stacks 0G6A "the whole remark: points 1 to 4"]
theorem total_shift_homotopy_degreewiseSplit_ofFlip :
    (∀ (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
        (φ : K ⟶ L),
        total.map ((shiftFunctor₂ C 1).map φ) (up ℤ) ≫ (L.totalShift₂Iso 1).hom =
          (K.totalShift₂Iso 1).hom ≫ (total.map φ (up ℤ))⟦(1 : ℤ)⟧') ∧
    (∀ (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (p q n : ℤ)
        (hpq : p + q = n),
        ((shiftFunctor₂ C 1).obj K).ιTotal (up ℤ) p q n hpq ≫ (K.totalShift₂Iso 1).hom.f n =
          p.negOnePow • K.ιTotal (up ℤ) p (q + 1) (n + 1) (by dsimp; lia) ≫
            (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) 1 n (n + 1) rfl).inv) ∧
    (∀ (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
        (f g : K ⟶ L)
        (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f) ((flipFunctor C (up ℤ) (up ℤ)).map g))
        (p q n : ℤ) (hpq : p + q = n),
        K.ιTotal (up ℤ) p q n hpq ≫ (totalMapHomotopy₂ h (up ℤ)).hom n (n - 1) =
          p.negOnePow • (h.hom q (q - 1)).f p ≫
            L.ιTotal (up ℤ) p (q - 1) (n - 1) (by dsimp; lia)) ∧
    (∀ (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
        (f : K ⟶ L)
        (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f) ((flipFunctor C (up ℤ) (up ℤ)).map f)),
        Homotopy.equivHomShiftSelf (total.map f (up ℤ)) (totalMapHomotopy₂ h (up ℤ)) =
          total.map (homShiftOfFlip (-1) (Homotopy.equivHomShiftSelf _ h)) (up ℤ) ≫
            (L.totalShift₂Iso (-1)).hom) ∧
    (∀ (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))
        [S.X₁.HasTotal (up ℤ)] [S.X₂.HasTotal (up ℤ)] [S.X₃.HasTotal (up ℤ)]
        (σ : ∀ q, ((rowShortComplex S).map
          (HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).Splitting),
        (∀ (p q n : ℤ) (hpq : p + q = n),
          S.X₃.ιTotal (up ℤ) p q n hpq ≫ (totalSplittingOfFlip S σ n).s =
            (σ q).s.f p ≫ S.X₂.ιTotal (up ℤ) p q n hpq) ∧
        (∀ (p q n : ℤ) (hpq : p + q = n),
          S.X₂.ιTotal (up ℤ) p q n hpq ≫ (totalSplittingOfFlip S σ n).r =
            (σ q).r.f p ≫ S.X₁.ιTotal (up ℤ) p q n hpq) ∧
        CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (totalSplittingOfFlip S σ) =
          total.map (homShiftOfFlip 1
            (CochainComplex.homOfDegreewiseSplit (rowShortComplex S) σ)) (up ℤ) ≫
            (S.X₁.totalShift₂Iso 1).hom) := by
  refine ⟨fun K L _ _ φ => totalShift₂Iso_hom_naturality φ 1,
    fun K _ p q n hpq => ?_, fun K L _ _ f g h p q n hpq => ?_,
    fun K L _ _ f h => equivHomShiftSelf_totalMapHomotopy₂ h,
    fun S _ _ _ σ => ⟨fun p q n hpq => ι_totS σ p q n hpq,
      fun p q n hpq => ι_totR σ p q n hpq, homOfDegreewiseSplit_totalSplittingOfFlip S σ⟩⟩
  · rw [K.ι_totalShift₂Iso_hom_f 1 p q n hpq (q + 1) rfl (n + 1) rfl]
    simp [shiftFunctor₂XXIso]
  · rw [ιTotal_totalMapHomotopy₂_hom h (up ℤ) p (q - 1) q n (n - 1) hpq
      ((up ℤ).prev_eq' (by simp)), ιTotalOrZero_eq _ _ _ _ _ (by dsimp; lia)]
    rfl

end HomologicalComplex₂
