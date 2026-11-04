module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute


@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The connecting morphism of a degreewise split sequence of cochain complexes

Let `0 → A → B → C → 0` be a short exact sequence of cochain complexes indexed by `ℤ` which is
split in each degree, with sections `s^n : C^n → B^n` and retractions `π^n : B^n → A^n`. The
family `δ^n = s^n ≫ d^n_B ≫ π^{n+1} : C^n → A^{n+1}` is a morphism of complexes
`δ : C → A⟦1⟧`, and the map it induces on cohomology is the connecting homomorphism
`H^n(C) → H^{n+1}(A)` of the long exact sequence, under the identification
`H^n(A⟦1⟧) ≅ H^{n+1}(A)`.

## Main definitions

* `AdmissibleSES`: A short complex of cochain complexes together with a splitting in every
  degree.
* `deltaFamily`: The family `δ^n = s^n ≫ d^n_B ≫ π^{n+1} : C^n → A^{n+1}`.

## Main results

* `main_theorem_delta_is_chain_map`: The family `deltaFamily` commutes with the differentials
  of `C` and of `A⟦1⟧`.
* `main_theorem_delta_components`: The components of `CochainComplex.homOfDegreewiseSplit` are
  given by `deltaFamily`.
* `main_theorem_delta_eq_connecting`: The map induced by `δ` on cohomology is the connecting
  homomorphism of the long exact sequence, followed by the inverse of the shift isomorphism.
-/

open CategoryTheory CategoryTheory.Limits CochainComplex

/-- An *admissible* (degreewise-split) short exact sequence of cochain complexes:
a `ShortComplex` of cochain complexes together with a chosen splitting in every
degree. The section is `(σ n).s : C^n → B^n` and the retraction is
`(σ n).r : B^n → A^n`. -/
@[sga "4½ Etat_0 1.2.4"]
structure AdmissibleSES (C : Type*) [Category C] [Preadditive C] where
  /-- The underlying short complex `0 → A → B → C → 0` of cochain complexes. -/
  S : ShortComplex (CochainComplex C ℤ)
  /-- The chosen degreewise splitting in each degree `n`. -/
  σ : (n : ℤ) → (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting

/-- The connecting family `δ^n = s^n ≫ d^n_B ≫ π^{n+1} : C^n → A^{n+1}`. -/
noncomputable def deltaFamily {C : Type*} [Category C] [Preadditive C]
    (E : AdmissibleSES C) (n : ℤ) : E.S.X₃.X n ⟶ E.S.X₁.X (n + 1) :=
  (E.σ n).s ≫ E.S.X₂.d n (n + 1) ≫ (E.σ (n + 1)).r

/-- The general components of the cocycle `cocycleOfDegreewiseSplit` agree with the
defining formula of `deltaFamily`. -/
theorem cocycleOfDegreewiseSplit_v_eq {C : Type*} [Category C] [Preadditive C]
    (E : AdmissibleSES C) (n m : ℤ) (h : n + 1 = m) :
    ((CochainComplex.cocycleOfDegreewiseSplit E.S E.σ :
        CochainComplex.HomComplex.Cochain E.S.X₃ E.S.X₁ 1)).v n m h
      = (E.σ n).s ≫ E.S.X₂.d n m ≫ (E.σ m).r := by
  unfold CochainComplex.cocycleOfDegreewiseSplit
  simp [CochainComplex.HomComplex.Cochain.mk_v]

/-- The family `deltaFamily E` commutes with the differentials of `C` and of `A⟦1⟧`, whose
differential is `-d_A`: `δ^n ≫ d^{n+1}_A = -(d^n_C ≫ δ^{n+1})`. -/
theorem main_theorem_delta_is_chain_map
    (C : Type*) [Category C] [Preadditive C]
    (E : AdmissibleSES C) (n : ℤ) :
    deltaFamily E n ≫ E.S.X₁.d (n + 1) (n + 1 + 1) =
      - (E.S.X₃.d n (n + 1) ≫ deltaFamily E (n + 1)) := by
  have hz := (CochainComplex.cocycleOfDegreewiseSplit E.S E.σ).δ_eq_zero 2
  have hv := CochainComplex.HomComplex.Cochain.congr_v hz n (n + 1 + 1) (by ring)
  rw [CochainComplex.HomComplex.δ_v 1 2 (by norm_num) _ n (n + 1 + 1) (by ring)
      (n + 1) (n + 1) (by ring) (by ring)] at hv
  simp only [CochainComplex.HomComplex.Cochain.zero_v] at hv
  rw [cocycleOfDegreewiseSplit_v_eq, cocycleOfDegreewiseSplit_v_eq] at hv
  have h2 : (2 : ℤ).negOnePow = 1 := by decide
  rw [h2, one_smul] at hv
  rw [eq_neg_iff_add_eq_zero, deltaFamily, deltaFamily]
  exact hv

/-- The degreewise components of the morphism `CochainComplex.homOfDegreewiseSplit E.S E.σ`
are given by `deltaFamily E`. -/
@[sga "4½ Etat_0 1.2.4" "partial"]
theorem main_theorem_delta_components
    (C : Type*) [Category C] [Preadditive C]
    (E : AdmissibleSES C) (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit E.S E.σ).f n = deltaFamily E n := by
  rw [CochainComplex.homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit_v_eq]
  rfl

-- Works around the Lean isDefEq-transparency change (types compared at default, not implicit).
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Let `z : T ⟶ (A⟦1⟧)^n` be a cycle and `z' : T ⟶ A^{n+1}` its image under the
identification `A.shiftFunctorObjXIso 1 n (n + 1) : (A⟦1⟧)^n ≅ A^{n+1}`. The shift isomorphism
`H^n(A⟦1⟧) ≅ H^{n+1}(A)` sends the cohomology class of `z` to the cohomology class of `z'`. -/
theorem cohomologyShiftIso_inv_homologyπ
    (C : Type*) [Category C] [Abelian C]
    (A : CochainComplex C ℤ) (n : ℤ)
    {T : C} (z : T ⟶ ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj A).X n)
    (hz : z ≫ ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).obj A).d n (n + 1) = 0)
    (z' : T ⟶ A.X (n + 1))
    (hz' : z' ≫ A.d (n + 1) (n + 1 + 1) = 0)
    (hcompat : z ≫ (A.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = z') :
    (((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1:ℤ)).obj A).liftCycles z (n+1) (by simp)
        hz) ≫
        (((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1:ℤ)).obj A).homologyπ n) ≫
        ((CochainComplex.ShiftSequence.shiftIso C 1 n (n + 1) (by ring)).app A).hom
      = A.liftCycles z' (n+1+1) (by simp) hz' ≫ A.homologyπ (n+1) := by
  rw [show (((CochainComplex.ShiftSequence.shiftIso C 1 n (n + 1) (by ring)).app A).hom)
        = (CochainComplex.ShiftSequence.shiftIso C 1 n (n+1) (by ring)).hom.app A from rfl]
  rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
  set φ := (CochainComplex.shiftShortComplexFunctorIso C 1 n (n+1) (by ring)).hom.app A with hφ
  rw [show ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1:ℤ)).obj A).homologyπ n
        = ((CochainComplex.shiftFunctor C 1 ⋙ HomologicalComplex.shortComplexFunctor C
            (ComplexShape.up ℤ) n).obj A).homologyπ from rfl]
  erw [ShortComplex.homologyπ_naturality φ]
  erw [ShortComplex.liftCycles_comp_cyclesMap_assoc]
  have hτ : z ≫ φ.τ₂ = z' := hcompat
  congr 1
  rw [← cancel_mono (((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) (n+1)).obj
      A).iCycles)]
  rw [ShortComplex.liftCycles_i]
  erw [HomologicalComplex.liftCycles_i]
  exact hτ

-- Works around the Lean isDefEq-transparency change (types compared at default, not implicit).
set_option backward.isDefEq.respectTransparency.types false in
/-- For a short exact sequence `E.S` split in each degree, the map
`H^n(C) → H^n(A⟦1⟧)` induced by `CochainComplex.homOfDegreewiseSplit E.S E.σ`, followed by the
shift isomorphism `H^n(A⟦1⟧) ≅ H^{n+1}(A)`, is the connecting homomorphism
`hS.δ n (n + 1) rfl`. -/
theorem homologyMap_homOfDegreewiseSplit_inv_eq_δ
    (C : Type*) [Category C] [Abelian C]
    (E : AdmissibleSES C)
    (hS : E.S.ShortExact) (n : ℤ) :
    HomologicalComplex.homologyMap (CochainComplex.homOfDegreewiseSplit E.S E.σ) n ≫
        ((CochainComplex.ShiftSequence.shiftIso C 1 n (n + 1) (by ring)).app E.S.X₁).hom
      = hS.δ n (n + 1) rfl := by
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by simp
  set x₃ := E.S.X₃.iCycles n with hx₃def
  have hx₃ : x₃ ≫ E.S.X₃.d n (n + 1) = 0 := by simp [hx₃def]
  have hx₃d : ∀ {Y : C} (k : E.S.X₃.X (n + 1) ⟶ Y), x₃ ≫ E.S.X₃.d n (n + 1) ≫ k = 0 := by
    intro Y k
    rw [← Category.assoc, hx₃, Limits.zero_comp]
  set x₂ := x₃ ≫ (E.σ n).s with hx₂def
  set x₁ := x₃ ≫ deltaFamily E n with hx₁def
  have hsg : (E.σ n).s ≫ E.S.g.f n = 𝟙 _ := (E.σ n).s_g
  have hx₂g : x₂ ≫ E.S.g.f n = x₃ := by
    rw [hx₂def, Category.assoc, hsg]; exact Category.comp_id x₃
  have hx₁compat : x₁ ≫ E.S.f.f (n + 1) = x₂ ≫ E.S.X₂.d n (n + 1) := by
    have hrf : (E.σ (n + 1)).r ≫ E.S.f.f (n + 1) = 𝟙 _ - E.S.g.f (n + 1) ≫ (E.σ (n + 1)).s :=
      (E.σ (n + 1)).r_f
    have hgd : E.S.X₂.d n (n + 1) ≫ E.S.g.f (n + 1) = E.S.g.f n ≫ E.S.X₃.d n (n + 1) :=
      (E.S.g.comm n (n + 1)).symm
    rw [hx₁def, hx₂def, deltaFamily]
    simp only [Category.assoc, hrf, Preadditive.comp_sub, Category.comp_id]
    rw [show E.S.X₂.d n (n + 1) ≫ E.S.g.f (n + 1) ≫ (E.σ (n + 1)).s
          = (E.S.X₂.d n (n + 1) ≫ E.S.g.f (n + 1)) ≫ (E.σ (n + 1)).s by rw [Category.assoc]]
    rw [hgd]
    simp only [Category.assoc]
    rw [show (E.σ n).s ≫ E.S.g.f n ≫ E.S.X₃.d n (n + 1) ≫ (E.σ (n + 1)).s
          = ((E.σ n).s ≫ E.S.g.f n) ≫ E.S.X₃.d n (n + 1) ≫ (E.σ (n + 1)).s by
            simp only [Category.assoc]]
    rw [hsg, Category.id_comp, hx₃d, sub_zero]
  have hδ := hS.δ_eq n (n + 1) rfl x₃ hx₃ x₂ hx₂g x₁ hx₁compat (n + 1 + 1) (by simp)
  have hlift₃ : E.S.X₃.liftCycles x₃ (n + 1) hnext hx₃ = 𝟙 _ := by
    rw [← cancel_mono (E.S.X₃.iCycles n), HomologicalComplex.liftCycles_i, hx₃def,
        Category.id_comp]
  rw [hlift₃, Category.id_comp] at hδ
  rw [← cancel_epi (E.S.X₃.homologyπ n)]
  rw [hδ]
  rw [← Category.assoc (E.S.X₃.homologyπ n), HomologicalComplex.homologyπ_naturality,
    Category.assoc]
  have hfn : (CochainComplex.homOfDegreewiseSplit E.S E.σ).f n = deltaFamily E n :=
    main_theorem_delta_components C E n
  have hzcompat : (x₃ ≫ (CochainComplex.homOfDegreewiseSplit E.S E.σ).f n)
      ≫ (E.S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = x₁ := by
    have hiso : (E.S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = 𝟙 _ := rfl
    rw [hx₁def, hfn, hiso]; exact Category.comp_id _
  have hzd : (x₃ ≫ (CochainComplex.homOfDegreewiseSplit E.S E.σ).f n)
      ≫ ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1:ℤ)).obj E.S.X₁).d n (n+1) = 0 := by
    rw [Category.assoc, (CochainComplex.homOfDegreewiseSplit E.S E.σ).comm n (n + 1)]
    exact hx₃d _
  have hcm : HomologicalComplex.cyclesMap (CochainComplex.homOfDegreewiseSplit E.S E.σ) n
      = ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1:ℤ)).obj E.S.X₁).liftCycles
          (x₃ ≫ (CochainComplex.homOfDegreewiseSplit E.S E.σ).f n) (n+1) hnext hzd := by
    rw [← cancel_mono (((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1:ℤ)).obj
        E.S.X₁).iCycles n)]
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.liftCycles_i, hx₃def]
  rw [hcm]
  have hx₁d : x₁ ≫ E.S.X₁.d (n + 1) (n + 1 + 1) = 0 := by
    rw [hx₁def, Category.assoc, main_theorem_delta_is_chain_map C E n, Preadditive.comp_neg,
      hx₃d, neg_zero]
  rw [cohomologyShiftIso_inv_homologyπ C E.S.X₁ n
      (x₃ ≫ (CochainComplex.homOfDegreewiseSplit E.S E.σ).f n) hzd x₁ hx₁d hzcompat]

/-- For a short exact sequence `E.S` split in each degree, the map induced on `n`-th cohomology
by the morphism `CochainComplex.homOfDegreewiseSplit E.S E.σ : C ⟶ A⟦1⟧` is the connecting
homomorphism `hS.δ n (n + 1) rfl : H^n(C) → H^{n+1}(A)` followed by the inverse of the shift
isomorphism `H^n(A⟦1⟧) ≅ H^{n+1}(A)`. -/
@[stacks 011K "the homology map read through the inverse of the shift identification"]
theorem main_theorem_delta_eq_connecting
    (C : Type*) [Category C] [Abelian C]
    (E : AdmissibleSES C)
    (hS : E.S.ShortExact) (n : ℤ) :
    HomologicalComplex.homologyMap (CochainComplex.homOfDegreewiseSplit E.S E.σ) n =
      hS.δ n (n + 1) rfl ≫
        ((CochainComplex.ShiftSequence.shiftIso C 1 n (n + 1) (by ring)).app E.S.X₁).inv := by
  rw [← homologyMap_homOfDegreewiseSplit_inv_eq_δ C E hS n]
  simp only [Functor.comp_obj, Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app]
  -- `comp_id` will not fire: the identity's object carries the functor spelling while the arrow
  -- carries the `homology` one. `exact` unifies at default transparency.
  exact (Category.comp_id _).symm
