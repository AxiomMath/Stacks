module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import StacksCore.LinearAlgebra.Matrix.CommSemiring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Resolutions by objects of bounded cohomological dimension: the replacement complex

Let `A` be an abelian category and `d : A → ℕ∞`. This file states the hypotheses on `d` and
builds, for a cochain complex `K`, a degree `n` and a monomorphism `ι : K.X n ⟶ M`, the
elementary replacement complex `Kp K n M ι` with its chain map `fmap K n M ι : K ⟶ Kp K n M ι`
and the cokernel complex of `fmap`.

## Main definitions

* `BoundedCohomologicalDimension`: the hypotheses on `d`.
* `TendsToNegInfty`: the growth condition `n + d (K.X n) → -∞` as `n → -∞`.
* `ElemReplBuild`: the data of an elementary replacement.
* `ElemReplConstruction.Kp`, `ElemReplConstruction.fmap`: the replacement complex and map.

## Implementation notes

The value `d` is taken in `ℕ∞`, whose truncated subtraction satisfies `⊤ - 1 = ⊤` and
`0 - 1 = 0`.

## References

* [Stacks: Tag 07K6](https://stacks.math.columbia.edu/tag/07K6)
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

example : (⊤ : ℕ∞) - 1 = ⊤ := by decide

example : (0 : ℕ∞) - 1 = 0 := by decide

namespace Stacks.BoundedCohomologicalDimension

variable {A : Type*} [Category A] [Abelian A]

/-- A function `d : A → ℕ∞` satisfies the *bounded cohomological dimension hypotheses* if
every object embeds into an object of `d`-value `0`, `d (X ⊞ Y) ≤ max (d X) (d Y)`, and for
every short exact sequence `0 → X₁ → X₂ → X₃ → 0` one has `d X₃ ≤ max (d X₁ - 1) (d X₂)`. -/
structure BoundedCohomologicalDimension (d : A → ℕ∞) : Prop where
  /-- Every object admits a monomorphism into an object of `d`-value `0`. -/
  embed : ∀ X : A, ∃ (B : A) (i : X ⟶ B), Mono i ∧ d B = 0
  /-- `d` is subadditive on binary biproducts. -/
  biprod_le : ∀ X Y : A, d (X ⊞ Y) ≤ max (d X) (d Y)
  /-- For a short exact sequence, `d X₃ ≤ max (d X₁ - 1) (d X₂)`. -/
  shortExact_le : ∀ S : ShortComplex A, S.ShortExact → d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)

/-- The growth condition "`n + d (K.X n) → -∞` as `n → -∞`": for every `N` there is `n₀`
such that for all `n ≤ n₀`, `d (K.X n)` is a natural number `m` with `n + m ≤ N`. -/
def TendsToNegInfty (d : A → ℕ∞) (K : CochainComplex A ℤ) : Prop :=
  ∀ N : ℤ, ∃ n₀ : ℤ, ∀ n : ℤ, n ≤ n₀ → ∃ m : ℕ, d (K.X n) = (m : ℕ∞) ∧ n + (m : ℤ) ≤ N

/-- Every object `X` admits a monomorphism `i : X ⟶ B` with `d B = 0` and
`d (cokernel i) ≤ d X - 1`. -/
theorem dimShift (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) :
    ∀ X : A, ∃ (B : A) (i : X ⟶ B), Mono i ∧ d B = 0 ∧ d (cokernel i) ≤ d X - 1 := by
  intro X
  obtain ⟨B, i, hi, hB⟩ := hd.embed X
  refine ⟨B, i, hi, hB, ?_⟩
  have hse : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  have hle := hd.shortExact_le _ hse
  rw [hB] at hle
  simpa using hle

/-- An elementary replacement of `K` at degree `n` along `ι : K.X n ⟶ M`: a complex `K'`
with `K'.X n = M`, the same `d`-values as `K` away from `{n, n + 1}`, a chain map
`f : K ⟶ K'`, and a short exact sequence `0 → K^n → M ⊞ K^{n+1} → K'.X (n+1) → 0` whose first
map is `biprod.lift ι (K.d n (n + 1))`. -/
structure ElemReplBuild (d : A → ℕ∞) (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    Type _ where
  /-- The replacement complex `K'`. -/
  K' : CochainComplex A ℤ
  /-- The comparison morphism `f : K ⟶ K'`. -/
  f : K ⟶ K'
  /-- The cokernel projection `g : M ⊞ K^{n+1} ⟶ K'.X (n+1)` exhibiting `K'.X (n+1)`
  as `Coker(biprod.lift ι (K.d n (n+1)))`. -/
  g : (M ⊞ K.X (n + 1)) ⟶ K'.X (n + 1)
  /-- The composite `biprod.lift ι (K.d n (n + 1)) ≫ g` vanishes. -/
  hg : biprod.lift ι (K.d n (n + 1)) ≫ g = 0
  /-- In degree `n` the new term is `M`. -/
  hK'n : K'.X n = M
  /-- Away from `{n, n+1}` the `d`-values of `K'` and `K` agree. -/
  hoff : ∀ m : ℤ, m ≠ n → m ≠ n + 1 → d (K'.X m) = d (K.X m)
  /-- The defining short exact sequence `0 → K^n → M ⊞ K^{n+1} → K'.X (n+1) → 0`. -/
  hses : (ShortComplex.mk (biprod.lift ι (K.d n (n + 1))) g hg).ShortExact

namespace ElemReplConstruction

/-- Underlying objects of the replacement complex: `M` in degree `n`, the cokernel
`M'` in degree `n+1`, and `K.X m` elsewhere. -/
noncomputable def XX (K : CochainComplex A ℤ) (n : ℤ) (M M' : A) : ℤ → A := fun m =>
  if m = n then M else if m = n + 1 then M' else K.X m

/-- In degree `n` the replacement objects are `M`. -/
@[simp]
lemma XX_n (K : CochainComplex A ℤ) (n : ℤ) (M M' : A) : XX K n M M' n = M := by
  simp [XX]

/-- In degree `n + 1` the replacement objects are `M'`. -/
@[simp]
lemma XX_n1 (K : CochainComplex A ℤ) (n : ℤ) (M M' : A) : XX K n M M' (n + 1) = M' := by
  simp [XX]

/-- Away from degrees `n` and `n + 1` the replacement objects are those of `K`. -/
lemma XX_off (K : CochainComplex A ℤ) (n : ℤ) (M M' : A) (m : ℤ) (h1 : m ≠ n) (h2 : m ≠ n + 1) :
    XX K n M M' m = K.X m := by
  simp [XX, h1, h2]

/-- The successor differential `XX i ⟶ XX (i+1)` of the replacement complex. -/
noncomputable def dd (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) i ⟶
      XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) (i + 1) :=
  if hn1 : i = n - 1 then
    eqToHom
        (by
          rw [hn1]; exact XX_off K n M _ (n - 1) (by omega) (by omega)) ≫
      (K.d (n - 1) n ≫ ι) ≫
      eqToHom
        (by
          rw [hn1]; simp)
  else
    if hnn : i = n then
      eqToHom
          (by
            rw [hnn]; simp) ≫
        (-(biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))))) ≫
        eqToHom
          (by
            rw [hnn]; simp)
    else
      if hn2 : i = n + 1 then
        eqToHom
            (by
              rw [hn2]; simp) ≫
          cokernel.desc (biprod.lift ι (K.d n (n + 1))) (biprod.snd ≫ K.d (n + 1) (n + 2))
            (by rw [← Category.assoc, biprod.lift_snd, HomologicalComplex.d_comp_d]) ≫
          eqToHom
            (by
              rw [hn2]; rw [show n + 1 + 1 = n + 2 from by ring]
              exact (XX_off K n M _ (n + 2) (by omega) (by omega)).symm)
      else
        eqToHom (XX_off K n M _ i (by omega) (by omega)) ≫
          K.d i (i + 1) ≫ eqToHom (XX_off K n M _ (i + 1) (by omega) (by omega)).symm

/-- In the cokernel `M'`, the images of `ι` composed with `-biprod.inl` and of
`K.d n (n + 1)` composed with `biprod.inr` agree. -/
private lemma comp_neg_inl_cokernel_eq (K : CochainComplex A ℤ) (n : ℤ) (M : A)
    (ι : K.X n ⟶ M) :
    ι ≫ (-(biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))))) =
      K.d n (n + 1) ≫ biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) := by
  have h := cokernel.condition (biprod.lift ι (K.d n (n + 1)))
  rw [Preadditive.comp_neg]
  rw [biprod.lift_eq] at h ⊢
  simp only [Preadditive.add_comp, Category.assoc] at h ⊢
  exact neg_eq_of_add_eq_zero_right h

/-- The composite `K^{n-1} → K^n → M → M'` of `K.d (n - 1) n`, `ι` and
`-(biprod.inl ≫ cokernel.π _)` vanishes. -/
lemma core1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    K.d (n - 1) n ≫ ι ≫ (-(biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))))) = 0 := by
  rw [comp_neg_inl_cokernel_eq, ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

/-- The composite `M → M' → K^{n+2}` of the two new differentials vanishes. -/
lemma core2 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    (-(biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))))) ≫
        cokernel.desc (biprod.lift ι (K.d n (n + 1))) (biprod.snd ≫ K.d (n + 1) (n + 2))
          (by rw [← Category.assoc, biprod.lift_snd, HomologicalComplex.d_comp_d]) =
      0 := by
  simp only [Preadditive.neg_comp, Category.assoc]
  rw [cokernel.π_desc, biprod.inl_snd_assoc, zero_comp, neg_zero]

/-- The composite `M' → K^{n+2} → K^{j+1}` vanishes, for `j = n + 2`. -/
lemma core3' (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (j : ℤ) (hj : n + 2 = j)
    (h : K.X (n + 2) = K.X j) :
    cokernel.desc (biprod.lift ι (K.d n (n + 1))) (biprod.snd ≫ K.d (n + 1) (n + 2))
          (by rw [← Category.assoc, biprod.lift_snd, HomologicalComplex.d_comp_d]) ≫
        eqToHom h ≫ K.d j (j + 1) =
      0 := by
  rw [← cancel_epi (cokernel.π (biprod.lift ι (K.d n (n + 1))))]
  rw [comp_zero, cokernel.π_desc_assoc, Category.assoc]
  rw [show eqToHom h ≫ K.d j (j + 1) = K.d (n + 2) (j + 1) from
      HomologicalComplex.eqToHom_comp_d _
        (show (ComplexShape.up ℤ).Rel (n + 2) (j + 1) by
          simp; omega)
        (show (ComplexShape.up ℤ).Rel j (j + 1) by simp)]
  rw [show K.d (n + 1) (n + 2) ≫ K.d (n + 2) (j + 1) = 0 from HomologicalComplex.d_comp_d _ _ _ _,
    comp_zero]

/-- For `i + 1 = n - 1`, the composite `K^i → K^{n-1} → K^n` of differentials, transported
along `eqToHom`, vanishes. -/
lemma core4 (K : CochainComplex A ℤ) (n i : ℤ) (hi : i + 1 = n - 1)
    (h : K.X (i + 1) = K.X (n - 1)) : K.d i (i + 1) ≫ eqToHom h ≫ K.d (n - 1) n = 0 := by
  rw [show eqToHom h ≫ K.d (n - 1) n = K.d (i + 1) n from
      HomologicalComplex.eqToHom_comp_d _
        (show (ComplexShape.up ℤ).Rel (i + 1) n by
          simp; omega)
        (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
  rw [HomologicalComplex.d_comp_d]

/-- Two consecutive differentials `dd` of the replacement complex compose to zero. -/
lemma dd_dd (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    dd K n M ι i ≫ dd K n M ι (i + 1) = 0 := by
  by_cases hA : i = n - 1
  · unfold dd
    rw [dite_eq_left hA, dite_eq_right (by omega), dite_eq_left (by omega)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    slice_lhs 2 4 => rw [core1 K n M ι]
    simp
  by_cases hB : i = n
  · unfold dd
    rw [dite_eq_right (by omega), dite_eq_left hB, dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_left (by omega)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    slice_lhs 2 3 => rw [core2 K n M ι]
    simp
  by_cases hC : i = n + 1
  · unfold dd
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left hC,
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
    simp only [Category.assoc, eqToHom_trans_assoc]
    slice_lhs 2 4 =>
      rw [core3' K n M ι (i + 1) (by omega) (by rw [show (i + 1 : ℤ) = n + 2 from by omega])]
    simp
  · by_cases hD : i + 1 = n - 1
    · unfold dd
      rw [dite_eq_right hA, dite_eq_right hB, dite_eq_right hC, dite_eq_left hD]
      simp only [Category.assoc, eqToHom_trans_assoc]
      slice_lhs 2 4 => rw [core4 K n i hD (by rw [hD])]
      simp
    · unfold dd
      rw [dite_eq_right hA, dite_eq_right hB, dite_eq_right hC, dite_eq_right hD,
        dite_eq_right (by omega), dite_eq_right (by omega)]
      simp only [Category.assoc]
      slice_lhs 3 4 => rw [eqToHom_trans, eqToHom_refl]
      rw [Category.id_comp, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

/-- The full differential of the replacement complex. -/
noncomputable def Kd (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i j : ℤ) :
    XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) i ⟶
      XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) j :=
  if h : i + 1 = j then dd K n M ι i ≫ eqToHom (by rw [h]) else 0

/-- The replacement complex `K'`. -/
noncomputable def Kp (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    CochainComplex A ℤ where
  X := XX K n M (cokernel (biprod.lift ι (K.d n (n + 1))))
  d := Kd K n M ι
  shape i j hij := by
    unfold Kd; rw [dite_eq_right]; intro h; apply hij
    simp [ComplexShape.up_Rel]; omega
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    unfold Kd; rw [dite_eq_left hij, dite_eq_left hjk]; subst hij hjk
    simp only [eqToHom_refl, Category.comp_id]; rw [dd_dd]

/-- The objects of `Kp K n M ι` are given by `XX`. -/
@[simp]
lemma Kp_X (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (m : ℤ) :
    (Kp K n M ι).X m = XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) m :=
  rfl

/-- The components of the comparison chain map `f : K ⟶ K'`. -/
noncomputable def ff (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    K.X i ⟶ XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) i :=
  if hn : i = n then
    eqToHom (by rw [hn]) ≫
      ι ≫
      eqToHom
        (by
          rw [hn]; simp)
  else
    if hn1 : i = n + 1 then
      eqToHom (by rw [hn1]) ≫
        (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) ≫
        eqToHom
          (by
            rw [hn1]; simp)
    else eqToHom (XX_off K n M _ i hn hn1).symm

/-- The differential `Kd` from degree `i` to `i + 1` is `dd` at `i`. -/
lemma Kd_succ (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    Kd K n M ι i (i + 1) = dd K n M ι i ≫ eqToHom rfl := by
  unfold Kd; rw [dite_eq_left rfl]

/-- In the cokernel `M'`, the images of `ι` composed with `-biprod.inl` and of
`K.d n (n + 1)` composed with `biprod.inr` agree. -/
lemma commcore_n (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    ι ≫ (-(biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))))) =
      K.d n (n + 1) ≫ biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) :=
  comp_neg_inl_cokernel_eq K n M ι

/-- The composite `K^{n+1} → M' → K^{n+2}` is the differential `K.d (n + 1) (n + 2)`. -/
lemma commcore_n1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) ≫
        cokernel.desc (biprod.lift ι (K.d n (n + 1))) (biprod.snd ≫ K.d (n + 1) (n + 2))
          (by rw [← Category.assoc, biprod.lift_snd, HomologicalComplex.d_comp_d]) =
      K.d (n + 1) (n + 2) := by
  rw [Category.assoc, cokernel.π_desc, biprod.inr_snd_assoc]

/-- The components `ff` commute with the differentials in degree `n`. -/
lemma comm_n (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    ff K n M ι n ≫ Kd K n M ι n (n + 1) = K.d n (n + 1) ≫ ff K n M ι (n + 1) := by
  rw [Kd_succ]; unfold ff dd
  rw [dite_eq_left rfl, dite_eq_right (by omega), dite_eq_left rfl, dite_eq_right (by omega),
    dite_eq_left rfl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [reassoc_of% commcore_n]

/-- The components `ff` commute with the differentials in degree `n + 1`. -/
lemma comm_n1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    ff K n M ι (n + 1) ≫ Kd K n M ι (n + 1) ((n + 1) + 1) =
      K.d (n + 1) ((n + 1) + 1) ≫ ff K n M ι ((n + 1) + 1) := by
  rw [Kd_succ]; unfold ff dd
  rw [dite_eq_right (by omega), dite_eq_left rfl, dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_left rfl, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [reassoc_of% commcore_n1]
  have h :
    K.d (n + 1) (n + 1 + 1) ≫
        eqToHom
          (show K.X (n + 1 + 1) = K.X (n + 2) by rw [show (n + 1 + 1 : ℤ) = n + 2 from by ring]) =
      K.d (n + 1) (n + 2) := by
    rw [HomologicalComplex.d_comp_eqToHom _
        (show (ComplexShape.up ℤ).Rel (n + 1) (n + 2) by
          simp; omega)
        (show (ComplexShape.up ℤ).Rel (n + 1) (n + 1 + 1) by simp)]
  rw [← h, Category.assoc, eqToHom_trans]

/-- The components `ff` commute with the differentials in degree `n - 1`. -/
lemma comm_nm1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) (hi : i = n - 1) :
    ff K n M ι i ≫ Kd K n M ι i (i + 1) = K.d i (i + 1) ≫ ff K n M ι (i + 1) := by
  subst hi
  rw [Kd_succ]; unfold ff dd
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left rfl,
    dite_eq_left (by omega)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← Category.assoc (K.d (n - 1) (n - 1 + 1)),
    HomologicalComplex.d_comp_eqToHom _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)
      (show (ComplexShape.up ℤ).Rel (n - 1) (n - 1 + 1) by simp)]

/-- The components `ff` commute with the differentials in a degree `i` with `i` and
`i + 1` both outside `{n, n + 1}`. -/
lemma comm_gen (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) (hA : i ≠ n - 1)
    (hB : i ≠ n) (hC : i ≠ n + 1) (hD : i + 1 ≠ n) (hE : i + 1 ≠ n + 1) :
    ff K n M ι i ≫ Kd K n M ι i (i + 1) = K.d i (i + 1) ≫ ff K n M ι (i + 1) := by
  rw [Kd_succ]; unfold ff dd
  rw [dite_eq_right hB, dite_eq_right hC, dite_eq_right hA, dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right hD, dite_eq_right hE]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The components `ff` commute with the differentials in every degree. -/
lemma ff_comm (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    ff K n M ι i ≫ Kd K n M ι i (i + 1) = K.d i (i + 1) ≫ ff K n M ι (i + 1) := by
  by_cases hA : i = n - 1
  · exact comm_nm1 K n M ι i hA
  by_cases hB : i = n
  · subst hB; exact comm_n K _ M ι
  by_cases hC : i = n + 1
  · subst hC; exact comm_n1 K _ M ι
  · by_cases hD : i + 1 = n
    · exact comm_nm1 K n M ι i (by omega)
    by_cases hE : i + 1 = n + 1
    · exfalso; omega
    · exact comm_gen K n M ι i hA hB hC hD hE

/-- The comparison chain map `f : K ⟶ K'`. -/
noncomputable def fmap (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    K ⟶ Kp K n M ι where
  f := ff K n M ι
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij; subst hij
    exact ff_comm K n M ι i

/-! ### Quasi-isomorphism of `fmap`

The map `fmap` is a quasi-isomorphism: there is a degreewise short exact sequence of
complexes `0 → K →^{fmap} Kp → Q → 0` with `Q` the acyclic two-term complex
`coker ι →^{-𝟙} coker ι` in degrees `n`, `n+1`. -/

/-- The map `coker(biprod.lift ι (K.d n (n+1))) → coker ι` induced by `biprod.fst`. -/
noncomputable def qmap (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    cokernel (biprod.lift ι (K.d n (n + 1))) ⟶ cokernel ι :=
  cokernel.desc (biprod.lift ι (K.d n (n + 1))) (biprod.fst ≫ cokernel.π ι)
    (by rw [← Category.assoc, biprod.lift_fst, cokernel.condition])

/-- The composite `K^{n+1} → M' → coker ι` vanishes. -/
lemma qmap_cond (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) ≫ qmap K n M ι = 0 := by
  rw [Category.assoc]; unfold qmap
  rw [cokernel.π_desc, biprod.inr_fst_assoc, zero_comp]

/-- The composite `M → M' → coker ι` is the projection `cokernel.π ι`. -/
private lemma inl_comp_cokernel_π_comp_qmap (K : CochainComplex A ℤ) (n : ℤ) (M : A)
    (ι : K.X n ⟶ M) :
    biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ qmap K n M ι = cokernel.π ι := by
  unfold qmap; rw [cokernel.π_desc, biprod.inl_fst_assoc]

/-- The map `qmap` is an epimorphism. -/
lemma qmap_epi (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) : Epi (qmap K n M ι) := by
  have h := inl_comp_cokernel_π_comp_qmap K n M ι
  have hh : Epi (biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ qmap K n M ι) := by
    rw [h]; infer_instance
  rw [← Category.assoc] at hh
  exact epi_of_epi (biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) (qmap K n M ι)

/-- For a cofork `s` of `biprod.inr ≫ cokernel.π _`, the composite `K^{n+1} → M' → s.pt`
vanishes. -/
private lemma inr_comp_cokernel_π_comp_cofork_π (K : CochainComplex A ℤ) (n : ℤ) (M : A)
    (ι : K.X n ⟶ M)
    (s : Cofork (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) 0) :
    biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π = 0 := by
  simpa only [zero_comp, Category.assoc] using s.condition

/-- For a cofork `s` of `biprod.inr ≫ cokernel.π _`, the composite
`K^n → M → M' → s.pt` through `ι` vanishes. -/
lemma qmap_sCond (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M)
    (s : Cofork (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) 0) :
    ι ≫ biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π = 0 := by
  have hcond :
    biprod.lift ι (K.d n (n + 1)) ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π = 0 := by
    rw [← Category.assoc, cokernel.condition, zero_comp]
  have hs := inr_comp_cokernel_π_comp_cofork_π K n M ι s
  have e : ι ≫ biprod.inl = biprod.lift ι (K.d n (n + 1)) - K.d n (n + 1) ≫ biprod.inr := by
    rw [show biprod.lift ι (K.d n (n + 1)) = ι ≫ biprod.inl + K.d n (n + 1) ≫ biprod.inr from
        biprod.lift_eq]
    abel
  rw [show
      ι ≫ biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π =
        (ι ≫ biprod.inl) ≫ (cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π)
      from by rw [Category.assoc],
    e, Preadditive.sub_comp, Category.assoc, hs, comp_zero, sub_zero, hcond]

/-- Every cofork `s` of `biprod.inr ≫ cokernel.π _` factors through `qmap`. -/
lemma qmap_sFac (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M)
    (s : Cofork (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) 0) :
    qmap K n M ι ≫
        cokernel.desc ι (biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π)
          (qmap_sCond K n M ι s) =
      s.π := by
  have hs := inr_comp_cokernel_π_comp_cofork_π K n M ι s
  have key :
    cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π =
      biprod.fst ≫ biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π := by
    conv_lhs =>
      rw [← Category.id_comp (cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π), ← biprod.total]
    simp only [Preadditive.add_comp, Category.assoc]
    rw [hs, comp_zero, add_zero]
  apply (cancel_epi (cokernel.π (biprod.lift ι (K.d n (n + 1))))).1
  rw [← Category.assoc]
  show (cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ qmap K n M ι) ≫ _ = _
  unfold qmap
  rw [cokernel.π_desc, Category.assoc, cokernel.π_desc]
  rw [← Category.assoc] at key ⊢
  exact key.symm

/-- `qmap` exhibits `coker ι` as the cokernel of `biprod.inr ≫ cokernel.π`, i.e. of
the `(n+1)`-component of `fmap`. -/
noncomputable def qmapIsCokernel (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    IsColimit (CokernelCofork.ofπ (qmap K n M ι) (qmap_cond K n M ι)) := by
  refine
    Cofork.IsColimit.mk _
      (fun s =>
        cokernel.desc ι (biprod.inl ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ s.π)
          (qmap_sCond K n M ι s))
      (fun s => ?_) (fun s m hm => ?_)
  · rw [Cofork.π_ofπ]; exact qmap_sFac K n M ι s
  · have := qmap_epi K n M ι
    rw [Cofork.π_ofπ] at hm
    exact (cancel_epi (qmap K n M ι)).1 (hm.trans (qmap_sFac K n M ι s).symm)

/-- Objects of the acyclic cokernel complex `Q`: `coker ι` in degrees `n` and `n+1`,
the zero object elsewhere. -/
noncomputable def QX (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) : ℤ → A := fun m =>
  if m = n then cokernel ι else if m = n + 1 then cokernel ι else (0 : A)

/-- In degree `n` the object of `Q` is `coker ι`. -/
@[simp]
lemma QX_n (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    QX K n M ι n = cokernel ι := by
  unfold QX; simp

/-- In degree `n + 1` the object of `Q` is `coker ι`. -/
@[simp]
lemma QX_n1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    QX K n M ι (n + 1) = cokernel ι := by
  unfold QX; simp

/-- Away from degrees `n` and `n + 1` the objects of `Q` are zero. -/
lemma QX_isZero_off (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (m : ℤ) (h1 : m ≠ n)
    (h2 : m ≠ n + 1) : IsZero (QX K n M ι m) := by
  unfold QX; rw [ite_eq_right h1, ite_eq_right h2]; exact isZero_zero A

/-- The differential of `Q`: `-𝟙` from degree `n` to `n+1`, zero otherwise. -/
noncomputable def Qd (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i j : ℤ) :
    QX K n M ι i ⟶ QX K n M ι j :=
  if h : i = n ∧ j = n + 1 then
    eqToHom (by rw [h.1, QX_n]) ≫ (-(𝟙 (cokernel ι))) ≫ eqToHom (by rw [h.2, QX_n1])
  else 0

/-- The acyclic cokernel complex `Q`. -/
noncomputable def Qcomplex (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    CochainComplex A ℤ where
  X := QX K n M ι
  d := Qd K n M ι
  shape i j hij := by
    unfold Qd; rw [dite_eq_right]; rintro ⟨h1, h2⟩; apply hij; simp [ComplexShape.up_Rel]; omega
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    unfold Qd
    by_cases h : i = n ∧ j = n + 1
    · rw [dite_eq_left h, dite_eq_right (by omega)]; simp
    · rw [dite_eq_right h]; simp

/-- The objects of `Qcomplex K n M ι` are given by `QX`. -/
@[simp]
lemma Qcomplex_X (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (m : ℤ) :
    (Qcomplex K n M ι).X m = QX K n M ι m :=
  rfl

/-- Components of the projection chain map `Kp ⟶ Q`. -/
noncomputable def pff (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    (Kp K n M ι).X i ⟶ (Qcomplex K n M ι).X i :=
  if hn : i = n then
    eqToHom (by rw [hn, Kp_X, XX_n]) ≫ cokernel.π ι ≫ eqToHom (by rw [hn, Qcomplex_X, QX_n])
  else
    if hn1 : i = n + 1 then
      eqToHom (by rw [hn1, Kp_X, XX_n1]) ≫ qmap K n M ι ≫ eqToHom (by rw [hn1, Qcomplex_X, QX_n1])
    else
      (by rw [Qcomplex_X]; exact (QX_isZero_off K n M ι i hn hn1).from_ _)

/-- The components `pff` commute with the differentials in degree `n`. -/
lemma pcomm_n (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    pff K n M ι n ≫ Qd K n M ι n (n + 1) = Kd K n M ι n (n + 1) ≫ pff K n M ι (n + 1) := by
  have hq := inl_comp_cokernel_π_comp_qmap K n M ι
  rw [Kd_succ]
  unfold pff Qd dd
  rw [dite_eq_left rfl, dite_eq_left ⟨rfl, rfl⟩, dite_eq_right (by omega), dite_eq_left rfl,
    dite_eq_right (by omega), dite_eq_left rfl]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Category.comp_id, Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
  rw [reassoc_of% hq]

/-- The components `pff` commute with the differentials in degree `n - 1`. -/
lemma pcomm_nm1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) (hi : i = n - 1) :
    pff K n M ι i ≫ Qd K n M ι i (i + 1) = Kd K n M ι i (i + 1) ≫ pff K n M ι (i + 1) := by
  subst hi
  rw [Kd_succ]
  have hQd : Qd K n M ι (n - 1) ((n - 1) + 1) = 0 := by
    unfold Qd; rw [dite_eq_right (by omega)]
  rw [hQd, comp_zero]
  conv_rhs => rw [pff]
  rw [dite_eq_left (show ((n : ℤ) - 1) + 1 = n by omega)]
  unfold dd
  rw [dite_eq_left (show (n : ℤ) - 1 = n - 1 from rfl)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
    reassoc_of% cokernel.condition, zero_comp, comp_zero]

/-- The components `pff` commute with the differentials in a degree `i ∉ {n - 1, n}`,
where the target `Q.X (i + 1)` is zero. -/
lemma pcomm_targetZero (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ)
    (hA : i ≠ n - 1) (hB : i ≠ n) :
    pff K n M ι i ≫ Qd K n M ι i (i + 1) = Kd K n M ι i (i + 1) ≫ pff K n M ι (i + 1) := by
  have hz : IsZero ((Qcomplex K n M ι).X (i + 1)) := by
    rw [Qcomplex_X]; exact QX_isZero_off K n M ι (i + 1) (by omega) (by omega)
  exact hz.eq_of_tgt _ _

/-- The components `pff` commute with the differentials in every degree. -/
lemma pff_comm (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    pff K n M ι i ≫ Qd K n M ι i (i + 1) = Kd K n M ι i (i + 1) ≫ pff K n M ι (i + 1) := by
  by_cases hA : i = n - 1
  · exact pcomm_nm1 K n M ι i hA
  by_cases hB : i = n
  · subst hB; exact pcomm_n K _ M ι
  · exact pcomm_targetZero K n M ι i hA hB

/-- The projection chain map `Kp ⟶ Q`. -/
noncomputable def pmap (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    Kp K n M ι ⟶ Qcomplex K n M ι
    where
  f := pff K n M ι
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij; subst hij
    exact pff_comm K n M ι i

/-- For `ι` a monomorphism, the `(n+1)`-component `biprod.inr ≫ cokernel.π _` of `fmap` is a
monomorphism. -/
lemma fmap_n1_mono (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) [hι : Mono ι] :
    Mono (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) := by
  have : Mono (biprod.lift ι (K.d n (n + 1))) :=
    mono_of_mono_fac (biprod.lift_fst ι (K.d n (n + 1)))
  have hse :
    (ShortComplex.mk (biprod.lift ι (K.d n (n + 1))) (cokernel.π (biprod.lift ι (K.d n (n + 1))))
        (cokernel.condition _)).Exact :=
    ShortComplex.exact_cokernel _
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z h hh
  have hh' : (h ≫ biprod.inr) ≫ cokernel.π (biprod.lift ι (K.d n (n + 1))) = 0 := by
    rw [Category.assoc]; exact hh
  set w := hse.lift (h ≫ biprod.inr) hh' with hw
  have hwf : w ≫ biprod.lift ι (K.d n (n + 1)) = h ≫ biprod.inr := hse.lift_f _ hh'
  have hwι : w ≫ ι = 0 := by
    have := congrArg (· ≫ biprod.fst) hwf
    simp only [Category.assoc, biprod.lift_fst, biprod.inr_fst, comp_zero] at this
    exact this
  have hw0 : w = 0 := by rw [← cancel_mono ι, hwι, zero_comp]
  have hzero : h ≫ (biprod.inr : K.X (n + 1) ⟶ M ⊞ K.X (n + 1)) = 0 := by
    rw [← hwf, hw0, zero_comp]
  have hsnd := congrArg (· ≫ (biprod.snd : M ⊞ K.X (n + 1) ⟶ K.X (n + 1))) hzero
  simpa using hsnd

/-- The degreewise composite `ff i ≫ pff i = 0`. -/
lemma ffpff_zero (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    ff K n M ι i ≫ pff K n M ι i = 0 := by
  by_cases hn : i = n
  · subst hn
    unfold ff pff
    rw [dite_eq_left rfl, dite_eq_left rfl]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ]
    first
    | rfl
    | (rw [reassoc_of% cokernel.condition]; simp)
  by_cases hn1 : i = n + 1
  · subst hn1
    unfold ff pff
    rw [dite_eq_right (by omega), dite_eq_left rfl, dite_eq_right (by omega), dite_eq_left rfl]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ]
    rw [reassoc_of% (qmap_cond K n M ι), zero_comp]
  · have hz : IsZero ((Qcomplex K n M ι).X i) := by
      rw [Qcomplex_X]; exact QX_isZero_off K n M ι i hn hn1
    exact hz.eq_of_tgt _ _

/-- Degreewise short exactness at degree `n`: `0 → K^n →^ι M → coker ι → 0`. -/
lemma degSE_n (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) [Mono ι] :
    (ShortComplex.mk (ff K n M ι n) (pff K n M ι n) (ffpff_zero K n M ι n)).ShortExact := by
  have hse : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    { exact := ShortComplex.exact_cokernel ι, mono_f := inferInstance, epi_g := coequalizer.π_epi }
  let e :
    (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)) ≅
      (ShortComplex.mk (ff K n M ι n) (pff K n M ι n) (ffpff_zero K n M ι n)) := by
    refine
      ShortComplex.isoMk (Iso.refl _)
        (eqToIso (XX_n K n M (cokernel (biprod.lift ι (K.d n (n + 1))))).symm)
        (eqToIso (QX_n K n M ι).symm) ?_ ?_
    · change
        (Iso.refl (K.X n)).hom ≫ ff K n M ι n =
          ι ≫
            (eqToIso
                (XX_n K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) :
                    XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) n = M).symm).hom
      unfold ff
      rw [dite_eq_left rfl]
      simp [eqToIso]
    · change
        (eqToIso
                (XX_n K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) :
                    XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) n = M).symm).hom ≫
            pff K n M ι n =
          cokernel.π ι ≫ (eqToIso (QX_n K n M ι : QX K n M ι n = cokernel ι).symm).hom
      unfold pff
      rw [dite_eq_left rfl]
      simp [eqToIso]
  exact (ShortComplex.shortExact_iff_of_iso e).mp hse

/-- Degreewise short exactness at degree `n+1`:
`0 → K^{n+1} →^{biprod.inr ≫ π} M' →^{qmap} coker ι → 0`. -/
lemma degSE_n1 (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) [Mono ι] :
    (ShortComplex.mk (ff K n M ι (n + 1)) (pff K n M ι (n + 1))
        (ffpff_zero K n M ι (n + 1))).ShortExact := by
  have := fmap_n1_mono K n M ι
  have := qmap_epi K n M ι
  have hex :
    (ShortComplex.mk (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) (qmap K n M ι)
        (qmap_cond K n M ι)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (qmapIsCokernel K n M ι)
  have hse :
    (ShortComplex.mk (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) (qmap K n M ι)
        (qmap_cond K n M ι)).ShortExact :=
    { exact := hex, mono_f := inferInstance, epi_g := inferInstance }
  let e :
    (ShortComplex.mk (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) (qmap K n M ι)
        (qmap_cond K n M ι)) ≅
      (ShortComplex.mk (ff K n M ι (n + 1)) (pff K n M ι (n + 1))
        (ffpff_zero K n M ι (n + 1))) := by
    refine
      ShortComplex.isoMk (Iso.refl _)
        (eqToIso (XX_n1 K n M (cokernel (biprod.lift ι (K.d n (n + 1))))).symm)
        (eqToIso (QX_n1 K n M ι).symm) ?_ ?_
    · change
        (Iso.refl (K.X (n + 1))).hom ≫ ff K n M ι (n + 1) =
          (biprod.inr ≫ cokernel.π (biprod.lift ι (K.d n (n + 1)))) ≫
            (eqToIso
                (XX_n1 K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) :
                    XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) (n + 1) =
                      cokernel (biprod.lift ι (K.d n (n + 1)))).symm).hom
      unfold ff
      rw [dite_eq_right (by omega), dite_eq_left rfl]
      simp [eqToIso]
    · change
        (eqToIso
                (XX_n1 K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) :
                    XX K n M (cokernel (biprod.lift ι (K.d n (n + 1)))) (n + 1) =
                      cokernel (biprod.lift ι (K.d n (n + 1)))).symm).hom ≫
            pff K n M ι (n + 1) =
          qmap K n M ι ≫ (eqToIso (QX_n1 K n M ι : QX K n M ι (n + 1) = cokernel ι).symm).hom
      unfold pff
      rw [dite_eq_right (by omega), dite_eq_left rfl]
      simp [eqToIso]
  exact (ShortComplex.shortExact_iff_of_iso e).mp hse

/-- Degreewise short exactness off `{n, n+1}`: `ff i` is an iso and the target `Q^i`
is zero, so `0 → K^i → K^i → 0 → 0` is short exact. -/
lemma degSE_off (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) (hn : i ≠ n)
    (hn1 : i ≠ n + 1) :
    (ShortComplex.mk (ff K n M ι i) (pff K n M ι i) (ffpff_zero K n M ι i)).ShortExact := by
  have hffiso : IsIso (ff K n M ι i) := by
    unfold ff; rw [dite_eq_right hn, dite_eq_right hn1]
    exact ⟨eqToHom (XX_off K n M _ i hn hn1), eqToHom_trans _ _, eqToHom_trans _ _⟩
  have hz : IsZero ((Qcomplex K n M ι).X i) := by
    rw [Qcomplex_X]; exact QX_isZero_off K n M ι i hn hn1
  have : Mono (ff K n M ι i) := by
    have := hffiso; infer_instance
  have hepi : Epi (pff K n M ι i) := IsZero.epi hz (pff K n M ι i)
  refine { exact := ?_, mono_f := inferInstance, epi_g := hepi }
  have := hffiso
  rw [ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)]
  exact (inferInstance : Epi (ff K n M ι i))

/-- `Q.d i (i+1) = -𝟙` (via eqToHom) is an isomorphism when `i = n`. -/
lemma Qd_n_isIso (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) :
    IsIso ((Qcomplex K n M ι).d n (n + 1)) := by
  show IsIso (Qd K n M ι n (n + 1))
  unfold Qd
  rw [dite_eq_left ⟨rfl, rfl⟩]
  have : IsIso (-(𝟙 (cokernel ι))) := by refine ⟨-(𝟙 (cokernel ι)), ?_, ?_⟩ <;> simp
  infer_instance

/-- The acyclic complex `Q` has vanishing homology in every degree. -/
lemma Q_acyclic (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M) (i : ℤ) :
    IsZero ((Qcomplex K n M ι).homology i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  by_cases hn : i = n
  · subst i
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp [CochainComplex.prev])
        (by simp [CochainComplex.next])]
    have hf0 : (Qcomplex K n M ι).d (n - 1) n = 0 := by
      show Qd K n M ι (n - 1) n = 0
      unfold Qd; rw [dite_eq_right (by omega)]
    have hg_iso : IsIso ((Qcomplex K n M ι).d n (n + 1)) := Qd_n_isIso K n M ι
    have : Mono ((Qcomplex K n M ι).d n (n + 1)) := by
      have := hg_iso; infer_instance
    rw [ShortComplex.exact_iff_mono _ hf0]
    exact (inferInstance : Mono ((Qcomplex K n M ι).d n (n + 1)))
  by_cases hn1 : i = n + 1
  · subst hn1
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp [CochainComplex.prev])
        (by simp [CochainComplex.next])]
    have hg0 : (Qcomplex K n M ι).d (n + 1) (n + 1 + 1) = 0 := by
      show Qd K n M ι (n + 1) (n + 1 + 1) = 0
      unfold Qd; rw [dite_eq_right (by omega)]
    have hf_iso : IsIso ((Qcomplex K n M ι).d n (n + 1)) := Qd_n_isIso K n M ι
    have : Epi ((Qcomplex K n M ι).d n (n + 1)) := by
      have := hf_iso; infer_instance
    rw [ShortComplex.exact_iff_epi _ hg0]
    exact (inferInstance : Epi ((Qcomplex K n M ι).d n (n + 1)))
  · have hz : IsZero ((Qcomplex K n M ι).X i) := by
      rw [Qcomplex_X]; exact QX_isZero_off K n M ι i hn hn1
    rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp [CochainComplex.prev])
        (by simp [CochainComplex.next])]
    exact ShortComplex.exact_of_isZero_X₂ _ hz

end ElemReplConstruction

end Stacks.BoundedCohomologicalDimension
