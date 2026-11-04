module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import Mathlib

/-!
# Irreducible numerical types

A numerical type with a single component has zero intersection matrix, so its
genus is `1 + m w (g - 1)` for the multiplicity `m`, weight `w` and component
genus `g`. This file classifies the one-component numerical types of a given
genus by the elementary factorizations of that genus, and deduces that there
are finitely many for each genus other than one.

## Main definitions

* `AlgebraicGeometry.NumericalType.IrreducibleTypes`: the one-component
  numerical types of a given genus.

## Main results

* `AlgebraicGeometry.NumericalType.intersection_self_eq_zero_of_componentCount_eq_one`
  and `AlgebraicGeometry.NumericalType.genus_eq_of_componentCount_eq_one`: the
  intersection matrix vanishes and the genus formula collapses.
* `AlgebraicGeometry.NumericalType.irreducibleTypes_equiv_factorizations_of_genus_neg`,
  `AlgebraicGeometry.NumericalType.irreducibleTypes_equiv_positive_pairs_of_genus_one`
  and
  `AlgebraicGeometry.NumericalType.irreducibleTypes_equiv_factorizations_of_one_lt_genus`:
  the classification in each range of the genus.
* `AlgebraicGeometry.NumericalType.finite_irreducibleTypes_of_genus_neg` and
  `AlgebraicGeometry.NumericalType.finite_irreducibleTypes_of_one_lt_genus`:
  finiteness away from genus one.

## References

* [Stacks Project, Tag 0C73](https://stacks.math.columbia.edu/tag/0C73)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The numerical type with one component, of multiplicity `m`, weight `w` and genus `c`, and
zero intersection number. -/
public def singletonNumericalType (m w c : ℤ) (hm : 0 < m) (hw : 0 < w)
    (hc : 0 ≤ c) : NumericalType where
  componentCount := 1
  componentCount_pos := by omega
  multiplicity := fun _ => m
  intersection := fun _ _ => 0
  weight := fun _ => w
  componentGenus := fun _ => c
  multiplicity_pos := fun _ => hm
  weight_pos := fun _ => hw
  componentGenus_nonneg := fun _ => hc
  intersection_symm := by simp
  intersection_nonneg := by simp
  connected := by
    rintro ⟨I, ⟨i, hi⟩, hI, -⟩
    apply hI
    ext j
    simp only [Set.mem_univ, iff_true]
    simpa [Fin.eq_zero i, Fin.eq_zero j] using hi
  intersection_mul_multiplicity := by simp
  weight_dvd_intersection := by simp

/-- The genus of `singletonNumericalType m w c` is `1 + m w (c - 1)`. -/
public lemma singletonNumericalType_genus (m w c : ℤ) (hm : 0 < m) (hw : 0 < w)
    (hc : 0 ≤ c) : genus (singletonNumericalType m w c hm hw hc) = 1 + m * w * (c - 1) := by
  unfold genus
  change 1 + (∑ _ : Fin 1, m * (w * (c - 1))) - (∑ _ : Fin 1, m * 0) / 2 = _
  simp
  ring

/-- In a one-component intersection matrix with positive multiplicity, every entry vanishes. -/
private lemma entry_eq_zero_of_fin_one (a : Fin 1 → Fin 1 → ℤ) (m : Fin 1 → ℤ)
    (hm : ∀ i, 0 < m i) (hmul : ∀ i, ∑ j, a i j * m j = 0) (i j : Fin 1) : a i j = 0 := by
  rw [Fin.eq_zero j]
  have h := hmul i
  norm_num at h
  exact h.resolve_right (ne_of_gt (hm 0))

/-- Two one-component numerical types with the same multiplicity, weight and genus of their
component are equal. -/
public lemma ext_of_componentCount_eq_one
    (T U : NumericalType) (hT : T.componentCount = 1) (hU : U.componentCount = 1)
    (hm : T.multiplicity ⟨0, T.componentCount_pos⟩ =
      U.multiplicity ⟨0, U.componentCount_pos⟩)
    (hw : T.weight ⟨0, T.componentCount_pos⟩ =
      U.weight ⟨0, U.componentCount_pos⟩)
    (hc : T.componentGenus ⟨0, T.componentCount_pos⟩ =
      U.componentGenus ⟨0, U.componentCount_pos⟩) : T = U := by
  cases T with
  | mk n hn m a w c hm' hw' hc' hs ha hconn hmul hdvd =>
    cases U with
    | mk n' hn' m' a' w' c' hm'' hw'' hc'' hs' ha' hconn' hmul' hdvd' =>
      simp only at hT hU
      subst n
      subst n'
      congr 1 <;> funext i <;> try funext j
      · simpa [Fin.eq_zero i] using hm
      · rw [entry_eq_zero_of_fin_one a m hm' hmul, entry_eq_zero_of_fin_one a' m' hm'' hmul']
      · simpa [Fin.eq_zero i] using hw
      · simpa [Fin.eq_zero i] using hc

/-- One-component numerical types of genus `g`. -/
public def IrreducibleTypes (g : ℤ) :=
  {T : NumericalType // T.componentCount = 1 ∧ genus T = g}

/-- The diagonal intersection number of the unique component is zero. -/
@[stacks 0C73 "diagonal intersection"]
public lemma intersection_self_eq_zero_of_componentCount_eq_one
    (T : NumericalType) (hT : T.componentCount = 1) :
    T.intersection ⟨0, T.componentCount_pos⟩ ⟨0, T.componentCount_pos⟩ = 0 := by
  cases T with
  | mk n hn m a w c hm hw hc hs ha hconn hmul hdvd =>
    simp only at hT
    subst n
    exact entry_eq_zero_of_fin_one a m hm hmul 0 0

/-- The genus formula for a one-component numerical type. -/
@[stacks 0C73 "genus formula"]
public lemma genus_eq_of_componentCount_eq_one (T : NumericalType)
    (hT : T.componentCount = 1) :
    genus T = 1 + T.multiplicity ⟨0, T.componentCount_pos⟩ *
      T.weight ⟨0, T.componentCount_pos⟩ *
        (T.componentGenus ⟨0, T.componentCount_pos⟩ - 1) := by
  cases T with
  | mk n hn m a w c hm hw hc hs ha hconn hmul hdvd =>
    simp only at hT
    subst n
    norm_num [genus, entry_eq_zero_of_fin_one a m hm hmul 0 0]
    ring

/-- The genus formula for an irreducible type, rearranged. -/
private lemma mul_mul_componentGenus_sub_one_eq (g : ℤ) (T : IrreducibleTypes g) :
    T.1.multiplicity ⟨0, T.1.componentCount_pos⟩ * T.1.weight ⟨0, T.1.componentCount_pos⟩ *
      (T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ - 1) = g - 1 := by
  have heq := genus_eq_of_componentCount_eq_one T.1 T.2.1
  rw [T.2.2] at heq
  omega

/-- In nonpositive genus, the unique component has genus zero. -/
private lemma componentGenus_eq_zero_of_genus_nonpos (g : ℤ) (hg : g ≤ 0)
    (T : IrreducibleTypes g) : T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ = 0 := by
  have heq := mul_mul_componentGenus_sub_one_eq g T
  have hm := T.1.multiplicity_pos ⟨0, T.1.componentCount_pos⟩
  have hw := T.1.weight_pos ⟨0, T.1.componentCount_pos⟩
  have hc := T.1.componentGenus_nonneg ⟨0, T.1.componentCount_pos⟩
  by_contra hne
  have hp := mul_nonneg (mul_pos hm hw).le
    (show 0 ≤ T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ - 1 by omega)
  omega

/-- In negative genus, the unique component has genus zero. -/
@[stacks 0C73 "negative genus component"]
public lemma componentGenus_eq_zero_of_genus_neg (g : ℤ) (hg : g < 0)
    (T : IrreducibleTypes g) :
    T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ = 0 :=
  componentGenus_eq_zero_of_genus_nonpos g hg.le T

/-- In negative genus, one-component numerical types correspond exactly to
positive factorizations of `1 - g`, via multiplicity and weight. -/
@[stacks 0C73 "negative genus classification"]
public lemma irreducibleTypes_equiv_factorizations_of_genus_neg (g : ℤ) (hg : g < 0) :
    ∃ e : IrreducibleTypes g ≃
        {p : ℤ × ℤ // 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 = 1 - g},
      ∀ T, (e T : ℤ × ℤ) =
        (T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
          T.1.weight ⟨0, T.1.componentCount_pos⟩) := by
  let f : IrreducibleTypes g →
      {p : ℤ × ℤ // 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 = 1 - g} := fun T =>
    ⟨(T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
        T.1.weight ⟨0, T.1.componentCount_pos⟩),
      T.1.multiplicity_pos _, T.1.weight_pos _, by
        have h := mul_mul_componentGenus_sub_one_eq g T
        rw [componentGenus_eq_zero_of_genus_neg g hg T] at h
        dsimp only
        omega⟩
  have hf : Function.Bijective f := by
    constructor
    · intro T U h
      apply Subtype.ext
      apply ext_of_componentCount_eq_one T.1 U.1 T.2.1 U.2.1
      · exact congrArg (fun p => p.1) (congrArg Subtype.val h)
      · exact congrArg (fun p => p.2) (congrArg Subtype.val h)
      · rw [componentGenus_eq_zero_of_genus_neg g hg T,
          componentGenus_eq_zero_of_genus_neg g hg U]
    · rintro ⟨⟨m, w⟩, hm, hw, hmw⟩
      let S := singletonNumericalType m w 0 hm hw (by omega)
      have hS : genus S = g := by
        rw [singletonNumericalType_genus]
        have hmw' : m * w = 1 - g := by simpa only [Prod.fst, Prod.snd] using hmw
        omega
      refine ⟨⟨S, rfl, hS⟩, ?_⟩
      apply Subtype.ext
      simp [f, S, singletonNumericalType]
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

/-- For fixed negative genus there are only finitely many one-component
numerical types. -/
@[stacks 0C73 "negative genus finiteness"]
public lemma finite_irreducibleTypes_of_genus_neg (g : ℤ) (hg : g < 0) :
    Set.Finite {T : NumericalType | T.componentCount = 1 ∧ genus T = g} := by
  obtain ⟨e, -⟩ := irreducibleTypes_equiv_factorizations_of_genus_neg g hg
  let S : Set (ℤ × ℤ) :=
    {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 = 1 - g}
  have hS : S.Finite := by
    apply ((Set.finite_Icc 1 (1 - g)).prod (Set.finite_Icc 1 (1 - g))).subset
    rintro ⟨m, w⟩ ⟨hm, hw, hmw⟩
    simp only at hm hw hmw
    simp only [Set.mem_prod, Set.mem_Icc]
    have hm0 : 0 ≤ m := le_of_lt hm
    have hw0 : 0 ≤ w := le_of_lt hw
    have hmle : m ≤ m * w := by nlinarith
    have hwle : w ≤ m * w := by nlinarith
    omega
  let : Fintype {p : ℤ × ℤ // 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 = 1 - g} :=
    hS.fintype
  let : Fintype (IrreducibleTypes g) := Fintype.ofEquiv _ e.symm
  rw [show {T : NumericalType | T.componentCount = 1 ∧ genus T = g} =
      Set.range (fun T : IrreducibleTypes g => T.1) by
    ext T
    simp [IrreducibleTypes]]
  exact Set.finite_range _

/-- In genus zero, the product of the multiplicity and weight is one. -/
private lemma multiplicity_mul_weight_eq_one_of_genus_zero (T : IrreducibleTypes 0) :
    T.1.multiplicity ⟨0, T.1.componentCount_pos⟩ * T.1.weight ⟨0, T.1.componentCount_pos⟩ = 1 := by
  have heq := mul_mul_componentGenus_sub_one_eq 0 T
  rw [componentGenus_eq_zero_of_genus_nonpos 0 le_rfl T] at heq
  omega

/-- In genus zero, the unique multiplicity is one. -/
@[stacks 0C73 "genus zero multiplicity"]
public lemma multiplicity_eq_one_of_genus_zero (T : IrreducibleTypes 0) :
    T.1.multiplicity ⟨0, T.1.componentCount_pos⟩ = 1 :=
  Int.eq_one_of_mul_eq_one_right (T.1.multiplicity_pos _).le
    (multiplicity_mul_weight_eq_one_of_genus_zero T)

/-- In genus zero, the unique weight is one. -/
@[stacks 0C73 "genus zero weight"]
public lemma weight_eq_one_of_genus_zero (T : IrreducibleTypes 0) :
    T.1.weight ⟨0, T.1.componentCount_pos⟩ = 1 :=
  Int.eq_one_of_mul_eq_one_left (T.1.weight_pos _).le
    (multiplicity_mul_weight_eq_one_of_genus_zero T)

/-- In genus zero, the unique component has genus zero. -/
@[stacks 0C73 "genus zero component"]
public lemma componentGenus_eq_zero_of_genus_zero (T : IrreducibleTypes 0) :
    T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ = 0 :=
  componentGenus_eq_zero_of_genus_nonpos 0 le_rfl T

/-- In genus one, the unique component has genus one. -/
@[stacks 0C73 "genus one component"]
public lemma componentGenus_eq_one_of_genus_one (T : IrreducibleTypes 1) :
    T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ = 1 := by
  have hz := mul_mul_componentGenus_sub_one_eq 1 T
  have hp := mul_pos (T.1.multiplicity_pos ⟨0, T.1.componentCount_pos⟩)
    (T.1.weight_pos ⟨0, T.1.componentCount_pos⟩)
  have := (mul_eq_zero.mp (hz.trans (sub_self 1))).resolve_left hp.ne'
  omega

/-- In genus one, multiplicity and weight range independently over all positive
integers. -/
@[stacks 0C73 "genus one classification"]
public lemma irreducibleTypes_equiv_positive_pairs_of_genus_one :
    ∃ e : IrreducibleTypes 1 ≃ {p : ℤ × ℤ // 0 < p.1 ∧ 0 < p.2},
      ∀ T, (e T : ℤ × ℤ) =
        (T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
          T.1.weight ⟨0, T.1.componentCount_pos⟩) := by
  let f : IrreducibleTypes 1 → {p : ℤ × ℤ // 0 < p.1 ∧ 0 < p.2} := fun T =>
    ⟨(T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
        T.1.weight ⟨0, T.1.componentCount_pos⟩),
      T.1.multiplicity_pos _, T.1.weight_pos _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro T U h
      apply Subtype.ext
      apply ext_of_componentCount_eq_one T.1 U.1 T.2.1 U.2.1
      · exact congrArg (fun p => p.1) (congrArg Subtype.val h)
      · exact congrArg (fun p => p.2) (congrArg Subtype.val h)
      · rw [componentGenus_eq_one_of_genus_one T,
          componentGenus_eq_one_of_genus_one U]
    · rintro ⟨⟨m, w⟩, hm, hw⟩
      let S := singletonNumericalType m w 1 hm hw (by omega)
      have hS : genus S = 1 := by simp [S, singletonNumericalType_genus]
      refine ⟨⟨S, rfl, hS⟩, ?_⟩
      apply Subtype.ext
      simp [f, S, singletonNumericalType]
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

/-- Above genus one, the unique component has genus greater than one. -/
@[stacks 0C73 "positive genus component"]
public lemma one_lt_componentGenus_of_one_lt_genus (g : ℤ) (hg : 1 < g)
    (T : IrreducibleTypes g) :
    1 < T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ := by
  have heq := mul_mul_componentGenus_sub_one_eq g T
  have hp := mul_pos (T.1.multiplicity_pos ⟨0, T.1.componentCount_pos⟩)
    (T.1.weight_pos ⟨0, T.1.componentCount_pos⟩)
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hp.le (show
    T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ - 1 ≤ 0 by omega)
  omega

/-- Above genus one, one-component numerical types correspond exactly to
positive three-factor factorizations of `g - 1`. -/
@[stacks 0C73 "positive genus classification"]
public lemma irreducibleTypes_equiv_factorizations_of_one_lt_genus (g : ℤ) (hg : 1 < g) :
    ∃ e : IrreducibleTypes g ≃
        {p : (ℤ × ℤ) × ℤ //
          0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2 ∧ p.1.1 * p.1.2 * p.2 = g - 1},
      ∀ T, (e T : (ℤ × ℤ) × ℤ) =
        ((T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
            T.1.weight ⟨0, T.1.componentCount_pos⟩),
          T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ - 1) := by
  let f : IrreducibleTypes g →
      {p : (ℤ × ℤ) × ℤ //
        0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2 ∧ p.1.1 * p.1.2 * p.2 = g - 1} := fun T =>
    ⟨((T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
        T.1.weight ⟨0, T.1.componentCount_pos⟩),
        T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ - 1),
      T.1.multiplicity_pos _, T.1.weight_pos _, by
        have := one_lt_componentGenus_of_one_lt_genus g hg T
        omega, by
        exact mul_mul_componentGenus_sub_one_eq g T⟩
  have hf : Function.Bijective f := by
    constructor
    · intro T U h
      have hv := congrArg Subtype.val h
      change ((T.1.multiplicity ⟨0, T.1.componentCount_pos⟩,
          T.1.weight ⟨0, T.1.componentCount_pos⟩),
          T.1.componentGenus ⟨0, T.1.componentCount_pos⟩ - 1) =
        ((U.1.multiplicity ⟨0, U.1.componentCount_pos⟩,
          U.1.weight ⟨0, U.1.componentCount_pos⟩),
          U.1.componentGenus ⟨0, U.1.componentCount_pos⟩ - 1) at hv
      apply Subtype.ext
      apply ext_of_componentCount_eq_one T.1 U.1 T.2.1 U.2.1
      · exact congrArg (fun p => p.1.1) hv
      · exact congrArg (fun p => p.1.2) hv
      · have hc := congrArg (fun p => p.2) hv
        omega
    · rintro ⟨⟨⟨m, w⟩, d⟩, hm, hw, hd, hmwd⟩
      simp only at hm hw hd hmwd
      let S := singletonNumericalType m w (d + 1) hm hw (by omega)
      have hS : genus S = g := by
        rw [singletonNumericalType_genus, show d + 1 - 1 = d by ring]
        have hmwd' : m * w * d = g - 1 := by
          simpa only [Prod.fst, Prod.snd] using hmwd
        omega
      refine ⟨⟨S, rfl, hS⟩, ?_⟩
      apply Subtype.ext
      simp [f, S, singletonNumericalType]
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

/-- For fixed genus greater than one there are only finitely many one-component
numerical types. -/
@[stacks 0C73 "positive genus finiteness"]
public lemma finite_irreducibleTypes_of_one_lt_genus (g : ℤ) (hg : 1 < g) :
    Set.Finite {T : NumericalType | T.componentCount = 1 ∧ genus T = g} := by
  obtain ⟨e, -⟩ := irreducibleTypes_equiv_factorizations_of_one_lt_genus g hg
  let S : Set ((ℤ × ℤ) × ℤ) :=
    {p | 0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2 ∧ p.1.1 * p.1.2 * p.2 = g - 1}
  have hS : S.Finite := by
    apply (((Set.finite_Icc 1 (g - 1)).prod (Set.finite_Icc 1 (g - 1))).prod
      (Set.finite_Icc 1 (g - 1))).subset
    rintro ⟨⟨m, w⟩, d⟩ ⟨hm, hw, hd, hmwd⟩
    simp only at hm hw hd hmwd
    simp only [Set.mem_prod, Set.mem_Icc]
    have hm0 : 0 ≤ m := le_of_lt hm
    have hw0 : 0 ≤ w := le_of_lt hw
    have hd0 : 0 ≤ d := le_of_lt hd
    have hmw0 : 0 ≤ m * w := mul_nonneg hm0 hw0
    have hmw1 : 1 ≤ m * w := by nlinarith
    have hm_mw : m ≤ m * w := by nlinarith
    have hw_mw : w ≤ m * w := by nlinarith
    have hmw_prod : m * w ≤ m * w * d := le_mul_of_one_le_right hmw0 hd
    have hmle : m ≤ m * w * d := hm_mw.trans hmw_prod
    have hwle : w ≤ m * w * d := hw_mw.trans hmw_prod
    have hdle : d ≤ m * w * d := le_mul_of_one_le_left hd0 hmw1
    omega
  let : Fintype {p : (ℤ × ℤ) × ℤ //
      0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2 ∧ p.1.1 * p.1.2 * p.2 = g - 1} := hS.fintype
  let : Fintype (IrreducibleTypes g) := Fintype.ofEquiv _ e.symm
  rw [show {T : NumericalType | T.componentCount = 1 ∧ genus T = g} =
      Set.range (fun T : IrreducibleTypes g => T.1) by
    ext T
    simp [IrreducibleTypes]]
  exact Set.finite_range _

end AlgebraicGeometry.NumericalType
