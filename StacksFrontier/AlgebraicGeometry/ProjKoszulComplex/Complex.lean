module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.SignedKoszul
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.TwistStalk

/-!
# The Koszul complex of the coordinates on projective space

Let `A` be a ring, grade `A[X₀, …, Xₙ]` by total degree and write `X = P^n_A` for
`Proj A[X₀, …, Xₙ]`. For an integer `a` the Koszul complex of the coordinates `X₀, …, Xₙ`,
graded so that the generator of the `j`-th exterior power sits in degree `j` and twisted by
`a`, is the complex of sheaves of modules

`0 ⟶ 𝒪_X(a) ⟶ … ⟶ 𝒪_X(a+j)^{⊕ binom(n+1, j)} ⟶ … ⟶ 𝒪_X(a+n+1) ⟶ 0`

whose `j`-th term is the direct sum of copies of `𝒪_X(a+j)` indexed by the `j`-element subsets
of `{0, …, n}` and whose differential takes the summand indexed by `s` to the summand indexed
by `s ∪ {i}`, for `i ∉ s`, by multiplication by `Xᵢ` with the Koszul sign of `i` in `s`.

This file constructs that complex and proves that its differential squares to zero. The index
type is taken to be the subsets of a given cardinality, so the rank of the `j`-th term is part
of the construction rather than an afterthought: the terms outside `0 ≤ j ≤ n+1` are direct
sums over an empty type, hence zero, with no case split anywhere.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.twistMulX`: multiplication by the coordinate
  `Xᵢ`, as a morphism `𝒪_X(d) ⟶ 𝒪_X(e)` for `e` any integer equal to `1 + d`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulTerm`: the `j`-th term
  `𝒪_X(a+j)^{⊕ binom(n+1, j)}`, as a direct sum indexed by the `j`-element subsets.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulCoeff`: the matrix entry of the
  differential, from the summand indexed by `s` to the one indexed by `t`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulDiff`: the differential
  `koszulTerm j ⟶ koszulTerm (j+1)`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulComplex`: the cochain complex.

## Main results

* `Stacks.AlgebraicGeometry.ProjKoszulComplex.card_koszulIndexFin`: the `j`-th term is a direct
  sum of `binom(n+1, j)` copies of `𝒪_X(a+j)`.
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulDiff_comp_koszulDiff`: **the differential
  squares to zero.**
* `Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulComplex_d`: the differential of the complex
  in the bidegrees where it can be nonzero.

## Implementation notes

The matrix entry `koszulCoeff` is a sum over all coordinates of a term supported on the one
index `i` for which `t = s ∪ {i}`, rather than a case split producing that `i`: the two lemmas
`koszulCoeff_eq` and `koszulCoeff_eq_zero` evaluate it, and no dependent `if` appears in the
definition of the complex.

Multiplication by `Xᵢ` is `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf` and not
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftInt`: the target twist of the
differential out of degree `j` has to be spelled `a + (j+1)`, which is the degree `1 + (a+j)` of
multiplication by a coordinate only up to an equality of integers, and transporting a morphism
along an equality of twisting sheaves is the `eqToHom` friction the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjEulerSequence/Contraction.lean` warn about. With the target
degree carried as a parameter, every degree in this file is named and no transport occurs inside
a bidegree.

The one `CategoryTheory.eqToHom` in the file is in `koszulD`, which spreads `koszulDiff` over
all bidegrees; it is at a reflexivity proof in every bidegree the complex uses, so
`CategoryTheory.eqToHom_refl` removes it immediately and `koszulD_self` is the only place it
is ever seen.

`CategoryTheory.Limits.HasFiniteBiproducts` is not an instance at the spelling the twisting
sheaves use, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjEulerSequence/Contraction.lean`; it is supplied here as a
`local instance`.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjKoszulComplex

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Components of a composite of biproduct matrices -/

/-- The components of a composite of two morphisms of finite biproducts are the matrix product
of the components: inserting `∑ⱼ πⱼ ≫ ιⱼ = 1` in the middle splits the composite over the
summands of the intermediate biproduct. -/
theorem biproduct_ι_comp_comp_π {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {J K L : Type} [Finite J] [Fintype K] [Finite L]
    (F : J → C) (G : K → C) (H : L → C) (φ : ⨁ F ⟶ ⨁ G) (ψ : ⨁ G ⟶ ⨁ H) (s : J) (u : L) :
    (biproduct.ι F s ≫ φ ≫ ψ) ≫ biproduct.π H u =
      ∑ t : K, (biproduct.ι F s ≫ φ ≫ biproduct.π G t) ≫
        (biproduct.ι G t ≫ ψ ≫ biproduct.π H u) :=
  calc (biproduct.ι F s ≫ φ ≫ ψ) ≫ biproduct.π H u
      = (biproduct.ι F s ≫ φ ≫ (∑ t : K, biproduct.π G t ≫ biproduct.ι G t) ≫ ψ) ≫
          biproduct.π H u := by rw [biproduct.total, Category.id_comp]
    _ = ∑ t : K, (biproduct.ι F s ≫ φ ≫ biproduct.π G t) ≫
          (biproduct.ι G t ≫ ψ ≫ biproduct.π H u) := by
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]

/-- Two composites of scalar multiples of the same pair of morphisms, taken in the two orders,
cancel as soon as the two products of scalars sum to zero. -/
theorem zsmul_comp_add_zsmul_comp_eq_zero {C : Type*} [Category C] [Preadditive C]
    {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R) (hcomm : f' ≫ g' = f ≫ g) (z w z' w' : ℤ)
    (hzw : z * w + z' * w' = 0) :
    (z • f) ≫ (w • g) + (z' • f') ≫ (w' • g') = 0 := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, smul_smul, smul_smul, hcomm, ← add_zsmul, hzw, zero_zsmul]

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The homogeneous ideal of a point of `Proj A[X₀, …, Xₙ]` is a prime ideal. -/
instance isPrime_toIdeal_koszul (x : ProjectiveSpectrum.top (polyGrading A n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-! ### Multiplication by a coordinate -/

/-- **Multiplication by the coordinate `Xᵢ`**, as a morphism `𝒪_X(d) ⟶ 𝒪_X(e)` of twisting
sheaves on `X = Proj A[X₀, …, Xₙ]`, for `e` any integer equal to `1 + d`. -/
def twistMulX (i : Fin (n + 1)) (d e : ℤ) (he : (1 : ℤ) + d = e) :
    twistingSheaf (polyGrading A n) d ⟶ twistingSheaf (polyGrading A n) e :=
  twistMulLeftIntOf (polyGrading A n) ⟨MvPolynomial.X i, X_mem_one A n i⟩ d e
    (by rw [Nat.cast_one]; exact he)

/-- Multiplication by two homogeneous elements of the same degree with the same value agree, the
degree-comparison proofs being irrelevant. -/
private theorem twistMulLeftIntOf_congr {k : ℕ} {α β : polyGrading A n k}
    (h : (α : MvPolynomial (Fin (n + 1)) A) = (β : MvPolynomial (Fin (n + 1)) A)) (d e : ℤ)
    (he he' : (k : ℤ) + d = e) :
    twistMulLeftIntOf (polyGrading A n) α d e he =
      twistMulLeftIntOf (polyGrading A n) β d e he' := by
  obtain rfl : α = β := Subtype.ext h
  rfl

/-- **Multiplication by two coordinates commutes**, both composites being multiplication by
their product. -/
theorem twistMulX_comp_comm (i i' : Fin (n + 1)) (d e g : ℤ) (he : (1 : ℤ) + d = e)
    (hg : (1 : ℤ) + e = g) :
    twistMulX A n i d e he ≫ twistMulX A n i' e g hg =
      twistMulX A n i' d e he ≫ twistMulX A n i e g hg :=
  have he' : ((1 : ℕ) : ℤ) + d = e := by rw [Nat.cast_one]; exact he
  have hg' : ((1 : ℕ) : ℤ) + e = g := by rw [Nat.cast_one]; exact hg
  (twistMulLeftIntOf_comp (polyGrading A n) ⟨MvPolynomial.X i, X_mem_one A n i⟩
      ⟨MvPolynomial.X i', X_mem_one A n i'⟩ d e g he' hg').trans
    ((twistMulLeftIntOf_congr A n (mul_comm _ _) d g _ _).trans
      (twistMulLeftIntOf_comp (polyGrading A n) ⟨MvPolynomial.X i', X_mem_one A n i'⟩
        ⟨MvPolynomial.X i, X_mem_one A n i⟩ d e g he' hg').symm)

/-! ### The terms and the differential -/

variable (a : ℤ)

/-- The family of copies of `𝒪_X(a+j)`, one for each `j`-element subset of the coordinates,
whose direct sum is the `j`-th term of the Koszul complex. -/
abbrev koszulFamily (j : ℤ) :
    koszulIndex (n + 1) j → SheafOfModules.{u} (projRingSheaf (polyGrading A n)) :=
  fun _ => twistingSheaf (polyGrading A n) (a + j)

/-- **The `j`-th term of the Koszul complex**, the direct sum of copies of `𝒪_X(a+j)` indexed by
the `j`-element subsets of the coordinates. For `j` outside `[0, n+1]` the index type is empty
and the term is zero. -/
abbrev koszulTerm (j : ℤ) : SheafOfModules.{u} (projRingSheaf (polyGrading A n)) :=
  ⨁ koszulFamily A n a j

/-- **The `j`-th term of the Koszul complex is a direct sum of `binom(n+1, j)` copies of
`𝒪_X(a+j)`**: its index type is the `j`-element subsets of the `n+1` coordinates. -/
theorem card_koszulIndexFin (j : ℕ) :
    Fintype.card (koszulIndex (n + 1) (j : ℤ)) = (n + 1).choose j :=
  card_koszulIndex (n + 1) j

/-- **The matrix entry of the Koszul differential**: multiplication by `Xᵢ` with the Koszul sign
of `i` in `s` when `t` is `s` with the new element `i`, and zero otherwise. -/
def koszulCoeff (j : ℤ) (s : koszulIndex (n + 1) j) (t : koszulIndex (n + 1) (j + 1)) :
    twistingSheaf (polyGrading A n) (a + j) ⟶ twistingSheaf (polyGrading A n) (a + (j + 1)) :=
  ∑ i : Fin (n + 1), if t.1 = insert i s.1 ∧ i ∉ s.1 then
    koszulSign i s.1 • twistMulX A n i (a + j) (a + (j + 1)) (by ring) else 0

/-- The matrix entry at a pair of indices differing by one element `i` is multiplication by
`Xᵢ` with its sign. The element `i` is determined by the pair, so the sum defining the entry has
only this one nonzero term. -/
theorem koszulCoeff_eq (j : ℤ) (s : koszulIndex (n + 1) j) (t : koszulIndex (n + 1) (j + 1))
    {i : Fin (n + 1)} (hi : i ∉ s.1) (ht : t.1 = insert i s.1) :
    koszulCoeff A n a j s t =
      koszulSign i s.1 • twistMulX A n i (a + j) (a + (j + 1)) (by ring) := by
  classical
  refine Eq.trans (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_) (ite_eq_left ⟨ht, hi⟩)
  intro b _ hb
  refine ite_eq_right fun h => hb ?_
  have hbt : b ∈ insert i s.1 := ht ▸ h.1 ▸ Finset.mem_insert_self b s.1
  exact (Finset.mem_insert.1 hbt).resolve_right h.2

/-- The matrix entry at a pair of indices not differing by a single new element vanishes. -/
theorem koszulCoeff_eq_zero (j : ℤ) (s : koszulIndex (n + 1) j)
    (t : koszulIndex (n + 1) (j + 1)) (h : ∀ i : Fin (n + 1), i ∉ s.1 → t.1 ≠ insert i s.1) :
    koszulCoeff A n a j s t = 0 :=
  Finset.sum_eq_zero fun i _ => ite_eq_right fun hc => h i hc.2 hc.1

/-- **The differential of the Koszul complex** from degree `j` to degree `j + 1`, the matrix
whose entries are `koszulCoeff`. -/
def koszulDiff (j : ℤ) : koszulTerm A n a j ⟶ koszulTerm A n a (j + 1) :=
  biproduct.matrix (koszulCoeff A n a j)

/-- The component of `koszulDiff` from the summand indexed by `s` to the summand indexed by `t`
is `koszulCoeff`. -/
theorem biproduct_ι_comp_koszulDiff_comp_π (j : ℤ) (s : koszulIndex (n + 1) j)
    (t : koszulIndex (n + 1) (j + 1)) :
    biproduct.ι (koszulFamily A n a j) s ≫ koszulDiff A n a j ≫
        biproduct.π (koszulFamily A n a (j + 1)) t =
      koszulCoeff A n a j s t := by
  rw [koszulDiff, ← Category.assoc, biproduct.ι_matrix, biproduct.lift_π]

/-- **The two routes from `s` to `s ∪ {i, i'}` cancel.** Both are multiplication by the product
`Xᵢ Xᵢ'`, and the two signs they carry sum to zero. -/
private theorem signed_pair_cancel (j : ℤ) {i i' : Fin (n + 1)} (hii' : i ≠ i')
    {s : Finset (Fin (n + 1))} (hi : i ∉ s) (hi' : i' ∉ s)
    (h1 : (1 : ℤ) + (a + j) = a + (j + 1))
    (h2 : (1 : ℤ) + (a + (j + 1)) = a + (j + 1 + 1)) :
    (koszulSign i s • twistMulX A n i (a + j) (a + (j + 1)) h1) ≫
        (koszulSign i' (insert i s) •
          twistMulX A n i' (a + (j + 1)) (a + (j + 1 + 1)) h2) +
      (koszulSign i' s • twistMulX A n i' (a + j) (a + (j + 1)) h1) ≫
        (koszulSign i (insert i' s) •
          twistMulX A n i (a + (j + 1)) (a + (j + 1 + 1)) h2) = 0 :=
  zsmul_comp_add_zsmul_comp_eq_zero _ _ _ _
    (twistMulX_comp_comm A n i' i (a + j) (a + (j + 1)) (a + (j + 1 + 1)) h1 h2) _ _ _ _
    (koszulSign_pair_add_eq_zero hii' hi hi')

/-- A product of two consecutive matrix entries from `s` through `t` to `u` vanishes unless `t`
is `s` with one new element and is contained in `u`. -/
private theorem koszulCoeff_comp_eq_zero_or (j : ℤ) (s : koszulIndex (n + 1) j)
    (u : koszulIndex (n + 1) (j + 1 + 1)) (t : koszulIndex (n + 1) (j + 1)) :
    koszulCoeff A n a j s t ≫ koszulCoeff A n a (j + 1) t u = 0 ∨
      ∃ i : Fin (n + 1), i ∉ s.1 ∧ t.1 = insert i s.1 ∧ t.1 ⊆ u.1 := by
  by_cases hts : ∃ i : Fin (n + 1), i ∉ s.1 ∧ t.1 = insert i s.1
  · obtain ⟨i, hi, hti⟩ := hts
    by_cases htu : t.1 ⊆ u.1
    · exact Or.inr ⟨i, hi, hti, htu⟩
    · refine Or.inl ((congrArg (CategoryStruct.comp _)
        (koszulCoeff_eq_zero A n a (j + 1) t u fun i' _ h => ?_)).trans comp_zero)
      exact htu (by rw [h]; exact Finset.subset_insert i' t.1)
  · exact Or.inl ((congrArg (fun f => f ≫ _)
      (koszulCoeff_eq_zero A n a j s t fun i hi h => hts ⟨i, hi, h⟩)).trans zero_comp)

/-- **Two consecutive differentials of the Koszul complex compose to zero.**

For indices `s` and `u` two degrees apart, the matrix entry of the composite at `(s, u)` is the
sum over the indices `t` in between of the products of the entries. If `s` is not contained in
`u` every product vanishes, since a nonzero entry forces an inclusion. Otherwise `u` is `s` with
two new elements `i` and `i'`, there are exactly two indices in between, and the two products
are multiplication by `Xᵢ Xᵢ'` with signs that cancel by
`Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulSign_insert_mul_koszulSign_insert`. -/
theorem koszulDiff_comp_koszulDiff (j : ℤ) :
    koszulDiff A n a j ≫ koszulDiff A n a (j + 1) = 0 := by
  classical
  refine biproduct.hom_ext' _ _ fun s => biproduct.hom_ext _ _ fun u => ?_
  rw [comp_zero, zero_comp, biproduct_ι_comp_comp_π,
    Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) =>
      congrArg₂ CategoryStruct.comp (biproduct_ι_comp_koszulDiff_comp_π A n a j s t)
        (biproduct_ι_comp_koszulDiff_comp_π A n a (j + 1) t u)]
  by_cases hsu : s.1 ⊆ u.1
  · obtain ⟨i, i', hii', hxy⟩ := Finset.card_eq_two.1 (show (u.1 \ s.1).card = 2 by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsu]
      have hs := s.2
      have hu := u.2
      omega)
    have him : i ∈ u.1 ∧ i ∉ s.1 :=
      Finset.mem_sdiff.1 (by rw [hxy]; exact Finset.mem_insert_self i {i'})
    have hi'm : i' ∈ u.1 ∧ i' ∉ s.1 :=
      Finset.mem_sdiff.1 (by
        rw [hxy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i'))
    have hu : u.1 = insert i (insert i' s.1) := by
      refine Finset.Subset.antisymm (fun z hz => ?_) fun z hz => ?_
      · by_cases hzs : z ∈ s.1
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzs)
        · have hzd : z ∈ u.1 \ s.1 := Finset.mem_sdiff.2 ⟨hz, hzs⟩
          rw [hxy] at hzd
          rcases Finset.mem_insert.1 hzd with rfl | hz'
          · exact Finset.mem_insert_self z _
          · rw [Finset.mem_singleton] at hz'
            subst hz'
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self z s.1)
      · rcases Finset.mem_insert.1 hz with rfl | hz'
        · exact him.1
        · rcases Finset.mem_insert.1 hz' with rfl | hz''
          · exact hi'm.1
          · exact hsu hz''
    have hint₂ : i ∉ insert i' s.1 := fun h =>
      (Finset.mem_insert.1 h).elim hii' him.2
    have hi'nt₁ : i' ∉ insert i s.1 := fun h =>
      (Finset.mem_insert.1 h).elim (fun h' => hii' h'.symm) hi'm.2
    have hne : koszulInsert s him.2 ≠ koszulInsert s hi'm.2 := by
      intro hcon
      have h : insert i s.1 = insert i' s.1 := congrArg Subtype.val hcon
      refine hi'nt₁ ?_
      rw [h]
      exact Finset.mem_insert_self i' s.1
    refine Eq.trans (Finset.sum_eq_add_of_mem (koszulInsert s him.2) (koszulInsert s hi'm.2)
      (Finset.mem_univ _) (Finset.mem_univ _) hne ?_) ?_
    · intro t _ ht
      obtain h | ⟨i'', hi'', hti'', htu⟩ := koszulCoeff_comp_eq_zero_or A n a j s u t
      · exact h
      · exfalso
        have hmem : i'' ∈ u.1 \ s.1 :=
          Finset.mem_sdiff.2 ⟨htu (hti'' ▸ Finset.mem_insert_self i'' s.1), hi''⟩
        rw [hxy] at hmem
        rcases Finset.mem_insert.1 hmem with rfl | hmem'
        · exact ht.1 (Subtype.ext hti'')
        · rw [Finset.mem_singleton] at hmem'
          subst hmem'
          exact ht.2 (Subtype.ext hti'')
    · exact (congrArg₂ HAdd.hAdd
        (congrArg₂ CategoryStruct.comp
          (koszulCoeff_eq A n a j s _ him.2 rfl)
          (koszulCoeff_eq A n a (j + 1) _ u hi'nt₁ (hu.trans (Finset.insert_comm i i' s.1))))
        (congrArg₂ CategoryStruct.comp
          (koszulCoeff_eq A n a j s _ hi'm.2 rfl)
          (koszulCoeff_eq A n a (j + 1) _ u hint₂ hu))).trans
          (signed_pair_cancel A n a j hii' him.2 hi'm.2 (by ring) (by ring))
  · refine Finset.sum_eq_zero fun t _ => ?_
    obtain h | ⟨i'', _, hti'', htu⟩ := koszulCoeff_comp_eq_zero_or A n a j s u t
    · exact h
    · exact absurd ((hti'' ▸ Finset.subset_insert i'' s.1).trans htu) hsu

/-! ### The complex -/

/-- The differential of the Koszul complex in an arbitrary pair of degrees: the Koszul
differential when the degrees are consecutive, and zero otherwise. -/
def koszulD (j k : ℤ) : koszulTerm A n a j ⟶ koszulTerm A n a k :=
  if h : j + 1 = k then koszulDiff A n a j ≫ eqToHom (congrArg (koszulTerm A n a) h) else 0

/-- In consecutive degrees `koszulD` is the Koszul differential `koszulDiff`. -/
theorem koszulD_self (j : ℤ) : koszulD A n a j (j + 1) = koszulDiff A n a j := by
  rw [koszulD, dite_eq_left rfl, eqToHom_refl, Category.comp_id]

/-- In non-consecutive degrees `koszulD` vanishes. -/
theorem koszulD_eq_zero (j k : ℤ) (h : ¬ j + 1 = k) : koszulD A n a j k = 0 :=
  dite_eq_right h

/-- **The Koszul complex of the coordinates on `P^n_A`, twisted by `a`**:

`0 ⟶ 𝒪_X(a) ⟶ … ⟶ 𝒪_X(a+j)^{⊕ binom(n+1, j)} ⟶ … ⟶ 𝒪_X(a+n+1) ⟶ 0`,

the `j`-th term being the direct sum of copies of `𝒪_X(a+j)` indexed by the `j`-element subsets
of the coordinates, and the differential taking the summand at `s` to the summand at `s ∪ {i}`
by multiplication by `Xᵢ` with the Koszul sign. The terms in degrees outside `[0, n+1]` are
direct sums over an empty index type, hence zero. -/
def koszulComplex : CochainComplex (SheafOfModules.{u} (projRingSheaf (polyGrading A n))) ℤ where
  X := koszulTerm A n a
  d := koszulD A n a
  shape i j h := koszulD_eq_zero A n a i j h
  d_comp_d' i j k hij hjk := by
    obtain rfl : j = i + 1 := hij.symm
    obtain rfl : k = i + 1 + 1 := hjk.symm
    rw [koszulD_self, koszulD_self, koszulDiff_comp_koszulDiff]

/-- The `j`-th term of `koszulComplex` is `koszulTerm`. -/
theorem koszulComplex_X (j : ℤ) : (koszulComplex A n a).X j = koszulTerm A n a j := rfl

/-- The differential of `koszulComplex` from degree `j` to degree `j + 1` is `koszulDiff`. -/
theorem koszulComplex_d (j : ℤ) :
    (koszulComplex A n a).d j (j + 1) = koszulDiff A n a j :=
  koszulD_self A n a j

end Stacks.AlgebraicGeometry.ProjKoszulComplex

end
