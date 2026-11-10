module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential

/-! # Derivations on a set-variable divided power extension

Tag 0F4I adjoins to a graded divided power algebra `A` a set of variables of a single positive
degree `d`. This file names the shape of that output as a predicate, `IsSetVariableExtension`, and
develops what is needed to extend a *graded derivation* across such an extension: a derivation is
not a ring homomorphism, so the colimit presentation of the extension has to be used at the level
of additive maps.

The coefficients of a set-variable extension are graded, not concentrated in degree zero, which is
why `DividedPowers.TateResolution.GradedDividedPowerPolynomial` cannot be used to express this:
that structure's `coefficient_mem` field pins the coefficient algebra to degree zero. In the
intended application — lifting a differential across a surjection with square-zero kernel, Tag
09PS — the coefficient algebra at each step is the previous step's algebra and does have positive
degrees.

## Main definitions

* `DividedPowers.TateResolution.IsSetVariableExtension` — the output shape of Tag 0F4I as a
  predicate on the coefficient map and the family of variables.

## Main results

* `DividedPowers.TateResolution.existsUnique_gradedDerivation_setVariableExtension` — a graded
  derivation of the coefficient algebra, compatible with its divided powers, extends uniquely to
  a graded derivation of the extension once a value is prescribed for each adjoined variable.
* `DividedPowers.TateResolution.finiteVariableStages_directedColimit_addHom` — the additive
  analogue of `finiteVariableStages_directedColimit`: a compatible family of additive maps out of
  the finite variable stages extends uniquely to an additive map out of the whole extension.
* `DividedPowers.TateResolution.map_smul_of_graded_leibniz` — an additive map killing degree zero
  and obeying the signed Leibniz rule on homogeneous elements is automatically `R`-linear, so a
  derivation may be carried as an additive map and upgraded for free.
* `DividedPowers.TateResolution.gradedDerivationToLinearMap` and
  `DividedPowers.TateResolution.isGradedDerivation_toLinearMap` — that upgrade, packaged.
* `DividedPowers.TateResolution.mem_grade_of_map_mem_grade` and
  `DividedPowers.TateResolution.mem_positiveEvenPart_of_map_mem_positiveEvenPart` — an injective
  degree-preserving algebra map reflects homogeneous degrees and the positive even part.
* `DividedPowers.TateResolution.IsSetVariableExtension.gradedPart_mem_finiteVariableStage` — a
  finite variable stage is a graded subring, so a derivation of it is determined by its values on
  homogeneous elements.

## Implementation notes

The derivation is built stage by stage over the finite subsets of the variable set, each
successor stage being the odd or even one-variable extension of its predecessor, and the stages
are then assembled by `finiteVariableStages_directedColimit_addHom`. Compatibility of the
stagewise derivations is not arranged by construction but deduced: a finite variable stage is a
graded subring of the ambient algebra, so a derivation of it is determined by its values on the
coefficients and the variables, which is `IsStageDerivation.eq_of_subset`. Both one-variable
cases are handled by the single statement
`exists_isStageDerivation_of_oneVariableExtension`, which takes the one-variable extension
abstractly.

A graded derivation needs no linearity hypothesis to be linear. The algebra structure on a finite
variable stage is supplied abstractly and need not restrict the ambient one, so a map out of a
stage cannot be assumed `R`-linear; but `algebraMap r` lies in degree zero of the stage, a graded
derivation kills degree zero, and the Leibniz rule then gives `D (algebraMap r * x) = algebraMap r
* D x`. So additive maps may be carried through the induction and upgraded for free, which is why
the colimit is developed for additive maps rather than for linear ones.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

open EvenVariableAlgebra OddVariableExtension

/-- The data presenting `C` as the graded divided power algebra obtained from `A` by adjoining a
set of variables of the single positive degree `d`. These are exactly the clauses produced by
`DividedPowers.TateResolution.exists_setVariableDividedPowerExtension`, named so that consumers
need not restate them. -/
public structure IsSetVariableExtension
    {R : Type u} {A : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (γ : DividedPowerStructure Aᵢ)
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (δ : DividedPowerStructure Cᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (d : ℕ) (hd : 0 < d) : Prop where
  /-- The coefficient map is injective. -/
  coefficient_injective : Function.Injective ι
  /-- The coefficient map preserves homogeneous degrees. -/
  coefficient_grade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m
  /-- The coefficient map preserves divided powers. -/
  coefficient_dpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
    δ.dpow n (ι a) = ι (γ.dpow n a)
  /-- Each adjoined variable is homogeneous of degree `d`. -/
  generator_mem : ∀ j : J, T j ∈ Cᵢ d
  /-- The finite variable stages cover the extension. -/
  finite_support : ∀ x : C, ∃ S : Finset J, x ∈ finiteVariableStage δ ι T S
  /-- Adjoining one variable to a finite stage is the relevant odd or even divided power
  extension. -/
  successor : ∀ (S : Finset J) (j : J), j ∉ S →
    letI : DecidableEq J := Classical.decEq J
    ∃ (aS : Algebra R (finiteVariableStage δ ι T S)),
      letI : Algebra R (finiteVariableStage δ ι T S) := aS
      ∃ (Sᵢ : ℕ → Submodule R (finiteVariableStage δ ι T S))
        (gS : GradedAlgebra Sᵢ),
        letI : GradedAlgebra Sᵢ := gS
        ∃ (cS : IsStrictlyGradedComm Sᵢ),
          letI : IsStrictlyGradedComm Sᵢ := cS
          ∃ δS : DividedPowerStructure Sᵢ,
            (∀ (n : ℕ) (b : finiteVariableStage δ ι T S),
              b ∈ positiveEvenPart Sᵢ →
                (δS.dpow n b : C) = δ.dpow n (b : C)) ∧
            (∀ hodd : Odd d,
              ∃ e : OddVariableExtension Sᵢ d ≃+*
                  finiteVariableStage δ ι T (insert j S),
                (∀ b : finiteVariableStage δ ι T S,
                  ((e (OddVariableExtension.inclusion Sᵢ d b) :
                    finiteVariableStage δ ι T (insert j S)) : C) = b) ∧
                ((e (OddVariableExtension.generator Sᵢ d) :
                  finiteVariableStage δ ι T (insert j S)) : C) = T j ∧
                (∀ (m : ℕ) (x : OddVariableExtension Sᵢ d),
                  x ∈ OddVariableExtension.grade Sᵢ d m ↔ (e x : C) ∈ Cᵢ m) ∧
                (∀ (n : ℕ) (x : OddVariableExtension Sᵢ d),
                  x ∈ positiveEvenPart (OddVariableExtension.grade Sᵢ d) →
                  δ.dpow n (e x : C) =
                    (e ((oddVariableDividedPowerStructure Sᵢ δS d hd hodd).dpow n x) : C))) ∧
            (∀ heven : Even d,
              letI : Fact (Even d) := ⟨heven⟩
              ∃ e : EvenVariableAlgebra (finiteVariableStage δ ι T S) ≃+*
                  finiteVariableStage δ ι T (insert j S),
                (∀ b : finiteVariableStage δ ι T S,
                  ((e (coeffEmbedding b) :
                    finiteVariableStage δ ι T (insert j S)) : C) = b) ∧
                ((e (monomial 1 1) :
                  finiteVariableStage δ ι T (insert j S)) : C) = T j ∧
                (∀ (m : ℕ) (x : EvenVariableAlgebra (finiteVariableStage δ ι T S)),
                  x ∈ EvenVariableAlgebra.grade Sᵢ d m ↔ (e x : C) ∈ Cᵢ m) ∧
                (∀ (n : ℕ) (x : EvenVariableAlgebra (finiteVariableStage δ ι T S)),
                  x ∈ positiveEvenPart (EvenVariableAlgebra.grade Sᵢ d) →
                  δ.dpow n (e x : C) =
                    (e ((evenVariableDividedPowerStructure d hd δS).dpow n x) : C)))

/-- The additive analogue of `finiteVariableStages_directedColimit`: if the finite variable stages
cover the extension, a family of additive maps out of them which agree wherever their arguments
agree extends uniquely to an additive map out of the whole extension. -/
@[stacks 0F4I "directed colimit of finite stages, additively"]
public theorem finiteVariableStages_directedColimit_addHom
    {R : Type u} {A : Type v} {C : Type z} {D : Type w} {J : Type*}
    [CommRing R] [Ring A] [Ring C] [AddCommGroup D] [Algebra R A] [Algebra R C]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ] (δ : DividedPowerStructure Cᵢ)
    (ι : A →ₐ[R] C) (T : J → C)
    (hfinite : ∀ x : C, ∃ S : Finset J, x ∈ finiteVariableStage δ ι T S)
    (f : (S : Finset J) → finiteVariableStage δ ι T S →+ D)
    (hcompat : ∀ (S U : Finset J)
      (x : finiteVariableStage δ ι T S)
      (y : finiteVariableStage δ ι T U),
      (x : C) = (y : C) → f S x = f U y) :
    ∃! g : C →+ D,
      ∀ (S : Finset J) (x : finiteVariableStage δ ι T S),
        g (x : C) = f S x := by
  classical
  let stage (x : C) : Finset J := Classical.choose (hfinite x)
  have memStage (x : C) : x ∈ finiteVariableStage δ ι T (stage x) :=
    Classical.choose_spec (hfinite x)
  let g : C →+ D :=
    { toFun := fun x => f (stage x) ⟨x, memStage x⟩
      map_zero' := by
        calc
          f (stage 0) ⟨0, memStage 0⟩ =
              f ∅ ⟨0, (finiteVariableStage δ ι T ∅).zero_mem⟩ := by
            apply hcompat
            rfl
          _ = 0 := map_zero (f ∅)
      map_add' := by
        intro x y
        have hx : x ∈ finiteVariableStage δ ι T (stage x ∪ stage y) :=
          finiteVariableStage_le_of_subset δ ι T Finset.subset_union_left (memStage x)
        have hy : y ∈ finiteVariableStage δ ι T (stage x ∪ stage y) :=
          finiteVariableStage_le_of_subset δ ι T Finset.subset_union_right (memStage y)
        calc
          f (stage (x + y)) ⟨x + y, memStage (x + y)⟩ =
              f (stage x ∪ stage y) ⟨x + y, add_mem hx hy⟩ := by
            apply hcompat
            rfl
          _ = f (stage x ∪ stage y) (⟨x, hx⟩ + ⟨y, hy⟩) := by congr 1
          _ = f (stage x ∪ stage y) ⟨x, hx⟩ + f (stage x ∪ stage y) ⟨y, hy⟩ :=
              map_add (f (stage x ∪ stage y)) _ _
          _ = f (stage x) ⟨x, memStage x⟩ + f (stage y) ⟨y, memStage y⟩ := by
            congr 1 <;> apply hcompat <;> rfl }
  refine ⟨g, ?_, ?_⟩
  · intro S x
    apply hcompat
    rfl
  · intro g' hg'
    ext x
    obtain ⟨S, hx⟩ := hfinite x
    calc
      g' x = f S ⟨x, hx⟩ := hg' S ⟨x, hx⟩
      _ = g x := by symm; apply hcompat; rfl

section Linearity

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The signed Leibniz rule with a homogeneous left factor extends to an arbitrary right factor,
by decomposing it. -/
public theorem leibniz_of_mem_grade_left (D : A →+ A)
    (hleib : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y))
    {i : ℕ} {x : A} (hx : x ∈ 𝒜 i) (y : A) :
    D (x * y) = D x * y + (-1 : R) ^ i • (x * D y) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 y]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 y]
  rw [Finset.mul_sum, map_sum, Finset.mul_sum, map_sum, Finset.mul_sum,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact hleib i m x _ hx (DirectSum.decompose 𝒜 y m).property

/-- An additive map which kills degree zero and satisfies the signed Leibniz rule on homogeneous
elements is automatically `R`-linear. No linearity hypothesis is needed: `algebraMap r` is
homogeneous of degree zero, so the map kills it and the Leibniz rule does the rest.

This is what lets a derivation be carried through the finite variable stages as an additive map,
where the `R`-algebra structure is supplied abstractly and `R`-linearity is not available. -/
public theorem map_smul_of_graded_leibniz (D : A →+ A)
    (hzero : ∀ x : A, x ∈ 𝒜 0 → D x = 0)
    (hleib : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y))
    (r : R) (x : A) : D (r • x) = r • D x := by
  have hmem : algebraMap R A r ∈ 𝒜 0 := SetLike.algebraMap_mem_graded 𝒜 r
  rw [Algebra.smul_def, leibniz_of_mem_grade_left 𝒜 D hleib hmem x, hzero _ hmem, zero_mul,
    zero_add, pow_zero, one_smul, Algebra.smul_def]

/-- An additive graded derivation, packaged as a linear map. -/
public noncomputable def gradedDerivationToLinearMap (D : A →+ A)
    (hzero : ∀ x : A, x ∈ 𝒜 0 → D x = 0)
    (hleib : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) :
    A →ₗ[R] A where
  toFun := D
  map_add' := D.map_add
  map_smul' := map_smul_of_graded_leibniz 𝒜 D hzero hleib

/-- `gradedDerivationToLinearMap 𝒜 D hzero hleib` agrees with `D` pointwise. -/
@[simp]
public theorem gradedDerivationToLinearMap_apply (D : A →+ A)
    (hzero : ∀ x : A, x ∈ 𝒜 0 → D x = 0)
    (hleib : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) (x : A) :
    gradedDerivationToLinearMap 𝒜 D hzero hleib x = D x := rfl

/-- A graded derivation satisfying the square-zero condition, recovered from the additive data. -/
public theorem isGradedDerivation_toLinearMap (D : A →+ A)
    (hzero : ∀ x : A, x ∈ 𝒜 0 → D x = 0)
    (hmem : ∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 1) → D x ∈ 𝒜 n)
    (hleib : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) :
    IsGradedDerivation 𝒜 (gradedDerivationToLinearMap 𝒜 D hzero hleib) where
  d_grade_zero hx := hzero _ hx
  d_mem hx := hmem _ _ hx
  leibniz hx hy := hleib _ _ _ _ hx hy

end Linearity

noncomputable section Extension


section GradedPartAux

variable {R : Type u} {C : Type v} [CommRing R] [Ring C] [Algebra R C]
  (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]

/-- The degree-`m` component of `-x` is minus the degree-`m` component of `x`. -/
public theorem gradedPart_neg (x : C) (m : ℕ) :
    gradedPart Cᵢ (-x) m = -gradedPart Cᵢ x m := by
  have h := gradedPart_add Cᵢ x (-x) m
  rw [add_neg_cancel, gradedPart_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Every element is the sum of its homogeneous components over some finite set of degrees. -/
public theorem exists_gradedPart_decomposition (x : C) :
    ∃ s : Finset ℕ, x = ∑ m ∈ s, gradedPart Cᵢ x m := by
  classical
  exact ⟨(DirectSum.decompose Cᵢ x).support, (DirectSum.sum_support_decompose Cᵢ x).symm⟩

/-- The degree-`m` component of a product of two finite sums is the double sum of the
degree-`m` components of the pairwise products. -/
public theorem gradedPart_mul_sum {s t : Finset ℕ} (a b : ℕ → C) (m : ℕ) :
    gradedPart Cᵢ ((∑ i ∈ s, a i) * ∑ k ∈ t, b k) m =
      ∑ i ∈ s, ∑ k ∈ t, gradedPart Cᵢ (a i * b k) m := by
  rw [Finset.sum_mul_sum, gradedPart_sum]
  exact Finset.sum_congr rfl fun i _ => gradedPart_sum Cᵢ _ _ m

/-- A product of homogeneous elements of degrees `i` and `k` is its own degree-`(i + k)`
component. -/
public theorem gradedPart_mul_homogeneous {i k m : ℕ} {x y : C} (hx : x ∈ Cᵢ i)
    (hy : y ∈ Cᵢ k) (hm : i + k = m) : gradedPart Cᵢ (x * y) m = x * y := by
  rw [← hm]
  exact gradedPart_of_mem_same Cᵢ (SetLike.mul_mem_graded hx hy)

/-- A product of homogeneous elements of degrees `i` and `k` has zero component in every
degree `m ≠ i + k`. -/
public theorem gradedPart_mul_homogeneous_of_ne {i k m : ℕ} {x y : C} (hx : x ∈ Cᵢ i)
    (hy : y ∈ Cᵢ k) (hm : i + k ≠ m) : gradedPart Cᵢ (x * y) m = 0 :=
  gradedPart_of_mem_ne Cᵢ (SetLike.mul_mem_graded hx hy) hm

/-- Every homogeneous component of a homogeneous element of a subring lies in that subring. -/
public theorem gradedPart_mem_subring_of_mem_grade {x : C} {i : ℕ} (hx : x ∈ Cᵢ i)
    (P : Subring C) (hxP : x ∈ P) (m : ℕ) : gradedPart Cᵢ x m ∈ P := by
  by_cases h : i = m
  · subst h
    rw [gradedPart_of_mem_same Cᵢ hx]
    exact hxP
  · rw [gradedPart_of_mem_ne Cᵢ hx h]
    exact P.zero_mem

end GradedPartAux



section GradedPartAux
variable {R : Type u} {C : Type v} [CommRing R] [Ring C] [Algebra R C]
  (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]

/-- The degree-`m` component of `x` vanishes when its `m`-th term in the direct-sum
decomposition does. -/
public theorem gradedPart_eq_zero_of_decompose_eq_zero {x : C} {m : ℕ}
    (hm : DirectSum.decompose Cᵢ x m = 0) : gradedPart Cᵢ x m = 0 := by
  rw [gradedPart, hm]
  rfl
end GradedPartAux

section Reflect
variable {R : Type u} {A : Type v} {C : Type z} [CommRing R] [Ring A] [Algebra R A]
  [Ring C] [Algebra R C]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
  (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] (ι : A →ₐ[R] C)
  (hgrade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m)

include hgrade in
/-- A degree-preserving algebra map commutes with taking homogeneous components. -/
public theorem gradedPart_algHom (a : A) (m : ℕ) :
    gradedPart Cᵢ (ι a) m = ι (gradedPart Aᵢ a m) := by
  classical
  have hsum : ι a = ∑ i ∈ (DirectSum.decompose Aᵢ a).support, ι (gradedPart Aᵢ a i) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose Aᵢ a]
    rw [map_sum]
    rfl
  by_cases hm : m ∈ (DirectSum.decompose Aᵢ a).support
  · rw [hsum, gradedPart_sum_homogeneous Cᵢ _ (fun i => ι (gradedPart Aᵢ a i))
      (fun i => hgrade i _ (gradedPart_mem Aᵢ a i)) m hm]
  · rw [gradedPart_eq_zero_of_decompose_eq_zero Aᵢ (DFinsupp.notMem_support_iff.mp hm),
      map_zero, hsum, gradedPart_sum]
    exact Finset.sum_eq_zero fun i hi =>
      gradedPart_of_mem_ne Cᵢ (hgrade i _ (gradedPart_mem Aᵢ a i)) fun h => hm (h ▸ hi)

include hgrade in
/-- An injective degree-preserving algebra map reflects homogeneity: if `ι a` lies in
degree `m`, so does `a`. -/
public theorem mem_grade_of_map_mem_grade (hinj : Function.Injective ι) (m : ℕ) {a : A}
    (ha : ι a ∈ Cᵢ m) : a ∈ Aᵢ m := by
  classical
  have hzero : ∀ i, i ≠ m → gradedPart Aᵢ a i = 0 := by
    intro i hi
    refine hinj ?_
    rw [map_zero, ← gradedPart_algHom Aᵢ Cᵢ ι hgrade a i]
    exact gradedPart_of_mem_ne Cᵢ ha (Ne.symm hi)
  rw [← DirectSum.sum_support_decompose Aᵢ a]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i = m
  · subst hi
    exact gradedPart_mem Aᵢ a i
  · rw [show ((DirectSum.decompose Aᵢ a i : Aᵢ i) : A) = gradedPart Aᵢ a i from rfl, hzero i hi]
    exact Submodule.zero_mem _

include hgrade in
/-- An injective degree-preserving algebra map reflects membership in the positive even
part. -/
public theorem mem_positiveEvenPart_of_map_mem_positiveEvenPart
    (hinj : Function.Injective ι) {a : A} (ha : ι a ∈ positiveEvenPart Cᵢ) :
    a ∈ positiveEvenPart Aᵢ := by
  classical
  have hzero : ∀ i, (¬ ∃ k : ℕ, i = 2 * (k + 1)) → gradedPart Aᵢ a i = 0 := by
    intro i hi
    refine hinj ?_
    rw [map_zero, ← gradedPart_algHom Aᵢ Cᵢ ι hgrade a i]
    exact gradedPart_eq_zero_of_mem_positiveEvenPart Cᵢ ha hi
  rw [← DirectSum.sum_support_decompose Aᵢ a]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : ∃ k : ℕ, i = 2 * (k + 1)
  · obtain ⟨k, hk⟩ := hi
    exact Submodule.mem_iSup_of_mem k (hk ▸ gradedPart_mem Aᵢ a i)
  · rw [show ((DirectSum.decompose Aᵢ a i : Aᵢ i) : A) = gradedPart Aᵢ a i from rfl, hzero i hi]
    exact Submodule.zero_mem _

end Reflect


section StageGraded

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ}
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ}
  {ι : A →ₐ[R] C} {T : J → C} {d : ℕ} {hd : 0 < d}

/-- In a set-variable extension, every divided power `δ.dpow n (T j)` of a variable is
homogeneous of some degree. -/
public theorem IsSetVariableExtension.exists_mem_grade_dpow_generator
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd) (j : J) (n : ℕ) :
    ∃ m : ℕ, δ.dpow n (T j) ∈ Cᵢ m := by
  by_cases hpos : T j ∈ positiveEvenPart Cᵢ
  · by_cases hn : n = 0
    · subst hn
      exact ⟨0, by rw [δ.dpow_zero hpos]; exact SetLike.one_mem_graded Cᵢ⟩
    · rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ (hC.generator_mem j) hpos with
        hz | ⟨k, hk⟩
      · refine ⟨0, ?_⟩
        rw [hz, δ.dpow_zero_eq_zero hn]
        exact Submodule.zero_mem _
      · exact ⟨2 * n * (k + 1), δ.dpow_mem_grade hn hpos (hk ▸ hC.generator_mem j)⟩
  · exact ⟨0, by rw [δ.dpow_null hpos]; exact Submodule.zero_mem _⟩

/-- A finite variable stage of a set-variable extension contains every homogeneous component
of each of its elements. -/
public theorem IsSetVariableExtension.gradedPart_mem_finiteVariableStage
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd) (S : Finset J) {x : C}
    (hx : x ∈ finiteVariableStage δ ι T S) (m : ℕ) :
    gradedPart Cᵢ x m ∈ finiteVariableStage δ ι T S := by
  have key : ∀ y ∈ finiteVariableStage δ ι T S, ∀ m,
      gradedPart Cᵢ y m ∈ finiteVariableStage δ ι T S := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
        rcases hz with ⟨a, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩
        · intro m
          rw [gradedPart_algHom Aᵢ Cᵢ ι hC.coefficient_grade a m]
          exact mem_finiteVariableStage_coefficient δ ι T S _
        · exact gradedPart_mem_subring_of_mem_grade Cᵢ (hC.generator_mem j) _
            (mem_finiteVariableStage_generator δ ι T hj)
        · obtain ⟨m₀, hm₀⟩ := hC.exists_mem_grade_dpow_generator j n
          exact gradedPart_mem_subring_of_mem_grade Cᵢ hm₀ _
            (mem_finiteVariableStage_dpow_generator δ ι T hj n)
    | zero => intro m; rw [gradedPart_zero]; exact Subring.zero_mem _
    | one =>
        exact gradedPart_mem_subring_of_mem_grade Cᵢ (SetLike.one_mem_graded Cᵢ) _
          (Subring.one_mem _)
    | add a b _ _ iha ihb =>
        intro m
        rw [gradedPart_add]
        exact Subring.add_mem _ (iha m) (ihb m)
    | neg a _ iha =>
        intro m
        rw [gradedPart_neg]
        exact Subring.neg_mem _ (iha m)
    | mul a b _ _ iha ihb =>
        intro m
        obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ a
        obtain ⟨t, ht⟩ := exists_gradedPart_decomposition Cᵢ b
        have hkey := gradedPart_mul_sum Cᵢ (s := s) (t := t)
          (gradedPart Cᵢ a) (gradedPart Cᵢ b) m
        rw [← hs, ← ht] at hkey
        rw [hkey]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun k _ => ?_
        by_cases hik : i + k = m
        · rw [gradedPart_mul_homogeneous Cᵢ (gradedPart_mem Cᵢ a i)
            (gradedPart_mem Cᵢ b k) hik]
          exact mul_mem (iha i) (ihb k)
        · rw [gradedPart_mul_homogeneous_of_ne Cᵢ (gradedPart_mem Cᵢ a i)
            (gradedPart_mem Cᵢ b k) hik]
          exact Subring.zero_mem _
  exact key x hx m

end StageGraded


section StageUnique

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ}
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ}
  {ι : A →ₐ[R] C} {T : J → C} {d : ℕ} {hd : 0 < d}

private theorem addHom_eq_zero_of_graded_leibniz
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd) (S : Finset J)
    (E : finiteVariableStage δ ι T S →+ C)
    (hzero : ∀ x : finiteVariableStage δ ι T S, (x : C) ∈ Cᵢ 0 → E x = 0)
    (hleib : ∀ (i k : ℕ) (x y : finiteVariableStage δ ι T S),
      (x : C) ∈ Cᵢ i → (y : C) ∈ Cᵢ k →
      E (x * y) = E x * (y : C) + (-1 : R) ^ i • ((x : C) * E y))
    (hcoeff : ∀ a : A, E ⟨ι a, mem_finiteVariableStage_coefficient δ ι T S a⟩ = 0)
    (hgen : ∀ (j : J) (hj : j ∈ S), E ⟨T j, mem_finiteVariableStage_generator δ ι T hj⟩ = 0)
    (hdp : ∀ (j : J) (hj : j ∈ S) (n : ℕ),
      E ⟨δ.dpow n (T j), mem_finiteVariableStage_dpow_generator δ ι T hj n⟩ = 0) :
    E = 0 := by
  classical
  have hhom : ∀ (x : C) (i : ℕ), x ∈ Cᵢ i → ∀ hx : x ∈ finiteVariableStage δ ι T S,
      E ⟨x, hx⟩ = 0 → ∀ (m : ℕ) (h : gradedPart Cᵢ x m ∈ finiteVariableStage δ ι T S),
      E ⟨gradedPart Cᵢ x m, h⟩ = 0 := by
    intro x i hxi hx hEx m h
    by_cases hm : i = m
    · subst hm
      rw [show (⟨gradedPart Cᵢ x i, h⟩ : finiteVariableStage δ ι T S) = ⟨x, hx⟩ from
        Subtype.ext (gradedPart_of_mem_same Cᵢ hxi)]
      exact hEx
    · rw [show (⟨gradedPart Cᵢ x m, h⟩ : finiteVariableStage δ ι T S) = 0 from
        Subtype.ext (gradedPart_of_mem_ne Cᵢ hxi hm), map_zero]
  have key : ∀ y ∈ finiteVariableStage δ ι T S, ∀ (m : ℕ)
      (h : gradedPart Cᵢ y m ∈ finiteVariableStage δ ι T S),
      E ⟨gradedPart Cᵢ y m, h⟩ = 0 := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
        rcases hz with ⟨a, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩
        · intro m h
          rw [show (⟨gradedPart Cᵢ (ι a) m, h⟩ : finiteVariableStage δ ι T S) =
            ⟨ι (gradedPart Aᵢ a m), mem_finiteVariableStage_coefficient δ ι T S _⟩ from
            Subtype.ext (gradedPart_algHom Aᵢ Cᵢ ι hC.coefficient_grade a m)]
          exact hcoeff _
        · exact hhom (T j) d (hC.generator_mem j)
            (mem_finiteVariableStage_generator δ ι T hj) (hgen j hj)
        · obtain ⟨m₀, hm₀⟩ := hC.exists_mem_grade_dpow_generator j n
          exact hhom (δ.dpow n (T j)) m₀ hm₀
            (mem_finiteVariableStage_dpow_generator δ ι T hj n) (hdp j hj n)
    | zero =>
        intro m h
        rw [show (⟨gradedPart Cᵢ (0 : C) m, h⟩ : finiteVariableStage δ ι T S) = 0 from
          Subtype.ext (gradedPart_zero Cᵢ m), map_zero]
    | one =>
        refine hhom 1 0 (SetLike.one_mem_graded Cᵢ) (Subring.one_mem _) ?_
        exact hzero 1 (SetLike.one_mem_graded Cᵢ)
    | add a b ha hb iha ihb =>
        intro m h
        rw [show (⟨gradedPart Cᵢ (a + b) m, h⟩ : finiteVariableStage δ ι T S) =
          ⟨gradedPart Cᵢ a m, hC.gradedPart_mem_finiteVariableStage S ha m⟩ +
          ⟨gradedPart Cᵢ b m, hC.gradedPart_mem_finiteVariableStage S hb m⟩ from
          Subtype.ext (gradedPart_add Cᵢ a b m), map_add, iha m _, ihb m _, add_zero]
    | neg a ha iha =>
        intro m h
        rw [show (⟨gradedPart Cᵢ (-a) m, h⟩ : finiteVariableStage δ ι T S) =
          -⟨gradedPart Cᵢ a m, hC.gradedPart_mem_finiteVariableStage S ha m⟩ from
          Subtype.ext (gradedPart_neg Cᵢ a m), map_neg, iha m _, neg_zero]
    | mul a b ha hb iha ihb =>
        intro m h
        obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ a
        obtain ⟨t, ht⟩ := exists_gradedPart_decomposition Cᵢ b
        have hkey := gradedPart_mul_sum Cᵢ (s := s) (t := t)
          (gradedPart Cᵢ a) (gradedPart Cᵢ b) m
        rw [← hs, ← ht] at hkey
        have hma : ∀ i, gradedPart Cᵢ a i ∈ finiteVariableStage δ ι T S := fun i =>
          hC.gradedPart_mem_finiteVariableStage S ha i
        have hmb : ∀ k, gradedPart Cᵢ b k ∈ finiteVariableStage δ ι T S := fun k =>
          hC.gradedPart_mem_finiteVariableStage S hb k
        have hterm : ∀ i k, gradedPart Cᵢ (gradedPart Cᵢ a i * gradedPart Cᵢ b k) m ∈
            finiteVariableStage δ ι T S := fun i k =>
          hC.gradedPart_mem_finiteVariableStage S (mul_mem (hma i) (hmb k)) m
        have hzeroterm : ∀ i k : ℕ,
            E (⟨gradedPart Cᵢ (gradedPart Cᵢ a i * gradedPart Cᵢ b k) m,
              hterm i k⟩ : finiteVariableStage δ ι T S) = 0 := by
          intro i k
          by_cases hik : i + k = m
          · rw [show (⟨gradedPart Cᵢ (gradedPart Cᵢ a i * gradedPart Cᵢ b k) m,
                hterm i k⟩ : finiteVariableStage δ ι T S) =
                (⟨gradedPart Cᵢ a i, hma i⟩ : finiteVariableStage δ ι T S) *
                ⟨gradedPart Cᵢ b k, hmb k⟩ from Subtype.ext
                (gradedPart_mul_homogeneous Cᵢ (gradedPart_mem Cᵢ a i)
                  (gradedPart_mem Cᵢ b k) hik),
              hleib i k _ _ (gradedPart_mem Cᵢ a i) (gradedPart_mem Cᵢ b k),
              iha i (hma i), ihb k (hmb k), zero_mul, mul_zero, smul_zero, add_zero]
          · rw [show (⟨gradedPart Cᵢ (gradedPart Cᵢ a i * gradedPart Cᵢ b k) m,
              hterm i k⟩ : finiteVariableStage δ ι T S) = 0 from Subtype.ext
              (gradedPart_mul_homogeneous_of_ne Cᵢ (gradedPart_mem Cᵢ a i)
                (gradedPart_mem Cᵢ b k) hik), map_zero]
        rw [show (⟨gradedPart Cᵢ (a * b) m, h⟩ : finiteVariableStage δ ι T S) =
            ∑ p ∈ s ×ˢ t, (⟨gradedPart Cᵢ (gradedPart Cᵢ a p.1 * gradedPart Cᵢ b p.2) m,
              hterm p.1 p.2⟩ : finiteVariableStage δ ι T S) from ?_, map_sum]
        · exact Finset.sum_eq_zero fun p _ => hzeroterm p.1 p.2
        · refine Subtype.ext ?_
          rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_product]
          exact hkey
  ext x
  obtain ⟨x, hx⟩ := x
  obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ x
  have hmem : ∀ m, gradedPart Cᵢ x m ∈ finiteVariableStage δ ι T S := fun m =>
    hC.gradedPart_mem_finiteVariableStage S hx m
  have hxsum : (⟨x, hx⟩ : finiteVariableStage δ ι T S) =
      ∑ m ∈ s, (⟨gradedPart Cᵢ x m, hmem m⟩ : finiteVariableStage δ ι T S) := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hs
  rw [AddMonoidHom.zero_apply, hxsum, map_sum]
  exact Finset.sum_eq_zero fun m _ => key x hx m (hmem m)

end StageUnique


section Sign
variable {R : Type u} [CommRing R]

/-- Scalar multiplication by `(-1 : R) ^ i` is left multiplication by `(-1) ^ i`. -/
public theorem neg_one_pow_smul_eq_mul {M : Type v} [Ring M] [Algebra R M] (i : ℕ) (z : M) :
    (-1 : R) ^ i • z = (-1 : M) ^ i * z := by
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

/-- The coercion from a subring commutes with scalar multiplication by `(-1 : R) ^ i`. -/
public theorem coe_neg_one_pow_smul {C : Type v} [Ring C] [Algebra R C] {P : Subring C}
    [Algebra R P] (i : ℕ) (z : P) :
    (((-1 : R) ^ i • z : P) : C) = (-1 : R) ^ i • (z : C) := by
  rw [neg_one_pow_smul_eq_mul (R := R) i z, neg_one_pow_smul_eq_mul (R := R) i (z : C)]
  push_cast
  rfl

end Sign

section SubringMk
variable {C : Type z} [Ring C]

private theorem mk_coe_zero {P Q : Subring C} (h : P ≤ Q) :
    (⟨((0 : P) : C), h (0 : P).2⟩ : Q) = 0 := rfl

private theorem mk_coe_add {P Q : Subring C} (h : P ≤ Q) (y z : P) :
    (⟨((y + z : P) : C), h (y + z).2⟩ : Q) = ⟨(y : C), h y.2⟩ + ⟨(z : C), h z.2⟩ := rfl

private theorem mk_coe_mul {P Q : Subring C} (h : P ≤ Q) (y z : P) :
    (⟨((y * z : P) : C), h (y * z).2⟩ : Q) = ⟨(y : C), h y.2⟩ * ⟨(z : C), h z.2⟩ := rfl

end SubringMk

section StageDerivation

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ}
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]

/-- The clauses carried through the stagewise construction of a derivation on a set-variable
extension: the prescribed values on the coefficients and the variables, vanishing in degree zero,
degree lowering, the signed Leibniz rule, and the divided power formula. The map is valued in the
ambient algebra, so that stages may be compared without transporting algebra structures. -/
private structure IsStageDerivation {δ : DividedPowerStructure Cᵢ} (ι : A →ₐ[R] C) (T : J → C)
    (dA : A →ₗ[R] A) (ev : J → A) (S : Finset J)
    (D : finiteVariableStage δ ι T S →+ C) : Prop where
  map_coeff : ∀ a : A, D ⟨ι a, mem_finiteVariableStage_coefficient δ ι T S a⟩ = ι (dA a)
  map_generator : ∀ (j : J) (hj : j ∈ S),
    D ⟨T j, mem_finiteVariableStage_generator δ ι T hj⟩ = ι (ev j)
  grade_zero : ∀ x : finiteVariableStage δ ι T S, (x : C) ∈ Cᵢ 0 → D x = 0
  grade_mem : ∀ (n : ℕ) (x : finiteVariableStage δ ι T S), (x : C) ∈ Cᵢ (n + 1) → D x ∈ Cᵢ n
  leibniz : ∀ (i k : ℕ) (x y : finiteVariableStage δ ι T S),
    (x : C) ∈ Cᵢ i → (y : C) ∈ Cᵢ k →
    D (x * y) = D x * (y : C) + (-1 : R) ^ i • ((x : C) * D y)
  map_dpow : ∀ (n : ℕ) (x : finiteVariableStage δ ι T S), n ≠ 0 →
    (x : C) ∈ positiveEvenPart Cᵢ →
    ∀ hmem : δ.dpow n (x : C) ∈ finiteVariableStage δ ι T S,
      D ⟨δ.dpow n (x : C), hmem⟩ = D x * δ.dpow (n - 1) (x : C)

variable {δ : DividedPowerStructure Cᵢ} {ι : A →ₐ[R] C} {T : J → C} {d : ℕ} {hd : 0 < d}
  {dA : A →ₗ[R] A} {ev : J → A}

/-- An endomorphism of a finite variable stage, read as a map into the ambient algebra. -/
private def stageCoe {S : Finset J}
    (D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S) :
    finiteVariableStage δ ι T S →+ C :=
  AddMonoidHom.mk' (fun x => (D x : C)) fun x y => by rw [map_add, Subring.coe_add]

private theorem stageCoe_apply {S : Finset J}
    (D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S)
    (x : finiteVariableStage δ ι T S) : stageCoe D x = (D x : C) := rfl

/-- The value of a stage derivation on a divided power of a variable is forced by its value on
the variable. -/
private theorem IsStageDerivation.dpow_generator_eq {S U : Finset J} (hSU : S ⊆ U)
    {D₁ : finiteVariableStage δ ι T S →+ C} {D₂ : finiteVariableStage δ ι T U →+ C}
    (h₁ : IsStageDerivation ι T dA ev S D₁) (h₂ : IsStageDerivation ι T dA ev U D₂)
    (j : J) (hj : j ∈ S) (n : ℕ) :
    D₁ ⟨δ.dpow n (T j), mem_finiteVariableStage_dpow_generator δ ι T hj n⟩ =
      D₂ ⟨δ.dpow n (T j), mem_finiteVariableStage_dpow_generator δ ι T (hSU hj) n⟩ := by
  by_cases hpos : T j ∈ positiveEvenPart Cᵢ
  · by_cases hn : n = 0
    · subst hn
      rw [show (⟨δ.dpow 0 (T j), mem_finiteVariableStage_dpow_generator δ ι T hj 0⟩ :
            finiteVariableStage δ ι T S) = 1 from Subtype.ext (δ.dpow_zero hpos),
        show (⟨δ.dpow 0 (T j), mem_finiteVariableStage_dpow_generator δ ι T (hSU hj) 0⟩ :
            finiteVariableStage δ ι T U) = 1 from Subtype.ext (δ.dpow_zero hpos),
        h₁.grade_zero 1 (SetLike.one_mem_graded Cᵢ),
        h₂.grade_zero 1 (SetLike.one_mem_graded Cᵢ)]
    · rw [h₁.map_dpow n ⟨T j, mem_finiteVariableStage_generator δ ι T hj⟩ hn hpos _,
        h₂.map_dpow n ⟨T j, mem_finiteVariableStage_generator δ ι T (hSU hj)⟩ hn hpos _,
        h₁.map_generator j hj, h₂.map_generator j (hSU hj)]
  · rw [show (⟨δ.dpow n (T j), mem_finiteVariableStage_dpow_generator δ ι T hj n⟩ :
          finiteVariableStage δ ι T S) = 0 from Subtype.ext (δ.dpow_null hpos),
      show (⟨δ.dpow n (T j), mem_finiteVariableStage_dpow_generator δ ι T (hSU hj) n⟩ :
          finiteVariableStage δ ι T U) = 0 from Subtype.ext (δ.dpow_null hpos),
      map_zero, map_zero]

/-- Derivations of nested finite variable stages carrying the same prescribed data agree
wherever both are defined. -/
private theorem IsStageDerivation.eq_of_subset
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd) {S U : Finset J} (hSU : S ⊆ U)
    {D₁ : finiteVariableStage δ ι T S →+ C} {D₂ : finiteVariableStage δ ι T U →+ C}
    (h₁ : IsStageDerivation ι T dA ev S D₁) (h₂ : IsStageDerivation ι T dA ev U D₂)
    (x : finiteVariableStage δ ι T S) :
    D₁ x = D₂ ⟨(x : C), finiteVariableStage_le_of_subset δ ι T hSU x.2⟩ := by
  set hle := finiteVariableStage_le_of_subset δ ι T hSU with hledef
  have hadd : ∀ y z : finiteVariableStage δ ι T S,
      D₁ (y + z) - D₂ ⟨((y + z : finiteVariableStage δ ι T S) : C), hle (y + z).2⟩ =
        (D₁ y - D₂ ⟨(y : C), hle y.2⟩) + (D₁ z - D₂ ⟨(z : C), hle z.2⟩) := by
    intro y z
    rw [mk_coe_add hle, map_add, map_add]
    abel
  have hsub : AddMonoidHom.mk'
      (fun y : finiteVariableStage δ ι T S => D₁ y - D₂ ⟨(y : C), hle y.2⟩) hadd = 0 := by
    refine addHom_eq_zero_of_graded_leibniz hC S _ ?_ ?_ ?_ ?_ ?_
    · intro y hy
      change D₁ y - D₂ ⟨(y : C), hle y.2⟩ = 0
      rw [h₁.grade_zero y hy, h₂.grade_zero _ hy, sub_zero]
    · intro i k y z hy hz
      change D₁ (y * z) - D₂ ⟨((y * z : finiteVariableStage δ ι T S) : C), hle (y * z).2⟩ =
        (D₁ y - D₂ ⟨(y : C), hle y.2⟩) * (z : C) +
          (-1 : R) ^ i • ((y : C) * (D₁ z - D₂ ⟨(z : C), hle z.2⟩))
      rw [mk_coe_mul hle, h₁.leibniz i k y z hy hz,
        h₂.leibniz i k ⟨(y : C), hle y.2⟩ ⟨(z : C), hle z.2⟩ hy hz, sub_mul, mul_sub, smul_sub]
      abel
    · intro a
      change D₁ ⟨ι a, _⟩ - D₂ ⟨_, _⟩ = 0
      rw [h₁.map_coeff a, h₂.map_coeff a, sub_self]
    · intro j hj
      change D₁ ⟨T j, _⟩ - D₂ ⟨_, _⟩ = 0
      rw [h₁.map_generator j hj, h₂.map_generator j (hSU hj), sub_self]
    · intro j hj n
      change D₁ ⟨δ.dpow n (T j), _⟩ - D₂ ⟨_, _⟩ = 0
      rw [h₁.dpow_generator_eq hSU h₂ j hj n, sub_self]
  have := DFunLike.congr_fun hsub x
  rw [AddMonoidHom.zero_apply] at this
  exact sub_eq_zero.mp (by
    change D₁ x - D₂ ⟨(x : C), hle x.2⟩ = 0
    exact this)

end StageDerivation


section StageBase

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ}
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ} {ι : A →ₐ[R] C} {T : J → C} {d : ℕ} {hd : 0 < d}
  {dA : A →ₗ[R] A} {ev : J → A}

/-- The empty stage is the image of the coefficient algebra, so the prescribed derivation of the
coefficients transports to it. -/
private theorem exists_isStageDerivation_empty
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd)
    [IsGradedDerivation Aᵢ dA] [IsCompatibleWithDifferential γ dA] :
    ∃ D : finiteVariableStage δ ι T (∅ : Finset J) →+
        finiteVariableStage δ ι T (∅ : Finset J),
      IsStageDerivation ι T dA ev (∅ : Finset J) (stageCoe D) := by
  have hsurj : ∀ x : C, x ∈ finiteVariableStage δ ι T (∅ : Finset J) → ∃ p : A, ι p = x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem y hy =>
        rcases hy with ⟨p, rfl⟩ | ⟨c, hc, -⟩
        · exact ⟨p, rfl⟩
        · exact absurd hc (Finset.notMem_empty c)
    | zero => exact ⟨0, map_zero ι⟩
    | one => exact ⟨1, map_one ι⟩
    | add a b _ _ iha ihb =>
        obtain ⟨p, hp⟩ := iha
        obtain ⟨q, hq⟩ := ihb
        exact ⟨p + q, by rw [map_add, hp, hq]⟩
    | neg a _ iha =>
        obtain ⟨p, hp⟩ := iha
        exact ⟨-p, by rw [map_neg, hp]⟩
    | mul a b _ _ iha ihb =>
        obtain ⟨p, hp⟩ := iha
        obtain ⟨q, hq⟩ := ihb
        exact ⟨p * q, by rw [map_mul, hp, hq]⟩
  let coeffHom : A →+* finiteVariableStage δ ι T (∅ : Finset J) :=
    { toFun := fun p => ⟨ι p, mem_finiteVariableStage_coefficient δ ι T ∅ p⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun p q => Subtype.ext (map_mul ι p q)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' := fun p q => Subtype.ext (map_add ι p q) }
  have hbij : Function.Bijective coeffHom := by
    refine ⟨fun p q hpq => hC.coefficient_injective (congrArg Subtype.val hpq), ?_⟩
    intro x
    obtain ⟨p, hp⟩ := hsurj x.1 x.2
    exact ⟨p, Subtype.ext hp⟩
  let coeffEquiv := RingEquiv.ofBijective coeffHom hbij
  have hce : ∀ p : A, coeffEquiv p =
      ⟨ι p, mem_finiteVariableStage_coefficient δ ι T ∅ p⟩ := fun _ => rfl
  have hcev : ∀ p : A, ((coeffEquiv p : finiteVariableStage δ ι T (∅ : Finset J)) : C) = ι p :=
    fun p => congrArg Subtype.val (hce p)
  have hsymm : ∀ x : finiteVariableStage δ ι T (∅ : Finset J),
      ι (coeffEquiv.symm x) = (x : C) := by
    intro x
    rw [← hcev (coeffEquiv.symm x), coeffEquiv.apply_symm_apply]
  have hsymmcoeff : ∀ p : A,
      coeffEquiv.symm ⟨ι p, mem_finiteVariableStage_coefficient δ ι T ∅ p⟩ = p := by
    intro p
    rw [← hce p, coeffEquiv.symm_apply_apply]
  refine ⟨AddMonoidHom.mk' (fun x => coeffEquiv (dA (coeffEquiv.symm x)))
    (fun x y => by rw [map_add, map_add, map_add]), ?_⟩
  have hD : ∀ x : finiteVariableStage δ ι T (∅ : Finset J),
      (stageCoe (AddMonoidHom.mk' (fun x => coeffEquiv (dA (coeffEquiv.symm x)))
        (fun x y => by rw [map_add, map_add, map_add]) :
          finiteVariableStage δ ι T (∅ : Finset J) →+
            finiteVariableStage δ ι T (∅ : Finset J))) x =
      ι (dA (coeffEquiv.symm x)) := by
    intro x
    rw [stageCoe_apply]
    exact hcev (dA (coeffEquiv.symm x))
  have hgrade : ∀ (m : ℕ) (x : finiteVariableStage δ ι T (∅ : Finset J)), (x : C) ∈ Cᵢ m →
      coeffEquiv.symm x ∈ Aᵢ m := by
    intro m x hx
    exact mem_grade_of_map_mem_grade Aᵢ Cᵢ ι hC.coefficient_grade hC.coefficient_injective m
      (by rw [hsymm]; exact hx)
  refine ⟨?_, fun j hj => absurd hj (Finset.notMem_empty j), ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hD, hsymmcoeff a]
  · intro x hx
    rw [hD, IsGradedDerivation.d_grade_zero (𝒜 := Aᵢ) (d := dA) (hgrade 0 x hx), map_zero]
  · intro n x hx
    rw [hD]
    exact hC.coefficient_grade n _
      (IsGradedDerivation.d_mem (𝒜 := Aᵢ) (d := dA) (hgrade (n + 1) x hx))
  · intro i k x y hx hy
    rw [hD, hD, hD, map_mul coeffEquiv.symm,
      IsGradedDerivation.leibniz (𝒜 := Aᵢ) (d := dA) (hgrade i x hx) (hgrade k y hy),
      map_add, map_mul, map_smul, map_mul, hsymm, hsymm]
  · intro n x hn hx hmem
    have hp : coeffEquiv.symm x ∈ positiveEvenPart Aᵢ :=
      mem_positiveEvenPart_of_map_mem_positiveEvenPart Aᵢ Cᵢ ι hC.coefficient_grade
        hC.coefficient_injective (by rw [hsymm]; exact hx)
    have hdn : ∀ m : ℕ, δ.dpow m (x : C) = ι (γ.dpow m (coeffEquiv.symm x)) := by
      intro m
      rw [← hsymm x]
      exact hC.coefficient_dpow m _ hp
    have hel : (⟨δ.dpow n (x : C), hmem⟩ : finiteVariableStage δ ι T (∅ : Finset J)) =
        coeffEquiv (γ.dpow n (coeffEquiv.symm x)) := by
      refine Subtype.ext ?_
      rw [hcev (γ.dpow n (coeffEquiv.symm x))]
      exact hdn n
    rw [hel, hD, coeffEquiv.symm_apply_apply,
      IsCompatibleWithDifferential.d_dpow (γ := γ) (d := dA) hn hp, map_mul, hdn (n - 1), hD]

end StageBase


section OneVariableStep

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ} {ι : A →ₐ[R] C} {T : J → C}
  {dA : A →ₗ[R] A} {ev : J → A}

/-- One step of the stagewise construction, stated for an abstract one-variable divided power
extension of the smaller stage: a graded derivation of that extension realising the prescribed
values transports along the identification of the extension with the larger stage. Both the odd
and the even case of Tag 0F4I's `successor` clause are instances of this. -/
private theorem exists_isStageDerivation_of_oneVariableExtension
    {S U : Finset J} {j : J} (hU : ∀ a : J, a ∈ U ↔ a = j ∨ a ∈ S)
    {D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S}
    (hD : IsStageDerivation ι T dA ev S (stageCoe D))
    {E : Type*} [Ring E] [Algebra R E] {Eᵢ : ℕ → Submodule R E} [GradedAlgebra Eᵢ]
    [IsStrictlyGradedComm Eᵢ] {δE : DividedPowerStructure Eᵢ}
    (incl : finiteVariableStage δ ι T S →+* E) (gen : E)
    (dE : E →ₗ[R] E) [IsGradedDerivation Eᵢ dE] [IsCompatibleWithDifferential δE dE]
    (hincl : ∀ b : finiteVariableStage δ ι T S, dE (incl b) = incl (D b))
    (hgen : dE gen = incl ⟨ι (ev j), mem_finiteVariableStage_coefficient δ ι T S (ev j)⟩)
    (e : E ≃+* finiteVariableStage δ ι T U)
    (he1 : ∀ b : finiteVariableStage δ ι T S,
      ((e (incl b) : finiteVariableStage δ ι T U) : C) = (b : C))
    (he2 : ((e gen : finiteVariableStage δ ι T U) : C) = T j)
    (he3 : ∀ (m : ℕ) (x : E), x ∈ Eᵢ m ↔ ((e x : finiteVariableStage δ ι T U) : C) ∈ Cᵢ m)
    (he4 : ∀ (n : ℕ) (x : E), x ∈ positiveEvenPart Eᵢ →
      δ.dpow n ((e x : finiteVariableStage δ ι T U) : C) =
        ((e (δE.dpow n x) : finiteVariableStage δ ι T U) : C)) :
    ∃ D' : finiteVariableStage δ ι T U →+ finiteVariableStage δ ι T U,
      IsStageDerivation ι T dA ev U (stageCoe D') := by
  set D' : finiteVariableStage δ ι T U →+ finiteVariableStage δ ι T U :=
    AddMonoidHom.mk' (fun x => e (dE (e.symm x)))
      (fun x y => by rw [map_add, map_add, map_add]) with hD'def
  have hcoe : ∀ x : finiteVariableStage δ ι T U,
      stageCoe D' x = ((e (dE (e.symm x)) : finiteVariableStage δ ι T U) : C) := by
    intro x
    rw [stageCoe_apply, hD'def]
    rfl
  have hmkS : ∀ (y : C) (hyS : y ∈ finiteVariableStage δ ι T S)
      (hyU : y ∈ finiteVariableStage δ ι T U),
      e.symm ⟨y, hyU⟩ = incl ⟨y, hyS⟩ := by
    intro y hyS hyU
    rw [show (⟨y, hyU⟩ : finiteVariableStage δ ι T U) = e (incl ⟨y, hyS⟩) from
      Subtype.ext (he1 ⟨y, hyS⟩).symm, e.symm_apply_apply]
  have hext : ∀ (y : C) (hyS : y ∈ finiteVariableStage δ ι T S)
      (hyU : y ∈ finiteVariableStage δ ι T U),
      stageCoe D' ⟨y, hyU⟩ = stageCoe D ⟨y, hyS⟩ := by
    intro y hyS hyU
    rw [hcoe, hmkS y hyS hyU, hincl ⟨y, hyS⟩, he1 (D ⟨y, hyS⟩), stageCoe_apply]
  have hgrade : ∀ (m : ℕ) (x : finiteVariableStage δ ι T U), (x : C) ∈ Cᵢ m →
      e.symm x ∈ Eᵢ m := by
    intro m x hx
    exact (he3 m (e.symm x)).mpr (by rw [e.apply_symm_apply]; exact hx)
  refine ⟨D', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hext (ι a) (mem_finiteVariableStage_coefficient δ ι T S a)
      (mem_finiteVariableStage_coefficient δ ι T U a)).trans (hD.map_coeff a)
  · intro j' hj'
    rcases (hU j').mp hj' with rfl | hj'S
    · rw [hcoe, show e.symm ⟨T j', mem_finiteVariableStage_generator δ ι T hj'⟩ = gen from by
        rw [show (⟨T j', mem_finiteVariableStage_generator δ ι T hj'⟩ :
          finiteVariableStage δ ι T U) = e gen from Subtype.ext he2.symm, e.symm_apply_apply],
        hgen, he1]
    · exact (hext (T j') (mem_finiteVariableStage_generator δ ι T hj'S)
        (mem_finiteVariableStage_generator δ ι T hj')).trans (hD.map_generator j' hj'S)
  · intro x hx
    rw [hcoe, show dE (e.symm x) = 0 from
      IsGradedDerivation.d_grade_zero (𝒜 := Eᵢ) (d := dE) (hgrade 0 x hx), map_zero]
    exact Subring.coe_zero _
  · intro n x hx
    rw [hcoe]
    exact (he3 n (dE (e.symm x))).mp
      (IsGradedDerivation.d_mem (𝒜 := Eᵢ) (d := dE) (hgrade (n + 1) x hx))
  · intro i k x y hx hy
    rw [hcoe, hcoe, hcoe, map_mul e.symm,
      IsGradedDerivation.leibniz (𝒜 := Eᵢ) (d := dE) (hgrade i x hx) (hgrade k y hy),
      neg_one_pow_smul_eq_mul (R := R), map_add, map_mul, map_mul, map_pow, map_neg, map_one]
    push_cast
    rw [← neg_one_pow_smul_eq_mul (R := R), map_mul e, Subring.coe_mul]
    simp only [RingEquiv.apply_symm_apply]
  · intro n x hn hx hmem
    have hX : e.symm x ∈ positiveEvenPart Eᵢ :=
      mem_positiveEvenPart_symm_of_ringEquiv Cᵢ Eᵢ (finiteVariableStage δ ι T U) e he3 hx
    have hform := he4 n (e.symm x) hX
    rw [e.apply_symm_apply] at hform
    have hform' := he4 (n - 1) (e.symm x) hX
    rw [e.apply_symm_apply] at hform'
    rw [show (⟨δ.dpow n (x : C), hmem⟩ : finiteVariableStage δ ι T U) =
        e (δE.dpow n (e.symm x)) from Subtype.ext hform, hcoe, e.symm_apply_apply,
      IsCompatibleWithDifferential.d_dpow (γ := δE) (d := dE) hn hX, map_mul, Subring.coe_mul,
      hcoe, ← hform']

end OneVariableStep


section StageGradedHyps

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ} {ι : A →ₐ[R] C} {T : J → C}
  {dA : A →ₗ[R] A} {ev : J → A} {S : Finset J}
  [Algebra R (finiteVariableStage δ ι T S)]
  (Sᵢ : ℕ → Submodule R (finiteVariableStage δ ι T S)) [GradedAlgebra Sᵢ]
  [IsStrictlyGradedComm Sᵢ]
  (hSmem : ∀ (m : ℕ) (b : finiteVariableStage δ ι T S), b ∈ Sᵢ m ↔ (b : C) ∈ Cᵢ m)

omit [GradedAlgebra Sᵢ] [IsStrictlyGradedComm Sᵢ] in
include hSmem in
/-- A grading of a finite variable stage which matches the ambient grading reflects the positive
even part. -/
private theorem mem_positiveEvenPart_of_mem_stage (b : finiteVariableStage δ ι T S)
    (hb : b ∈ positiveEvenPart Sᵢ) : (b : C) ∈ positiveEvenPart Cᵢ := by
  induction hb using Submodule.iSup_induction' with
  | mem c b hbm => exact Submodule.mem_iSup_of_mem c ((hSmem _ b).mp hbm)
  | zero => simp
  | add b b' _ _ ih ih' => simpa using Submodule.add_mem _ ih ih'

omit [GradedAlgebra Sᵢ] [IsStrictlyGradedComm Sᵢ] in
include hSmem in
/-- A stage derivation, read through a matching grading of the stage, satisfies the hypotheses
needed to regard it as a graded derivation of the stage. -/
private theorem isStageDerivation_graded_hyps
    {D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S}
    (hD : IsStageDerivation ι T dA ev S (stageCoe D)) :
    (∀ b : finiteVariableStage δ ι T S, b ∈ Sᵢ 0 → D b = 0) ∧
      (∀ (n : ℕ) (b : finiteVariableStage δ ι T S), b ∈ Sᵢ (n + 1) → D b ∈ Sᵢ n) ∧
      ∀ (i k : ℕ) (x y : finiteVariableStage δ ι T S), x ∈ Sᵢ i → y ∈ Sᵢ k →
        D (x * y) = D x * y + (-1 : R) ^ i • (x * D y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    refine Subtype.ext ?_
    rw [← stageCoe_apply D b, hD.grade_zero b ((hSmem 0 b).mp hb), Subring.coe_zero]
  · intro n b hb
    refine (hSmem n (D b)).mpr ?_
    rw [← stageCoe_apply D b]
    exact hD.grade_mem n b ((hSmem (n + 1) b).mp hb)
  · intro i k x y hx hy
    refine Subtype.ext ?_
    rw [Subring.coe_add, Subring.coe_mul, coe_neg_one_pow_smul, Subring.coe_mul,
      ← stageCoe_apply D (x * y), ← stageCoe_apply D x, ← stageCoe_apply D y,
      hD.leibniz i k x y ((hSmem i x).mp hx) ((hSmem k y).mp hy)]

include hSmem in
/-- The stagewise divided power structure is compatible with the stage derivation. -/
private theorem isStageDerivation_compatible (δS : DividedPowerStructure Sᵢ)
    (hδ : ∀ (n : ℕ) (b : finiteVariableStage δ ι T S), b ∈ positiveEvenPart Sᵢ →
      ((δS.dpow n b : finiteVariableStage δ ι T S) : C) = δ.dpow n (b : C))
    {D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S}
    (hD : IsStageDerivation ι T dA ev S (stageCoe D))
    (hzero : ∀ b : finiteVariableStage δ ι T S, b ∈ Sᵢ 0 → D b = 0)
    (hleib : ∀ (i k : ℕ) (x y : finiteVariableStage δ ι T S), x ∈ Sᵢ i → y ∈ Sᵢ k →
      D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) :
    IsCompatibleWithDifferential δS (gradedDerivationToLinearMap Sᵢ D hzero hleib) := by
  constructor
  intro n b hn hb
  have hbC : (b : C) ∈ positiveEvenPart Cᵢ := mem_positiveEvenPart_of_mem_stage Sᵢ hSmem b hb
  have h1 : ((δS.dpow n b : finiteVariableStage δ ι T S) : C) = δ.dpow n (b : C) := hδ n b hb
  have hmem : δ.dpow n (b : C) ∈ finiteVariableStage δ ι T S := h1 ▸ (δS.dpow n b).2
  refine Subtype.ext ?_
  rw [Subring.coe_mul, hδ (n - 1) b hb, gradedDerivationToLinearMap_apply,
    gradedDerivationToLinearMap_apply, ← stageCoe_apply D (δS.dpow n b), ← stageCoe_apply D b,
    show (δS.dpow n b : finiteVariableStage δ ι T S) =
      (⟨δ.dpow n (b : C), hmem⟩ : finiteVariableStage δ ι T S) from Subtype.ext h1,
    hD.map_dpow n b hn hbC hmem]

end StageGradedHyps


section StageInduction

open EvenVariableAlgebra OddVariableExtension

variable {R : Type u} {A : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ}
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ} {ι : A →ₐ[R] C} {T : J → C} {d : ℕ} {hd : 0 < d}
  {dA : A →ₗ[R] A} {ev : J → A}

/-- A stage derivation, read through a matching grading of the stage, is a graded derivation of
the stage compatible with the stagewise divided powers. -/
private theorem exists_gradedDerivation_of_isStageDerivation {S : Finset J}
    [Algebra R (finiteVariableStage δ ι T S)]
    (Sᵢ : ℕ → Submodule R (finiteVariableStage δ ι T S)) [GradedAlgebra Sᵢ]
    [IsStrictlyGradedComm Sᵢ]
    (hSmem : ∀ (m : ℕ) (b : finiteVariableStage δ ι T S), b ∈ Sᵢ m ↔ (b : C) ∈ Cᵢ m)
    (δS : DividedPowerStructure Sᵢ)
    (hδ : ∀ (n : ℕ) (b : finiteVariableStage δ ι T S), b ∈ positiveEvenPart Sᵢ →
      ((δS.dpow n b : finiteVariableStage δ ι T S) : C) = δ.dpow n (b : C))
    {D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S}
    (hD : IsStageDerivation ι T dA ev S (stageCoe D)) :
    ∃ dS : finiteVariableStage δ ι T S →ₗ[R] finiteVariableStage δ ι T S,
      IsGradedDerivation Sᵢ dS ∧ IsCompatibleWithDifferential δS dS ∧ ∀ b, dS b = D b := by
  obtain ⟨hzeroS, hmemS, hleibS⟩ := isStageDerivation_graded_hyps Sᵢ hSmem hD
  exact ⟨gradedDerivationToLinearMap Sᵢ D hzeroS hleibS,
    isGradedDerivation_toLinearMap Sᵢ D hzeroS hmemS hleibS,
    isStageDerivation_compatible Sᵢ hSmem δS hδ hD hzeroS hleibS, fun _ => rfl⟩

/-- A derivation realising the prescribed data exists on every finite variable stage. The empty
stage is the image of the coefficient algebra; each successor stage is the relevant one-variable
divided power extension, across which the derivation is extended by the one-variable mapping
property for graded derivations. -/
private theorem exists_isStageDerivation
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd)
    [IsGradedDerivation Aᵢ dA] [IsCompatibleWithDifferential γ dA]
    (hev : ∀ j : J, ev j ∈ Aᵢ (d - 1)) (S : Finset J) :
    ∃ D : finiteVariableStage δ ι T S →+ finiteVariableStage δ ι T S,
      IsStageDerivation ι T dA ev S (stageCoe D) := by
  let instDec : DecidableEq J := Classical.decEq J
  refine Finset.induction_on S (exists_isStageDerivation_empty hC) ?_
  intro j S₀ hjS₀ ih
  obtain ⟨D, hD⟩ := ih
  obtain ⟨aS, Sᵢ, gS, cS, δS, hδ, hoddbr, hevenbr⟩ := hC.successor S₀ j hjS₀
  let := aS
  let := gS
  let := cS
  have hfSmem : ι (ev j) ∈ finiteVariableStage δ ι T S₀ :=
    mem_finiteVariableStage_coefficient δ ι T S₀ (ev j)
  rcases Nat.even_or_odd d with heven | hodd
  · let : Fact (Even d) := ⟨heven⟩
    obtain ⟨e, he1, he2, he3, he4⟩ := hevenbr heven
    have hSmem : ∀ (m : ℕ) (b : finiteVariableStage δ ι T S₀),
        b ∈ Sᵢ m ↔ (b : C) ∈ Cᵢ m := by
      intro m b
      have h1 : EvenVariableAlgebra.coeffEmbedding b ∈
          EvenVariableAlgebra.grade Sᵢ d m ↔ (b : C) ∈ Cᵢ m := by rw [he3, he1]
      rw [← h1, EvenVariableAlgebra.coeffEmbedding_mem_grade_iff]
    obtain ⟨dS, _, _, hdS⟩ := exists_gradedDerivation_of_isStageDerivation Sᵢ hSmem δS hδ hD
    obtain ⟨dExt, hdExt, -⟩ := existsUnique_gradedDerivation_evenVariableAlgebra Sᵢ δS dS d hd
      (⟨ι (ev j), hfSmem⟩ : finiteVariableStage δ ι T S₀)
      ((hSmem (d - 1) _).mpr (hC.coefficient_grade (d - 1) (ev j) (hev j)))
    let : IsGradedDerivation (EvenVariableAlgebra.grade Sᵢ d) dExt := hdExt.1
    let : IsCompatibleWithDifferential (evenVariableDividedPowerStructure d hd δS) dExt :=
      hdExt.2.2.2
    exact exists_isStageDerivation_of_oneVariableExtension (fun a => Finset.mem_insert) hD
      (δE := evenVariableDividedPowerStructure d hd δS) EvenVariableAlgebra.coeffEmbedding
      (EvenVariableAlgebra.monomial 1 1) dExt
      (fun b => (hdExt.2.1 b).trans
        (congrArg EvenVariableAlgebra.coeffEmbedding (hdS b)))
      hdExt.2.2.1 e he1 he2 he3 he4
  · obtain ⟨e, he1, he2, he3, he4⟩ := hoddbr hodd
    have hSmem : ∀ (m : ℕ) (b : finiteVariableStage δ ι T S₀),
        b ∈ Sᵢ m ↔ (b : C) ∈ Cᵢ m := by
      intro m b
      have h1 : OddVariableExtension.inclusion Sᵢ d b ∈
          OddVariableExtension.grade Sᵢ d m ↔ (b : C) ∈ Cᵢ m := by rw [he3, he1]
      rw [← h1]
      refine ⟨fun hb => OddVariableExtension.inclusion_mem_grade Sᵢ d m hb, fun hb => ?_⟩
      rw [OddVariableExtension.mem_grade_iff] at hb
      exact hb.1
    obtain ⟨dS, _, _, hdS⟩ := exists_gradedDerivation_of_isStageDerivation Sᵢ hSmem δS hδ hD
    obtain ⟨dExt, hdExt, -⟩ := existsUnique_gradedDerivation_oddVariableExtension Sᵢ δS dS d hd
      hodd
      (⟨ι (ev j), hfSmem⟩ : finiteVariableStage δ ι T S₀)
      ((hSmem (d - 1) _).mpr (hC.coefficient_grade (d - 1) (ev j) (hev j)))
    let : IsGradedDerivation (OddVariableExtension.grade Sᵢ d) dExt := hdExt.1
    let : IsCompatibleWithDifferential
        (oddVariableDividedPowerStructure Sᵢ δS d hd hodd) dExt := hdExt.2.2.2
    exact exists_isStageDerivation_of_oneVariableExtension (fun a => Finset.mem_insert) hD
      (δE := oddVariableDividedPowerStructure Sᵢ δS d hd hodd)
      (OddVariableExtension.inclusion Sᵢ d) (OddVariableExtension.generator Sᵢ d) dExt
      (fun b => (hdExt.2.1 b).trans
        (congrArg (OddVariableExtension.inclusion Sᵢ d) (hdS b)))
      hdExt.2.2.1 e he1 he2 he3 he4

end StageInduction


/-- A graded derivation of the coefficient algebra which is compatible with its divided powers
extends, uniquely, to a graded derivation of a set-variable divided power extension once a value
of degree `d - 1` is prescribed for each adjoined variable. No cycle condition is imposed on the
prescribed values and the extension need not be square-zero, which is what the square-zero lift
of Tag 09PS requires. -/
public theorem existsUnique_gradedDerivation_setVariableExtension
    {R : Type u} {A : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (γ : DividedPowerStructure Aᵢ)
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (δ : DividedPowerStructure Cᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (d : ℕ) (hd : 0 < d)
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T d hd)
    (dA : A →ₗ[R] A) [IsGradedDerivation Aᵢ dA] [IsCompatibleWithDifferential γ dA]
    (ev : J → A) (hev : ∀ j : J, ev j ∈ Aᵢ (d - 1)) :
    ∃! D : C →ₗ[R] C,
      IsGradedDerivation Cᵢ D ∧ (∀ a : A, D (ι a) = ι (dA a)) ∧
        (∀ j : J, D (T j) = ι (ev j)) ∧ IsCompatibleWithDifferential δ D := by
  classical
  choose DS hDS using exists_isStageDerivation (dA := dA) (ev := ev) hC hev
  have hcompat : ∀ (S U : Finset J) (x : finiteVariableStage δ ι T S)
      (y : finiteVariableStage δ ι T U), (x : C) = (y : C) →
      stageCoe (DS S) x = stageCoe (DS U) y := by
    intro S U x y hxy
    rw [IsStageDerivation.eq_of_subset hC (Finset.subset_union_left (s₁ := S) (s₂ := U))
        (hDS S) (hDS (S ∪ U)) x,
      IsStageDerivation.eq_of_subset hC (Finset.subset_union_right (s₁ := S) (s₂ := U))
        (hDS U) (hDS (S ∪ U)) y]
    exact congrArg (stageCoe (DS (S ∪ U))) (Subtype.ext hxy)
  obtain ⟨G, hG, hGuniq⟩ := finiteVariableStages_directedColimit_addHom Cᵢ δ ι T
    hC.finite_support (fun S => stageCoe (DS S)) hcompat
  have hzero : ∀ x : C, x ∈ Cᵢ 0 → G x = 0 := by
    intro x hx
    obtain ⟨S, hS⟩ := hC.finite_support x
    rw [hG S ⟨x, hS⟩]
    exact (hDS S).grade_zero ⟨x, hS⟩ hx
  have hmem : ∀ (n : ℕ) (x : C), x ∈ Cᵢ (n + 1) → G x ∈ Cᵢ n := by
    intro n x hx
    obtain ⟨S, hS⟩ := hC.finite_support x
    rw [hG S ⟨x, hS⟩]
    exact (hDS S).grade_mem n ⟨x, hS⟩ hx
  have hleib : ∀ (i k : ℕ) (x y : C), x ∈ Cᵢ i → y ∈ Cᵢ k →
      G (x * y) = G x * y + (-1 : R) ^ i • (x * G y) := by
    intro i k x y hx hy
    obtain ⟨S, hS⟩ := hC.finite_support x
    obtain ⟨U, hU⟩ := hC.finite_support y
    have hxV : x ∈ finiteVariableStage δ ι T (S ∪ U) :=
      finiteVariableStage_le_of_subset δ ι T Finset.subset_union_left hS
    have hyV : y ∈ finiteVariableStage δ ι T (S ∪ U) :=
      finiteVariableStage_le_of_subset δ ι T Finset.subset_union_right hU
    rw [hG (S ∪ U) ⟨x * y, mul_mem hxV hyV⟩, hG (S ∪ U) ⟨x, hxV⟩, hG (S ∪ U) ⟨y, hyV⟩]
    exact (hDS (S ∪ U)).leibniz i k ⟨x, hxV⟩ ⟨y, hyV⟩ hx hy
  refine ⟨gradedDerivationToLinearMap Cᵢ G hzero hleib,
    ⟨isGradedDerivation_toLinearMap Cᵢ G hzero hmem hleib, ?_, ?_, ?_⟩, ?_⟩
  · intro a
    rw [gradedDerivationToLinearMap_apply,
      hG ∅ ⟨ι a, mem_finiteVariableStage_coefficient δ ι T ∅ a⟩]
    exact (hDS ∅).map_coeff a
  · intro j
    rw [gradedDerivationToLinearMap_apply,
      hG {j} ⟨T j, mem_finiteVariableStage_generator δ ι T (Finset.mem_singleton_self j)⟩]
    exact (hDS {j}).map_generator j (Finset.mem_singleton_self j)
  · constructor
    intro n x hn hx
    obtain ⟨S, hS⟩ := hC.finite_support x
    obtain ⟨S', hS'⟩ := hC.finite_support (δ.dpow n x)
    have hxV : x ∈ finiteVariableStage δ ι T (S ∪ S') :=
      finiteVariableStage_le_of_subset δ ι T Finset.subset_union_left hS
    have hdV : δ.dpow n x ∈ finiteVariableStage δ ι T (S ∪ S') :=
      finiteVariableStage_le_of_subset δ ι T Finset.subset_union_right hS'
    rw [gradedDerivationToLinearMap_apply, gradedDerivationToLinearMap_apply,
      hG (S ∪ S') ⟨δ.dpow n x, hdV⟩, hG (S ∪ S') ⟨x, hxV⟩]
    exact (hDS (S ∪ S')).map_dpow n ⟨x, hxV⟩ hn hx hdV
  · intro D' hD'
    let : IsGradedDerivation Cᵢ D' := hD'.1
    let : IsCompatibleWithDifferential δ D' := hD'.2.2.2
    have hrestrict : ∀ S : Finset J,
        IsStageDerivation ι T dA ev S
          (AddMonoidHom.mk' (fun x : finiteVariableStage δ ι T S => D' (x : C))
            (fun x y => by rw [Subring.coe_add, map_add])) := by
      intro S
      exact ⟨fun a => hD'.2.1 a, fun j _ => hD'.2.2.1 j,
        fun x hx => IsGradedDerivation.d_grade_zero (𝒜 := Cᵢ) (d := D') hx,
        fun n x hx => IsGradedDerivation.d_mem (𝒜 := Cᵢ) (d := D') hx,
        fun i k x y hx hy => IsGradedDerivation.leibniz (𝒜 := Cᵢ) (d := D') hx hy,
        fun n x hn hx _ => IsCompatibleWithDifferential.d_dpow (γ := δ) (d := D') hn hx⟩
    have hkey : ∀ (S : Finset J) (x : finiteVariableStage δ ι T S),
        D'.toAddMonoidHom (x : C) = stageCoe (DS S) x := by
      intro S x
      exact IsStageDerivation.eq_of_subset hC (Finset.Subset.refl S) (hrestrict S) (hDS S) x
    exact LinearMap.ext fun x =>
      (DFunLike.congr_fun (hGuniq D'.toAddMonoidHom hkey) x).trans
        (gradedDerivationToLinearMap_apply Cᵢ G hzero hleib x).symm


end Extension

end DividedPowers.TateResolution

end
