module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessResolution.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree

/-!
# The Euler characteristic of a direct sum of *different* modules

`AlgebraicGeometry.eulerCharacteristic_biprodPow` gives `χ(X, 𝒢^{⊞ n}) = n · χ(X, 𝒢)` for the
powers of a *single* module, unconditionally. This file gives the heterogeneous statements

  `χ(X, 𝒜 ⊞ ℬ) = χ(X, 𝒜) + χ(X, ℬ)`  and  `χ(X, ⨁ⱼ ℰⱼ) = ∑ⱼ χ(X, ℰⱼ)`,

which are **not** unconditional: they carry the two facts that make `χ` well defined — finite
dimensionality of each `Hⁿ` over `k` ([Stacks, Tag 02O6]) and vanishing of all but finitely many
of them ([Stacks, Tag 01XJ]) — as hypotheses on the **summands only**.

## Why the hypotheses cannot be dropped

The equal-summand case escapes them because `Module.finrank k (Fin n → V) = n · Module.finrank k V`
holds for every `k`-vector space `V`, both sides being zero when `V` is infinite-dimensional and
`n` is positive (`Module.finrank_fun_fin`). The heterogeneous statement has no such escape:
`Module.finrank k (V × W) = Module.finrank k V + Module.finrank k W` is **false** for `V`
infinite-dimensional and `W` of dimension one, the left side being zero and the right side one.
So although the cohomology of a biproduct *is* the product of the cohomologies with no hypothesis
at all (`AlgebraicGeometry.nonempty_cohomologyOverField_biprod_linearEquiv`), the dimension count
needs finiteness, and the alternating sum needs the vanishing in order to be a finite sum at all.

That is why the proofs below go through the additivity of [Stacks, Tag 08AA] rather than through
the splitting: `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_outer` already carries
exactly those two hypotheses for the two outer terms of a short exact sequence, and the biproduct
sits in the middle of the split short exact sequence
`AlgebraicGeometry.biprodShortComplex`. Nothing is assumed about the biproduct itself.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_biprod`: **`χ(X, 𝒜 ⊞ ℬ) = χ(X, 𝒜) + χ(X, ℬ)`**, with
  finite dimensionality below a bound `N` and vanishing above it assumed for `𝒜` and `ℬ` only.
* `AlgebraicGeometry.isZero_cohomologyOverField_biprod` and
  `AlgebraicGeometry.isZero_cohomologyOverField_biproduct`: vanishing of the cohomology in a
  fixed degree passes to a binary biproduct and to a finite biproduct.
* `AlgebraicGeometry.SheafOfModules.isCoherent_biproduct`: a finite biproduct of coherent modules
  is coherent.
* `AlgebraicGeometry.eulerCharacteristic_biproduct`: **`χ(X, ⨁ⱼ ℰⱼ) = ∑ⱼ χ(X, ℰⱼ)`** for a
  finite family, with the same two hypotheses assumed uniformly on the summands.

## Implementation notes

**`HasFiniteBiproducts X.Modules` is not an instance**, although it is one term —
`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`, the category being abelian. It
is supplied here as a *local* instance, as in
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessResolution/Basic.lean`, since a new global
instance on `X.Modules` changes instance search for every consumer of this tree. The same fact at
a general site is `StacksDraft.Ch18.Sec28.Tag03EU.hasFiniteBiproducts_sheafOfModules`; it is not
used, because its file's import closure (the monoidal sheaf tensor, colimits of sheaves of
modules, flatness) is far larger than the one-line `of_hasFiniteProducts` it would replace.

Following that file, the **public** statements take `[HasBiproduct ℰ]` as a binder rather than
relying on the local instance: that is the more general statement, and a statement relying on the
local instance can fail to elaborate after a private induction has been elaborated. At a use site
the binder is discharged by `CategoryTheory.Limits.HasBiproduct.of_hasProduct ℰ`, the finite
products being available in an abelian category.

**The induction splits off one summand through the kernel sequence.**
`CategoryTheory.Limits.kernelBiproductπIso` identifies the biproduct over the complement of an
index with the kernel of the projection at it, so `0 ⟶ ⨁_{j ≠ i} ℰⱼ ⟶ ⨁ⱼ ℰⱼ ⟶ ℰᵢ ⟶ 0` is short
exact with the whole biproduct in the **middle**, the one position that needs no degree shift.
Mathlib states no decomposition of a `Fin (r + 1)`-indexed biproduct into a binary one, and none
is needed.

**No `@[stacks]` attribute is attached.** [Stacks, Tag 08AA] is not proved: what the statements
below assume is the content of Tags 02O6 and 01XJ for the summands, and the additivity they are
derived from assumes it for the outer two terms of its sequence.

## References

* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### A binary biproduct -/

/-- **Vanishing of the cohomology in a fixed degree passes to a binary biproduct.** The biproduct
sits in the middle of the split short exact sequence `0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0`, and the middle
position of a short exact sequence needs no degree shift
(`AlgebraicGeometry.isZero_cohomologyOverField_of_shortExact`). There is no hypothesis on `f` or
on the modules. -/
theorem isZero_cohomologyOverField_biprod (A B : X.Modules) (n : ℕ)
    (hA : IsZero (cohomologyOverField k f A n)) (hB : IsZero (cohomologyOverField k f B n)) :
    IsZero (cohomologyOverField k f (A ⊞ B) n) :=
  isZero_cohomologyOverField_of_shortExact k f
    (biprodShortComplexSplitting A B).shortExact n hA hB

/-- **`χ(X, 𝒜 ⊞ ℬ) = χ(X, 𝒜) + χ(X, ℬ)`.** For `X` proper over a field and coherent `𝒜`, `ℬ`,
the Euler characteristic is additive over a binary biproduct, given finite dimensionality of
`Hⁿ(X, 𝒜)` and `Hⁿ(X, ℬ)` below a bound `N` ([Stacks, Tag 02O6]) and their vanishing above it
([Stacks, Tag 01XJ]). Nothing is assumed about the biproduct beyond coherence, which
`AlgebraicGeometry.SheafOfModules.isCoherent_biprod` supplies from coherence of the summands.

Unlike `AlgebraicGeometry.eulerCharacteristic_biprodPow`, this is **not** unconditional; see the
module docstring for the counterexample that rules the hypotheses out.

The tag of [Stacks, Tag 08AA] is not attached: this is an instance of it, not a proof of it. -/
theorem eulerCharacteristic_biprod [IsProper f] (A B : X.Modules)
    [hA : A.IsCoherent] [hB : B.IsCoherent] (hAB : (A ⊞ B).IsCoherent) (N : ℕ)
    (hfinA : ∀ n < N, FiniteDimensional k (cohomologyOverField k f A n))
    (hfinB : ∀ n < N, FiniteDimensional k (cohomologyOverField k f B n))
    (hvanA : ∀ n, N ≤ n → IsZero (cohomologyOverField k f A n))
    (hvanB : ∀ n, N ≤ n → IsZero (cohomologyOverField k f B n)) :
    @eulerCharacteristic k _ X f _ (A ⊞ B) hAB =
      eulerCharacteristic k f A + eulerCharacteristic k f B :=
  @eulerCharacteristic_add_of_shortExact_of_outer k _ X f _ (biprodShortComplex A B)
    (biprodShortComplexSplitting A B).shortExact hA hAB hB N hfinA hfinB hvanA hvanB

/-! ### A finite biproduct -/

attribute [local instance] hasFiniteBiproducts_modules

/-- A biproduct over an empty index type is a zero object. -/
private theorem isZero_biproduct_of_isEmpty {J : Type} [IsEmpty J] (E : J → X.Modules)
    [HasBiproduct E] : IsZero (⨁ E) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext _ _ fun j => isEmptyElim j

/-- Removing one index from a type with `m + 1` elements leaves `m` elements. -/
private theorem card_subtype_ne_eq {J : Type} [Fintype J] [DecidableEq J] {m : ℕ} (i : J)
    (hcard : Fintype.card J = m + 1) : Fintype.card {j // j ≠ i} = m := by
  rw [Fintype.card_subtype_compl (p := fun j => j = i), Fintype.card_subtype_eq, hcard]
  omega

/-- The kernel sequence of the projection of a biproduct to a summand is short exact. -/
private theorem shortExact_kernelSequence_biproduct_π {J : Type} (E : J → X.Modules)
    [HasBiproduct E] (i : J) : (ShortComplex.kernelSequence (biproduct.π E i)).ShortExact := by
  have : IsSplitEpi (biproduct.π E i) := IsSplitEpi.mk' ⟨biproduct.ι E i, by simp⟩
  exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance
    (inferInstanceAs (Epi (biproduct.π E i)))

/-- The induction behind `AlgebraicGeometry.SheafOfModules.isCoherent_biproduct`, on the number of
summands. -/
private theorem isCoherent_biproduct_aux :
    ∀ (N : ℕ) {J : Type} [Fintype J] (E : J → X.Modules), Fintype.card J = N →
      (∀ j, (E j).IsCoherent) → (⨁ E).IsCoherent := by
  classical
  intro N
  induction N with
  | zero =>
    intro J _ E hcard _
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp hcard
    have hz := isZero_biproduct_of_isEmpty E
    exact SheafOfModules.isCoherent_of_isZero hz
  | succ N ih =>
    intro J _ E hcard h
    obtain ⟨i⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    have hcard' := card_subtype_ne_eq i hcard
    have hSE := shortExact_kernelSequence_biproduct_π E i
    have hrest := ih (Subtype.restrict (fun j => j ≠ i) E) hcard' fun j => h j.1
    let P : ObjectProperty X.Modules := fun M => M.IsCoherent
    let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
    exact P.prop_X₂_of_shortExact hSE
      (P.prop_of_iso (kernelBiproductπIso E i).symm hrest) (h i)

/-- **A finite biproduct of coherent modules is coherent.** Coherent modules form a weak Serre
class ([Stacks, Tag 01BY]), so they contain the zero object and are closed under extensions; the
induction splits off one summand through the kernel sequence of its projection. -/
theorem SheafOfModules.isCoherent_biproduct {J : Type} [Finite J] (E : J → X.Modules)
    [HasBiproduct E] (h : ∀ j, (E j).IsCoherent) : (⨁ E).IsCoherent := by
  let _ := Fintype.ofFinite J
  exact isCoherent_biproduct_aux _ E rfl h

/-- The induction behind `AlgebraicGeometry.isZero_cohomologyOverField_biproduct`, on the number
of summands. -/
private theorem isZero_cohomologyOverField_biproduct_aux (n : ℕ) :
    ∀ (N : ℕ) {J : Type} [Fintype J] (E : J → X.Modules), Fintype.card J = N →
      (∀ j, IsZero (cohomologyOverField k f (E j) n)) →
      IsZero (cohomologyOverField k f (⨁ E) n) := by
  classical
  intro N
  induction N with
  | zero =>
    intro J _ E hcard _
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp hcard
    have hz := isZero_biproduct_of_isEmpty E
    exact isZero_cohomologyOverField_of_isZero k f hz n
  | succ N ih =>
    intro J _ E hcard h
    obtain ⟨i⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    have hcard' := card_subtype_ne_eq i hcard
    have hSE := shortExact_kernelSequence_biproduct_π E i
    have hrest := ih (Subtype.restrict (fun j => j ≠ i) E) hcard' fun j => h j.1
    exact isZero_cohomologyOverField_of_shortExact k f hSE n
      (hrest.of_iso (cohomologyOverFieldIso k f (kernelBiproductπIso E i) n)) (h i)

/-- **Vanishing of the cohomology in a fixed degree passes to a finite biproduct.** -/
theorem isZero_cohomologyOverField_biproduct {J : Type} [Finite J] (E : J → X.Modules)
    [HasBiproduct E] (n : ℕ) (h : ∀ j, IsZero (cohomologyOverField k f (E j) n)) :
    IsZero (cohomologyOverField k f (⨁ E) n) := by
  let _ := Fintype.ofFinite J
  exact isZero_cohomologyOverField_biproduct_aux k f n _ E rfl h

/-- The induction behind `AlgebraicGeometry.eulerCharacteristic_biproduct`, on the number of
summands. The two cited inputs are carried uniformly in a single bound `N`, which is what makes
the induction go through: the inductive hypothesis is applied to the biproduct over the
complement of an index, whose bound must be the same one. -/
private theorem eulerCharacteristic_biproduct_aux [IsProper f] (N : ℕ) :
    ∀ (m : ℕ) {J : Type} [Fintype J] (E : J → X.Modules), Fintype.card J = m →
      ∀ (hE : ∀ j, (E j).IsCoherent) (hEb : (⨁ E).IsCoherent),
      (∀ (j : J) (n : ℕ), n < N → FiniteDimensional k (cohomologyOverField k f (E j) n)) →
      (∀ (j : J) (n : ℕ), N ≤ n → IsZero (cohomologyOverField k f (E j) n)) →
      @eulerCharacteristic k _ X f _ (⨁ E) hEb =
        ∑ j, @eulerCharacteristic k _ X f _ (E j) (hE j) := by
  classical
  intro m
  induction m with
  | zero =>
    intro J _ E hcard hE hEb _ _
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp hcard
    have hz := isZero_biproduct_of_isEmpty E
    rw [eulerCharacteristic_eq_zero_of_isZero k f _ hEb hz]
    simp
  | succ m ih =>
    intro J _ E hcard hE hEb hfin hvan
    obtain ⟨i⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    have hcard' := card_subtype_ne_eq i hcard
    have hSE := shortExact_kernelSequence_biproduct_π E i
    have hE' : ∀ j : {j // j ≠ i}, (Subtype.restrict (fun j => j ≠ i) E j).IsCoherent :=
      fun j => hE j.1
    have hE'b : (⨁ Subtype.restrict (fun j => j ≠ i) E).IsCoherent :=
      isCoherent_biproduct_aux _ _ hcard' hE'
    have hkerC : (kernel (biproduct.π E i)).IsCoherent := by
      let P : ObjectProperty X.Modules := fun M => M.IsCoherent
      let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
      exact P.prop_of_iso (kernelBiproductπIso E i).symm hE'b
    have hkerfin : ∀ n < N,
        FiniteDimensional k (cohomologyOverField k f (kernel (biproduct.π E i)) n) := by
      intro n hn
      have := finiteDimensional_cohomologyOverField_biproduct k f
        (Subtype.restrict (fun j => j ≠ i) E) n fun j => hfin j.1 n hn
      exact Module.Finite.equiv
        (cohomologyOverFieldIso k f (kernelBiproductπIso E i) n).toLinearEquiv.symm
    have hkervan : ∀ n, N ≤ n →
        IsZero (cohomologyOverField k f (kernel (biproduct.π E i)) n) := fun n hn =>
      (isZero_cohomologyOverField_biproduct_aux k f n _
          (Subtype.restrict (fun j => j ≠ i) E) hcard' fun j => hvan j.1 n hn).of_iso
        (cohomologyOverFieldIso k f (kernelBiproductπIso E i) n)
    have hadd : @eulerCharacteristic k _ X f _ (⨁ E) hEb =
        @eulerCharacteristic k _ X f _ (kernel (biproduct.π E i)) hkerC +
          @eulerCharacteristic k _ X f _ (E i) (hE i) :=
      @eulerCharacteristic_add_of_shortExact_of_outer k _ X f _ _ hSE hkerC hEb (hE i) N
        hkerfin (fun n hn => hfin i n hn) hkervan (hvan i)
    -- the summands over the complement of `i`, re-indexed from the subtype to `univ.erase i`
    have hsub : (∑ j : {j // j ≠ i}, @eulerCharacteristic k _ X f _
          (Subtype.restrict (fun j => j ≠ i) E j) (hE' j)) =
        ∑ j ∈ Finset.univ.erase i, @eulerCharacteristic k _ X f _ (E j) (hE j) :=
      (Finset.sum_subtype (Finset.univ.erase i) (fun x => by simp)
        fun j => @eulerCharacteristic k _ X f _ (E j) (hE j)).symm
    rw [hadd,
      @eulerCharacteristic_eq_of_iso k _ X f _ (kernel (biproduct.π E i))
        (⨁ Subtype.restrict (fun j => j ≠ i) E) hkerC hE'b (kernelBiproductπIso E i),
      ih (Subtype.restrict (fun j => j ≠ i) E) hcard' hE' hE'b
        (fun j n hn => hfin j.1 n hn) fun j n hn => hvan j.1 n hn]
    rw [hsub]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- **`χ(X, ⨁ⱼ ℰⱼ) = ∑ⱼ χ(X, ℰⱼ)` for a finite family.** For `X` proper over a field and each
`ℰⱼ` coherent, the Euler characteristic is additive over a finite biproduct, given finite
dimensionality of each `Hⁿ(X, ℰⱼ)` below a bound `N` ([Stacks, Tag 02O6]) and their vanishing
above it ([Stacks, Tag 01XJ]). The bound is uniform in `j`, which is what a consumer gets from
those two tags on a proper `X`.

Nothing is assumed about the biproduct beyond coherence, which
`AlgebraicGeometry.SheafOfModules.isCoherent_biproduct` supplies from coherence of the summands.
The `[HasBiproduct ℰ]` binder is discharged at a use site by
`CategoryTheory.Limits.HasBiproduct.of_hasProduct ℰ`; see the implementation notes.

The tag of [Stacks, Tag 08AA] is not attached: this is an instance of it, not a proof of it. -/
theorem eulerCharacteristic_biproduct [IsProper f] {J : Type} [Fintype J] (E : J → X.Modules)
    [HasBiproduct E] (hE : ∀ j, (E j).IsCoherent) (hEb : (⨁ E).IsCoherent) (N : ℕ)
    (hfin : ∀ (j : J) (n : ℕ), n < N → FiniteDimensional k (cohomologyOverField k f (E j) n))
    (hvan : ∀ (j : J) (n : ℕ), N ≤ n → IsZero (cohomologyOverField k f (E j) n)) :
    @eulerCharacteristic k _ X f _ (⨁ E) hEb =
      ∑ j, @eulerCharacteristic k _ X f _ (E j) (hE j) :=
  eulerCharacteristic_biproduct_aux k f N _ E rfl hE hEb hfin hvan

end AlgebraicGeometry

end
