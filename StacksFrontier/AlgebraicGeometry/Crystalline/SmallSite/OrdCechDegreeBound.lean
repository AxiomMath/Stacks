module

public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechCoverComplex

/-!
# What the alternating Čech complex of [Stacks, Tag 07MN] implies about vanishing

[Stacks, Tag 07MN] asserts that for a finite affine open covering `X = ⋃_{λ ∈ Λ} U_λ` with `Λ`
totally ordered the total complex of the double complex

`M^{n, m} = ⨁_{λ_0 < ⋯ < λ_n} M_{λ_0 … λ_n} ⊗̂_{D_{λ_0 … λ_n}} Ω^m_{D_{λ_0 … λ_n}}`

computes `RΓ(Cris(X/S), F)`.  The statement is
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesOrdCechCohomology` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechCoverComplex.lean`, and it is **not
proved**; that file's "What is and is not proved" section lists the five groups of missing inputs.

This file proves what follows from the assertion once it is granted, and the one thing it is wanted
for elsewhere in the chapter is a vanishing bound.  The remark's double complex is supported in the
box `0 ≤ n < #Λ`, `0 ≤ m ≤ e`: the Čech direction because a strictly increasing tuple
`λ_0 < ⋯ < λ_n` in a set of `#Λ` elements forces `n + 1 ≤ #Λ`, and the de Rham direction because
`Ω^m_{D_β}` vanishes above the number of generators.  So its total complex is supported in degrees
`≤ #Λ - 1 + e`, and `H^i(Cris(X/S), F) = 0` for `i ≥ #Λ + e`.

That is the mechanism clause (2) of [Stacks, Tag 07MR] runs on — "the alternating Čech complex for
a finite affine cover, which is what reduces clause (2) to the affine case" of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/VanishingStatements.lean`.  The bound proved
here, `#Λ + e ≤ i`, is *sharper* than the `q + e < i` that [Stacks, Tag 07MR] clause (2) asserts,
and `isZero_cohomologyFunctor_of_computesOrdCechCohomology'` records the weaker form the tag
states.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `OrdCechTuple.card_le` — a strictly increasing `(n + 1)`-tuple in `Λ` forces `n + 1 ≤ #Λ`.
* `OrdCechTuple.isEmpty_of_card_le` — **there are no strictly increasing `(n + 1)`-tuples once
  `#Λ ≤ n`**, so the alternating Čech complex of a covering with `#Λ` members stops there.
* `isZero_ordCechTerm_of_isZero` and `isZero_ordCechTerm_of_card_le` — the term `M^{n, m}` of the
  double complex vanishes when every local de Rham term in that bidegree does, and in particular
  for every `m` once `#Λ ≤ n`.
* `OrdCechTotalComparison.isZero_X` — **the double complex of [Stacks, Tag 07MN] vanishes in every
  bidegree of total degree `≥ #Λ + e`**, given that the local completed de Rham complexes vanish
  above degree `e`.
* `OrdCechTotalComparison.isZero_total_X` — hence its total complex vanishes in those degrees.
* `OrdCechTotalComparison.isZero_cohomologyFunctor` and
  `isZero_cohomologyFunctor_of_computesOrdCechCohomology` — **hence `H^i(Cris(X/S), F) = 0` for
  `i ≥ #Λ + e`**, which is the conclusion clause (2) of [Stacks, Tag 07MR] wants.
* `subsingleton_cohomology_of_computesOrdCechCohomology` — the same conclusion in the
  `Subsingleton (cohomology S G i)` spelling that
  `...SmallSite.AbelianVanishing07MR` uses.
* `computesOrdCechCohomology_of_cohomologyIso` — **the first step of the hint of
  [Stacks, Tag 07MN] isolated**: "replace `F` by `F ⊗ Ω^*_{X/S}`, which changes nothing because
  `RΓ` of the two agree by [Stacks, Tag 07LM]" uses nothing about [Stacks, Tag 07LM] beyond a
  degreewise isomorphism of the cohomology of the two coefficient sheaves.

## What is and is not proved

**[Stacks, Tag 07MN] is not proved here and no tag attribute is placed in this file.**  Every
result below takes the remark's conclusion — a term of
`...SmallSite.OrdCechTotalComparison`, or the proposition
`...SmallSite.ComputesOrdCechCohomology` — as a hypothesis, so each is a conditional statement and
none of them is the tag.  Equally, none of them is a step towards the tag: they are what the tag
buys, recorded so that the claim "07MN is what reduces clause (2) of [Stacks, Tag 07MR] to the
affine case" is machine-checked rather than asserted in prose.

Two hypotheses beyond the remark's conclusion appear, and both are delimiters rather than
weakenings of anything:

* `[Finite Λ]`, which [Stacks, Tag 07MN] itself imposes ("choose a finite affine open covering")
  and which `...SmallSite.OrdCechTotalComparison` already carries.  It is not removable: with `Λ`
  infinite there are strictly increasing tuples of every length, the Čech direction of the double
  complex is unbounded, and no vanishing bound of this shape exists.
* `hlen`, that the local completed de Rham complexes `M_β ⊗̂_{D_β} Ω^*_{D_β}` vanish in degrees
  `> e`.  This is the content that clause (2) of [Stacks, Tag 07MR] carries as
  `S.toClosedFiber.HasEmbeddingDimensionLE e`: the embedding dimension bounds the number of
  generators of `P_β`, hence the rank of `Ω_{D_β}`, hence the length of the de Rham complex.  It
  is not removable either, and for the same reason — an `...SmallSite.OrdDeRhamSystem` whose
  carried complexes are unbounded gives a total complex with terms in arbitrarily high degree.
  What is *not* done here is the derivation of `hlen` from `HasEmbeddingDimensionLE`, which needs
  the envelopes `D_β` themselves (item 2 of the "What is and is not proved" section of
  `CechCoverComplex.lean`) and [Stacks, Tag 07KK] at each of them; so this file does not discharge
  clause (2) of [Stacks, Tag 07MR], it supplies the step from 07MN to it.

## References

* [Stacks Project, Tag 07MN](https://stacks.math.columbia.edu/tag/07MN)
* [Stacks Project, Tag 07MM](https://stacks.math.columbia.edu/tag/07MM)
* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {Λ : Type u} [LinearOrder Λ]

/-! ### The Čech degrees in which the double complex can be nonzero -/

/-- **A strictly increasing `(n + 1)`-tuple of indices forces `n + 1 ≤ #Λ`**, the tuple being an
injection of an `(n + 1)`-element type into `Λ`. -/
theorem OrdCechTuple.card_le [Finite Λ] {n : ℕ} (β : OrdCechTuple Λ n) :
    n + 1 ≤ Nat.card Λ := by
  simpa using Nat.card_le_card_of_injective β.1 β.2.injective

/-- **A covering with `#Λ` members has no strictly increasing tuples of length `> #Λ`**, so the
alternating Čech complex of [Stacks, Tag 07MN] has no terms in Čech degree `≥ #Λ`. -/
theorem OrdCechTuple.isEmpty_of_card_le [Finite Λ] {n : ℕ} (hn : Nat.card Λ ≤ n) :
    IsEmpty (OrdCechTuple Λ n) :=
  ⟨fun β => by have := OrdCechTuple.card_le β; omega⟩

variable {T : CechSystem S Λ} {F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}

/-- **The term `M^{n, m}` of the double complex of [Stacks, Tag 07MN] vanishes as soon as every
local de Rham term in that bidegree does**, being their product. -/
theorem isZero_ordCechTerm_of_isZero (K : OrdDeRhamSystem T F) {n m : ℕ}
    (h : ∀ β : OrdCechTuple Λ n, IsZero ((K.complex n β).X m)) :
    IsZero (ordCechTerm K n m) := by
  change IsZero (∏ᶜ fun β : OrdCechTuple Λ n => (K.complex n β).X m)
  rw [IsZero.iff_id_eq_zero]
  exact Pi.hom_ext _ _ fun β => (h β).eq_of_tgt _ _

/-- **The double complex of [Stacks, Tag 07MN] vanishes identically in Čech degrees `≥ #Λ`**: the
product defining `M^{n, m}` is then indexed by the empty type. -/
theorem isZero_ordCechTerm_of_card_le [Finite Λ] (K : OrdDeRhamSystem T F) {n : ℕ}
    (hn : Nat.card Λ ≤ n) (m : ℕ) : IsZero (ordCechTerm K n m) :=
  isZero_ordCechTerm_of_isZero K fun β => (OrdCechTuple.isEmpty_of_card_le hn).elim β

/-! ### The vanishing bound the double complex carries -/

namespace OrdCechTotalComparison

variable [Finite Λ] {K : OrdDeRhamSystem T F}
  {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}

/-- **The double complex `M^{•,•}` of [Stacks, Tag 07MN] vanishes in every bidegree of total
degree `≥ #Λ + e`**, where `e` bounds the degrees in which the local completed de Rham complexes
`M_β ⊗̂_{D_β} Ω^*_{D_β}` are nonzero.

Of the four bidegree regions, the two negative ones are the `isZero_of_neg_cech` and
`isZero_of_neg_deRham` fields; in the first quadrant a bidegree `(n, m)` of total degree
`≥ #Λ + e` has either `#Λ ≤ n`, where the Čech index type is empty
(`isZero_ordCechTerm_of_card_le`), or `e < m`, where every local de Rham term vanishes. -/
theorem isZero_X (C : OrdCechTotalComparison K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (i₁ i₂ : ℤ) (hi : (Nat.card Λ : ℤ) + e ≤ i₁ + i₂) :
    IsZero ((C.double.X i₁).X i₂) := by
  rcases lt_or_ge i₁ 0 with h₁ | h₁
  · exact C.isZero_of_neg_cech i₁ i₂ h₁
  rcases lt_or_ge i₂ 0 with h₂ | h₂
  · exact C.isZero_of_neg_deRham i₁ i₂ h₂
  lift i₁ to ℕ using h₁
  lift i₂ to ℕ using h₂
  have hi' : Nat.card Λ + e ≤ i₁ + i₂ := by exact_mod_cast hi
  refine (C.termIso i₁ i₂).isZero_iff.2 ?_
  rcases le_or_gt (Nat.card Λ) i₁ with hn | hn
  · exact isZero_ordCechTerm_of_card_le K hn i₂
  · exact isZero_ordCechTerm_of_isZero K fun β => hlen i₁ β i₂ (by omega)

/-- **The total complex of the double complex of [Stacks, Tag 07MN] vanishes in degrees
`≥ #Λ + e`**: every summand of such a term has total degree `≥ #Λ + e` and so vanishes by
`OrdCechTotalComparison.isZero_X`. -/
theorem isZero_total_X (C : OrdCechTotalComparison K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (j : ℤ) (hj : (Nat.card Λ : ℤ) + e ≤ j) :
    letI := C.hasTotal
    IsZero ((C.double.total (ComplexShape.up ℤ)).X j) := by
  let := C.hasTotal
  refine HomologicalComplex₂.isZero_total_X_of_isZero C.double (ComplexShape.up ℤ) j
    fun i₁ i₂ hπ => C.isZero_X hlen i₁ i₂ ?_
  have hπ' : i₁ + i₂ = j := hπ
  omega

/-- **Granting [Stacks, Tag 07MN], `H^i(Cris(X/S), F) = 0` for `i ≥ #Λ + e`**, where `#Λ` is the
number of members of the chosen finite affine open covering and `e` bounds the degrees in which
the local completed de Rham complexes are nonzero.

This is the conclusion clause (2) of [Stacks, Tag 07MR] asserts, and with a sharper bound: the tag
states vanishing for `q + e < i`, which `isZero_cohomologyFunctor'` derives from this. -/
theorem isZero_cohomologyFunctor (C : OrdCechTotalComparison K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (j : ℕ) (hj : Nat.card Λ + e ≤ j) :
    IsZero ((cohomologyFunctor S j).obj G) := by
  let := C.hasTotal
  refine (C.computesCohomology j).some.isZero_iff.1 ?_
  exact StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X (j : ℤ)
    (C.isZero_total_X hlen (j : ℤ) (by exact_mod_cast hj))

/-- The bound of `OrdCechTotalComparison.isZero_cohomologyFunctor` in the form clause (2) of
[Stacks, Tag 07MR] states it, with a strict inequality. -/
theorem isZero_cohomologyFunctor' (C : OrdCechTotalComparison K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (j : ℕ) (hj : Nat.card Λ + e < j) :
    IsZero ((cohomologyFunctor S j).obj G) :=
  C.isZero_cohomologyFunctor hlen j (le_of_lt hj)

end OrdCechTotalComparison

/-- **Granting [Stacks, Tag 07MN] in the form of the proposition
`...SmallSite.ComputesOrdCechCohomology`, `H^i(Cris(X/S), F) = 0` for `i ≥ #Λ + e`.** -/
theorem isZero_cohomologyFunctor_of_computesOrdCechCohomology [Finite Λ]
    {K : OrdDeRhamSystem T F} {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (h07MN : ComputesOrdCechCohomology K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (j : ℕ) (hj : Nat.card Λ + e ≤ j) :
    IsZero ((cohomologyFunctor S j).obj G) :=
  h07MN.some.isZero_cohomologyFunctor hlen j hj

/-- The bound of `isZero_cohomologyFunctor_of_computesOrdCechCohomology` with the strict
inequality clause (2) of [Stacks, Tag 07MR] uses. -/
theorem isZero_cohomologyFunctor_of_computesOrdCechCohomology' [Finite Λ]
    {K : OrdDeRhamSystem T F} {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (h07MN : ComputesOrdCechCohomology K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (j : ℕ) (hj : Nat.card Λ + e < j) :
    IsZero ((cohomologyFunctor S j).obj G) :=
  isZero_cohomologyFunctor_of_computesOrdCechCohomology h07MN hlen j (le_of_lt hj)

/-- **The vanishing of `isZero_cohomologyFunctor_of_computesOrdCechCohomology` in the
`Subsingleton (cohomology S G i)` spelling** that `...SmallSite.Vanishing07MR` and
`...SmallSite.AbelianVanishing07MR` use.  The two spellings agree by
`...SmallSite.subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections` together with
`...SmallSite.rightDerivedGlobalSectionsIso`. -/
theorem subsingleton_cohomology_of_computesOrdCechCohomology [Finite Λ]
    {K : OrdDeRhamSystem T F} {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (h07MN : ComputesOrdCechCohomology K G) {e : ℕ}
    (hlen : ∀ (n : ℕ) (β : OrdCechTuple Λ n) (m : ℕ), e < m → IsZero ((K.complex n β).X m))
    (j : ℕ) (hj : Nat.card Λ + e ≤ j) :
    Subsingleton (cohomology S G j) :=
  (subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections S G j).2
    (((rightDerivedGlobalSectionsIso S j).app G).isZero_iff.2
      (isZero_cohomologyFunctor_of_computesOrdCechCohomology h07MN hlen j hj))

/-! ### The first step of the hint, isolated -/

/-- **The replacement of `F` by `F ⊗ Ω^*_{X/S}` in the hint of [Stacks, Tag 07MN] uses nothing
about [Stacks, Tag 07LM] beyond a degreewise isomorphism of cohomology.**  The hint begins "we may
replace `F` by `F ⊗_{𝒪_{X/S}} Ω^*_{X/S}`, since `RΓ` of the two agree by [Stacks, Tag 07LM]";
granted a family of isomorphisms `H^j(Cris(X/S), G') ≅ H^j(Cris(X/S), G)`, the double complex and
both of its differentials are untouched and only the comparison of the total complex is
re-targeted.

So this measures that step: what [Stacks, Tag 07LM] has to supply for it is exactly the family
`e`, and nothing about the de Rham complexes themselves.  The vanishing clause of
[Stacks, Tag 07LM] is `...SmallSite.Vanishing07LM` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalDeRhamComplex.lean`.  It is proved, as
`...SmallSite.vanishing07LM` of `SmallSite/Vanishing07LMProof.lean`.  That does not yet give `e`,
and nothing here supplies it: the assertion of [Stacks, Tag 07LM] that the two cohomologies agree is
available only at `F = 𝒪_{X/S}`, where the de Rham complex exists, and only in the form
`...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` — an
isomorphism after `Ru_{X/S, *}` rather than the degreewise isomorphism of the groups
`H^j(Cris(X/S), −)` this theorem consumes. -/
theorem computesOrdCechCohomology_of_cohomologyIso [Finite Λ]
    {K : OrdDeRhamSystem T F} {G G' : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (h : ComputesOrdCechCohomology K G')
    (e : ∀ j : ℕ, (cohomologyFunctor S j).obj G' ≅ (cohomologyFunctor S j).obj G) :
    ComputesOrdCechCohomology K G :=
  ⟨{ h.some with
      computesCohomology := fun j => ⟨(h.some.computesCohomology j).some ≪≫ e j⟩ }⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
