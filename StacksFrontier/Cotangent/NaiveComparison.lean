module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Homology.DoubleExtend

/-!
# Comparison of the cotangent complex with the naive cotangent complex

For a commutative `A`-algebra `B`, the truncation `τ_{≥ -1} L_{B/A}` of the cotangent complex is
canonically quasi-isomorphic to the naive cotangent complex `NL_{B/A}`, the two-term complex
`I/I² → Ω_{A[B]⁄A} ⊗_{A[B]} B` attached to the canonical polynomial presentation `A[B] → B`.
This file proves the degree-zero part of that comparison, and builds the two-term complex
`NL(P → B)` attached to an arbitrary presentation `P → B`, which is the source of the
comparison map.

## Main definitions

* `CommAlgCat.naiveExtension`: the canonical polynomial presentation `A[B] → B`, as an
  `Algebra.Extension`; its `Algebra.Extension.cotangentComplex` is `NL_{B/A}`.
* `CommAlgCat.naiveHomologyZero`: the degree-zero cohomology of `NL_{B/A}`, the cokernel of its
  differential.
* `Algebra.Extension.naiveComplex`: the complex `NL(P → B)` of a presentation `P → B`.
* `Algebra.Extension.naiveComplexXNegOneIso` and `Algebra.Extension.naiveComplexXZeroIso`:
  its two nonzero terms are `J/J²` and `Ω[P⁄A] ⊗[P] B`.

## Main results

* `CommAlgCat.naiveHomologyZeroIso`: `H⁰(NL_{B/A}) = Ω[B⁄A]`.
* `CommAlgCat.cotangentComplexHomologyZeroIsoNaive`: the degree-zero clause of Tag 08RB,
  `H⁰(L_{B/A}) = H⁰(NL_{B/A})`.
* `Algebra.Extension.naiveComplex_d`: the differential of `NL(P → B)` is
  `Algebra.Extension.cotangentComplex`.
* `Algebra.Extension.isZero_naiveComplex_X`: `NL(P → B)` vanishes outside degrees `-1` and `0`.

## Implementation notes

For the degree-zero comparison both sides are pinned by named canonical maps, not merely
asserted to be isomorphic. On the cotangent side the identification with `Ω[B⁄A]` is
`CommAlgCat.cotangentComplex_homologyZeroIso` (Tag 08QF), whose inverse is the derivation
`b ↦ [1 ⊗ d [b]]` and whose forward map is the augmentation of the standard resolution. On the
naive side it is induced by `Algebra.Extension.toKaehler`, using that `toKaehler` is surjective
and that its kernel is the image of the differential of `NL_{B/A}`.

A presentation is Mathlib's `Algebra.Extension A B`; its `Cotangent` is `J/J²` as a `B`-module,
its `CotangentSpace` is `Ω[P⁄A] ⊗[P] B`, and its `cotangentComplex` is the differential. The
complex `NL(P → B)` is Mathlib's two-term `HomologicalComplex.double` for the relation `1 ⟶ 0`
of `ComplexShape.down ℕ`, reindexed into cohomological degrees by
`ComplexShape.embeddingDownNat`, so that simplicial degree `n` sits in cohomological degree
`-n`; this is the same reindexing the cotangent complex uses.

### What this file does not prove about 08RB

The tag asserts that the *canonical comparison map* `c : NL_{B/A} → τ_{≥ -1} L_{B/A}` of Tag
08R7 is a quasi-isomorphism. That map is `Stacks.Cotangent.comparisonAtNaive` of
`StacksFrontier/Cotangent/NaiveComparisonMap.lean`, the map of Tag 08R9 at the object
`A[B] → B`; what is not proved here is that it is a quasi-isomorphism. The missing clause is
degree `-1`.

The *modules* there are known to agree:
`Stacks.Cotangent.cotangentComplexHomologyNegOneIsoH1Cotangent` of
`StacksFrontier/Cotangent/CotangentComplexHomologyNegOne.lean` proves
`H^{-1}(L_{B/A}) = Algebra.H1Cotangent A B = H¹(NL_{B/A})` for every ring map `A → B`. It does
not go through the source's argument — the transitivity triangle of `A → A[B] → B` together
with Tag 08RA, of which the triangle (Tag 08QX) is in
`StacksFrontier/Cotangent/Triangle/Fundamental.lean` only under two carried hypotheses — but
through the two long exact sequences of Remark 09D5, so the isomorphism it produces is a
connecting homomorphism, which is not identified with the one `c` induces.

That `c` does induce an isomorphism in degree `-1` is, however, proved:
`Stacks.Cotangent.isIso_homologyMap_evalCone_conormalExtension` of
`StacksFrontier/Cotangent/NaiveComparisonQuasiIso.lean`. What is still missing for Tag 08RB is the
passage from that to `c` itself: `IsIso (HomologicalComplex.homologyMap (evalCone …) 0)`, after
which `cone (evalCone …)` has no cohomology in degrees `≥ -2` — the degrees `≥ 1` being free by
`Stacks.Cotangent.isZero_cotangentCone_X_one` and `Algebra.Extension.isZero_naiveComplex_X`, and
degree `-2` needing the vanishing of `H^{-2}(cone(d))`, which
`Stacks.Cotangent.isIso_homologyMap_conormalToCotangentComplex` supplies — and
`CategoryTheory.Triangulated.TStructure.isIso₂_truncGE_map_of_isLE`, already used for
`Stacks.Cotangent.truncGEConeIso`, makes `τ_{≥ -1}` of `Q (evalCone …)` an isomorphism.

## References

* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 08R9](https://stacks.math.columbia.edu/tag/08R9)
* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF)
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The canonical polynomial presentation `A[B] → B`, as an extension. Its cotangent complex
`Algebra.Extension.cotangentComplex`, that is `I/I² → Ω_{A[B]⁄A} ⊗_{A[B]} B`, is the naive
cotangent complex `NL_{B/A}` of the source. -/
noncomputable abbrev naiveExtension : Algebra.Extension A ↥B :=
  (Algebra.Generators.self A ↥B).toExtension

/-- The degree-zero cohomology of the naive cotangent complex: the cokernel of
`I/I² → Ω_{A[B]⁄A} ⊗_{A[B]} B`. -/
noncomputable abbrev naiveHomologyZero :=
  (naiveExtension A B).CotangentSpace ⧸ LinearMap.range (naiveExtension A B).cotangentComplex

/-- The degree-zero cohomology of the naive cotangent complex is `Ω[B⁄A]`, by the surjectivity of
`Algebra.Extension.toKaehler` and the exactness of `NL_{B/A}` at its right-hand term. -/
noncomputable def naiveHomologyZeroIso : naiveHomologyZero A B ≃ₗ[↥B] Ω[↥B⁄A] :=
  (Submodule.quotEquivOfEq _ _
      (LinearMap.exact_iff.mp Algebra.Extension.exact_cotangentComplex_toKaehler).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ Algebra.Extension.toKaehler_surjective)

/-- **Stacks 08RB, degree zero.** The degree-zero cohomology of the cotangent complex `L_{B/A}`
agrees with the degree-zero cohomology of the naive cotangent complex `NL_{B/A}`; both are
`Ω[B⁄A]`, by the augmentation of the standard resolution on one side and by
`Algebra.Extension.toKaehler` on the other. -/
@[stacks 08RB "degree zero: H⁰(L_{B/A}) = H⁰(NL_{B/A})"]
noncomputable def cotangentComplexHomologyZeroIsoNaive :
    (cotangentComplex A B).homology 0 ≅ ModuleCat.of ↥B (naiveHomologyZero A B) :=
  cotangentComplex_homologyZeroIso A B ≪≫ (naiveHomologyZeroIso A B).symm.toModuleIso

end CommAlgCat

namespace Algebra.Extension

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (P : Extension.{v} R S)

/-- **Stacks Project, Tag 08R9 (the source of the displayed map).**

The naive cotangent complex `NL(P → B) : J/J² ⟶ Ω[P⁄A] ⊗[P] B` of a presentation, in
cohomological degrees `-1` and `0`. -/
@[stacks 08R9 "the source complex (J/J² → Ω_{P/A} ⊗_P B) of the displayed map, for a
presentation P → B, in cohomological degrees -1 and 0"]
public noncomputable def naiveComplex : CochainComplex (ModuleCat.{v} S) ℤ :=
  (HomologicalComplex.double (ModuleCat.ofHom P.cotangentComplex)
      ComplexShape.downNatRelOneZero).extend ComplexShape.embeddingDownNat

/-- In cohomological degree `-1` the naive cotangent complex of a presentation is `J/J²`. -/
public noncomputable def naiveComplexXNegOneIso :
    (naiveComplex P).X (-1) ≅ ModuleCat.of S P.Cotangent :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := 1) (by simp) ≪≫
    HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero

/-- In cohomological degree `0` the naive cotangent complex of a presentation is
`Ω[P⁄A] ⊗[P] B`. -/
public noncomputable def naiveComplexXZeroIso :
    (naiveComplex P).X 0 ≅ ModuleCat.of S P.CotangentSpace :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := 0) (by simp) ≪≫
    HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero one_ne_zero

/-- The differential of the naive cotangent complex of a presentation is
`Algebra.Extension.cotangentComplex`. -/
public theorem naiveComplex_d :
    (naiveComplex P).d (-1) 0 = (naiveComplexXNegOneIso P).hom ≫
      ModuleCat.ofHom P.cotangentComplex ≫ (naiveComplexXZeroIso P).inv := by
  have hext : (naiveComplex P).d (-1) 0 = _ :=
    HomologicalComplex.extend_d_eq
      (HomologicalComplex.double (ModuleCat.ofHom P.cotangentComplex)
        ComplexShape.downNatRelOneZero)
      ComplexShape.embeddingDownNat (i := 1) (j := 0) (by simp) (by simp)
  rw [hext, HomologicalComplex.double_d _ ComplexShape.downNatRelOneZero one_ne_zero]
  rfl

/-- The naive cotangent complex of a presentation vanishes outside cohomological degrees `-1`
and `0`. -/
public theorem isZero_naiveComplex_X (n : ℤ) (hn : n ≠ -1) (hn' : n ≠ 0) :
    IsZero ((naiveComplex P).X n) := by
  by_cases hmem : ∃ m : ℕ, ComplexShape.embeddingDownNat.f m = n
  · obtain ⟨m, rfl⟩ := hmem
    refine (HomologicalComplex.isZero_double_X (ModuleCat.ofHom P.cotangentComplex)
      ComplexShape.downNatRelOneZero m ?_ ?_).of_iso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := m) rfl)
    · rintro rfl
      exact hn (by simp)
    · rintro rfl
      exact hn' (by simp)
  · exact HomologicalComplex.isZero_extend_X _ _ n (by tauto)

end Algebra.Extension

end
