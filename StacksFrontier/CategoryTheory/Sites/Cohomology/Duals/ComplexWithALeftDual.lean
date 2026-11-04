module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LeftDualOfALocallyStrictlyPerfectComplex
import StacksCore.Tactic.StacksAttribute

/-!
# A complex of modules with a left dual

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules admitting a left dual
`𝒢^•` in the monoidal category of complexes of `𝒪`-modules, the tensor product being the total
complex of the tensor product of [Stacks, Tag 01CA]. This file assembles the three assertions of
[Stacks, Tag 0FPA] into one statement:

1. `ℱ^•` is locally bounded;
2. every term `ℱ^n` is locally a direct summand of a finite free `𝒪`-module;
3. the given left dual *is* the one constructed in [Stacks, Tag 0FP9] — there is an isomorphism
   of `𝒢^•` with `SheafHom^•(ℱ^•, 𝒪)` carrying `η` to `η = ∑ ηₙ` and `ε = ∑ εₙ`.

The three are proved under one hypothesis, exactly the tag's: that `ℱ^•` has a left dual. In
particular neither boundedness nor strict perfectness is assumed; both are conclusions.

## Main results

* `isLocallyStrictlyPerfect_of_exactPairing`: [Stacks, Tag 0FPS], local strict perfectness of a
  complex with a left dual.
* `isLocallyBounded_and_isLocallyDirectSummand_and_isoDualComplex_of_exactPairing`: **[Stacks, Tag
  0FPA]**, all three assertions.
* `isLocallyStrictlyPerfect_and_isoDualComplex_of_exactPairing`: **[Stacks, Tag 0FPS]**, local
  strict perfectness of `ℱ^•` together with the identification of the given dual and its pairings.

## Implementation notes

**Why a ringed site.** [Stacks, Tag 0FPA] is stated for a ringed space `(X, 𝒪_X)` and
[Stacks, Tag 0FPS] is its verbatim analogue for a ringed site `(C, 𝒪)`; the statement below is
the site one, which specializes to the space one by reading a covering of an open as a
neighbourhood of each of its points.

**What assertion (3) asserts.** The complex of [Stacks, Tag 0FP9] is `𝒢₀^• = SheafHom^•(ℱ^•, 𝒪)`,
namely `Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect`: the dual sheaves of
[Stacks, Tag 0FNY] as terms, the signed transpose as differential, and the pairings `η₀ = ∑ ηₙ` and
`ε₀ = ∑ εₙ` of [Stacks, Tag 0FPR]. The isomorphism `e` of assertion (3) satisfies
`η ≫ ℱ^• ◁ e = η₀` and `e ▷ ℱ^• ≫ ε₀ = ε`, so it identifies the triple `(𝒢^•, η, ε)` with
`(𝒢₀^•, η₀, ε₀)`, not merely the underlying complexes.

## References

* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
* [Stacks Project, Tag 0FPS](https://stacks.math.columbia.edu/tag/0FPS)
* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FFR](https://stacks.math.columbia.edu/tag/0FFR)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v}) (K L : CochainComplex (Mod R) ℤ)

/-- **[Stacks, Tag 0FPS]**. A complex of `𝒪`-modules with a left dual is locally strictly perfect:
every object of the site has a covering sieve on whose members `ℱ^•` is strictly perfect. -/
theorem isLocallyStrictlyPerfect_of_exactPairing
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) :
    IsLocallyStrictlyPerfect R K :=
  fun U => exists_cover_isStrictlyPerfect_of_exactPairing R K L p U

/-- **[Stacks, Tag 0FPA].** Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of
`𝒪`-modules. If `ℱ^•` has a left dual `𝒢^•` in the monoidal category of complexes of
`𝒪`-modules, then all three of the following hold.

1. `ℱ^•` is locally bounded: every object of the site has a covering sieve on whose members all
   but finitely many terms of `ℱ^•` restrict to zero, the finite set of surviving degrees
   depending on the member.
2. Every term `ℱ^n` is locally a direct summand of a finite free `𝒪`-module.
3. The left dual is the one constructed in [Stacks, Tag 0FP9]: `𝒢^•` is isomorphic to the complex
   `SheafHom^•(ℱ^•, 𝒪)` of [Stacks, Tag 0FPR] by an isomorphism carrying the coevaluation and the
   evaluation of the given pairing to `η = ∑ ηₙ` and `ε = ∑ εₙ`. -/
@[stacks 0FPA "the WHOLE statement of the tag under the tag's OWN hypothesis, for a ringed site \
— of which the ringed space of the tag is a case — and over the monoidal structure on complexes \
of 𝒪-modules whose tensor product is the one of Tag 01CA: a complex `ℱ^•` with a left dual \
`𝒢^•` is (1) locally bounded, (2) has every term a local direct summand of a finite free module, \
and (3) has `𝒢^•` the complex of Example 0FP9, namely `SheafHom^•(ℱ^•, 𝒪)` — \
`Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect`, the dual sheaves of Tag 0FNY \
in the opposite degrees with the signed-transpose differential — together WITH its pairings: the \
isomorphism carries η and ε to the η = ∑ ηₙ and ε = ∑ εₙ that Tag 0FPR puts on that complex, so \
the triple `(𝒢^•, η, ε)` is identified with Example 0FP9's triple and not merely the underlying \
complexes. (3) is uniqueness of left duals (Tag 0FFR, `CategoryTheory.rightDualIso`) applied to \
the left dual Tag 0FPR builds from the local strict perfectness of Tag 0FPS, which (1) and (2) \
supply. The site-level analogue of the whole tag is Tag 0FPS, \
`Stacks.SheafOfModules.Strict.exists_cover_isStrictlyPerfect_of_exactPairing` for its first \
assertion"]
theorem isLocallyBounded_and_isLocallyDirectSummand_and_isoDualComplex_of_exactPairing
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) :
    letI := monoidalCategoryCochainComplex R
    letI := p
    letI := exactPairingDualComplexOfLocallyStrictlyPerfect
      (isLocallyStrictlyPerfect_of_exactPairing R K L p)
    (∀ U : C, ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), T g →
        ∃ S : Finset ℤ, ∀ n ∉ S, IsZero ((K.X n).over V)) ∧
      (∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) ∧
      ∃ e : L ≅ dualComplexOfLocallyStrictlyPerfect R K
          (isLocallyStrictlyPerfect_of_exactPairing R K L p),
        η_ K L ≫ K ◁ e.hom =
            η_ K (dualComplexOfLocallyStrictlyPerfect R K
              (isLocallyStrictlyPerfect_of_exactPairing R K L p)) ∧
          e.hom ▷ K ≫ ε_ K (dualComplexOfLocallyStrictlyPerfect R K
              (isLocallyStrictlyPerfect_of_exactPairing R K L p)) = ε_ K L := by
  let := monoidalCategoryCochainComplex R
  let := p
  let := exactPairingDualComplexOfLocallyStrictlyPerfect
    (isLocallyStrictlyPerfect_of_exactPairing R K L p)
  refine ⟨fun U => isLocallyBounded_of_exactPairing R K L p U,
    fun n => isLocallyDirectSummandOfFiniteFree_X R K L p n,
    rightDualIso p (exactPairingDualComplexOfLocallyStrictlyPerfect
      (isLocallyStrictlyPerfect_of_exactPairing R K L p)), ?_, ?_⟩
  · have h := @coevaluation_comp_rightAdjointMate _ _ _ K K
      ⟨dualComplexOfLocallyStrictlyPerfect R K
        (isLocallyStrictlyPerfect_of_exactPairing R K L p)⟩ ⟨L⟩ (𝟙 K)
    rw [MonoidalCategory.id_whiskerRight, Category.comp_id] at h
    simpa [rightDualIso] using h
  · have h := @rightAdjointMate_comp_evaluation _ _ _ K K
      ⟨dualComplexOfLocallyStrictlyPerfect R K
        (isLocallyStrictlyPerfect_of_exactPairing R K L p)⟩ ⟨L⟩ (𝟙 K)
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp] at h
    simpa [rightDualIso] using h

/-- **[Stacks, Tag 0FPS]**. Let `(C, 𝒪)` be a ringed site and `ℱ^•` a complex of `𝒪`-modules with a
left dual `𝒢^•` in the monoidal category of complexes of `𝒪`-modules. Then every object of the site
has a covering on whose members `ℱ^•` is strictly perfect, and the left dual is the complex of
[Stacks, Tag 0FPR] together with its pairings. -/
@[stacks 0FPS "the WHOLE tag, under the tag's OWN hypothesis that `ℱ^•` has a left dual `𝒢^•` \
in the monoidal category of complexes of 𝒪-modules of Tag 0FPQ, whose tensor product is the one \
of Tag 01CA. Both conclusions: every object of the site has a covering on whose members `ℱ^•` is \
strictly perfect in the sense of Tag 08FL — the witness \
`Stacks.SheafOfModules.Strict.IsLocallyStrictlyPerfect`, unfolding to the covering sieve and \
`IsStrictlyPerfect` of the restricted complex — and `𝒢^•` is the left dual of Example 0FPR with \
its pairings: it is isomorphic to \
`Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect`, the complex \
`SheafHom^•(ℱ^•, 𝒪)`, by an isomorphism matching the coevaluation and the evaluation of the \
given pairing with those of \
`Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect`, the η = ∑ ηₙ and \
ε = ∑ εₙ of that example — which is uniqueness of left duals (Tag 0FFR)"]
theorem isLocallyStrictlyPerfect_and_isoDualComplex_of_exactPairing
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) :
    letI := monoidalCategoryCochainComplex R
    letI := p
    letI := exactPairingDualComplexOfLocallyStrictlyPerfect
      (isLocallyStrictlyPerfect_of_exactPairing R K L p)
    IsLocallyStrictlyPerfect R K ∧
      ∃ e : L ≅ dualComplexOfLocallyStrictlyPerfect R K
          (isLocallyStrictlyPerfect_of_exactPairing R K L p),
        η_ K L ≫ K ◁ e.hom =
            η_ K (dualComplexOfLocallyStrictlyPerfect R K
              (isLocallyStrictlyPerfect_of_exactPairing R K L p)) ∧
          e.hom ▷ K ≫ ε_ K (dualComplexOfLocallyStrictlyPerfect R K
              (isLocallyStrictlyPerfect_of_exactPairing R K L p)) = ε_ K L :=
  ⟨isLocallyStrictlyPerfect_of_exactPairing R K L p,
    (isLocallyBounded_and_isLocallyDirectSummand_and_isoDualComplex_of_exactPairing
      R K L p).2.2⟩

end Stacks.SheafOfModules.Strict

end

end
