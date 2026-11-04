module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal

/-!
# Stacks 0AHJ: monomorphisms and representability read off the higher diagonals

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. Following the indexing convention of Stacks 04YX — `Δ_{f,0} = f`,
`Δ_{f,1} = Δ_f` and `Δ_{f,2} = Δ_{Δ_f}`, so that the index counts how many times the diagonal is
taken — write

`Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`,  `Δ_{f,2} : 𝒳 ⟶ 𝒳 ×_{Δ_{f,1}, 𝒳 ×_𝒴 𝒳, Δ_{f,1}} 𝒳`

for the first and second relative diagonals. **Stacks 0AHJ** asserts three things:

1. `f` is a monomorphism if and only if `Δ_{f,1}` is an isomorphism;
2. `f` is representable by algebraic spaces if and only if `Δ_{f,1}` is a monomorphism;
3. moreover, `Δ_{f,2}` is always a monomorphism.

All three are proved below.

The proof is the source's reassembly of three cited results and nothing more. Clause (1) is
Stacks 04ZZ: a 1-morphism is a monomorphism exactly when it is fully faithful, and by Stacks 04Z7
full faithfulness is exactly the diagonal being an equivalence. Clause (2) in the direction
"representable ⟹ `Δ_{f,1}` a monomorphism" is part (3) of Stacks 04YQ; in the converse direction
monomorphy of `Δ_{f,1}` gives, by Stacks 05UK, that `Δ_{f,1}` is full, hence — this is the step
that factors through clause (2) of Stacks 04YY, that `Δ_{f,2}` is an isomorphism — that `f` is
faithful, and faithfulness is representability by Stacks 04Y5. Clause (3) is clause (2) in the
first direction applied to `Δ_{f,1}`, which is representable by algebraic spaces unconditionally
by part (1) of Stacks 04XS.

## Main results

All four live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isMonomorphism_iff_isEquivalence_relativeDiagonal`: **Stacks 0AHJ**, part (1).
* `isRepresentableByAlgebraicSpaces_iff_isMonomorphism_relativeDiagonal`: **Stacks 0AHJ**,
  part (2).
* `isMonomorphism_secondRelativeDiagonal`: **Stacks 0AHJ**, the final assertion that `Δ_{f,2}`
  is always a monomorphism.
* `isMonomorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`: the easy direction of
  part (2), i.e. part (3) of Stacks 04YQ repackaged as monomorphy in the sense of Stacks 04ZW;
  it is what the final assertion is applied to.

## Implementation notes

"Monomorphism" is `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` (**Stacks 04ZW**), the
library's one notion: representability by algebraic spaces together with monomorphy of every
algebraic space representing a base change along a scheme-valued point of the target.
"Representable by algebraic spaces" is `AlgebraicGeometry.IsRepresentableByAlgebraicSpaces`, and
"isomorphism of algebraic stacks" is `CategoryTheory.Functor.IsEquivalence` of the underlying
functor, exactly as in `StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalRepresentable`. The
two diagonals are `AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`, so the second is
literally the first applied twice; this is the spelling of
`StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalSeparation`, the library's Stacks 04YZ.

The reverse directions of parts (1) and (2) pass through the implication (2) ⟹ (3) of
**Stacks 04Y5** (faithfulness implies representability by algebraic spaces),
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`,
at the one 1-morphism `f` under discussion. For part (1) it is needed only because
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` has representability as a conjunct: the
monomorphy clause itself follows from full faithfulness by
`AlgebraicGeometry.Stack.mono_representingMaps_of_full_and_faithful`. The forward directions are
`isMonomorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces` above and, for part (1),
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`.

Monomorphy of a representing algebraic space is read in the category of algebraic spaces by
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` and in the category of presheaves by
Stacks 05UK; the two are exchanged by `AlgebraicGeometry.Space.mono_hom_iff_mono`, parts (1) and
(2) of Stacks 042M.

## References

* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YX](https://stacks.math.columbia.edu/tag/04YX)
* [Stacks Project, Tag 04YY](https://stacks.math.columbia.edu/tag/04YY)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 0AHJ](https://stacks.math.columbia.edu/tag/0AHJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A monomorphism of algebraic stacks has a full and faithful underlying functor. -/
private theorem full_and_faithful_of_isMonomorphism (g : 𝒳 ⟶ 𝒴) (hm : IsMonomorphism B S hS g) :
    (CatFiberedInGroupoids.homFunctor g.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor g.hom).Faithful :=
  Stack.full_and_faithful_homFunctor_of_mono_representingMaps B S hS g.hom hm.1
    fun U y hy F hF he => (Space.mono_hom_iff_mono B S hS _).2 (hm.2 U y hy F hF he)

/-- **The easy direction of part (2) of Stacks 0AHJ.** The first relative diagonal `Δ_{f,1}` of a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is representable by algebraic spaces is
a monomorphism in the sense of Stacks 04ZW.

This is part (3) of Stacks 04YQ, repackaged: that lemma supplies the representability conjunct —
part (1) of Stacks 04XS — and the monomorphy clause, and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` is their conjunction. -/
theorem isMonomorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsMonomorphism B S hS (relativeDiagonalAlgebraicStacks B S hS f) :=
  let ⟨hΔ, hmono⟩ :=
    Stack.mono_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f hf
  ⟨hΔ, hmono⟩

/-- **Stacks 0AHJ, part (1).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a
monomorphism (Stacks 04ZW) if and only if its first relative diagonal `Δ_{f,1}` is an isomorphism,
i.e. has underlying functor an equivalence of categories.

Both directions pass through full faithfulness of `f`: Stacks 04Z7 says `Δ_{f,1}` is an
equivalence exactly when `f` is fully faithful, Stacks 05UK turns the monomorphy clause into full
faithfulness, and Stacks 04ZZ turns full faithfulness back into the monomorphy clause.

The representability conjunct of `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` in
the "if" direction is the implication (2) ⟹ (3) of **Stacks 04Y5** at `f`. -/
@[stacks 0AHJ "part (1)"]
theorem isMonomorphism_iff_isEquivalence_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsMonomorphism B S hS f ↔
      Functor.IsEquivalence
        (CatFiberedInGroupoids.homFunctor (relativeDiagonalAlgebraicStacks B S hS f).hom) := by
  have hdiag := TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  refine ⟨fun hm => ?_, fun h => ?_⟩
  · exact hdiag.1 (full_and_faithful_of_isMonomorphism B S hS f hm)
  · exact isMonomorphism_of_full_and_faithful B S hS f (hdiag.2 h).1 (hdiag.2 h).2

/-- **Stacks 0AHJ, part (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is
representable by algebraic spaces if and only if its first relative diagonal `Δ_{f,1}` is a
monomorphism (Stacks 04ZW).

The "only if" direction is part (3) of Stacks 04YQ. For the converse, Stacks 05UK makes `Δ_{f,1}`
full, which by Stacks 04Z7 — the content clause (2) of Stacks 04YY reads as `Δ_{f,2}` being an
isomorphism — makes `f` faithful, and faithfulness is representability by Stacks 04Y5.

That last step, the implication (2) ⟹ (3) of **Stacks 04Y5** at `f`, is
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`. -/
@[stacks 0AHJ "part (2)"]
theorem isRepresentableByAlgebraicSpaces_iff_isMonomorphism_relativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ↔
      IsMonomorphism B S hS (relativeDiagonalAlgebraicStacks B S hS f) := by
  refine ⟨isMonomorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f,
    fun hm => isRepresentableByAlgebraicSpaces_of_faithful B S hS f ?_⟩
  exact TwoFibreProductOver.faithful_of_full_diagonal
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (full_and_faithful_of_isMonomorphism B S hS _ hm).1

/-- **Stacks 0AHJ, the final assertion.** The second relative diagonal `Δ_{f,2}` of any
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a monomorphism (Stacks 04ZW). No
hypothesis on `f` is needed.

This is the "only if" direction of part (2) applied to `Δ_{f,1}`, which is representable by
algebraic spaces unconditionally by part (1) of Stacks 04XS. -/
@[stacks 0AHJ "the second diagonal is always a monomorphism"]
theorem isMonomorphism_secondRelativeDiagonal (f : 𝒳 ⟶ 𝒴) :
    IsMonomorphism B S hS
      (relativeDiagonalAlgebraicStacks B S hS (relativeDiagonalAlgebraicStacks B S hS f)) :=
  isMonomorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS
    (relativeDiagonalAlgebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
