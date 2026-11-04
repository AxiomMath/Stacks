module

public import StacksFrontier.Algebra.Homology.DegreewiseLeftDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules

/-!
# The terms of a complex of modules with a left dual have left duals

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules admitting a left dual
`𝒢^•` in the monoidal category of complexes of `𝒪`-modules of [Stacks, Tag 0FPQ]. Then for
every `n` the term `𝒢^{-n}` is a left dual of the term `ℱ^n` in the monoidal category of
`𝒪`-modules, with the degree-`n` components `ηₙ`, `εₙ` of the coevaluation and the evaluation
of the complexes as its pairing.

This is the degreewise reading of a dual complex, converse to the assembly of
[Stacks, Tag 0FP9] and to the termwise statement of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Duals/TermwiseDualsOfAComplexOfModules.lean`,
which starts from a local finiteness hypothesis on the terms and produces their duals.

## Main results

* `Stacks.Cohomology.MonoidalComplexesOfModules.degreewiseExactPairing`: the dual pair
  `(ℱ^n, 𝒢^{-n})` of `𝒪`-modules.
* `Stacks.Cohomology.MonoidalComplexesOfModules.degreewiseHasRightDual`: the same read as
  `CategoryTheory.HasRightDual`, which is Mathlib's spelling of "`𝒢^{-n}` is a left dual of
  `ℱ^n`".

## Implementation notes

**Which monoidal structure.** The ambient structure on `Mod(𝒪)` here is
`SheafOfModules.monoidalCategorySheafTensor`, because that is the one over which
[Stacks, Tag 0FPQ] builds the monoidal category of complexes, and the degreewise pairing of a
pairing of complexes lives in the structure the complexes are tensored with. The repository's
duality cluster for a single module — the pairings of [Stacks, Tag 0FNY] and the converse
[Stacks, Tag 0FNZ], which turns a left dual into the local finite-free-summand condition — is
instead stated for `Stacks.SheafOfModules.Strict.monoidalCategory`. The two structures have
the same tensor product on objects but no identification of their associators and unitors is
available, and `MonoidalPreadditive` is established only for the former, so the output below
does not yet feed [Stacks, Tag 0FNZ].

**No differential is involved.** The two triangle identities in degree `n` already hold for
the underlying graded objects, so the whole content is
`CochainComplex.exactPairingXApply`; the hypotheses that theorem needs of the base category
are discharged here by the instances that [Stacks, Tag 0FPQ] already provides.

## References

* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.Cohomology.MonoidalComplexesOfModules

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.monoidalPreadditiveSheafTensor SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v}) (K L : Complexes R)

/-- **The terms of a dual pair of complexes of `𝒪`-modules are a dual pair.** If `L` is a
left dual of `K` in the monoidal category of complexes, then in every degree `n` the term
`L^{-n}` is a left dual of `K^n` in `Mod(𝒪)`, with the degree-`n` components of the
coevaluation and the evaluation of `K` and `L` as its pairing. -/
@[instance_reducible]
public def degreewiseExactPairing (p : ExactPairing K L) (n : ℤ) :
    ExactPairing (K.X n) (L.X (-n)) :=
  letI := p
  CochainComplex.exactPairingXApply K L n

/-- The degreewise duals of a dual complex read as `HasRightDual`. Mathlib's `rightDual` is
the Stacks *left* dual, so this is the same assertion as `degreewiseExactPairing`. -/
@[instance_reducible]
public def degreewiseHasRightDual (p : ExactPairing K L) (n : ℤ) : HasRightDual (K.X n) where
  rightDual := L.X (-n)
  exact := degreewiseExactPairing R K L p n

end Stacks.Cohomology.MonoidalComplexesOfModules

end

end
