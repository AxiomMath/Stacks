module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Termwise duals of a complex of modules on a ringed site

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules each of whose terms is,
locally on the site, a direct summand of a finite free `𝒪`-module — the termwise half of the
hypothesis of [Stacks, Tag 0FPR], which asks that every object of `C` admit a covering
`{Uᵢ → U}` with `ℱ^•|_{Uᵢ}` strictly perfect.

[Stacks, Tag 0FPR] forms the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` and asserts that `𝒢^•`,
together with `η = ∑ ηₙ` and `ε = ∑ εₙ`, is a left dual of `ℱ^•` in the monoidal category of
complexes of `𝒪`-modules of [Stacks, Tag 0FPQ]. The `ηₙ` and `εₙ` it sums are the coevaluation
and evaluation of [Stacks, Tag 0FNY] at the term `ℱ^n`. This file supplies exactly those
degreewise pairings, for every term at once; what it does **not** supply is the passage to
complexes. That passage is now carried out — see the "Implementation notes" below, which also
retire the two obstructions this file used to record.

## Main definitions

* `Stacks.SheafOfModules.IsTermwiseLocallyDirectSummandOfFiniteFree`: every term of a complex of
  `𝒪`-modules is locally a direct summand of a finite free `𝒪`-module.

## Main results

* `Stacks.SheafOfModules.termwiseExactPairingDualSheaf`: for each `n`, the dual sheaf
  `SheafHom(ℱ^n, 𝒪)` is a left dual of `ℱ^n`, with the coevaluation `ηₙ` and evaluation `εₙ` of
  [Stacks, Tag 0FNY].
* `Stacks.SheafOfModules.termwiseHasRightDual`: the same statement read as `HasRightDual`.

## Implementation notes

**Which dual, and in which category.** Mathlib's `CategoryTheory.ExactPairing X Y` carries the
same data as [Stacks, Tag 0FFP] — a coevaluation `η : 𝟙 ⟶ X ⊗ Y` and an evaluation
`ε : Y ⊗ X ⟶ 𝟙` satisfying the two triangle identities — but names it the other way round:
Stacks says `Y` is a *left* dual of `X`, while Mathlib's `HasRightDual X` has
`rightDual X = Y`. So the Stacks assertion "`SheafHom(ℱ^n, 𝒪)` is a left dual of `ℱ^n`" is
`ExactPairing (ℱ^n) (SheafHom(ℱ^n, 𝒪))`, and that is what is stated below; `HasLeftDual` would
be the opposite direction and is not what the tag says. The ambient monoidal category is
`Stacks.SheafOfModules.Strict.monoidalCategory`, the repository's monoidal structure on
`Mod(𝒪)` for the duality cluster, in which the pairings of [Stacks, Tag 0FNY] are stated.

**The hypothesis is the minimal one.** Only the termwise condition is assumed; the boundedness
that [Stacks, Tag 0FPR] also carries is not needed for a degreewise statement, so it is not
required. [Stacks, Tag 0FPR]'s hypothesis implies the one used here.

**Why the complex-level statement is not here, and what is no longer in the way.** Two
apparent obstructions are not in the way, and what remains is only
the construction of the dual *complex* over a site.

The first is the differential. Assembling `η = ∑ ηₙ` and `ε = ∑ εₙ` out of the degreewise
pairings, and checking the two triangle identities for the sums, is available in the abstract:
`CategoryTheory.GradedObject.Monoidal.exactPairingOfDegreewise`, which carries
[Stacks, Tag 0FP9] — the ringed-space twin of [Stacks, Tag 0FPR] — does it for any graded object
of a monoidal preadditive category with bounded support. What that does not give is that `η` and
`ε` are morphisms of *complexes* rather than of graded objects, and for that one needs
the signed-transpose differential of the `ModuleCat` analogue [Stacks, Tag 0FNK], which is
proved with elements. It has a counterpart over a site:
`StacksFrontier/Algebra/Homology/AssembleLeftDual.lean` carries the whole passage element-free, for
any monoidal preadditive category with the graded-monoidal hypotheses —
`CochainComplex.coevaluationHom` and `CochainComplex.evaluationHom` for the sums,
`CochainComplex.exactPairingOfDegreewise` for the two triangle identities, and
`CochainComplex.exactPairingOfSignedTranspose` for the whole statement from the signed transpose
`d_L^{-n-1} = (-1)^n (d_K^n)ᘁ`, the convention of [Stacks, Tag 0FNK].

The second is an apparent monoidal-structure mismatch, which would block even the graded
assembly: the pairings of [Stacks, Tag 0FNY] are stated for `Strict.monoidalCategory`, over
which `MonoidalPreadditive`, the preservation of the empty colimit by the tensor, and
`HasTensor₄ObjExt` would have to be established. **They are.**
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalStrictColimits.lean` establishes exactly
those three — `Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf`,
`preservesColimit_tensorLeft`, `preservesColimit_tensorRight`, `hasGoodTensor₁₂Tensor`,
`hasGoodTensorTensor₂₃`, `hasTensor₄ObjExt` — and builds
`Stacks.SheafOfModules.Strict.monoidalCategoryCochainComplex`, the monoidal category of
complexes over the tensor product of [Stacks, Tag 01CA], on top of them. No coherence lemma
comparing associators is needed, and none is missing.

The *construction* of `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` as a complex over a site — its terms
`dualSheaf 𝒪 h𝒪 (ℱ^{-j})` and its differential the signed transpose — is no longer owed either:
it is `Stacks.SheafOfModules.Strict.dualComplex` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Duals/DualComplexOfModules.lean`, where
`Stacks.SheafOfModules.Strict.exactPairingDualComplex` assembles the sums and both triangle
identities. What is still owed for the full assertion of [Stacks, Tag 0FPR] is therefore only
the tag's own hypothesis: that statement carries a single global finite set of degrees outside
which `ℱ^•` vanishes, where the tag supplies boundedness only *locally*, so that `η = ∑ ηₙ`
has to be made sense of as a locally finite sum.

**Universes.** The module universe is forced equal to the ring universe `max u v`, as it is
throughout the [Stacks, Tag 0FNY] cluster: the internal hom of [Stacks, Tag 03EM] makes a
section of `SheafHom(ℱ, 𝒢)` over `U` a morphism of presheaves on `C/U`. This is inherited, not
imposed here.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace Stacks.SheafOfModules

attribute [local instance] Strict.monoidalCategory monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))

/-- Every term of a complex of `𝒪`-modules is locally a direct summand of a finite free
`𝒪`-module. This is the termwise half of the hypothesis of [Stacks, Tag 0FPR], which asks that
every object of the site admit a covering on which the whole complex is strictly perfect. -/
public def IsTermwiseLocallyDirectSummandOfFiniteFree
    (F : CochainComplex
      (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) ℤ) : Prop :=
  ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 (F.X n)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable (F : CochainComplex
  (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) ℤ)

/-- **[Stacks, Tag 0FPR], the degreewise pairings.** For each degree `n`, the dual sheaf
`SheafHom(ℱ^n, 𝒪)` is a left dual of the term `ℱ^n` in the monoidal category of `𝒪`-modules:
the coevaluation `ηₙ : 𝒪 ⟶ ℱ^n ⊗ SheafHom(ℱ^n, 𝒪)` and the evaluation
`εₙ : SheafHom(ℱ^n, 𝒪) ⊗ ℱ^n ⟶ 𝒪` of [Stacks, Tag 0FNY] satisfy the two triangle identities.

These are exactly the `ηₙ` and `εₙ` that [Stacks, Tag 0FPR] sums to form `η` and `ε`. -/
@[stacks 0FPR "the degreewise pairings only: for each n the dual sheaf `SheafHom(ℱⁿ, 𝒪)` is a \
left dual of the term `ℱⁿ`, with the coevaluation ηₙ and evaluation εₙ of Tag 0FNY, in the \
monoidal category of 𝒪-modules `Strict.monoidalCategory`. NOT the assertion of the tag, which \
is about the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)`: neither the sums η = ∑ ηₙ and ε = ∑ εₙ, nor \
the triangle identities for them, nor the left-dual property of `𝒢^•` in the monoidal category \
of complexes of Tag 0FPQ, is proved here. Those three are proved over a site by \
`Stacks.SheafOfModules.Strict.dualComplex` and \
`Stacks.SheafOfModules.Strict.exactPairingDualComplex`, for a complex of globally bounded \
support. The construction of `𝒢^•` is available under the tag's own hypothesis, that every \
object has a covering on which `ℱ^•` is strictly perfect, as \
`Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect`, and the left-dual assertion \
under that hypothesis is \
`Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect`. See the \
module's Implementation notes",
  instance_reducible]
public def termwiseExactPairingDualSheaf
    (hF : IsTermwiseLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) (n : ℤ) :
    ExactPairing (F.X n) (dualSheaf 𝒪 h𝒪 (F.X n)) :=
  exactPairingDualSheafOfLocalSummand 𝒪 h𝒪 (F.X n) (hF n)

/-- The termwise duals of [Stacks, Tag 0FPR] read as `HasRightDual`. Mathlib's `rightDual` is
the Stacks *left* dual, so this is the same assertion as `termwiseExactPairingDualSheaf`. -/
@[instance_reducible]
public def termwiseHasRightDual
    (hF : IsTermwiseLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F) (n : ℤ) :
    HasRightDual (F.X n) where
  rightDual := dualSheaf 𝒪 h𝒪 (F.X n)
  exact := termwiseExactPairingDualSheaf 𝒪 h𝒪 F hF n

end Stacks.SheafOfModules

end

end
