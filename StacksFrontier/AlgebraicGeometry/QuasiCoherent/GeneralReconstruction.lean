module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ModuleSupportComplement
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlobalForm
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGluedFunctor
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionLocalForm
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionMatchedPair
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionRestrictionSquare
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionTargetAffine

/-!
# Gabriel–Rosenberg reconstruction on a quasi-compact quasi-separated scheme

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Given

* an affine open `U ⊆ X`, and
* a finitely presented quasi-coherent `𝒪_X`-module `G` whose support is the complement of `U`,

the modules collected here produce the quasi-compact open `V ⊆ Y` complementary to the support of
`e.functor.obj G`, show that `V` is affine, and produce an isomorphism of schemes `f_U : V ≅ U`
together with an invertible `𝒪_V`-module `L_U` such that the equivalence induced by `e` on the
two restrictions is inverse image along `f_U` followed by `- ⊗_{𝒪_V} L_U`.  For an affine open
cover of `X` the opens so produced cover `Y`, and the local functors glue to a single functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.supportSet` — the set of points at which the stalk of a sheaf of modules is
  nonzero, in the spelling `AlgebraicGeometry.IsSupportedOn` uses.
* `AlgebraicGeometry.supportComplement` — its open complement, for a module of finite type.

## Main results

* `AlgebraicGeometry.isCompact_compl_supportSet` — the complement of the support of a finitely
  presented quasi-coherent module on a quasi-compact scheme is quasi-compact.
* `AlgebraicGeometry.quasicoherentSupportedOn_supportSet_correspondence` — for a finitely
  presented quasi-coherent `G`, the equivalence `e` matches the modules supported on the support
  of `G` with those supported on the support of `e.functor.obj G` ([Stacks, Tag 0GPG]).
* `AlgebraicGeometry.exists_isEquivalence_restrictionSquare` — for quasi-compact opens `U` and
  `V` whose complements are matched by `e`, an equivalence `QCoh(𝒪_U) ≌ QCoh(𝒪_V)` commuting
  with the two restrictions.
* `AlgebraicGeometry.isAffine_of_supportedCorrespondence` — in that situation, `V` is affine if
  `U` is.
* `AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_supportedCorrespondence` — for such a
  matched pair `(U, V)` with `U` affine, the isomorphism `f_U : V ≅ U` and the invertible module
  `L_U` above.
* `AlgebraicGeometry.exists_isAffineOpen_schemeIso_invertibleSheaf_of_isFinitePresentation` —
  the same with only `U` and `G` given, `V` being produced.
* `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isFinitePresentation` — for
  an affine open cover `U i` of `X`, the produced opens `V i` are affine and cover `Y`, and each
  carries the pair `(f_i, L_i)`.
* `AlgebraicGeometry.exists_gluedQuasicoherentFunctor_restrictIso` — the covering hypothesis `hU`
  of `AlgebraicGeometry.ReconstructionGlue.gluedQuasicoherentFunctor` discharged, so the local
  functors glue to a single functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.

## Implementation notes

This file declares nothing and only re-exports the modules above, which are kept separate so
that each elaborates within the budget.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.3 (Tag 0GPG)](https://stacks.math.columbia.edu/tag/0GPG)
* [Stacks Project, Lemma 56.6.4 (Tag 0GPH)](https://stacks.math.columbia.edu/tag/0GPH)
* [Stacks Project, Lemma 56.6.5 (Tag 0GPI)](https://stacks.math.columbia.edu/tag/0GPI)
* [Stacks Project, Lemma 28.25.1 (Tag 01PH)](https://stacks.math.columbia.edu/tag/01PH)
-/

