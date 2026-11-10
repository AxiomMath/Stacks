module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonCompSheafTensor
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraidingGlue
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerInvLaw
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The source comparison of Tag 0B3V's base-change square for the conormal isomorphism

`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChange` reduces the base-change
clause of Tag 0B3V for the conormal isomorphism to three hypotheses of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_source`, the first of which
is an identification

`Φ : h^*((π^*\ker q) ⊗ 𝒪_{𝐏(ℰ)}(-1)) ⟶ (π'^*\ker q') ⊗ 𝒪_{𝐏(ℰ')}(-1)`

of the sources of the two untwisted tautological maps, where `h` is the base-change morphism of
the two bundles. **This file constructs it**, as an isomorphism, with no hypothesis beyond the
base-change data `g`, `hE`, `Q`, `Q'`, `hL`, `hq` that Tag 0B3V's statement already carries.

The construction is the tensor product of the two comparisons of the factors, taken after Tag
01CD's identification of the pullback of a tensor product:

* on the first factor, the square `h ≫ π = π' ≫ g` identifies `h^*π^*(\ker q)` with
  `π'^*g^*(\ker q)`, and `Stacks.Divisors.quotientKernelBaseChange` identifies `g^*(\ker q)`
  with `\ker q'`;
* on the second factor, `Stacks.RelativeProj.symTwistBaseChangeIso` identifies `h^*𝒪(1)` with
  `𝒪'(1)`, and `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` carries that
  to an identification of `h^*𝒪(-1)` with `𝒪'(-1)`.

## Main definitions

* `Stacks.ProjectiveBundleConormal.schemePullbackCompNatIso`,
  `schemePullbackCompIso`: **the identification `f^*j^* ≅ i^*k^*` of a commuting square of
  schemes, at the scheme spelling of the pullback of modules.**
  `Stacks.ClosedImmersion.pullbackCompIso` is the same identification at the modules of the
  underlying ringed spaces; the two are definitionally equal, but the objects
  are not interchangeable inside a `⊗`, so the kernel factor of `Φ` is built from this one.
* `Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso`: `h^*π^*(\ker q) ≅ π'^*(\ker q')`.
* `Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation`: **the pullback along `h` of the
  evaluation pairing of `𝒪(1)`**, as an inverse law `h^*𝒪(1) ⊗ h^*𝒪(-1) ≅ 𝒪_{𝐏(ℰ')}` read
  through Tag 01CD and `h^*𝒪_{𝐏(ℰ)} ≅ 𝒪_{𝐏(ℰ')}`.
* `Stacks.ProjectiveBundleConormal.symTwistBundleBaseChangeIso`: `h^*𝒪(1) ≅ 𝒪'(1)`, which is
  `Stacks.RelativeProj.symTwistBaseChangeIso` at this file's spelling of the two bundles. **It
  is the one crossing between the two spellings**, and it exists as a declaration because that
  crossing is affordable at a bare `≅` and nowhere else.
* `Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso`: **`h^*𝒪(-1) ≅ 𝒪'(-1)`**,
  the passage from the comparison of the tautological twists to the comparison of their
  inverses. This is the step recorded as missing in the "What is still owed" of
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChange`.
* `Stacks.ProjectiveBundleConormal.twistedSourceBaseChangeIso` and
  `twistedSourceBaseChange`: **`Φ`**, as an isomorphism and as the morphism at the spelling
  `conormalCanonicalMap_baseChange_of_source` takes it at.

## Main results

* `Stacks.ProjectiveBundleConormal.bundleBaseChangeHom_comp_toBase` and
  `bundleBaseChange_comm_toShHom`: the base-change square of the two bundles, at the scheme
  spelling and at the ringed-space spelling its sheaves of modules are formed over.
* `Stacks.ProjectiveBundleConormal.twistedSourceBaseChangeIso_hom`: `Φ` spelled out.
* `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_naturality`: a morphism of modules may
  be moved across the square's identification.
* `Stacks.ProjectiveBundleConormal.pullbackTensorComparison_comp` and
  `pullbackTensorComparison_pullbackCongr_inv`: the comparison of [Stacks, Tag 01CD] against the
  composition law for pullback and against the comparison of the pullbacks along two equal
  morphisms, at the scheme spelling.
* `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pullbackTensorComparison`: **the
  identification of a commuting square is compatible with the comparison of [Stacks, Tag
  01CD]**, factor by factor. This is the piece of `hsrc` recorded as owed in the "What is still
  owed" below as (1).
* `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_modulePullbackUnitIso`: **the unit half
  of the same coherence** — the square's identification against the comparison `f^*𝒪 ≅ 𝒪` down
  the two legs. The repository already had the composition law for that comparison, for a
  factorisation rather than for a square
  (`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` and `..._comp`), and a record that
  said otherwise was wrong.
* `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_tensorHom_comp_pullbackPairing`: **the
  square's identification is pinned by a pulled-back pairing.** The tensor, morphism and unit
  halves assembled: for any `p : A ⊗ B ⟶ 𝒪_{W₂}`, the square's identification in the two tensor
  factors followed by `p` pulled back down one leg is `p` pulled back down the other. At the
  evaluation pairing of `𝒪(1)` this is the left pin of `schemePullbackCompIso` that the
  inverse-line factor of the source coherence consumes.
* `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_comp_twistPullbackSourceIso`: **the
  square's identification is inverse to `Stacks.Chow.GenuineChern.twistPullbackSourceIso`**,
  which is the shape the pinning of the twist comparison is stated against.
* `Stacks.ProjectiveBundleConormal.hasTrivialSelfBraiding_pullbackInverseTautologicalTwist`:
  `h^*𝒪(-1)` has trivial self-braiding for the re-seated monoidal structure.
* `Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp`: **the twist
  factor of `Φ`, tensored with the twist comparison and followed by the evaluation pairing of
  `𝒪'(1)`, is the pulled-back evaluation pairing.** This is the monoidal half of `hΦ`.
* `Stacks.ProjectiveBundleConormal.pullbackKernelTautologicalMapTwisted`: **the pullback along
  `h` of the untwisted tautological map `ṽ`**, read through Tag 01CD and the pulled-back
  evaluation pairing. This is Tag 01CD's half of `hΦ`.
* `Stacks.ProjectiveBundleConormal.twistQuotientPullback_comp_symTwistBundleBaseChangeIso`,
  `twistPullbackSourceIso_comp_pullbackTautologicalMap` and
  `schemePullbackCompIso_comp_pullbackTautologicalMap`: **the pinning of the comparison of the
  tautological twists**, restated at this file's spelling, then with both sides unfolded, then
  read against the square's identification. This is
  `Stacks.RelativeProj.symTwistBaseChangeIso_spec` brought to the shape `Φ` is built at.
* `Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso_comp_kernelTautologicalMap`: **the
  kernel factor of `Φ` carries the base change of `v` to `v'`.** This is the mathematical
  content of `hΦ` on the first tensor factor.
* `Stacks.ProjectiveBundleConormal.twistedSourceBaseChangeIso_comp_kernelTautologicalMapTwisted`
  and `twistedSourceBaseChange_comp_kernelTautologicalMapTwisted`: **`hΦ`**, at the two
  spellings of the pullback functor.
* `Stacks.Monoidal.braidedSnakeHyp`,
  `Stacks.Monoidal.isoOfTensorInverseBraided` and
  `isoOfTensorInverseBraided_tensorHom_comp`: the general monoidal statements the two halves are
  assembled from, in a symmetric monoidal category where the object being inverted has trivial
  self-braiding.

## Implementation notes

**The factors are ascribed at `AlgebraicGeometry.Scheme.Modules`, not at the modules of the
underlying sheafed space.** `Stacks.ProjectiveBundleConormal.twistedSource` is a `⊗` of
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor`, which is installed on
`AlgebraicGeometry.Scheme.Modules`; stating the two factor comparisons with
`RingedSpaceModuleAdjunction.modulePullback` in their types makes the `⊗` of
`MonoidalCategory.tensorIso` unify at `SheafOfModules (structureSheafRing _)` instead, where no
`MonoidalCategoryStruct` is found and the assembly does not elaborate. Writing
`AlgebraicGeometry.Scheme.Modules.pullback` — definitionally the same functor — is what makes it
go through. The two spellings being definitionally equal, `twistedSourceBaseChange` is
nonetheless accepted for the hypothesis `Φ`, whose type is written with `modulePullback`.

**The cost of the imports is in the chart hypothesis, not in the twist comparison.**
`...ProjectiveBundleConormal.BaseChange` has 1455 modules in its closure;
`...Chow.GenuineChern.TwistPullbackIso`, which carries the twist comparison itself, adds 64;
`...Chow.GenuineChern.BundleBaseChangeTwist`, which discharges that comparison's chart
hypothesis for the base-change morphism, adds 1165. Since the comparison cannot be used without
its chart hypothesis, hosting this material in `BaseChange.lean` would take that module's
closure from 1455 to 2624; it is therefore hosted
here, where only the users of `Φ` pay.

## What is still owed, precisely

Of the three hypotheses of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_source`, this file supplies
the first two. **`hΦ`, the base change of the untwisted tautological map, is proved**, as
`Stacks.ProjectiveBundleConormal.twistedSourceBaseChange_comp_kernelTautologicalMapTwisted`, so
`conormalCanonicalMap_baseChange_of_twistedSourceBaseChange` now rests on one hypothesis. What
remains is:

**`hsrc`, the source coherence.** The first of its three pieces is supplied here and the
second, together with the whole assembly, in the sibling module
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceCoherence`, so that `hsrc` rests on
the third alone; and the third is proved in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause`, which closes the
clause.
Writing `P` for
`Stacks.ProjectiveBundleConormal.pullbackSourceIso` at `ℰ`, `P'` for it at `ℰ'`, `K` for
`Stacks.Divisors.conormalSourceBaseChange` and `R` for
`Stacks.ClosedImmersion.pullbackCompIso` at the square `σ' ≫ h = g ≫ σ`, `hsrc` says

`K.hom ≫ (P').inv = g^*(P.inv) ≫ R.hom ≫ σ'^*Φ`,

and all four of `P`, `P'`, `K` and `Φ` are a Tag 01CD comparison followed by a `⊗` of two factor
comparisons. So `hsrc` splits into exactly three pieces, and each was located:

1. **The Tag 01CD coherence of the square.** **Supplied**, as
   `Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pullbackTensorComparison`: splitting
   the pullback of a tensor product commutes with moving it across the square, factor by factor.

   No *bridge* is needed of
   `Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp` from `Stacks.DerivedPullback`'s
   `pullbackFunctor`/`modulePullbackComp` spelling to
   `Stacks.ProjectiveBundleConormal.pullbackTensorComparison` and to
   `Stacks.RingedSpace.comparisonBifunctorIso`: all
   three of those crossings are `rfl` —
   `pullbackTensorComparison f A B = Stacks.PullbackTensorCoherence.pullbackTensorComparison
   f.toLRSHom.toShHom A B`, `(Scheme.Modules.pullbackComp f j).hom.app M` against
   `Stacks.PullbackTensorCoherence.pullbackCompIso`, and
   `(Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app (A, B) =
   pullbackTensorComparison f A B`, which is the spelling
   `Stacks.Divisors.conormalSourcePullbackTensor` uses.

   The remaining discrepancy is in the *conclusion* of
   `Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp`: its `⊗ₘ` is that of
   `Stacks.PullbackGradedAlgebra.monoidalCategory`, while this file works in the re-seated
   `SheafOfModules.monoidalCategorySheafTensor`, and the two monoidal structures are **not**
   definitionally equal. That passage is
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonCompSheafTensor`, whose
   implementation notes record which of the three ways of making it are deterministic timeouts.
2. **The kernel factor**: `g^*(\ker q) ≅ \ker q'` obtained through the two section collapses
   `σ ≫ π = 𝟙` and `σ' ≫ π' = 𝟙` and the kernel factor of `Φ`, against
   `Stacks.Divisors.quotientKernelBaseChange`. It is proved as
   `Stacks.ProjectiveBundleConormal.kernelFactor_coherence` in the sibling module
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceCoherence`. It needed no new
   geometry: it is `Stacks.Modules.sectionSquare_coherence` — which is stated at this very square
   with these two section identities — restated at `schemePullbackCompIso` and
   `pullbackSectionNatIso`, together with the naturality of the section collapse at the kernel
   comparison.
3. **The inverse-line factor**: the two identifications of `g^*(Q.L^{⊗ -1})` with
   `(Q'.L)^{⊗ -1}`, one as `Stacks.Divisors.inverseQuotientBaseChange` and one as `σ'^*` of the
   twist factor of `Φ` read through
   `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso` at both ends, must be shown
   equal. The twist factor of `Φ` is `Stacks.Monoidal.isoOfTensorInverseBraided` and is pinned
   against the evaluation pairing of this file's monoidal structure
   (`inverseTwistBundleBaseChangeIso_tensorHom_comp`).

   **This is proved**, in
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause`, as
   `Stacks.ProjectiveBundleConormal.inverseLineFactor`; so is the clause itself, as
   `conormalCanonicalMap_baseChange` there. It is the hypothesis `hinv` of
   `Stacks.ProjectiveBundleConormal.sourceCoherence`, and it is **not provable from the
   hypotheses that statement carries**, by any route: `e` and `e'` are independent parameters
   there, and `Stacks.ProjectiveBundleConormal.inverseTwistBaseChangeIso_injective` shows that
   one side of `hinv` determines `e'` while the other does not mention it. The relation it needs
   is the compatibility of the *positive* lines, `positiveLine_coherence` in the sibling module,
   whose parameters `hqe` and `hqe'` every assembly point of the clause carries. The passage from
   that compatibility to `hinv` is a pin calculus in the `mulIso'` handedness of
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineDetermination`, not the
   left-handed one of
   `StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.InvIsoLeftPin`. The twist factor's
   own pin `inverseTwistBundleBaseChangeIso_tensorHom_comp` below is in the left form, and it
   converts by one braiding; what fixes the handedness is where the snake identity is spent. The
   left pin spends it at its *source*, which in all three `invIso`-shaped factors is a pulled-back
   inverse whose snake is not available; the right pin spends it at its *target*, which is always
   a plain `Stacks.ProjBundleInverseBaseChange.negOneTensorInverse`, whose snake is
   `negOneTensorInverse_snake`.

   **The geometric input that pin calculus needs of this square is proved here.** Its three
   halves are `schemePullbackCompIso_pullbackTensorComparison` (tensor),
   `schemePullbackCompIso_naturality` (morphism) and
   `schemePullbackCompIso_modulePullbackUnitIso` (**unit**), and their assembly is
   `schemePullbackCompIso_tensorHom_comp_pullbackPairing`: the square's identification in two
   tensor factors, followed by any pairing `A ⊗ B ⟶ 𝒪_{W₂}` pulled back down one leg, is that
   pairing pulled back down the other. At the evaluation pairing of `𝒪(1)` that is the left pin
   of `schemePullbackCompIso`, the pulled-back pairings being the shape
   `pullbackInvertibleEvaluation` is built in.

   Two apparent obstacles are **not** among them. The crossing from `tensorProductIso` to `⊗ₘ` is
   free, being
   `Stacks.PullbackSheafTensor.tensorSheafMap_eq_tensorHom`; and the two localized monoidal
   structures — `Stacks.SheafInternalHom.monoidalCategory`, over which
   `Stacks.ProjBundleInverseBaseChange.negOneMulIso` and `negOneMulIso'` are stated, and
   `SheafOfModules.monoidalCategorySheafTensor`, over which `invertibleEvaluation` and every
   `⊗ₘ` in this file live — are one re-seating apart on the nose, by
   `SheafOfModules.monoidalCategorySheafTensor_eq_reseat` and
   `sheafInternalHom_monoidalCategory_eq`, both `rfl`, and the comparison of two tensor inverses
   is unchanged by that re-seating (`Stacks.TensorPowers.invIso_reseatTensorInverse`).

   What that does **not** make free is the ascription of the pairings
   themselves. `(Stacks.ProjBundleInverseBaseChange.pullbackTensorIso g M N).hom` and
   `(pullbackUnitMonoidalIso g).hom` — the two factors of the `mulIso` of
   `pullbackTensorInverse`, which is what `tensorHom_comp_mulIso_ofIso` pins the three
   `invIso`-shaped factors of `hinv` against — do not ascribe at the corresponding
   `pullbackTensorComparisonIso` and `modulePullbackUnitIso` types: that is a *type* mismatch.
   The residue is exactly the two outer conjugating factors
   `AlgebraicGeometry.SheafOfModules.tensorIso` and `unitIso` of the re-seating that those two
   definitions carry; the middle factor crosses on the nose
   (`(Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso g M N).hom =
   pullbackTensorComparison g M N` by `rfl`), and `negOneMulIso'_eq` carries the same pair of
   conjugations, so what is owed is their cancellation across a `⊗ₘ` and a pullback and nothing
   else.

   **That cancellation is proved, generically**, in
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SourceInverseLine`: the two
   conjugating factors are the re-seating's own comparisons
   (`Stacks.ProjectiveBundleConormal.tensorIso_eq_sheafTensorIso` and `unitIso_eq`, each
   `CategoryTheory.Iso.ext` on the `hom` fields), and
   `CategoryTheory.MonoidalCategory.reseat_pin` carries a left pin across a re-seating for an
   arbitrary pair of pairings, so nothing has to be bridged per pairing. The snake that
   `tensorHom_comp_mulIso_ofIso` additionally asks of its source inverse is **not** disposed of
   by `Stacks.TensorPowers.TensorInverse.tensorHom_comp_mulIso_ofIso_braided`, since that would
   conflate two objects: that lemma trades the snake for a trivial
   self-braiding and the braiding relation of the two trivialisations *of the source*, and the
   source here is `Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse`, not Tag 01CU's
   `(-1)`st power. `Stacks.ProjBundleInverseBaseChange.negOneMulIso_eq_braiding` is the relation
   at the plain power, which is the *target*. That is why the right-handed pin is the reachable
   one.

   What is owed after that is the three pins and the assembly, plus one obstacle that
   module records: the recognition of the re-seated trivialisations as `invertibleEvaluation` and
   as the pulled-back pairing of `schemePullbackCompIso_tensorHom_comp_pullbackPairing` **cannot
   be taken by `rw` or `simp`** — a goal naming both `AlgebraicGeometry.Scheme.Modules` and
   `SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _)`
   under a `⊗` is not type-correct at `implicit` transparency, and the tactic reports the
   mismatch on `MonoidalCategoryStruct.tensorObj`. Those recognitions have to be taken in term
   mode or as hypotheses generated by unification from `reseat_pin`. **The term-mode route is
   taken**, and the two pins that need no re-seating with it:
   `Stacks.ProjectiveBundleConormal.pullbackPairing_pullbackPairing`,
   `schemePullbackCompIso_pin` and `inverseTwistBundleBaseChangeIso_pullback_pin`, in
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.InverseLineFactor`.

**No `@[stacks 0B3V]` attribute is attached in this file**: nothing here states a clause of
the tag. The label is on `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange` in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause`.

## How `hΦ` is assembled, and what it costs

Every placement of these crossings except this one fails, and
the shape of the proof is entirely dictated by them.

`Stacks.RelativeProj.symTwistBaseChangeIso_spec` is stated in the spelling of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange` — the base-change
morphism written as `Stacks.ProjectiveBundle.baseChangeHom` and the quasi-coherence of the
graded pieces as `isQuasicoherentPieces_of_isQuasicoherent` — while every declaration here is in
the spelling of `Stacks.ProjectiveBundleConormal.bundleBaseChangeHom` and `symPieces`. Three
facts about that crossing govern the proof:

1. **At a bare `≅` of two objects it is cheap.** That is
   `Stacks.ProjectiveBundleConormal.symTwistBundleBaseChangeIso`, and it is the only place the
   crossing is made.
2. **Underneath a `⊗` it does not finish.** With the twist comparison entering the monoidal
   half at its own spelling, the two spellings end up in the *implicit object arguments* of
   `MonoidalCategoryStruct.tensorHom`, and matching them against those of the evaluation
   pairing exhausts the recursion depth. This is why
   `inverseTwistBundleBaseChangeIso_tensorHom_comp` is stated with
   `symTwistBundleBaseChangeIso`: with one spelling throughout there is nothing to cross.
3. **It cannot be combined with the unfolding of `twistQuotientPullback` and
   `twistQuotientTarget`.** Stating the restatement and the two unfoldings as one declaration
   is a `(deterministic) timeout at whnf`; split into
   `twistQuotientPullback_comp_symTwistBundleBaseChangeIso` (the crossing, nothing else) and
   `twistPullbackSourceIso_comp_pullbackTautologicalMap` (the two unfoldings and one
   reassociation, from the first), both pass, the second in about a second.

Two further rules the assembly obeys:

* **Every reassociation is hoisted to a bare category.** `Category.assoc` on morphisms of
  `AlgebraicGeometry.Scheme.Modules` is not affordable in place; `reassocAux`, `cancelLeftAux`,
  `mapEqAux`, `kernelFactorAux`, `tensorCompAux`, `assembleAux` and `tensorWhiskerAux` carry all
  of it, and each use is an `apply` whose every unification is syntactic because the
  definitional crossings are supplied as separate equations (`kernelTwistedBaseChangeIso_hom`,
  `kernelTautologicalMap_eq`, `pullback_map_kernelTautologicalMap`,
  `twistedSourceBaseChangeIso_hom`). An `apply` that leaves any of them to the unifier reaches the
  maximum recursion depth.
* **The monoidal step of
  `twistedSourceBaseChangeIso_comp_kernelTautologicalMapTwisted` is an unascribed `have`.**
  Writing that intermediate equation out with `⊗ₘ` and `▷` in a statement of its own does not
  elaborate, for the reason in (2): a hand-written monoidal statement re-derives the object
  arguments from the ascription instead of taking them from the terms.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe v u

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- **The snake hypothesis of `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso`,
from a trivial self-braiding.** For an inverse law `hx : A ⊗ Y ≅ 𝟙` and the braided inverse law
`β_ Y A ≪≫ hx : Y ⊗ A ≅ 𝟙` in the other order, the two are snake-compatible as soon as `Y` has
trivial self-braiding. This is `Stacks.Monoidal.braiding_eval_snake` at the two orders of one
pairing. -/
theorem braidedSnakeHyp {A Y : C} (hb : Stacks.GradedSections.HasTrivialSelfBraiding Y)
    (hx : A ⊗ Y ≅ 𝟙_ C) :
    (β_ Y A ≪≫ hx).hom ▷ Y ≫ (λ_ Y).hom =
      (α_ Y A Y).hom ≫ Y ◁ hx.hom ≫ (ρ_ Y).hom := by
  have := hb
  have h := braiding_eval_snake (L := Y) (L' := A) (β_ Y A ≪≫ hx).hom
  rw [Iso.trans_hom, ← Category.assoc (β_ A Y).hom, SymmetricCategory.symmetry,
    Category.id_comp] at h
  exact h.symm

/-- **The comparison `X ≅ Y` of two tensor inverses in a symmetric monoidal category**, from a
comparison `e : A ≅ B` of the objects being inverted and the two inverse laws *in the natural
order* `A ⊗ X ≅ 𝟙` and `B ⊗ Y ≅ 𝟙`. This is `Stacks.Monoidal.isoOfTensorInverse`, whose second
inverse law is taken in the other order, with the braiding inserted. -/
def isoOfTensorInverseBraided {A B X Y : C} (e : A ≅ B) (hx : A ⊗ X ≅ 𝟙_ C)
    (hy : B ⊗ Y ≅ 𝟙_ C) : X ≅ Y :=
  isoOfTensorInverse e hx (β_ Y B ≪≫ hy)

/-- **`Stacks.Monoidal.isoOfTensorInverseBraided` is pinned by the two inverse laws.** Tensored
with `e` on the left and followed by `hy`, it is `hx`.

This is `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso` read in the natural order
on both sides: that statement has the comparison of the inverses on the *left* of the `⊗` and
the two inverse laws in the other order, and the braiding carries one form to the other, the
self-braiding of `X` being trivial. -/
theorem isoOfTensorInverseBraided_tensorHom_comp {A B X Y : C}
    (hb : Stacks.GradedSections.HasTrivialSelfBraiding X) (e : A ≅ B) (hx : A ⊗ X ≅ 𝟙_ C)
    (hy : B ⊗ Y ≅ 𝟙_ C) :
    (e.hom ⊗ₘ (isoOfTensorInverseBraided e hx hy).hom) ≫ hy.hom = hx.hom := by
  rw [isoOfTensorInverseBraided]
  have h := isoOfTensorInverse_tensorHom_comp_of_mulIso e hx (β_ X A ≪≫ hx) (β_ Y B ≪≫ hy)
    (braidedSnakeHyp hb hx)
  rw [Iso.trans_hom, Iso.trans_hom] at h
  calc (e.hom ⊗ₘ (isoOfTensorInverse e hx (β_ Y B ≪≫ hy)).hom) ≫ hy.hom
      = (e.hom ⊗ₘ (isoOfTensorInverse e hx (β_ Y B ≪≫ hy)).hom) ≫
          (β_ B Y).hom ≫ (β_ Y B).hom ≫ hy.hom := by
        rw [← Category.assoc (β_ B Y).hom, SymmetricCategory.symmetry, Category.id_comp]
    _ = (β_ A X).hom ≫ ((isoOfTensorInverse e hx (β_ Y B ≪≫ hy)).hom ⊗ₘ e.hom) ≫
          (β_ Y B).hom ≫ hy.hom := by
        rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]
    _ = (β_ A X).hom ≫ (β_ X A).hom ≫ hx.hom := by rw [h]
    _ = hx.hom := by rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end Stacks.Monoidal

namespace Stacks.ProjectiveBundleConormal

-- `Stacks.ProjectiveBundleConormal.monoidalSheafTensor` is `CanonicalMap.lean`'s monoidal
-- structure on `AlgebraicGeometry.Scheme.Modules`, the one `twistedSource` is a `⊗` of. It is a
-- `local instance` there, so it has to be re-enabled here.
attribute [local instance] monoidalSheafTensor

/-- **The symmetric structure of the re-seated tensor product, at the scheme spelling.** Its
commutativity constraint is `Stacks.SheafOfModules.tensorSheafBraiding` by
`SheafOfModules.braiding_sheafTensor_eq`. Deliberately local, for the same reason
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor` is: the projection to `BraidedCategory`
takes its `MonoidalCategory` argument instance-implicitly, so naming the symmetric structure
here is what makes `β_` resolve at the structure `twistedSource` is a `⊗` of. -/
@[instance_reducible] local instance symmSheafTensor (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategorySheafTensor X.toRingedSpace.sheaf

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules) [E'.IsQuasicoherent]
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (Q : Stacks.Divisors.InvertibleQuotient X E) (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
  (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)

/-! ### The identification of a commuting square, at the scheme spelling -/

section Square

variable {Z₁ Z₂ W₁ W₂ : Scheme.{u}} {i : Z₁ ⟶ Z₂} {k : Z₂ ⟶ W₂} {f : Z₁ ⟶ W₁} {j : W₁ ⟶ W₂}

/-- **The identification `f^*j^* ≅ i^*k^*` furnished by a commuting square of schemes**, at
`AlgebraicGeometry.Scheme.Modules` rather than at the modules of the underlying ringed spaces.

`Stacks.ClosedImmersion.pullbackCompNatIso` is the same identification for the ringed-space
spelling `RingedSpaceModuleAdjunction.modulePullback`, and the two functors are definitionally
the same; what is not interchangeable is the *objects*. With the kernel factor of
`Φ` built from the ringed-space spelling, the assembly of `hΦ` has to cross
`(Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback π).obj F)` against its
`modulePullback` counterpart *underneath a `⊗`*, and the unifier does not finish. Built from
this one, there is nothing to cross. -/
def schemePullbackCompNatIso (e : i ≫ k = f ≫ j) :
    Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback k ⋙ Scheme.Modules.pullback i :=
  Scheme.Modules.pullbackComp f j ≪≫ (Scheme.Modules.pullbackCongr e).symm ≪≫
    (Scheme.Modules.pullbackComp i k).symm

/-- The component of `Stacks.ProjectiveBundleConormal.schemePullbackCompNatIso`, with its source
and target written without `⋙` so that a consumer need not cross `CategoryTheory.Functor.comp`
to read them. -/
def schemePullbackCompIso (e : i ≫ k = f ≫ j) (M : W₂.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback j).obj M) ≅
      (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback k).obj M) :=
  (schemePullbackCompNatIso e).app M

/-- **A morphism of modules on `W₂` may be moved across the square's identification.** -/
theorem schemePullbackCompIso_naturality (e : i ≫ k = f ≫ j) {M N : W₂.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback j).map φ) ≫
        (schemePullbackCompIso e N).hom =
      (schemePullbackCompIso e M).hom ≫
        (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback k).map φ) :=
  (schemePullbackCompNatIso e).hom.naturality φ

/-- The cancellation of the square's identification against its inverse, over a bare category:
three isomorphisms, the middle one traversed in opposite directions on the two sides. Hoisted
because the three factors are isomorphisms of `AlgebraicGeometry.Scheme.Modules` and
reassociating them in place is not affordable. -/
private theorem cancelSquareAux {D : Type u} [Category.{v} D] {A P Q B : D} (m : A ≅ P)
    (t : Q ≅ P) (n : B ≅ Q) : (m.hom ≫ t.inv ≫ n.inv) ≫ (n.hom ≫ t.hom ≫ m.inv) = 𝟙 A := by
  simp

/-- The step from the naturality of Tag 01CD to the pulled-back untwisting, over a bare
category. -/
private theorem pullbackUntwistAux {D : Type u} [Category.{v} D] {S T P T₂ M U : D} (pb : S ⟶ T)
    (w : T ⟶ T₂) (m : S ⟶ P) (pq : P ≅ T₂) (ev : P ⟶ M) (u2u : M ⟶ U) (r : S ⟶ M)
    (hn : pb ≫ w = m ≫ pq.hom) (hr : m ≫ ev = r) :
    pb ≫ w ≫ pq.inv ≫ ev ≫ u2u = r ≫ u2u := by
  rw [← Category.assoc, hn, Category.assoc, pq.hom_inv_id_assoc, ← Category.assoc, hr]

/-- One reassociation, over a bare category. Hoisted because the three factors are morphisms of
`AlgebraicGeometry.Scheme.Modules` and `Category.assoc` is not affordable on them in place. -/
private theorem reassocAux {D : Type u} [Category.{v} D] {A B C₁ C₂ : D} (a : A ⟶ B) (b : B ⟶ C₁)
    (c : C₁ ⟶ C₂) (r : A ⟶ C₂) (h : (a ≫ b) ≫ c = r) : a ≫ b ≫ c = r := by
  rw [← Category.assoc]; exact h

/-- Cancelling a one-sided inverse off the left, over a bare category. -/
private theorem cancelLeftAux {D : Type u} [Category.{v} D] {A B C₁ : D} {s : A ⟶ B} {t : B ⟶ A}
    {x : A ⟶ C₁} {y : B ⟶ C₁} (hst : s ≫ t = 𝟙 A) (h : t ≫ x = y) : s ≫ y = x := by
  rw [← h, ← Category.assoc, hst, Category.id_comp]

/-- Carrying a factorisation across a functor, over bare categories. This is two instances of
`CategoryTheory.Functor.map_comp`; stated here so that the functor
`AlgebraicGeometry.Scheme.Modules.pullback π'` is an opaque argument when they are used. -/
private theorem mapEqAux {D D₂ : Type u} [Category.{v} D] [Category.{v} D₂] (F : D ⥤ D₂)
    {A B P R : D} {a : A ⟶ B} {b : B ⟶ R} {c : A ⟶ P} {d : P ⟶ R} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by rw [← F.map_comp, ← F.map_comp, h]

/-- The bookkeeping of
`Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso_comp_kernelTautologicalMap`, over a
bare category: the two factors of the kernel comparison, the inclusion and the tautological map,
against the naturality of the square (`h1`), the compatibility of the kernel comparison with the
inclusion (`h2`) and the pinning of the twist comparison (`h3`). Every reassociation happens
here; `h0`, `h0'` and `h4` are the three definitional crossings, each supplied as its own
equation so that nothing is left for the unifier to discover. -/
private theorem kernelFactorAux {D : Type u} [Category.{v} D] {A P K' S' O' B Pe T : D}
    {sk : A ⟶ P} {pq : P ⟶ K'} {ki : K' ⟶ S'} {t' : S' ⟶ O'} {mi : A ⟶ B} {sE : B ⟶ Pe}
    {pgi : P ⟶ Pe} {phE : Pe ⟶ S'} {mt : B ⟶ T} {st : T ⟶ O'} {kiso : A ⟶ K'} {ktm : K' ⟶ O'}
    {mk : A ⟶ T} (h0 : kiso = sk ≫ pq) (h0' : ktm = ki ≫ t') (h1 : mi ≫ sE = sk ≫ pgi)
    (h2 : pq ≫ ki = pgi ≫ phE) (h3 : sE ≫ phE ≫ t' = mt ≫ st) (h4 : mi ≫ mt = mk) :
    kiso ≫ ktm = mk ≫ st := by
  rw [h0, h0', ← h4]
  simp only [Category.assoc]
  rw [reassoc_of% h2, ← reassoc_of% h1, h3]

/-- Replacing the tail of a composite, over a bare category. -/
private theorem tensorCompAux {D : Type u} [Category.{v} D] {A₀ C₀ D₀ E₀ : D} {kt : A₀ ⟶ C₀}
    {m : C₀ ⟶ D₀} {wv : A₀ ⟶ E₀} {sev pbev : E₀ ⟶ D₀} (a2 : kt ≫ m = wv ≫ sev)
    (a3 : sev = pbev) : kt ≫ m = wv ≫ pbev := by rw [a2, a3]

/-- The last step of `hΦ`, over a bare category: Tag 01CD's comparison is the same first factor
on both sides, so the clause follows from the two halves once the tail has been matched. -/
private theorem assembleAux {D : Type u} [Category.{v} D] {A₀ B₀ C₀ D₀ E₀ : D} {psi : A₀ ⟶ C₀}
    {p : A₀ ⟶ B₀} {kt : B₀ ⟶ C₀} {m : C₀ ⟶ D₀} {wv : B₀ ⟶ E₀} {pbev : E₀ ⟶ D₀} {r : A₀ ⟶ D₀}
    (h0 : psi = p ≫ kt) (a2 : kt ≫ m = wv ≫ pbev) (a1 : p ≫ wv ≫ pbev = r) : psi ≫ m = r := by
  rw [h0, Category.assoc, a2]; exact a1

/-- **A factorisation of one tensor factor, moved across a `⊗`**, in a bare monoidal category:
if `k ≫ v = w ≫ s` then tensoring with `t` and following with a pairing on the right-hand
factor gives the same composite either way. Hoisted because `MonoidalCategory.tensorHom_id` and
`tensorHom_comp_tensorHom` are not affordable on morphisms of
`AlgebraicGeometry.Scheme.Modules`. -/
private theorem tensorWhiskerAux {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A B X Y P R U : D} (k : A ⟶ B) (t : X ⟶ Y) (v : B ⟶ R) (w : A ⟶ P) (s : P ⟶ R)
    (ev : R ⊗ Y ⟶ U) (h : k ≫ v = w ≫ s) :
    (k ⊗ₘ t) ≫ (v ▷ Y) ≫ ev = (w ▷ X) ≫ (s ⊗ₘ t) ≫ ev := by
  have key : (k ⊗ₘ t) ≫ (v ▷ Y) = (w ▷ X) ≫ (s ⊗ₘ t) := by
    simp only [← MonoidalCategory.tensorHom_id]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, h]
  rw [← Category.assoc, key, Category.assoc]

/-- **A triple composite in each factor of a `⊗`**, in a bare monoidal category. Hoisted because
`MonoidalCategory.tensorHom_comp_tensorHom` is not affordable on morphisms of
`AlgebraicGeometry.Scheme.Modules`. -/
private theorem tensorTripleAux {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : D} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄)
    (a' : Y₁ ⟶ Y₂) (b' : Y₂ ⟶ Y₃) (c' : Y₃ ⟶ Y₄) :
    (a ≫ b ≫ c) ⊗ₘ (a' ≫ b' ≫ c') = (a ⊗ₘ a') ≫ (b ⊗ₘ b') ≫ (c ⊗ₘ c') := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]

/-- Turning a naturality square around both of its isomorphisms, over a bare category: from
`p.hom ≫ c = a ≫ b ≫ q.hom` read `p.inv` against `q.inv`. -/
private theorem invFormAux {D : Type u} [Category.{v} D] {S T U V W : D} (p : S ≅ T) (q : V ≅ U)
    {c : T ⟶ U} {a : S ⟶ W} {b : W ⟶ V} (h : p.hom ≫ c = a ≫ b ≫ q.hom) :
    p.inv ≫ a ≫ b = c ≫ q.inv :=
  calc p.inv ≫ a ≫ b = p.inv ≫ (a ≫ b ≫ q.hom) ≫ q.inv := by simp
    _ = p.inv ≫ (p.hom ≫ c) ≫ q.inv := by rw [h]
    _ = c ≫ q.inv := by simp

/-- The bookkeeping of
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pullbackTensorComparison`, over a bare
category: the three factors `p`, `cg`, `kk` of the square's identification against the
composition law (`h1`, `h3`) and the comparison of pullbacks along equal morphisms (`h2`), with
`h4` the one monoidal step. Every reassociation happens here. -/
private theorem squareTensorAux {D : Type u} [Category.{v} D]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : D}
    {p : O₁ ⟶ O₂} {cg : O₂ ⟶ O₃} {kk : O₃ ⟶ O₄} {ai : O₄ ⟶ O₅} {bi : O₅ ⟶ O₆}
    {pfj : O₂ ⟶ O₇} {pik : O₃ ⟶ O₈} {af : O₁ ⟶ O₉} {bf : O₉ ⟶ O₁₀}
    {tp : O₁₀ ⟶ O₇} {tc : O₇ ⟶ O₈} {tk : O₈ ⟶ O₆} {tr : O₁₀ ⟶ O₆}
    (h1 : p ≫ pfj = af ≫ bf ≫ tp) (h2 : cg ≫ pik = pfj ≫ tc)
    (h3 : kk ≫ ai ≫ bi = pik ≫ tk) (h4 : tr = tp ≫ tc ≫ tk) :
    (p ≫ cg ≫ kk) ≫ ai ≫ bi = af ≫ bf ≫ tr := by
  rw [h4]
  simp only [Category.assoc]
  rw [h3, reassoc_of% h2, reassoc_of% h1]

end Square

/-! ### Tag 01CD and the identification of a commuting square -/

section SquareTensor

variable {Z₁ Z₂ W₁ W₂ : Scheme.{u}} {i : Z₁ ⟶ Z₂} {k : Z₂ ⟶ W₂} {f : Z₁ ⟶ W₁} {j : W₁ ⟶ W₂}

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the composition law for pullback**,
at the scheme spelling. This is
`Stacks.PullbackSheafTensor.sheafTensorComparison_comp`, whose statement spells the modules over
the underlying ringed spaces, and **this declaration is the one crossing between the two
spellings**: combining it with the passage from
`Stacks.PullbackGradedAlgebra.monoidalCategory`'s `⊗ₘ` to the re-seated one is a
`(deterministic) timeout at isDefEq`, so the two crossings are taken in two declarations, that
passage in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonCompSheafTensor`
and this one here. -/
theorem pullbackTensorComparison_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    (A B : Z.Modules) :
    (Scheme.Modules.pullbackComp f j).hom.app (A ⊗ B) ≫
        pullbackTensorComparison (f ≫ j) A B =
      (Scheme.Modules.pullback f).map (pullbackTensorComparison j A B) ≫
        pullbackTensorComparison f ((Scheme.Modules.pullback j).obj A)
          ((Scheme.Modules.pullback j).obj B) ≫
          ((Scheme.Modules.pullbackComp f j).hom.app A ⊗ₘ
            (Scheme.Modules.pullbackComp f j).hom.app B) :=
  Stacks.PullbackSheafTensor.sheafTensorComparison_comp f.toLRSHom.toShHom
    j.toLRSHom.toShHom A B

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the comparison of the pullbacks
along two equal morphisms**, in the inverse direction, which is the direction
`Stacks.ProjectiveBundleConormal.schemePullbackCompNatIso` traverses it. Proved by substituting
the equality, after which the comparison is the identity and only
`MonoidalCategory.tensorHom_id` is left. -/
theorem pullbackTensorComparison_pullbackCongr_inv {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y}
    (e : f₁ = f₂) (A B : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).inv.app (A ⊗ B) ≫ pullbackTensorComparison f₁ A B =
      pullbackTensorComparison f₂ A B ≫
        ((Scheme.Modules.pullbackCongr e).inv.app A ⊗ₘ
          (Scheme.Modules.pullbackCongr e).inv.app B) := by
  subst e
  change 𝟙 _ ≫ pullbackTensorComparison f₁ A B =
      pullbackTensorComparison f₁ A B ≫ (𝟙 _ ⊗ₘ 𝟙 _)
  rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp,
    Category.comp_id]

/-- `Stacks.ProjectiveBundleConormal.schemePullbackCompIso` spelled out as its three factors, so
that a consumer need not unfold an `Iso.trans` of natural isomorphisms. -/
theorem schemePullbackCompIso_hom (e : i ≫ k = f ≫ j) (M : W₂.Modules) :
    (schemePullbackCompIso e M).hom =
      (Scheme.Modules.pullbackComp f j).hom.app M ≫
        (Scheme.Modules.pullbackCongr e).inv.app M ≫
          (Scheme.Modules.pullbackComp i k).inv.app M := rfl

/-- **The identification of a commuting square is compatible with the comparison of [Stacks, Tag
01CD]**: for a commuting square `i ≫ k = f ≫ j` of schemes and two modules `A`, `B` on `W₂`,
splitting the pullback of `A ⊗ B` over the tensor product commutes with moving it across the
square, the two splittings being compared factor by factor.

This is the Tag 01CD coherence of the square recorded as owed in this module's "What is still
owed, precisely". It is the composition law (`pullbackTensorComparison_comp`) at `(f, j)` and at
`(i, k)` together with `pullbackTensorComparison_pullbackCongr_inv`, assembled over a bare
category by `Stacks.ProjectiveBundleConormal.squareTensorAux`; the one monoidal step, that the
`⊗` of the two three-step composites is the three-step composite of the `⊗`s, is
`Stacks.ProjectiveBundleConormal.tensorTripleAux` over a bare monoidal category and is accepted
against `schemePullbackCompIso_hom` definitionally, so nothing is rewritten under a `⊗`. -/
theorem schemePullbackCompIso_pullbackTensorComparison (e : i ≫ k = f ≫ j) (A B : W₂.Modules) :
    (schemePullbackCompIso e (A ⊗ B)).hom ≫
        (Scheme.Modules.pullback i).map (pullbackTensorComparison k A B) ≫
        pullbackTensorComparison i ((Scheme.Modules.pullback k).obj A)
          ((Scheme.Modules.pullback k).obj B) =
      (Scheme.Modules.pullback f).map (pullbackTensorComparison j A B) ≫
        pullbackTensorComparison f ((Scheme.Modules.pullback j).obj A)
          ((Scheme.Modules.pullback j).obj B) ≫
          ((schemePullbackCompIso e A).hom ⊗ₘ (schemePullbackCompIso e B).hom) := by
  apply squareTensorAux (pullbackTensorComparison_comp f j A B)
    (pullbackTensorComparison_pullbackCongr_inv e A B)
    (invFormAux ((Scheme.Modules.pullbackComp i k).app (A ⊗ B))
      (MonoidalCategory.tensorIso ((Scheme.Modules.pullbackComp i k).app A)
        ((Scheme.Modules.pullbackComp i k).app B))
      (pullbackTensorComparison_comp i k A B))
    (tensorTripleAux _ _ _ _ _ _)

end SquareTensor

/-! ### The unit of [Stacks, Tag 01CD] and the identification of a commuting square -/

section SquareUnit

variable {Z₁ Z₂ W₁ W₂ : Scheme.{u}} {i : Z₁ ⟶ Z₂} {k : Z₂ ⟶ W₂} {f : Z₁ ⟶ W₁} {j : W₁ ⟶ W₂}

/-- The passage from two triangles to a square, over a bare category: the square's
identification is the composition law of one leg followed by the two factors the other leg
contributes, so a statement holding of each leg separately holds across the square once the
first leg's composition law is cancelled off the left. -/
private theorem unitSquareAux {D : Type u} [Category.{v} D] {A B C₁ C₂ T : D}
    (p : A ≅ B) (b : B ⟶ C₁) (c : C₁ ⟶ C₂) (d : C₂ ⟶ T) (y : A ⟶ T) (w : B ⟶ T)
    (h1 : b ≫ c ≫ d = w) (h2 : p.inv ≫ y = w) :
    (p.hom ≫ b ≫ c) ≫ d = y := by
  rw [Category.assoc, Category.assoc, h1, ← h2, p.hom_inv_id_assoc]

/-- **The identification of a commuting square is compatible with the comparison `f^*𝒪 ≅ 𝒪`**:
for a commuting square `i ≫ k = f ≫ j` of schemes, reading the twice-pulled-back structure
sheaf as the structure sheaf down one leg of the square agrees, across the square's
identification, with reading it down the other.

This is the **unit half** of the Tag 01CD coherence of the square, the companion of
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_pullbackTensorComparison` (the tensor
half) and of `schemePullbackCompIso_naturality` (the morphism half). The three together pin
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso` against a pulled-back evaluation
pairing, which is `schemePullbackCompIso_tensorHom_comp_pullbackPairing` below.

**It is not new mathematics.** The composition law
for the unit comparison *is* in the repository, for a factorisation `f ≫ g = h` rather than for
a square: `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`, which already carries the
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` factor that turns a triangle into a square, and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp`. Instantiating the first at `(i, k)`
with `h := f ≫ j` and the second at `(f, j)` gives two factorisations of the same morphism
`(f ≫ j)^*𝒪 ⟶ 𝒪`, and `schemePullbackCompIso_hom` is exactly the three factors that remain once
the composition law of the second leg is cancelled off the left; `unitSquareAux` performs that
cancellation over a bare category.

Two spellings are crossed here and both are `rfl`:
`AlgebraicGeometry.Scheme.unitModule` against the monoidal unit `𝟙_` of
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor`, and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` against
`RingedSpaceModuleAdjunction.modulePullbackUnitIso`, which is the spelling
`Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation` is built at. The statement is
therefore made directly at the spelling its consumer wants. -/
theorem schemePullbackCompIso_modulePullbackUnitIso (e : i ≫ k = f ≫ j) :
    (schemePullbackCompIso e (𝟙_ (W₂.Modules))).hom ≫
        (Scheme.Modules.pullback i).map (modulePullbackUnitIso k.toLRSHom.toShHom).hom ≫
          (modulePullbackUnitIso i.toLRSHom.toShHom).hom =
      (Scheme.Modules.pullback f).map (modulePullbackUnitIso j.toLRSHom.toShHom).hom ≫
        (modulePullbackUnitIso f.toLRSHom.toShHom).hom := by
  rw [schemePullbackCompIso_hom]
  exact unitSquareAux ((Scheme.Modules.pullbackComp f j).app (Scheme.unitModule W₂))
    _ _ _ _ _ (Scheme.Modules.pullbackUnitIso_comp_eq i k (f ≫ j) e)
    (Scheme.Modules.pullbackUnitIso_comp f j)

/-- Reading a square of four isomorphisms the other way round, over a bare category. Hoisted
because the four factors are isomorphisms of `AlgebraicGeometry.Scheme.Modules` and inverting
them in place is not affordable. -/
private theorem invSquareAux {D : Type u} [Category.{v} D] {V W X₁ X₂ Y₁ Y₂ : D}
    (m : V ⟶ W) (x : W ≅ X₁) (y : X₁ ≅ X₂) (a : V ≅ Y₁) (b : Y₁ ≅ Y₂) (t : Y₂ ⟶ X₂)
    (h : m ≫ x.hom ≫ y.hom = a.hom ≫ b.hom ≫ t) :
    t ≫ y.inv ≫ x.inv = b.inv ≫ a.inv ≫ m := by
  have ht : t = b.inv ≫ a.inv ≫ m ≫ x.hom ≫ y.hom := by
    rw [h]; simp
  rw [ht]; simp

/-- The assembly of the three halves into the pin of the square against a pulled-back pairing,
over a bare category: the inverted tensor half (`h1`), the morphism half at the pairing (`h2`)
and the unit half (`h3`). Every reassociation happens here. -/
private theorem pairingSquareAux {D : Type u} [Category.{v} D]
    {P Q R₁ R₂ R₃ R₄ S₁ S₂ S₃ S₄ T : D}
    (t : P ⟶ Q) (ai : Q ⟶ R₁) (bi : R₁ ⟶ R₂) (pk : R₂ ⟶ R₃) (ck : R₃ ⟶ R₄) (ui : R₄ ⟶ T)
    (af : P ⟶ S₁) (bf : S₁ ⟶ S₂) (pj : S₂ ⟶ S₃) (cj : S₃ ⟶ S₄) (uf : S₄ ⟶ T)
    (m : S₂ ⟶ R₂) (s : S₃ ⟶ R₃)
    (h1 : t ≫ ai ≫ bi = af ≫ bf ≫ m)
    (h2 : pj ≫ s = m ≫ pk)
    (h3 : s ≫ ck ≫ ui = cj ≫ uf) :
    t ≫ ai ≫ bi ≫ pk ≫ ck ≫ ui = af ≫ bf ≫ pj ≫ cj ≫ uf := by
  rw [reassoc_of% h1, ← reassoc_of% h2, h3]

/-- **The identification of a commuting square is pinned by a pulled-back pairing.** For a
commuting square `i ≫ k = f ≫ j` of schemes, two modules `A`, `B` on `W₂` and any pairing
`p : A ⊗ B ⟶ 𝒪_{W₂}`, the square's identification in the two tensor factors, followed by the
pairing pulled back down the leg `k` then `i`, is the pairing pulled back down the leg `j` then
`f`.

Each of the two pulled-back pairings is written out as Tag 01CD backwards, the pullback of the
pairing, and the comparison `f^*𝒪 ≅ 𝒪` — the shape
`Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation` is built in, at `p` the
evaluation pairing of `𝒪(1)`. So this statement at `A = tautologicalTwist`,
`B = inverseTautologicalTwist` and `p = invertibleEvaluation` is the **left pin of
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso`** that the inverse-line factor of the
source coherence needs, in the sense of
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.InvIsoLeftPin`.

The three inputs are the three halves of the Tag 01CD coherence of the square and nothing else:
`schemePullbackCompIso_pullbackTensorComparison` read backwards by `invSquareAux`,
`schemePullbackCompIso_naturality` at `p`, and `schemePullbackCompIso_modulePullbackUnitIso`.
`pairingSquareAux` assembles them over a bare category, so nothing is rewritten underneath a
`⊗`. -/
theorem schemePullbackCompIso_tensorHom_comp_pullbackPairing (e : i ≫ k = f ≫ j)
    (A B : W₂.Modules) (p : A ⊗ B ⟶ 𝟙_ (W₂.Modules)) :
    ((schemePullbackCompIso e A).hom ⊗ₘ (schemePullbackCompIso e B).hom) ≫
        (pullbackTensorComparisonIso i ((Scheme.Modules.pullback k).obj A)
            ((Scheme.Modules.pullback k).obj B)).inv ≫
          (Scheme.Modules.pullback i).map (pullbackTensorComparisonIso k A B).inv ≫
            (Scheme.Modules.pullback i).map ((Scheme.Modules.pullback k).map p) ≫
              (Scheme.Modules.pullback i).map
                  (modulePullbackUnitIso k.toLRSHom.toShHom).hom ≫
                (modulePullbackUnitIso i.toLRSHom.toShHom).hom =
      (pullbackTensorComparisonIso f ((Scheme.Modules.pullback j).obj A)
          ((Scheme.Modules.pullback j).obj B)).inv ≫
        (Scheme.Modules.pullback f).map (pullbackTensorComparisonIso j A B).inv ≫
          (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback j).map p) ≫
            (Scheme.Modules.pullback f).map
                (modulePullbackUnitIso j.toLRSHom.toShHom).hom ≫
              (modulePullbackUnitIso f.toLRSHom.toShHom).hom := by
  refine pairingSquareAux _ _ _ _ _ _ _ _ _ _ _ (schemePullbackCompIso e (A ⊗ B)).hom
    (schemePullbackCompIso e (𝟙_ (W₂.Modules))).hom ?_
    (schemePullbackCompIso_naturality e p)
    (schemePullbackCompIso_modulePullbackUnitIso e)
  exact invSquareAux (schemePullbackCompIso e (A ⊗ B)).hom
    ((Scheme.Modules.pullback i).mapIso (pullbackTensorComparisonIso k A B))
    (pullbackTensorComparisonIso i _ _)
    ((Scheme.Modules.pullback f).mapIso (pullbackTensorComparisonIso j A B))
    (pullbackTensorComparisonIso f _ _) _
    (schemePullbackCompIso_pullbackTensorComparison e A B)

end SquareUnit

/-- **The base-change morphism of the two bundles lies over `g`**: `h ≫ π = π' ≫ g`. This is
`Stacks.ProjectiveBundle.baseChangeHom_toBase` at the presentation
`Stacks.ProjectiveBundleConormal.bundle`. -/
theorem bundleBaseChangeHom_comp_toBase :
    bundleBaseChangeHom g E E' hE ≫ (bundle E).toBase = (bundle E').toBase ≫ g :=
  Stacks.ProjectiveBundle.baseChangeHom_toBase g E (symPieces E) E' (symPieces E') hE

/-- **The base-change square of the two bundles, at the ringed-space spelling** their sheaves of
modules are formed over, which is the form `Stacks.ClosedImmersion.pullbackCompIso` consumes. -/
theorem bundleBaseChange_comm_toShHom :
    (bundle E').toBase.toLRSHom.toShHom ≫ g.toLRSHom.toShHom =
      (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom ≫
        (bundle E).toBase.toLRSHom.toShHom :=
  Stacks.Conormal.comm_toShHom (bundleBaseChangeHom_comp_toBase g E E' hE).symm

/-- **The square's identification is inverse to `Stacks.Chow.GenuineChern.twistPullbackSourceIso`
at `ℰ`.** That comparison `π'^*g^*ℰ ≅ h^*π^*ℰ` is the one
`Stacks.RelativeProj.symTwistBaseChangeIso_spec` pins the comparison of the tautological twists
against, and it is assembled from the same three factors as
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso` with the middle one traversed the other
way; so the two compose to the identity.

Stated in this direction, with both maps forward, because the inverse of either composite is not
affordable to form: the cancellation is paid by
`Stacks.ProjectiveBundleConormal.cancelSquareAux` over a bare category. -/
theorem schemePullbackCompIso_comp_twistPullbackSourceIso :
    (schemePullbackCompIso (bundleBaseChangeHom_comp_toBase g E E' hE).symm E).hom ≫
      (Stacks.Chow.GenuineChern.twistPullbackSourceIso g (symPieces E) (symPieces E')
        (bundleBaseChangeHom g E E' hE)
        (bundleBaseChangeHom_comp_toBase g E E' hE)).hom = 𝟙 _ :=
  cancelSquareAux
    ((Scheme.Modules.pullbackComp (bundleBaseChangeHom g E E' hE) (bundle E).toBase).app E)
    ((Scheme.Modules.pullbackCongr (bundleBaseChangeHom_comp_toBase g E E' hE).symm).app E)
    ((Scheme.Modules.pullbackComp (bundle E').toBase g).app E)

/-- **The first factor of `Φ`**: `h^*π^*(\ker q) ≅ π'^*(\ker q')`. The square
`h ≫ π = π' ≫ g` moves the pullback along `h` past the one along `π`, and
`Stacks.Divisors.quotientKernelBaseChange` identifies `g^*(\ker q)` with `\ker q'`.

The square's identification is taken at the scheme spelling
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso`, not at
`Stacks.ClosedImmersion.pullbackCompIso`; the two are definitionally equal, and that module's
docstring records what crossing the choice avoids. -/
def kernelTwistedBaseChangeIso :
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q)) ≅
      (Scheme.Modules.pullback (bundle E').toBase).obj (kernel Q'.q) :=
  schemePullbackCompIso (bundleBaseChangeHom_comp_toBase g E E' hE).symm (kernel Q.q) ≪≫
    (Scheme.Modules.pullback (bundle E').toBase).mapIso
      (Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).1

/-! ### The pulled-back evaluation pairing and the twist factor of `Φ` -/

/-- **The pullback along `h` of the evaluation pairing of `𝒪(1)`**, as an inverse law
`h^*𝒪_{𝐏(ℰ)}(1) ⊗ h^*𝒪_{𝐏(ℰ)}(-1) ≅ 𝒪_{𝐏(ℰ')}`: Tag 01CD splits the pullback over the tensor
product, the pullback of `Stacks.ProjectiveBundleConormal.invertibleEvaluation` is taken, and
`RingedSpaceModuleAdjunction.modulePullbackUnitIso` reads `h^*𝒪_{𝐏(ℰ)}` as `𝒪_{𝐏(ℰ')}`. -/
def pullbackInvertibleEvaluation :
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        (tautologicalTwist E (symPieces E)) ⊗
      (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        (inverseTautologicalTwist E) ≅ 𝟙_ ((bundle E').scheme.Modules) :=
  (pullbackTensorComparisonIso (bundleBaseChangeHom g E E' hE)
      (tautologicalTwist E (symPieces E)) (inverseTautologicalTwist E)).symm ≪≫
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).mapIso
      (invertibleEvaluation (tautologicalTwist E (symPieces E))) ≪≫
    modulePullbackUnitIso (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom

/-- **`h^*𝒪_{𝐏(ℰ)}(-1)` is invertible**, at the spelling of the sheaf of rings that
`SheafOfModules.hasTrivialSelfBraiding_sheafTensor` asks for. The pullback of an invertible
module is invertible by Tag 0B8L, and `AlgebraicGeometry.Scheme.presheaf` with
`AlgebraicGeometry.Scheme.ringCatSheaf` is the spelling instance search finds it at; the two are
definitionally equal and this declaration is the one crossing between them. -/
local instance isInvertible_pullback_inverseTautologicalTwist :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      ((bundle E').scheme.toRingedSpace.sheaf).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((bundle E').scheme.toRingedSpace.sheaf)).property
      ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        (inverseTautologicalTwist E)) :=
  inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible
    (bundle E').scheme.presheaf (bundle E').scheme.ringCatSheaf.2 _)

/-- **`h^*𝒪_{𝐏(ℰ)}(-1)` has trivial self-braiding** for the re-seated monoidal structure. This is
`SheafOfModules.hasTrivialSelfBraiding_sheafTensor`, and it is the hypothesis
`Stacks.Monoidal.braiding_eval_snake` consumes. It is recorded as a theorem rather than an
instance because instance search does not reach it: the braided structure in its conclusion is
the one `Stacks.ProjectiveBundleConormal.symmSheafTensor` provides by projection, and matching
that against the conclusion of `hasTrivialSelfBraiding_sheafTensor` is not something synthesis
does on its own. -/
theorem hasTrivialSelfBraiding_pullbackInverseTautologicalTwist :
    Stacks.GradedSections.HasTrivialSelfBraiding
      ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        (inverseTautologicalTwist E)) :=
  SheafOfModules.hasTrivialSelfBraiding_sheafTensor _ _

/-- **The comparison of the tautological twists, at this file's spelling of the bundles.**
`Stacks.RelativeProj.symTwistBaseChangeIso` is the same isomorphism with
`Stacks.ProjectiveBundle.baseChangeHom` and `isQuasicoherentPieces_of_isQuasicoherent` in its
type where this file writes `Stacks.ProjectiveBundleConormal.bundleBaseChangeHom` and
`symPieces`; the two are definitionally equal, and **this declaration is the one crossing
between them**.

It is worth its own name because the crossing is affordable exactly here, at a bare `≅` of two
objects, and nowhere else: the twist comparison enters `Φ` inside a `⊗`, and
crossing the two spellings underneath the `⊗` of
`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp` exhausts the
recursion depth, because the two spellings then sit in the *implicit object arguments* of
`MonoidalCategoryStruct.tensorHom`. Every declaration below therefore uses this one. -/
def symTwistBundleBaseChangeIso :
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        (tautologicalTwist E (symPieces E)) ≅ tautologicalTwist E' (symPieces E') :=
  Stacks.RelativeProj.symTwistBaseChangeIso g E E' hE

/-- **The second factor of `Φ`**: `h^*𝒪_{𝐏(ℰ)}(-1) ≅ 𝒪_{𝐏(ℰ')}(-1)`.

`Stacks.RelativeProj.symTwistBaseChangeIso` is the comparison `h^*𝒪(1) ≅ 𝒪'(1)` of the
tautological twists, stated at exactly this presentation of the bundle and unconditional in `g`,
`ℰ` and `ℰ'`; `Stacks.Monoidal.isoOfTensorInverseBraided` turns it into a comparison of the
inverses, using only the two evaluation pairings. So this too is unconditional, and in
particular it does not depend on `Q` or `Q'`.

**Why not `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso`**, which is the same
comparison obtained from the uniqueness of tensor inverses: that one is built in the localized
monoidal structure, and nothing pins it against the evaluation pairing of *this* structure.
Built as `Stacks.Monoidal.isoOfTensorInverse` it is pinned, by
`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp` below, which is
the monoidal half of `hΦ`. -/
def inverseTwistBundleBaseChangeIso :
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
        (inverseTautologicalTwist E) ≅ inverseTautologicalTwist E' :=
  @Stacks.Monoidal.isoOfTensorInverseBraided _ _ (monoidalSheafTensor _) (symmSheafTensor _)
    _ _ _ _ (symTwistBundleBaseChangeIso g E E' hE)
    (pullbackInvertibleEvaluation g E E' hE)
    (invertibleEvaluation (tautologicalTwist E' (symPieces E')))

/-- **The twist factor of `Φ` is pinned by the two evaluation pairings**: tensored with the
comparison of the tautological twists and followed by the evaluation pairing of `𝒪_{𝐏(ℰ')}(1)`,
it is the pullback along `h` of the evaluation pairing of `𝒪_{𝐏(ℰ)}(1)`.

This is the monoidal half of `hΦ`. It is
`Stacks.Monoidal.isoOfTensorInverseBraided_tensorHom_comp`, whose snake hypothesis is discharged
by `Stacks.ProjectiveBundleConormal.hasTrivialSelfBraiding_pullbackInverseTautologicalTwist`. -/
theorem inverseTwistBundleBaseChangeIso_tensorHom_comp :
    ((symTwistBundleBaseChangeIso g E E' hE).hom ⊗ₘ
        (inverseTwistBundleBaseChangeIso g E E' hE).hom) ≫
      (invertibleEvaluation (tautologicalTwist E' (symPieces E'))).hom =
    (pullbackInvertibleEvaluation g E E' hE).hom := by
  apply Stacks.Monoidal.isoOfTensorInverseBraided_tensorHom_comp
    (hasTrivialSelfBraiding_pullbackInverseTautologicalTwist g E E' hE)

/-- **`Φ` as an isomorphism**: `h^*((π^*\ker q) ⊗ 𝒪(-1)) ≅ (π'^*\ker q') ⊗ 𝒪'(-1)`. Tag 01CD
splits the pullback over the tensor product, and the two factors are then compared separately by
`Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso` and
`inverseTwistBundleBaseChangeIso`. -/
def twistedSourceBaseChangeIso :
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj (twistedSource E Q) ≅
      twistedSource E' Q' :=
  pullbackTensorComparisonIso (bundleBaseChangeHom g E E' hE)
      ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
      (inverseTautologicalTwist E) ≪≫
    MonoidalCategory.tensorIso (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq)
      (inverseTwistBundleBaseChangeIso g E E' hE)

/-- **`Φ`**, at the spelling
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_source` takes its first
hypothesis at. This is the forward map of
`Stacks.ProjectiveBundleConormal.twistedSourceBaseChangeIso`; the ascription is the one crossing
between `AlgebraicGeometry.Scheme.Modules.pullback` and
`RingedSpaceModuleAdjunction.modulePullback`, which are definitionally the same functor. -/
def twistedSourceBaseChange :
    (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).obj (twistedSource E Q) ⟶
      twistedSource E' Q' :=
  (twistedSourceBaseChangeIso g E E' hE Q Q' hL hq).hom

/-- **`Φ` spelled out**: Tag 01CD's comparison followed by the tensor product of the two factor
comparisons.

Stated for `Stacks.ProjectiveBundleConormal.twistedSourceBaseChangeIso`, whose source is
ascribed at `AlgebraicGeometry.Scheme.Modules.pullback`, rather than for
`twistedSourceBaseChange`, whose source is ascribed at
`RingedSpaceModuleAdjunction.modulePullback`; the two morphisms are the same term, and the
decomposition is the same statement, but reading it at the second spelling makes the equation
cross between the two pullback functors and that crossing exhausts the
recursion depth now that the twist factor is `Stacks.Monoidal.isoOfTensorInverseBraided`. -/
theorem twistedSourceBaseChangeIso_hom :
    (twistedSourceBaseChangeIso g E E' hE Q Q' hL hq).hom =
      (pullbackTensorComparisonIso (bundleBaseChangeHom g E E' hE)
            ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
            (inverseTautologicalTwist E)).hom ≫
        (MonoidalCategory.tensorIso (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq)
            (inverseTwistBundleBaseChangeIso g E E' hE)).hom :=
  Iso.trans_hom
    (pullbackTensorComparisonIso (bundleBaseChangeHom g E E' hE)
      ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
      (inverseTautologicalTwist E))
    (MonoidalCategory.tensorIso (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq)
      (inverseTwistBundleBaseChangeIso g E E' hE))

/-- **`Φ` is invertible.** Both factors of
`Stacks.ProjectiveBundleConormal.twistedSourceBaseChangeIso` are isomorphisms, and
`conormalCanonicalMap_baseChange_of_source` does not need `Φ` to be one; it is recorded because
the clause of Tag 0B3V it serves is a statement about isomorphisms. -/
instance isIso_twistedSourceBaseChange :
    IsIso (twistedSourceBaseChange g E E' hE Q Q' hL hq) :=
  inferInstanceAs (IsIso (twistedSourceBaseChangeIso g E E' hE Q Q' hL hq).hom)

/-- **The pullback along `h` of the untwisted tautological map `ṽ`**, read through Tag 01CD and
the pulled-back evaluation pairing: Tag 01CD's comparison, followed by the pullback of the
untwisted tautological map whiskered by `h^*𝒪(-1)` and then the pulled-back evaluation pairing,
is the pullback of `ṽ` read in `𝒪_{𝐏(ℰ')}`.

This is Tag 01CD's half of `hΦ`: the naturality of
`Stacks.ProjectiveBundleConormal.pullbackTensorComparison` in the first variable, followed by
the cancellation of that comparison against itself inside
`Stacks.ProjectiveBundleConormal.pullbackInvertibleEvaluation`. -/
theorem pullbackKernelTautologicalMapTwisted :
    (pullbackTensorComparisonIso (bundleBaseChangeHom g E E' hE)
          ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
          (inverseTautologicalTwist E)).hom ≫
        ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
            (kernelTautologicalMap E Q) ▷
          (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).obj
            (inverseTautologicalTwist E)) ≫
      (pullbackInvertibleEvaluation g E E' hE).hom =
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
        (kernelTautologicalMapTwisted E Q) ≫
      modulePullbackUnitToUnit (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom := by
  have hn := pullbackTensorComparison_naturality_left (bundleBaseChangeHom g E E' hE)
    (kernelTautologicalMap E Q) (inverseTautologicalTwist E)
  have hr : (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
        (kernelTautologicalMap E Q ▷ inverseTautologicalTwist E) ≫
      (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
        (invertibleEvaluation (tautologicalTwist E (symPieces E))).hom =
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
      (kernelTautologicalMapTwisted E Q) :=
    ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map_comp _ _).symm
  exact pullbackUntwistAux _ _ _ _ _ _ _ hn hr

/-! ### The base change of the untwisted tautological map -/

/-- **The comparison of the tautological twists is pinned**, restated at this file's spelling of
the bundles. This is `Stacks.RelativeProj.symTwistBaseChangeIso_spec` with
`Stacks.ProjectiveBundle.baseChangeHom` and `isQuasicoherentPieces_of_isQuasicoherent` read as
`Stacks.ProjectiveBundleConormal.bundleBaseChangeHom` and `symPieces`, and it is the *only*
place that crossing is made inside an equation of morphisms. -/
theorem twistQuotientPullback_comp_symTwistBundleBaseChangeIso :
    Stacks.Chow.GenuineChern.twistQuotientPullback g (symPieces E) (symPieces E')
          (bundleBaseChangeHom g E E' hE)
          (bundleBaseChangeHom_comp_toBase g E E' hE) ≫
        (symTwistBundleBaseChangeIso g E E' hE).hom =
      Stacks.Chow.GenuineChern.twistQuotientTarget g (symPieces E') hE.inv :=
  Stacks.RelativeProj.symTwistBaseChangeIso_spec g E E' hE

/-- **The pinning of the twist comparison, with both of its sides spelled out.**
`Stacks.Chow.GenuineChern.twistQuotientPullback` and `twistQuotientTarget` are unfolded and the
left-hand side reassociated.

Separate from
`Stacks.ProjectiveBundleConormal.twistQuotientPullback_comp_symTwistBundleBaseChangeIso` on
purpose: the two unfoldings and the reassociation are affordable from the restated equation and
are *not* affordable from
`Stacks.RelativeProj.symTwistBaseChangeIso_spec` directly, where they would have to be made in
the same `isDefEq` as the crossing of the two spellings and the whole exhausts the heartbeat
budget. -/
@[ega "II 4.2.10"]
theorem twistPullbackSourceIso_comp_pullbackTautologicalMap :
    (Stacks.Chow.GenuineChern.twistPullbackSourceIso g (symPieces E) (symPieces E')
          (bundleBaseChangeHom g E E' hE)
          (bundleBaseChangeHom_comp_toBase g E E' hE)).hom ≫
        (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
          (tautologicalMap E (symPieces E)) ≫
        (symTwistBundleBaseChangeIso g E E' hE).hom =
      (Scheme.Modules.pullback (bundle E').toBase).map hE.inv ≫
        tautologicalMap E' (symPieces E') :=
  reassocAux _ _ _ _ (twistQuotientPullback_comp_symTwistBundleBaseChangeIso g E E' hE)

/-- **The base change of the untwisted tautological map, read against the square's
identification.** The previous statement is pinned against
`Stacks.Chow.GenuineChern.twistPullbackSourceIso`; this one is pinned against
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso`, which is what the kernel factor of `Φ`
is built from. The two compose to the identity by
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_comp_twistPullbackSourceIso`. -/
theorem schemePullbackCompIso_comp_pullbackTautologicalMap :
    (schemePullbackCompIso (bundleBaseChangeHom_comp_toBase g E E' hE).symm E).hom ≫
        (Scheme.Modules.pullback (bundle E').toBase).map hE.inv ≫
          tautologicalMap E' (symPieces E') =
      (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
          (tautologicalMap E (symPieces E)) ≫
        (symTwistBundleBaseChangeIso g E E' hE).hom :=
  cancelLeftAux (schemePullbackCompIso_comp_twistPullbackSourceIso g E E' hE)
    (twistPullbackSourceIso_comp_pullbackTautologicalMap g E E' hE)

/-- `Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso` spelled out: the square's
identification followed by the pullback of the kernel comparison. One definitional crossing,
`CategoryTheory.Functor.mapIso`. -/
theorem kernelTwistedBaseChangeIso_hom :
    (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq).hom =
      (schemePullbackCompIso (bundleBaseChangeHom_comp_toBase g E E' hE).symm
          (kernel Q.q)).hom ≫
        (Scheme.Modules.pullback (bundle E').toBase).map
          (Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).1.hom :=
  Iso.trans_hom _ _

/-- `Stacks.ProjectiveBundleConormal.kernelTautologicalMap` spelled out. -/
theorem kernelTautologicalMap_eq :
    kernelTautologicalMap E' Q' =
      (Scheme.Modules.pullback (bundle E').toBase).map (kernel.ι Q'.q) ≫
        tautologicalMap E' (symPieces E') :=
  rfl

/-- The pullback along `h` of `Stacks.ProjectiveBundleConormal.kernelTautologicalMap`, split over
its two factors. One `CategoryTheory.Functor.map_comp` and one unfolding. -/
theorem pullback_map_kernelTautologicalMap :
    (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
          ((Scheme.Modules.pullback (bundle E).toBase).map (kernel.ι Q.q)) ≫
        (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
          (tautologicalMap E (symPieces E)) =
      (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
        (kernelTautologicalMap E Q) :=
  ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map_comp _ _).symm

/-- **The kernel factor of `Φ` carries the base change of `v` to `v'`**: `h^*v` followed by the
comparison of the tautological twists is the comparison of the kernels followed by `v'`.

This is the mathematical content of `hΦ` on the first tensor factor. Its inputs are the
naturality of the square's identification at `kernel.ι q`, the compatibility of
`Stacks.Divisors.quotientKernelBaseChange` with `kernel.ι`, and
`Stacks.ProjectiveBundleConormal.schemePullbackCompIso_comp_pullbackTautologicalMap`; all the
reassociation is paid by
`Stacks.ProjectiveBundleConormal.kernelFactorAux` over a bare category. -/
theorem kernelTwistedBaseChangeIso_comp_kernelTautologicalMap :
    (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq).hom ≫ kernelTautologicalMap E' Q' =
      (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
          (kernelTautologicalMap E Q) ≫
        (symTwistBundleBaseChangeIso g E E' hE).hom := by
  apply kernelFactorAux (kernelTwistedBaseChangeIso_hom g E E' hE Q Q' hL hq)
    (kernelTautologicalMap_eq E' Q')
    (schemePullbackCompIso_naturality (bundleBaseChangeHom_comp_toBase g E E' hE).symm
      (kernel.ι Q.q))
    (mapEqAux (Scheme.Modules.pullback (bundle E').toBase)
      (Stacks.Divisors.quotientKernelBaseChange g E E' hE Q Q' hL hq).2)
    (schemePullbackCompIso_comp_pullbackTautologicalMap g E E' hE)
    (pullback_map_kernelTautologicalMap g E E' hE Q)

/-- **`hΦ`, the base change of the untwisted tautological map**, at the scheme spelling of the
pullback: `Φ` followed by `ṽ'` is the pullback of `ṽ` read in `𝒪_{𝐏(ℰ')}`.

Tag 01CD's comparison is the first factor of `Φ` and also the first factor of
`Stacks.ProjectiveBundleConormal.pullbackKernelTautologicalMapTwisted`, so it cancels; what
remains is the kernel factor
(`Stacks.ProjectiveBundleConormal.kernelTwistedBaseChangeIso_comp_kernelTautologicalMap`) moved
across the `⊗` and the twist factor
(`Stacks.ProjectiveBundleConormal.inverseTwistBundleBaseChangeIso_tensorHom_comp`).

The monoidal step is taken with an *unascribed* `have`: writing the intermediate
equation out with `⊗ₘ` and `▷` in a statement of its own is what does not elaborate, because
the implicit object arguments of `MonoidalCategoryStruct.tensorHom` then have to be crossed
against those of the pairing. Taken from the types of the terms themselves there is nothing to
cross. -/
theorem twistedSourceBaseChangeIso_comp_kernelTautologicalMapTwisted :
    (twistedSourceBaseChangeIso g E E' hE Q Q' hL hq).hom ≫
        kernelTautologicalMapTwisted E' Q' =
      (Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map
          (kernelTautologicalMapTwisted E Q) ≫
        modulePullbackUnitToUnit (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom := by
  have htw := tensorWhiskerAux (kernelTwistedBaseChangeIso g E E' hE Q Q' hL hq).hom
    (inverseTwistBundleBaseChangeIso g E E' hE).hom (kernelTautologicalMap E' Q')
    ((Scheme.Modules.pullback (bundleBaseChangeHom g E E' hE)).map (kernelTautologicalMap E Q))
    (symTwistBundleBaseChangeIso g E E' hE).hom
    (invertibleEvaluation (tautologicalTwist E' (symPieces E'))).hom
    (kernelTwistedBaseChangeIso_comp_kernelTautologicalMap g E E' hE Q Q' hL hq)
  apply assembleAux (twistedSourceBaseChangeIso_hom g E E' hE Q Q' hL hq)
    (tensorCompAux htw (inverseTwistBundleBaseChangeIso_tensorHom_comp g E E' hE))
    (pullbackKernelTautologicalMapTwisted g E E' hE Q)

/-- **`hΦ` at the `modulePullback` spelling** that
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_source` takes its second
hypothesis at. This declaration is the one crossing between
`AlgebraicGeometry.Scheme.Modules.pullback` and
`RingedSpaceModuleAdjunction.modulePullback`, as `twistedSourceBaseChange` is for the morphism
itself. -/
theorem twistedSourceBaseChange_comp_kernelTautologicalMapTwisted :
    twistedSourceBaseChange g E E' hE Q Q' hL hq ≫ kernelTautologicalMapTwisted E' Q' =
      (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).map
          (kernelTautologicalMapTwisted E Q) ≫
        modulePullbackUnitToUnit (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom :=
  twistedSourceBaseChangeIso_comp_kernelTautologicalMapTwisted g E E' hE Q Q' hL hq

/-! ### The clause with `Φ` supplied -/

variable {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
  (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
  (hqe' : (Scheme.Modules.pullbackId X').inv.app E' ≫
    (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
      (Scheme.Modules.pullbackComp σ' (bundle E').toBase).inv.app E' ≫
        (Scheme.Modules.pullback σ').map (tautologicalMap E' (symPieces E')) ≫ e'.hom = Q'.q)
  [IsImmersion σ] [IsImmersion σ']

include hqe hqe' in
/-- **Tag 0B3V's base-change clause for the conormal isomorphism, with the source comparison and
the base change of the untwisted tautological map supplied.** This is
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_source` at
`Φ = Stacks.ProjectiveBundleConormal.twistedSourceBaseChange`, with its `hΦ` discharged by
`Stacks.ProjectiveBundleConormal.twistedSourceBaseChange_comp_kernelTautologicalMapTwisted`, so
that the clause now rests on a single hypothesis: the source coherence `hsrc`. That is a
statement about the `Φ` built in this file and it is not proved here; see this module's "What is
still owed, precisely". -/
theorem conormalCanonicalMap_baseChange_of_twistedSourceBaseChange
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (hsrc : (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
            (twistedSource E Q)).hom ≫
          (modulePullback σ'.toLRSHom.toShHom).map
            (twistedSourceBaseChange g E E' hE Q Q' hL hq)) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        conormalCanonicalMap E' Q' hσ' e' hqe' =
      (Scheme.Modules.pullback g).map (conormalCanonicalMap E Q hσ e hqe) ≫
        Stacks.Conormal.conormalBaseChangeMap comm :=
  conormalCanonicalMap_baseChange_of_source g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe' comm
    (twistedSourceBaseChange g E E' hE Q Q' hL hq)
    (twistedSourceBaseChange_comp_kernelTautologicalMapTwisted g E E' hE Q Q' hL hq) hsrc

end Stacks.ProjectiveBundleConormal

end
