module

public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
import StacksCore.Tactic.StacksAttribute

/-! # A left dual in `D(O)` is the derived dual `RSheafHom(M, O)`

Let `(C, O)` be a ringed site and let `M` be an object of `D(O)` admitting a left dual `N` in the
symmetric monoidal category `D(O)` of Stacks 0FPT, that is, an exact pairing with coevaluation
`η : O ⟶ M ⊗^L_O N` and evaluation `ε : N ⊗^L_O M ⟶ O`. Then

`M^∨ = RSheafHom(M, O) ≅ N`,

so the left dual is the dual object constructed in Example 0FPU; the identification is the
transpose, under the pairing, of the evaluation `ε' : M^∨ ⊗ M ⟶ O` of Example 0FPU, and it
carries `ε'` to `ε`. That is the second assertion of Stacks 0FPV.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedMonoidalTensorComparison`: the tensor product of the
  symmetric monoidal structure of Stacks 0FPT is the derived tensor product that Stacks 08J8 is
  stated over.
* `AlgebraicGeometry.RingedSite.derivedMonoidalUnitIso`: its unit is the structure sheaf in
  degree zero.
* `AlgebraicGeometry.RingedSite.derivedDualEvaluationMonoidal`: the evaluation of Example 0FPU
  read in the monoidal category of Stacks 0FPT, `ε' : M^∨ ⊗ M ⟶ 𝟙`.
* `AlgebraicGeometry.RingedSite.DerivedCurrySourceNatural`: naturality of the bijection of
  Stacks 08J8 in its source variable, as a proposition; it holds, by
  `AlgebraicGeometry.RingedSite.derivedCurrySourceNatural`.
* `AlgebraicGeometry.RingedSite.derivedDualToLeftDual`: the morphism `M^∨ ⟶ N` which the exact
  pairing matches with `ε'`.
* `AlgebraicGeometry.RingedSite.derivedDualIsoLeftDual` and
  `AlgebraicGeometry.RingedSite.leftDualIsoDerivedDual`: the identification `M^∨ ≅ N` and its
  inverse.

## Main results

* `AlgebraicGeometry.RingedSite.whiskerRight_derivedDualToLeftDual`: the morphism `M^∨ ⟶ N`
  carries the evaluation `ε` of the pairing back to the evaluation `ε'` of Example 0FPU. This
  pins it down — it is not an unconstrained morphism of its type — and it is the compatibility
  of the two duality data on the evaluation side.
* `AlgebraicGeometry.RingedSite.derivedCurrySourceNatural`: the proposition
  `DerivedCurrySourceNatural` holds, so none of the declarations below carries it.
* `AlgebraicGeometry.RingedSite.isIso_derivedDualToLeftDual`: **Stacks 0FPV**, second assertion:
  that morphism is an isomorphism, so a left dual of `M` *is* the dual object of Example 0FPU.

## What this file does not contain

Stacks 0FPV has two assertions, and only the second is proved here.

* That `M` is **perfect** is **absent**: no declaration below asserts
  `AlgebraicGeometry.RingedSite.IsPerfect M`. The source proves it by a local argument —
  restrict the pairing to a slice, write the coevaluation there as a finite sum `Σ fᵢ ⊗ gᵢ`
  against a K-flat complex of flat modules (Stacks 06YF), exhibit `M` as a direct summand of a
  finitely generated subcomplex, read off finite Tor amplitude, and induct on pseudo-coherence
  down to Stacks 08CP — and only then applies the criterion of Stacks 08G7,
  `Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion`.

  The **first step is available**. `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal` makes derived
  restriction to a localized site strongly monoidal, unconditionally, for the structure of
  Stacks 0FPT in which left duals are taken here; composed with
  `CategoryTheory.ExactPairing.map` of `StacksFrontier.CategoryTheory.Monoidal.Rigid`, which this
  file imports, it restricts the pairing to the slice. That composition is
  `AlgebraicGeometry.RingedSite.exactPairingRestrict` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualRestrictsToSlices`. It is only
  Mathlib that has the reflections `CategoryTheory.ExactPairing.ofFaithful` and
  `CategoryTheory.ExactPairing.ofFullyFaithful` and not the direct image.

  **There is no universe obstruction.** `AlgebraicGeometry.RingedSite.isPerfect_of_locally` is
  stated at `RingedSite.{u, u, w}`, the sections of the structure sheaf at an arbitrary universe,
  and its hypotheses are only the four sheafification side conditions of the ambient cluster.
  The `{0}`-pinned comparison `Stacks.SheafOfModules.restrictComplexAlongOverIso` and the four
  exactness instances of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations` each
  have a universe-polymorphic counterpart, which the general form of Stacks 08FU part (3) uses,
  and `isPerfect_of_forall_coveringFamily_strictlyPerfect` of Stacks 08G6 part (1), to which it
  reduces, is universe polymorphic too.

  **The far end of the Tor-amplitude route is on the diagonal as well.**
  `torAmplitudePerfectnessCriterion` of Stacks 08G7, the Stacks 08G8 criterion
  `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_iff_isPseudoCoherent_and_`
  `locallyHasFiniteTorDimension`, and the Stacks 08GA summand lemmas
  `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_left_of_biprod` and
  `isPerfect_right_of_biprod` are all stated on the diagonal `RingedSite.{u, u, u}`.
  `IsStrictlyPerfect` of Stacks 08FL is not monomorphic in `Type` (it carries four independent
  universes),
  `Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude` is
  stated at `RingedSite.{u, v, w}` with everything free, and
  `Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree` wants `max u v`, which the
  diagonal satisfies. The inputs stated at a fixed sections universe, and the polymorphic
  replacement for each, are listed in the implementation notes of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/PerfectnessCriterion.lean`. The
  diagonal, not a freer shape, is the ceiling: a slice of a `RingedSite.{u, v, w}` is a
  `RingedSite.{max u v, v, max u v}`, and Stacks 08G7 is read on every slice.

  What perfectness still owes is therefore steps 2 to 6 of the source argument — the local
  finite-sum expression of the coevaluation, the finitely generated bounded subcomplex it factors
  through (whose monoidal half is
  `CategoryTheory.ExactPairing.retractOfCoevaluationFactors`), the Tor amplitude, and the
  induction on pseudo-coherence. The **ringed-space** proof of the
  analogous Stacks 0FPD takes a shorter route than the source's and does not touch Tor amplitude
  at all: `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing` of
  `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualIsPerfect` goes through the
  locality of perfectness, a bounded-above K-flat representative, and "a retract of a perfect
  object is perfect". Compared with that route, what the site side lacks is exactly three
  things, and the first two are assembly rather than mathematics:

  * the coevaluation read as a chain map out of `O[0]`. Every ingredient is available —
    `AlgebraicGeometry.RingedSite.derivedMonoidalUnitIso` below,
    `AlgebraicGeometry.RingedSite.isStrictlyPerfect_structureSheafComplex` of
    `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect`, Stacks 08FR
    part (1) `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, and the K-flat
    resolutions of Stacks 06YS `Stacks.SheafOfModules.exists_isKFlat_isFlat_quasiIso_epi`
    (`StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTermsSurjective`) and
    `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` — and the first step of the
    local finite-sum expression is available too, as
    `AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection` of
    `StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalPureTensorSections`, which
    is stated at `RingedSite.{u, u, u}` and whose own module docstring names it as this step;
  * the retract itself, which on the monoidal side is the fully generic
    `CategoryTheory.nonempty_retract_map_of_factorization` of
    `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract`, usable verbatim
    along `AlgebraicGeometry.RingedSite.derivedRestriction`;
  * the finitely generated subcomplex engine. **The sieve-indexed span engine is available**, in
    three modules of `StacksDraft.CategoryTheory.Sites.Cohomology.Perfect`:
    `ExtensionByZeroArrowSections`, `SieveIndexedSpan` and `SieveIndexedSubcomplexGenerators`,
    over a small site with `HasSheafify J AddCommGrpCat.{u}`. The index is a pair:
    `Stacks.Sites.ExtensionByZero.GenIdx U W` is
    `Σ α, (W ⟶ U α)`, `Stacks.Sites.ExtensionByZero.genAt` is the generator of `j_{U!}O_U` at an
    arrow, `Stacks.Sites.ExtensionByZero.exists_sieve_eq_sum_smul_genAt` is the arrow-indexed
    replacement of `exists_eq_smul_res_extGen`, `Stacks.Sites.ExtensionByZero.InSpan` is the
    span of a set of those indices, `spanSieve_mem` and `spanSieveFinset_mem` replace
    `exists_nhd_inSpan` and `exists_nhd_inSpan_finset`, and
    `Stacks.Sites.ExtensionByZero.exists_sieve_closed_span` replaces `exists_closed_span`: over
    a covering sieve, a finite graded set of arrow generators spanning the given sections and
    closed under the differential. `exists_resS_eq_zero_of_not_mem` has no counterpart and needs
    none — the arrow is part of the index, not a side condition on it. The generator side is
    Stacks 03EW part (3), `Stacks.SheafOfModules.exists_epi_from_sum_extensionByZero` of
    `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionByExtensionsByZero`,
    and the resolution step it feeds is the universe-general Stacks 05T7
    `CochainComplex.exists_quasiIso_prop`.

  Closing the space route on a site also needs "a retract of a perfect object is perfect" there,
  and that step is **available**: `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_`
  `retract` of `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Retracts`, at this cluster's
  diagonal `RingedSite.{u, u, u}`. It is Stacks 08GA — on the diagonal — applied to the
  splitting of a retract in a pretriangulated category,
  `CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction`, which was already public and
  mentions no space.

  **The shorter ringed-space route does not close 0FPV on a site, and the subcomplex engine is
  not the only thing it is missing.** What
  the space proof extracts from its subcomplex is a *strictly perfect* local model: over the
  shrunken open `Z`, `Stacks.Cohomology.LeftDualPerfect.restrictImageIso` identifies the
  restriction of the degree-`n` term with a finite sum of copies of `O_Z`, because
  `Stacks.Cohomology.LeftDualPerfect.extUnitIso`, the unit `O_Z ⟶ (j_{Z!}O_Z)|_Z`, is an
  isomorphism. On a site that unit is an isomorphism exactly when `Z` is **subterminal**:
  `Stacks.SheafOfModules.ExtensionByZero.isIso_extensionByZeroAdjunction_unit`
  (`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroUnitIso.lean:113`) carries
  `IsIso (Over.forgetAdjStar U).unit`, which `isIso_forgetAdjStar_unit_opens` (`:42`) supplies
  for an open of a space because morphisms of opens are unique, and which Stacks 00Y2,
  `CategoryTheory.GrothendieckTopology.isIso_unit_and_sheafAdjunctionCocontinuous_counit_of_`
  `isSubterminal` (`StacksFrontier/CategoryTheory/Sites/Localization/MoreLocalization.lean:165`),
  records as the general condition. Over a general ringed site `j_{Z!}O_Z` restricted to the
  slice over `Z` is free on the *arrows* into `Z`, so it is not a direct summand of a finite
  free module and `IsStrictlyPerfect`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/ConeOfAMorphism.lean:196`) is
  not available for the subcomplex the engine generates. That subcomplex is *finitely
  generated*, which is what the source's own route consumes, and not strictly perfect.

  So perfectness on a site needs the source's own route, and both of its ends are available.
  Stacks 08G7 `Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/PerfectnessCriterion.lean:317`)
  concludes `AlgebraicGeometry.RingedSite.IsPerfect` from `HasTorAmplitude T E a b` together
  with `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom E (a - 1)`, and Stacks 08G8
  `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_isPseudoCoherent_of_`
  `locallyHasFiniteTorDimension`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PerfectnessCriterion.lean:218`) does the
  same from pseudo-coherence and locally finite Tor dimension; `Stacks.SheafOfModules.`
  `DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/FlatRepresentative.lean:117`),
  Stacks 08G3 `hasTorAmplitude_of_biprod`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/DirectSummands.lean:79`) and the
  retract form that lemma is read at,
  `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_retract` (`:69` of the same
  file), are what turn "a direct summand of a bounded complex of flat modules" into finite Tor
  amplitude. The retract form is the shape the pairing produces, and it needs no splitting of
  the retract: Tor amplitude is a vanishing statement about the image of a functor.

  **The step the pseudo-coherence descent ends on is proved; the induction that feeds it is
  not.** The descent runs from `IsPseudoCoherentFrom E m` to `IsPseudoCoherentFrom E (m - 1)`,
  steps 5 and 6 of the source's proof. The end of that descent is
  `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_bottomCover`
  (`StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/BottomCoverDescent.lean:176`): it concludes
  `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom E n` from a local approximation
  `α : 𝒦 ⟶ E|_V` in degrees `≥ n` whose source is bounded, vanishes below `n`, is a direct
  summand of a finite free module in every degree *above* `n`, and in degree `n` is only
  *covered* by such a summand — an epimorphism `𝒜 ⟶ 𝒦^n` and nothing more. That is the source's
  own last sentence, "a surjection `O^{⊕r} ⟶ 𝒦^{m-1}` then gives the required complex", and it
  is the one place in the route where a merely finitely generated degree is admissible — which
  is why the subcomplex not being strictly perfect (two paragraphs below) does not block the
  argument. The derived form is `isPseudoCoherentFrom_Q_of_local_bottomCover` (`:200` of the same
  file); the complex it builds is `HomologicalComplex.bottomCover` of
  `StacksFrontier.Algebra.Homology.CoverOfTheLowestTerm`, the degreewise pullback that replaces
  `𝒦^n` by `𝒜`, and the cohomology comparison is read with
  `HomologicalComplex.isIso_homologyMap_of_epi_f` and
  `HomologicalComplex.epi_homologyMap_of_epi_f` of
  `StacksFrontier.Algebra.Homology.HomologyOfADegreewiseEpi`.

  What the descent still owes is its **input**: the approximation `α` itself, which is the body
  of steps 5 and 6 — the finitely generated subcomplex `𝒦` assembled from the `fᵢ`, the `d(fᵢ)`
  and a strictly perfect complex above degree `m`; the realization of `s ∘ i` as a map of
  complexes by Stacks 08FR; the homotopy that kills it, enlarging `𝒦^{m-1}` by the image of
  `h^m`; and the diagram of triangles that makes `H^{m-1}(σ_{≤ m-1}𝒦) ⟶ H^{m-1}(ℒ)` surjective.

  **The subcomplex `𝒦` is built, and the two remaining steps are the triangle bookkeeping
  rather than missing machinery.** `Stacks.Sites.ExtensionByZero.subcomplex` and its inclusion
  `Stacks.Sites.ExtensionByZero.subcomplexι` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SieveIndexedSubcomplex` consume the
  predicate — through `Stacks.Sites.ExtensionByZero.exists_coeff_of_inSpan`, which extracts
  coefficients from `Submodule.span` membership — and
  `Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` assembles the engine's
  `exists_sieve_closed_span` into the statement the route wants: over a covering sieve of `V`,
  over each member `W` a cochain complex with a degreewise *monomorphism* into `P`, each term a
  quotient of a finite sum of copies of `j_{W!}O_W`, zero in the degrees below `L` and in the
  degrees where `P` vanishes, and carrying sections over the restrictions of the given ones. It
  is finitely generated and not strictly perfect, for the subterminality reason recorded two
  paragraphs below, which is exactly what the bottom-cover descent admits.

  The construction factors through `Stacks.Sites.ExtensionByZero.genSubcomplex`, the subcomplex
  generated degreewise by any family `g n : A n ⟶ P^n` admitting a lift `A n ⟶ A (n + 1)` of the
  differential. That generality is not decoration: step 6's enlargement of `𝒦^{m-1}` by the
  image of `h^m` is a family of the same shape with a different `A`, so it is an instance of
  `genSubcomplex` and needs no second construction. The lift is not itself a differential: its
  coefficients are chosen one degree at a time, so nothing makes
  `Stacks.Sites.ExtensionByZero.liftMap` composed with itself zero, and there is accordingly no
  chain map whose degreewise image could be taken. `genSubcomplex` recovers `d ∘ d = 0` on the
  images instead, where `image.ι` is monic and `P`'s own `d ∘ d = 0` is available.

  Worth recording against that file: `Stacks.AlgebraicGeometry.ExtendBoundedComplex.subComplex`
  (`StacksFrontier/AlgebraicGeometry/DerivedCoherent/ExtendBoundedComplex.lean:103`) already builds
  a degreewise-image subcomplex in any abelian category, with term `Im(A^n ⊕ A^{n-1} ⟶ P^n)` and
  **no** closedness hypothesis at all — it is `genSubcomplex` at the lift
  `biprod.desc biprod.inr 0`. So a subcomplex containing prescribed sections can be had on a
  site without `exists_sieve_closed_span`; what the engine's closedness buys is the smaller
  generator count `(S n).card` instead of `(S n).card + (S (n-1)).card`. It is not imported by
  the new file — not because of a cycle, its closure contains nothing under
  `StacksDraft.CategoryTheory.Sites.Cohomology`, but because that closure is 514 in-repo modules
  against the new file's 30.

  Stacks 08FR is proved on a site in **both** parts: part (2), "a map of complexes whose class in `D(O_U)` vanishes is homotopic
  to zero on a covering", is
  `AlgebraicGeometry.RingedSite.exists_coveringSieve_homotopy_zero_of_derived_zero`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/LocalNullHomotopyOfDerivedZero.`
  `lean:87`), at `RingedSite.{u, v, w}` with the modules in `SheafOfModules.{w}`; the one
  universe-sensitive input of its proof is Stacks 08FP (1) at its diagonal-universe form.

  **The triangle bookkeeping is proved, in all four of its pieces.** The pieces, in the order the source's inductive step
  performs them:

  1. The strictly perfect `ℰ ⟶ M` with its cone `ℒ` vanishing in degrees `≥ m` is
     `AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_with_cone`
     (in `CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalApproximationWithCone.lean`):
     over the arrows of a covering presieve, a strictly perfect `P` vanishing below `m`, a map
     `α : P ⟶ E|_V` invertible on cohomology above `m` and epic in degree `m`, and
     `H^i(C(α)) = 0` for every `i ≥ m`. Both halves were already in the library: the truncated
     approximation is the stupid truncation in degrees `≥ m`, by
     `Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc_general` and
     `HomologicalComplex.isIso_homologyMap_ιStupidTrunc_embeddingUpIntGE`, and the cone vanishing
     is
     `CochainComplex.isZero_homology_mappingCone_of_approximation`
     (`StacksFrontier/Algebra/Homology/DerivedCategory/MappingConeApproximation.lean:72`), itself a
     reading of `DerivedCategory.triangle_obj₃_isLE_of_approximation`
     (`StacksFrontier/Algebra/Homology/DerivedCategory/TriangleApproximation.lean:66`) at the
     mapping-cone triangle. The triangle is a mapping-cone triangle, so `ℒ` is a complex, which
     is what the descent below consumes.
  2. The two applications of 08FR to `s ∘ i` are
     `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_homotopy_of_section`
     (`StrictlyPerfect/LocalComplexMapOfARetraction.lean:160`): given `t : M ⟶ K` in `D(O|_U)`
     with `t ≫ Q(κ) = 𝟙`, along a covering sieve `t ∘ i` is a map of complexes `σ` and `σ ≫ κ`
     is homotopic to `i`. The difficulty is that part (1) restricts with `SheafOfModules.overMap` and part (2) with
     `SheafOfModules.overFunctor` onto an iterated slice, so neither could be fed the other's
     output; `exists_coveringSieve_homotopy_zero_of_derived_zero_overMap` (`:114` of the same
     file) closes that along `Stacks.SheafOfModules.sliceBackwardComplexIso`.
  3. The morphism of triangles with its dotted arrow is
     `CategoryTheory.Pretriangulated.exists_triangleMorphism`
     (`StacksFrontier/CategoryTheory/Triangulated/TriangleRetractHomology.lean:73`), TR3 packaged
     as a morphism of the category `Triangle C` so that two of them compose.
  4. The comparison in degree `m - 1` is
     `CategoryTheory.Pretriangulated.isSplitEpi_hom₃_of_comp` (`:100` of the same file), and it
     is **stronger than the source's**. The source reads the two stacked morphisms of triangles
     through `H^{m-1}`, notes that the outer columns compose to the identity, and concludes that
     `H^{m-1}(σ_{≤ m-1}𝒦) ⟶ H^{m-1}(ℒ)` is surjective. But their composite is a self-morphism
     of a distinguished triangle which is the identity on the first two vertices, so the
     triangulated five lemma — Mathlib's `isIso₃_of_isIso₁₂`, carrying `@[stacks 014A]` — makes
     its third component an isomorphism in `D(O)` itself, and `σ_{≤ m-1}𝒦 ⟶ ℒ` is therefore a
     split epimorphism before any homological functor is applied. No exact sequence, and no
     hypothesis that the middle row be distinguished.

  The brutal truncation the construction needs is available —
  `Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc` of
  `StrictlyPerfect/BrutalTruncation.lean:72`, at a general site and a free module universe.

  **What the inductive step still needs is the retract, which is the hypothesis `t` of item 2 and
  of item 4.** On a site nothing produces it yet, but the remainder is three named pieces and
  not a chain. The two ends are generic and available —
  `CategoryTheory.ExactPairing.retractOfCoevaluationFactors`
  (`StacksFrontier/CategoryTheory/Monoidal/Rigid.lean:101`) turns a factorization of the
  coevaluation into a retract, and
  `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract`
  (`Perfect/Retracts.lean:132`) draws perfectness from one — and of what sits between
  them the following is available on a site:

  * the coevaluation read as a morphism between the images of two complexes,
    `AlgebraicGeometry.RingedSite.coevaluationUnitHom` of
    `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualCoevaluation`, pinned down by
    `unitIso_hom_comp_coevaluationUnitHom` and restricted to a slice by
    `coevaluationUnitHomRestrict`, to which Stacks 08FR (1) applies at
    `isStrictlyPerfect_restrictComplex_structureSheafComplex`;
  * the flatness step `Tot(𝒦 ⊗ 𝒩) ⊂ Tot(ℳ ⊗ 𝒩)`,
    `Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f`
    (`Topology/Sheaves/Cohomology/PerfectComplexes/TotalComplexMono.lean:87`), which is stated
    for an arbitrary small site rather than for the site of opens;
  * the decomposition of a section of a total tensor complex into a finite sum of pure tensors
    over a covering, `AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection`
    (`TensorComplex/LocalPureTensorSections.lean:269`), for an arbitrary section;
  * **two further inputs, both present.**
    First, the compatibility of the two models of `Tot` on sections — that file's own note says
    it does not supply it, and another file does:
    `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_inv_tensorComplexSection`
    (`TensorComplex/TotalComplexComparisonSections.lean:84`) carries `tensorComplexSection` to
    `tensorTotalSectionAt`, which is exactly the crossing between the spelling the coevaluation
    lands in and the spelling the decomposition is stated at. Second, the dictionary between a
    chain map out of `O[0]` and its value at the unit section, which the ringed-space route
    carries in `StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/UnitComplexMaps.lean`: on a site it is stronger and already
    proved, as `AlgebraicGeometry.RingedSite.evalAtOneHom` and `structureSheafHomIso`
    (`InternalHom/FromTheStructureSheaf.lean:179`, `:311`), evaluation at `1` being an
    isomorphism of complexes `RSheafHom(O[0], I) ≅ I`.

  Two further inputs of that list are available on a site as well:

  * the cocycle criterion, `Stacks.Cohomology.LeftDualPerfect.d_eq_zero_of_mono`
    (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/TotalComplexLocalSections.lean:229`), generalized in place to an arbitrary
    small site — its one input is `Stacks.SheafOfModules.injective_app_of_mono`, which holds at
    any object of any site, and the open entered only as the object the sections are over;
  * the lift of a decomposed section,
    `AlgebraicGeometry.RingedSite.tensorComplexMap_sum_tensorComplexSection_lift`
    (`TensorComplex/LiftOfPureTensorSums.lean:89`). Its ringed-space form
    `mapBifunctorMap_lift_eq` was **not** generalized in place, and the reason is worth keeping:
    that lemma is written in a different vocabulary, `HomologicalComplex.ιMapBifunctor` of
    `LeftDualPerfect.pureTensor` with restriction by that file's `res` for `W ≤ V` of opens, and
    generalizing it would install a second site-wide pure-tensor vocabulary beside this
    directory's `tensorComplexSection`. The statement also carries no restriction, because a
    presheaf-of-modules restriction `M.val.map g.op` lands in
    `(ModuleCat.restrictScalars …).obj (M.val.obj (op W))` and a sum of pure tensors built from
    such terms is type-correct only up to unfolding `restrictScalars`; the producer's sections
    already live over the member of the covering sieve, and `PresheafOfModules.restrictₛₗ` is the
    spelling with the right target type.

  **The K-flatness identification is available.**
  `isKFlat_iff_kFlat` (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/LeftDualRingedSpaceJoin.lean:132`) is stated at `{C : Type u} [SmallCategory.{u} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})` — an arbitrary small site. Only its
  *file* is in the ringed-space tree.

  **What is left is the assembly, and it is two things, neither a binder generalization.**

  **Piece one is proved.** The chain-level dictionary between a map of complexes out of
  `O[0]` and a degree-zero cocycle section is
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UnitComplexCocycles`: taking the value
  at the unit section `1` is a bijection
  (`AlgebraicGeometry.RingedSite.unitComplexHomEquivCocycles`) from maps of complexes
  `O[0]|_U ⟶ A|_U` onto the sections of `A^0` over `U` killed by the differential, and it commutes
  with restriction along an arrow of the site
  (`AlgebraicGeometry.RingedSite.cocycleOfUnitComplexHom_restrict`). Its halves are
  `cocycleOfUnitComplexHom`, `unitComplexHom_ext`, `cocycleOfUnitComplexHom_d` and
  `unitComplexHomOfCocycle`.

  **No terminal object is assumed anywhere.** The ringed-space dictionary
  (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/UnitComplexMaps.lean:35`, `:109`, `:124`) spreads a section over `op ⊤` by
  `homOfLE le_top`, a lattice fact about `Opens T`, so it does not port by widening a binder. What
  replaces it is that the slice site `C/U` has the terminal object `𝟙 U` for *every* `U`, with no
  hypothesis on `C`, and the whole dictionary is stated over the slice; what does the work is
  Mathlib's `SheafOfModules.unitHomEquiv` on the slice followed by
  `Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`, the value at `1` over `𝟙 U`.
  A port under `[HasTerminal C]` would have been
  faithful — the source's own first move is "assume `C` has a final object `X`" — and was not
  needed.

  Three remarks on the construction.
  The route is Mathlib's `HomologicalComplex.mkHomFromSingle`, which asks that the source be a
  literal `single`; `HomologicalComplex.singleMapHomologicalComplex` is used directly rather than
  through its special case `restrictStructureSheafComplexIso` (`Perfect/Duals.lean:241`),
  which is sealed to `simp` and carries a 280-module closure. A detour through
  `Stacks.SheafOfModules.overFunctorUnitIso` is not needed at all: `(unit O).over U` and
  `unit (O|_U)` are definitionally equal here, which is already what lets
  `structureSheafOver_hom_bijective` be stated by composing `unitHomEquiv` with
  `over_sections_eval_bijective`. And the round trip is `rfl`, every `eqToHom` in
  `singleMapHomologicalComplex` and `mkHomFromSingle` sitting between definitionally equal
  objects; the restriction compatibility is *not* `rfl` and needs the naturality of `(β.f 0).val`
  along `Over.homMk g (by simp) : Over.mk (𝟙 V ≫ g) ⟶ Over.mk (𝟙 U)` — written with `g` rather
  than with `𝟙 V ≫ g`, so that the slice restriction is definitionally
  `PresheafOfModules.restrictₛₗ g.op` — together with `PresheafOfModules.unit_map_one`.

  **Piece two's core is proved.** The site form of `nonempty_retract_restrict` is
  `Stacks.Cohomology.LeftDualOnASite.nonempty_retract_restrict` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualRetractOnASlice`: given K-flat
  representatives of the pairing, `j : 𝒦 ⟶ ℳ`, a `σ : 𝒮 ⟶ ℳ ⊗ 𝒩` whose class is `Q(j) ▷ Q(𝒩)`
  up to `Θ`, and a cocycle section of `𝒮^0` over `U` whose map of complexes out of `O[0]|_U`
  represents the restricted coevaluation, `M|_U` is a retract of `𝒦|_U` in `D(O|_U)`. It is the
  generic `CategoryTheory.nonempty_retract_map_of_factorization` fed
  `(restriction X U).mapDerivedCategory` with
  `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`,
  `(symmetricMonoidalDerived O).unitIso` and `.comparison`, three components of
  `Functor.mapDerivedCategoryFactors`, `coevaluationUnitHom` and piece one's
  `unitComplexHomOfCocycle`.

  Two remarks on it. The three spellings of the slice's structure sheaf needed **no
  comparison**: `Stacks.DerivedTensor.ExtensionByZero.restriction X U` and the
  `SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U` of the cocycle
  dictionary unified, and the module doc of
  `Sites/Cohomology/DerivedTensor/ExtensionByZeroTensor.lean:75-80` already said they would —
  definitionally equal though not reducibly so, which costs instances rather than terms. And a
  `letI` in a *statement* must not be rewritten to `let _` even where the linter asks for that in
  tactic blocks: it stops the monoidal structures registering as instances and the hypothesis
  re-elaborates as an `Iso` instead of an equation.

  **What remains is the production of that hypothesis, and then the three uses.** On the space
  side those are `exists_local_cocycle_data` and `restrict_map_eq_cocycleHom`
  (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/LeftDualRetract.lean:141`, `:163`), then `exists_local_retract`
  (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/LeftDualLocalRetract.lean:34`) and `isPerfect_of_coevaluationFactors`
  (`LeftDualDirectSummand.lean:92`). On a site the chain is: apply Stacks 08FR (1) to
  `coevaluationUnitHomRestrict` to get a map of complexes over a covering sieve — this is where
  that lemma's five instance existentials have to be unpacked and worked under, since they cannot
  be discharged against ambient ones; take its value at `1` with `cocycleOfUnitComplexHom`;
  decompose that section with `exists_sieve_sum_tensorTotalSection`, crossing from `tensorTotal`
  to `tensorComplex` by `tensorTotalIsoTensorComplex_inv_tensorComplexSection`; build `𝒦` with
  `exists_sieve_subcomplex`; lift with `tensorComplexMap_sum_tensorComplexSection_lift` and
  `mono_mapBifunctorMap_f`, and get the cocycle condition from `d_eq_zero_of_mono`; take `Θ` from
  `exists_iso_whiskerRight_comp`; and conclude with the lemma above, together with the sieve
  transitivity that threads it.

  **The lift link of that chain is one declaration.**
  `AlgebraicGeometry.RingedSite.d_sum_tensorComplexSection_lift_eq_zero` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.CocycleLiftOfPureTensorSums` performs
  the three cited steps at once: for a degreewise-monic `j : 𝒦 ⟶ ℳ`, a termwise flat `𝒩`, and a
  degree-zero cocycle section of `Tot(ℳ ⊗ 𝒩)` written as a finite sum of pure tensors whose
  `ℳ`-factors lift along `j`, the lifted sum is a cocycle of `Tot(𝒦 ⊗ 𝒩)` — which is what makes
  the factored coevaluation a morphism of `D(O|_U)` and not merely a section. Two spellings of
  `Tot(j ⊗ 𝒩)` meet there with no bridge, recorded as `tensorComplexMap_eq_mapBifunctorMap`: the
  composite `((tensorComplex O).map j).app 𝒩 ≫ ((tensorComplex O).obj ℳ).map (𝟙 𝒩)` that the lift
  lemma is stated at is *not* definitionally `HomologicalComplex.mapBifunctorMap j (𝟙 𝒩)`, since
  its second factor is the identity only by functoriality, but its first factor alone is, by
  `rfl`, and `curriedTensor (MonoidalComplexesOfModules.Mod X.O) = Tensor.sheafTensor X.O` by
  `rfl` too.

  **One link needs more than the chain above provides.**
  `Stacks.Sites.ExtensionByZero.exists_sieve_subcomplex` does not take an arbitrary complex. It
  takes `ιP : ∀ n α, j_{U n α !}O_{U n α} ⟶ P^n` *together with*
  `hc : ∀ n, IsColimit (cofanP O P U ιP n)` — each term of `P` must **be** a direct sum of
  extensions by zero of structure sheaves of slices, not merely be covered by one. An
  epimorphism is not enough, and epimorphisms are what the extension-by-zero presentation
  cluster supplies (`Algebra/Category/ModuleCat/Sheaf/ExtensionByZeroQuasiCompact.lean:172`,
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FiniteExtensionByZeroPresentation.lean:313`, `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtensionByZeroRefinePresentation.lean:389`).
  Nothing in the chain above gives an arbitrary representative `ℳ` that shape, and the
  Stacks 06YS resolutions do not: `exists_kFlat_quasiIso` (`KFlat/Resolution.lean:93`) gives
  K-flatness only, and `exists_isKFlat_isFlat_quasiIso_epi`
  (`KFlat/ResolutionWithFlatTermsSurjective.lean:172`) gives *flat* terms, the terms of its
  colimit being filtered colimits of sums of extensions by zero rather than sums of them.

  **What does supply the shape, and in what weaker form.**
  `Stacks.Cohomology.IsSumOfExtensionByZeroStructureSheaves`
  (`Sites/Cohomology/DerivedTensor/ResolutionByExtensionsByZero.lean:218`) is exactly the
  predicate "isomorphic to a direct sum of extensions by zero of structure sheaves of slices",
  which is what `IsColimit (cofanP …)` asks for; and
  `exists_resolutionByDirectSumsExtensionsByZero` (`:276` of that file) produces a
  `ResolutionByDirectSumsExtensionsByZero` (`:230`), a sequential system whose rungs have terms
  of that shape. But the rungs resolve the *truncations* `G.truncLE (n + 1)`, not `G`: the
  colimit, which is what maps quasi-isomorphically to `G`, has filtered-colimit terms. So what is
  needed between the resolution and `exists_sieve_subcomplex` is a boundedness-plus-truncation
  bridge — for `M` in `D^b(O)`, which the second paragraph of the source's proof arranges, a
  single rung suffices once `G.truncLE (n + 1) ⟶ G` is a quasi-isomorphism.

  **That bridge is built**, as
  `Stacks.DerivedTensor.ResolutionByExtensionsByZero.exists_isSum_quasiIso_of_isStrictlyLE`
  (`Sites/Cohomology/DerivedTensor/BoundedTermwiseSumResolution.lean`): a complex strictly
  `≤ a` receives a quasi-isomorphism from a bounded above complex each of whose terms satisfies
  `IsSumOfExtensionByZeroStructureSheaves`. Three things make it short, each of them already
  available and none of them restated here. Mathlib supplies the truncation step: `ιTruncLE` is an
  isomorphism for a complex that is `IsStrictlyLE` at that degree, which
  `Algebra/Homology/DerivedCategory/Basic.lean:470` already uses as `inv (K.ιTruncLE n)`. The
  077J ladder already carries `quasiIso`, `boundedAbove` and `term_isSum` as *fields*
  (`DerivedTensor/ResolutionBySumsOfExtensionsByZero.lean:342`), so one rung is read off rather
  than constructed. And no spelling bridge is needed: the canonical
  `IsSumOfExtensionByZeroStructureSheaves` (`:271` of that file) is stated in `cofanP`'s own
  `SheafOfModules.extensionByZero` spelling over `Tensor.ringSheaf R`, with
  `R : Sheaf J CommRingCat` — and `exists_sieve_subcomplex` takes `O : Sheaf J RingCat`, which
  `Tensor.ringSheaf R` is, so the two meet at `O := Tensor.ringSheaf R` with no bridge.

  There are **two** parallel
  `IsSumOfExtensionByZeroStructureSheaves`/`ResolutionByDirectSumsExtensionsByZero` pairs, one in
  `Stacks.SheafOfModules` over `X : RingedSite`
  (`DerivedTensor/ResolutionByExtensionsByZero.lean:218`, `:230`) and one in
  `Stacks.DerivedTensor.ResolutionByExtensionsByZero` over a ring sheaf
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ResolutionBySumsOfExtensionsByZero.lean:271`, `:342`), each with live consumers. The bridge
  above is built on the ring-sheaf one, because that is the side `exists_sieve_subcomplex` is on.

  The presentation is then delivered in the consumed form by
  `exists_cofanP_isColimit_of_term_isSum` (the coproduct cocone transported along the
  isomorphism; `IsColimit` is data, so it comes back under `Nonempty`), and the two are packaged
  as `exists_quasiIso_cofanP_isColimit_of_isStrictlyLE`, which returns `Q`, the
  quasi-isomorphism `q : Q ⟶ G`, the vanishing `∀ n, b < n → IsZero (Q.X n)` in exactly the
  shape of `exists_sieve_subcomplex`'s `hb`, and the `ιP`/`hc` pair. What remains for the
  composite is therefore the threading of 08FR (1), the cocycle and the two sieve steps — no
  missing hypothesis.

  The inputs of piece two, all of which that composite consumes: it is the
  wiring of the generic
  `CategoryTheory.nonempty_retract_map_of_factorization` (`:75` of the same file, which mentions
  no space or site) through the derived restriction functor. The inputs are:

  * the restriction functor is **monoidal on derived categories**, which the generic lemma asks
    for as `[F.Monoidal]`: `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`
    (`Sites/Cohomology/Monoidal/DerivedRestrictionMonoidal.lean:190`), on a site at
    `RingedSite.{u, u, u}`, discharging every hypothesis of
    `CategoryTheory.Functor.mapDerivedCategoryMonoidal` including K-flatness of a restriction
    (Stacks 0E8K);
  * the unit and tensor comparisons: `(symmetricMonoidalDerived O).unitIso` and `.comparison`;
  * the morphism to be factored: `AlgebraicGeometry.RingedSite.coevaluationUnitHomRestrict`;
  * the chain map produced from the lifted section: `unitComplexHomOfCocycle` of piece one, with
    `cocycleOfUnitComplexHom_restrict` for its restriction;
  * the translator `Stacks.SheafOfModules.DerivedMonoidal.exists_iso_whiskerRight_comp`
    (`StacksFrontier/Homology/DerivedCategory/Monoidal/DerivedTensorIsoNaturality.lean:83`), already
    site-general.

  The ringed-space composite to replay is then
  `Stacks.Cohomology.LeftDualPerfect.exists_local_retract`
  (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/LeftDualLocalRetract.lean:34`, forty lines) and
  `isPerfect_of_coevaluationFactors` (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/LeftDualDirectSummand.lean:92`). One thing
  to check when writing it: whether `Stacks.Cohomology.DerivedRestriction.restriction X U`
  (`DerivedTensor/ExtensionByZeroTensor.lean:161`) and
  `SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U`, which the
  dictionary of piece one is stated at, are the same functor or need a comparison.

  Note that Stacks 08FR (1)'s conclusion existentially
  quantifies five instances, and the chain map and equation it produces have types depending on
  them. They cannot be discharged against ambient instances —
  `CategoryTheory.Limits.PreservesFiniteLimits` carries the preservation data rather than being a
  proposition, so the instance 08FR (1) chose and any other are different terms and
  `mapDerivedCategory` built from them is a different functor. Consumers must take the instances
  out of the existential and work under them.

  **And one piece after item 4 is not in that list and is not proved**: the source's "using the
  induced map of long exact sequences of cohomology sheaves from the morphism of triangles
  above, a diagram chase shows this implies `H^i(K) ⟶ H^i(M)` is an isomorphism for `i ≥ m` and
  surjective for `i = m - 1`". The four-lemma that does it exists in the repo, as the private
  `isIso_homology₃_of_triangleMap` and `epi_homology₃_of_triangleMap` of
  `PseudoCoherent/DistinguishedTriangles.lean:253` and `:300`, stated for a morphism of
  distinguished triangles of the homotopy category; what is absent is the instance of them that
  reads the split epimorphism of item 4 backwards along the two rows. That is the remaining gap
  between item 4 and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_bottomCover`.

  The complex-level analogue of the whole argument *is* in the library, for the monoidal category
  of complexes rather than for `D(O)`: Stacks 0FPA and Stacks 0FPS in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyBoundedDualComplex` and
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyStrictlyPerfectDualComplex`, where
  the slice restriction of complexes is monoidal by
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal`.
* The comparison of the two **coevaluations** is absent, for the reason recorded in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing`: the coevaluation of
  Example 0FPU exists only once the comparison `M ⊗^L_O M^∨ ⟶ RSheafHom(M, M)` of Stacks 08JD is
  known to be invertible, which is the third assertion of Stacks 08JJ and is not in this
  library. Only the evaluation side of the compatibility is therefore stated, as
  `whiskerRight_derivedDualToLeftDual`.

## Implementation notes

**Nothing is assumed.** The argument below needs exactly one of the three naturality clauses of
Stacks 08J8, naturality in the source variable, and that clause is proved:
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality`.
`DerivedCurrySourceNatural` below names the clause as a proposition — it is the form the
declarations of this file read it in, and the form the ringed-space statement Stacks 0FPD uses —
and `derivedCurrySourceNatural` inhabits it.

The inhabitation is written as a `rw` with the naturality lemma rather than as the term
`fun _ _ _ _ u h => derivedCurryHomEquiv_naturality_source X u h`, which does not elaborate:
the two statements are definitionally equal but not syntactically so, and checking that under
the local monoidal instances of this file exhausts the recursion depth, which `rw` avoids by
matching the two sides and closing the result by reflexivity.

**The argument.** It is uniqueness of left duals, in the elementary form that does not require
the monoidal category to be closed — so `CategoryTheory.rightDualIsoIhomUnit` is not used,
`D(O)` not being known to be monoidal closed. The morphism `M^∨ ⟶ N` is the transpose of `ε'`
under the pairing; the inverse is the transpose of `ε` under Stacks 08J8. Each composite is
checked by transposing once, and in each case what remains is an identity of the shape
`(h ▷ M) ≫ ε = ε'`, which naturality in the source supplies. The two triangle identities enter
only through Mathlib's `CategoryTheory.tensorRightHomEquiv`.

**Why the inverse is not a definition.** The transpose of `ε` under Stacks 08J8 is
`(derivedCurryHomEquiv …).symm (pairingEvaluation …)`. Naming it is possible, but no statement
about it can then be *proved*: every route to its defining equation has to unfold the name
underneath the coercion of a morphism-group `AddEquiv`, and at these arguments that exhausts the
recursion depth — the same obstruction `DualityPairing` records for the round-trip form of
Stacks 0FPU's evaluation, and raising the limit with an option is a workaround this development
does not accept. The inverse is therefore introduced inside the proofs, where it is a local
variable carrying its defining equation as a hypothesis; the *definition*
`derivedDualToLeftDual` is the direction that needs no transpose under Stacks 08J8, and it is
the one the statements below are about.

**Two spellings of the derived tensor product.** The monoidal structure of Stacks 0FPT is
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, whose tensor product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, while Stacks 08J8 is stated over
`Stacks.SheafOfModules.derivedTensorProductFunctor`. The two are identified by
`Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso` and
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`; their composite is
`derivedMonoidalTensorComparison` below, and it is the only bridge used. The unit of the
monoidal structure is identified with `AlgebraicGeometry.RingedSite.derivedStructureSheaf`, the
structure sheaf in degree zero, by `CochainComplex.KFlatMonoidal.derivedUnitIso`.

The universes are the diagonal `RingedSite.{u, u, u}` with the derived category the standard one,
as they are for the whole derived-internal-Hom cluster and for the monoidal structure of
Stacks 0FPT.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The symmetric monoidal structure on `D(O)` of Stacks 0FPT**, in which left duals are
taken. -/
local instance derivedMonoidalStructure :
    MonoidalCategory
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O

/-- **The tensor product of the monoidal structure of Stacks 0FPT is the derived tensor product
that Stacks 08J8 is stated over.** The monoidal structure is built over
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` and the derived internal Hom over
`Stacks.SheafOfModules.derivedTensorProductFunctor`; this is the composite of the two comparisons
that identify them. -/
def derivedMonoidalTensorComparison :
    curriedTensor
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      Stacks.SheafOfModules.derivedTensorProductFunctor X :=
  Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O ≪≫
    (Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).symm

/-- **The unit of the monoidal structure of Stacks 0FPT is the structure sheaf in degree
zero.** -/
def derivedMonoidalUnitIso :
    𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      derivedStructureSheaf X :=
  CochainComplex.KFlatMonoidal.derivedUnitIso _
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O)

/-- **Naturality of the bijection of Stacks 08J8 in its source variable**: precomposing a
morphism `A ⟶ RSheafHom(B, Z)` with `u : A' ⟶ A` corresponds to precomposing the morphism
`A ⊗^L_O B ⟶ Z` matched with it with `u ⊗ 1`.

This is one of the three functoriality clauses of Stacks 08J8. It is proved —
`derivedCurrySourceNatural` inhabits it — and is named as a proposition because that is the
form in which the declarations below and the ringed-space statement of Stacks 0FPD read it. -/
def DerivedCurrySourceNatural : Prop :=
  ∀ (A A' B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (u : A' ⟶ A)
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z),
    derivedCurryHomEquiv X A' B Z (u ≫ h) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app B ≫
        derivedCurryHomEquiv X A B Z h

/-- **Stacks 08J8 is natural in its source variable**, so the proposition
`DerivedCurrySourceNatural` holds: it is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, which the argument below
therefore needs no hypothesis for. -/
theorem derivedCurrySourceNatural : DerivedCurrySourceNatural X := by
  intro A A' B Z u h
  rw [derivedCurryHomEquiv_naturality_source X u h]

section Comparison

variable {X}
variable (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The comparison of the two derived tensor products, read at a fixed right factor `M`: the
monoidal tensor `A ⊗ M` of Stacks 0FPT is the derived tensor product `A ⊗^L_O M` that
Stacks 08J8 is stated over. -/
def derivedTensorRightComparison
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    A ⊗ M ≅ ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj M :=
  ((derivedMonoidalTensorComparison X).app A).app M

/-- The comparison of the two derived tensor products is natural in the left factor. -/
theorem derivedTensorRightComparison_naturality
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : A' ⟶ A) :
    u ▷ M ≫ (derivedTensorRightComparison M A).hom =
      (derivedTensorRightComparison M A').hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app M := by
  have h := NatTrans.congr_app ((derivedMonoidalTensorComparison X).hom.naturality u) M
  rw [NatTrans.comp_app, NatTrans.comp_app] at h
  exact h

/-- **The evaluation of Example 0FPU**, read in the monoidal category of Stacks 0FPT: the
evaluation `ε' : M^∨ ⊗ M ⟶ 𝟙` obtained from
`AlgebraicGeometry.RingedSite.derivedDualEvaluation` across the comparison of the two derived
tensor products and the identification of the unit with the structure sheaf. -/
def derivedDualEvaluationMonoidal :
    derivedDual X M ⊗ M ⟶
      𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (derivedTensorRightComparison M (derivedDual X M)).hom ≫
    derivedDualEvaluation X M ≫ (derivedMonoidalUnitIso X).inv

/-- Reading `derivedDualEvaluationMonoidal` back across the two identifications gives the
evaluation of Example 0FPU. -/
theorem derivedDualEvaluationMonoidal_eq :
    (derivedTensorRightComparison M (derivedDual X M)).inv ≫
        derivedDualEvaluationMonoidal M ≫ (derivedMonoidalUnitIso X).hom =
      derivedDualEvaluation X M := by
  dsimp only [derivedDualEvaluationMonoidal]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end Comparison

section Pairing

variable {X}
variable (M N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  [ExactPairing M N]

/-- **The evaluation of the exact pairing**, read as a morphism into the structure sheaf in
degree zero and across the comparison of the two derived tensor products: `ε : N ⊗^L_O M ⟶ O`. -/
def pairingEvaluation :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj N).obj M ⟶
      derivedStructureSheaf X :=
  (derivedTensorRightComparison M N).inv ≫ ε_ M N ≫ (derivedMonoidalUnitIso X).hom

/-- **The morphism `M^∨ ⟶ N` matched with the evaluation of Example 0FPU.** It is the transpose,
under the exact pairing, of the evaluation `ε' : M^∨ ⊗ M ⟶ 𝟙` of Example 0FPU. -/
def derivedDualToLeftDual : derivedDual X M ⟶ N :=
  tensorRightHomEquiv (derivedDual X M) M N
      (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (derivedDualEvaluationMonoidal M) ≫
    (λ_ N).hom

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The evaluation of the pairing is the transpose of the inverse left unitor.** This is the
triangle identity `CategoryTheory.ExactPairing.coevaluation_evaluation` read through Mathlib's
`CategoryTheory.tensorRightHomEquiv`. -/
theorem tensorRightHomEquiv_evaluation :
    tensorRightHomEquiv N M N
        (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (ε_ M N) = (λ_ N).inv := by
  simp [tensorRightHomEquiv]

/-- **The morphism `M^∨ ⟶ N` carries the evaluation of the pairing to the evaluation of
Example 0FPU.** This pins `derivedDualToLeftDual` down — it is not an unconstrained morphism of
its type — and it is the compatibility of the two duality data on the evaluation side. -/
theorem whiskerRight_derivedDualToLeftDual :
    derivedDualToLeftDual M N ▷ M ≫ ε_ M N = derivedDualEvaluationMonoidal M := by
  have hg : derivedDualToLeftDual M N ≫ (λ_ N).inv =
      tensorRightHomEquiv (derivedDual X M) M N
        (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (derivedDualEvaluationMonoidal M) := by
    dsimp only [derivedDualToLeftDual]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := tensorRightHomEquiv_symm_naturality (Y := M) (Y' := N)
    (Z := 𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (derivedDualToLeftDual M N) (λ_ N).inv
  rw [hg, Equiv.symm_apply_apply, ← tensorRightHomEquiv_evaluation M N,
    Equiv.symm_apply_apply] at h
  exact h.symm

/-- **The transpose of the evaluation of the pairing under Stacks 08J8**, as the round-trip
equation that characterizes it. -/
theorem derivedCurryHomEquiv_symm_pairingEvaluation :
    derivedCurryHomEquiv X N M (derivedStructureSheaf X)
        ((derivedCurryHomEquiv X N M (derivedStructureSheaf X)).symm
          (pairingEvaluation M N)) = pairingEvaluation M N :=
  (derivedCurryHomEquiv X N M (derivedStructureSheaf X)).apply_symm_apply _

/-- **There is a morphism `N ⟶ M^∨` matched with the evaluation of the pairing by Stacks 08J8**,
namely its transpose. It is produced in this form because no statement about the transpose as a
*named* morphism can be proved; see the implementation notes of this file. -/
theorem exists_curry_eq_pairingEvaluation :
    ∃ f : N ⟶ derivedDual X M,
      derivedCurryHomEquiv X N M (derivedStructureSheaf X) f = pairingEvaluation M N :=
  ⟨_, derivedCurryHomEquiv_symm_pairingEvaluation M N⟩

/-- The transpose of the evaluation of the pairing under Stacks 08J8 is a right inverse of
`derivedDualToLeftDual`. -/
theorem derivedDualToLeftDual_comp (f : N ⟶ derivedDual X M)
    (hf : derivedCurryHomEquiv X N M (derivedStructureSheaf X) f = pairingEvaluation M N) :
    derivedDualToLeftDual M N ≫ f = 𝟙 (derivedDual X M) := by
  have hθ := derivedTensorRightComparison_naturality M (derivedDualToLeftDual M N)
  have hθinv : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (derivedDualToLeftDual M N)).app M ≫ (derivedTensorRightComparison M N).inv =
      (derivedTensorRightComparison M (derivedDual X M)).inv ≫
        derivedDualToLeftDual M N ▷ M := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hθ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  apply (derivedCurryHomEquiv X (derivedDual X M) M (derivedStructureSheaf X)).injective
  rw [derivedCurrySourceNatural X N (derivedDual X M) M (derivedStructureSheaf X)
      (derivedDualToLeftDual M N) f, hf,
    ← derivedDualEvaluation_eq]
  dsimp only [pairingEvaluation]
  rw [← Category.assoc, hθinv]
  simp only [Category.assoc]
  rw [reassoc_of% whiskerRight_derivedDualToLeftDual M N]
  exact derivedDualEvaluationMonoidal_eq M

/-- The transpose of the evaluation of the pairing under Stacks 08J8 is a left inverse of
`derivedDualToLeftDual`. -/
theorem comp_derivedDualToLeftDual (f : N ⟶ derivedDual X M)
    (hf : derivedCurryHomEquiv X N M (derivedStructureSheaf X) f = pairingEvaluation M N) :
    f ≫ derivedDualToLeftDual M N = 𝟙 N := by
  have hfev : f ▷ M ≫ derivedDualEvaluationMonoidal M = ε_ M N := by
    have hc : derivedCurryHomEquiv X N M (derivedStructureSheaf X)
          (f ≫ 𝟙 (derivedDual X M)) =
        derivedCurryHomEquiv X N M (derivedStructureSheaf X) f :=
      congrArg (fun g => derivedCurryHomEquiv X N M (derivedStructureSheaf X) g)
        (Category.comp_id f)
    have hpev : pairingEvaluation M N =
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app M ≫
          derivedDualEvaluation X M := by
      rw [← hf, ← hc, derivedCurrySourceNatural X (derivedDual X M) N M
        (derivedStructureSheaf X) f (𝟙 (derivedDual X M)), ← derivedDualEvaluation_eq]
    have hθ := derivedTensorRightComparison_naturality M f
    dsimp only [derivedDualEvaluationMonoidal]
    rw [← Category.assoc, hθ]
    simp only [Category.assoc]
    rw [← reassoc_of% hpev]
    dsimp only [pairingEvaluation]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have h := tensorRightHomEquiv_symm_naturality (Y := M) (Y' := N)
    (Z := 𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) f
    (tensorRightHomEquiv (derivedDual X M) M N
      (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (derivedDualEvaluationMonoidal M))
  rw [Equiv.symm_apply_apply, hfev, Equiv.symm_apply_eq, tensorRightHomEquiv_evaluation] at h
  dsimp only [derivedDualToLeftDual]
  rw [← Category.assoc, h, Iso.inv_hom_id]

/-- **Stacks 0FPV, second assertion: a left dual of `M` is the dual object of Example 0FPU.**
The morphism `M^∨ = RSheafHom(M, O) ⟶ N` which the exact pairing matches with the evaluation of
Example 0FPU is an isomorphism; its inverse is the morphism which the tensor–internal-Hom
bijection of Stacks 08J8 matches with the evaluation of the pairing. -/
@[stacks 0FPV "the left dual is the object constructed in Example 0FPU, namely the derived dual \
`RSheafHom(M, O)` of Tag 08JD, and the identification is the morphism matched with the \
evaluation of Example 0FPU by the pairing; see \
`AlgebraicGeometry.RingedSite.whiskerRight_derivedDualToLeftDual` for the compatibility of the \
two evaluations. The monoidal structure on `D(O)` is the one of Tag 0FPT, \
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, and a left dual is Mathlib's \
`CategoryTheory.ExactPairing`, which is Definition 0FFP"]
theorem isIso_derivedDualToLeftDual : IsIso (derivedDualToLeftDual M N) := by
  obtain ⟨f, hf⟩ := exists_curry_eq_pairingEvaluation M N
  exact ⟨f, derivedDualToLeftDual_comp M N f hf, comp_derivedDualToLeftDual M N f hf⟩

/-- **The identification `M^∨ ≅ N` of Stacks 0FPV.** The dual object `M^∨ = RSheafHom(M, O)` of
Example 0FPU is a left dual `N` of `M`, by the morphism that the pairing matches with the
evaluation of Example 0FPU. -/
def derivedDualIsoLeftDual : derivedDual X M ≅ N :=
  letI := isIso_derivedDualToLeftDual M N
  asIso (derivedDualToLeftDual M N)

/-- **The identification `N ≅ M^∨` of Stacks 0FPV**, in the direction the source states it: a
left dual of `M` in `D(O)` is the dual object of Example 0FPU. -/
def leftDualIsoDerivedDual : N ≅ derivedDual X M :=
  (derivedDualIsoLeftDual M N).symm

end Pairing

end AlgebraicGeometry.RingedSite

end
