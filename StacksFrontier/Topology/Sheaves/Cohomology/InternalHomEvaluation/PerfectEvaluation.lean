module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLocality.InvertibilityOnACovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.DerivedEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect

/-!
# Evaluation of derived internal Homs against a perfect complex

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`. Stacks 0G40 says
that if `K` is perfect then the evaluation morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

of Stacks 0A8U is an isomorphism.

## Main results

* `Stacks.SheafOfModules.exists_cover_hasStrictlyPerfectModelOver`: a perfect object acquires a
  strictly perfect model on a family of opens covering the space.
* `Stacks.SheafOfModules.derivedSheafHomEvaluation_isIso_of_isPerfect` (Stacks 0G40): the
  evaluation morphism of Stacks 0A8U is an isomorphism when `K` is perfect. Nothing is assumed of
  `L` or `M`.

## How the assertion is reached

The theorem is the ringed-site statement
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_isPerfect` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect`, read off at the
site of opens of the space; that file carries the argument and its own account of it. In outline
it is the route that
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect` takes for
the diagonal of Stacks 0BYS: replace invertibility of a derived morphism, once and for all, by
quasi-isomorphy of a morphism of complexes, because quasi-isomorphy is local on the site while
the derived morphism has **no restriction compatibility in the library** — and, this route being
available, needs none.

The local invertibility it starts from is nowhere in the library, and the route to it is the one
that `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect` takes
for the diagonal of Stacks 0BYS: replace invertibility of a derived morphism, once and for all,
by quasi-isomorphy of a morphism of complexes, because quasi-isomorphy is local on the site
while the derived morphism has no restriction compatibility to hand. The first step of that
route is `Stacks.SheafOfModules.isIso_derivedSheafHomEvaluation_iff_quasiIso` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationCriteria`: the morphism
of Stacks 0A8U is invertible at representatives exactly when the evaluation morphism of internal
Hom complexes `AlgebraicGeometry.RingedSite.evaluationMap` of Stacks 0A92 between them is a
quasi-isomorphism. Two statements about that morphism of complexes then remain, and neither is
anywhere in either Lean tree. Both are now there, the first in full and the second down to one
case:

* the invertibility criterion — the morphism of Stacks 0A8U is invertible at representatives
  exactly when the evaluation morphism of internal Hom complexes
  `AlgebraicGeometry.RingedSite.evaluationMap` of Stacks 0A92 between them is a quasi-isomorphism.
  On a ringed space this is
  `Stacks.SheafOfModules.isIso_derivedSheafHomEvaluation_iff_quasiIso` of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationCriteria`; the
  criterion is needed on the slice site `X.over V`, which is a ringed site and not a ringed
  space, and the ringed-site form is
  `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_iff_quasiIso` of
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationModels`, of which the
  ringed-space statements are now the instantiations;
* the restriction square — that the restriction of `evaluationMap` to the site over an open is,
  up to the comparison isomorphisms `AlgebraicGeometry.RingedSite.tensorTotalOverIso` and
  `AlgebraicGeometry.RingedSite.DerivedHomRestriction.complexMap`, the `evaluationMap` formed
  over that open. This is `AlgebraicGeometry.RingedSite.evaluationMap_restrict_square` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationRestriction`, proved
  following the template
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_restrict_square`;
* the base case — that `evaluationMap` is a quasi-isomorphism when its source complex is
  strictly perfect. The analogues for the interchange morphism are
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand` and its
  tensor-factor companion, each a dévissage along the stupid filtration down to the trivialised
  single-degree case. For `evaluationMap` the variable at issue occupies two slots at once, a
  tensor factor and the source of the inner internal Hom, so both rows of the dévissage are
  covariant in it and the target row is an iterated internal Hom. That dévissage is
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationStrictlyPerfect`, ending in
  `AlgebraicGeometry.RingedSite.evaluationMap_quasiIso_of_isFiniteFreeSummand`, and what it
  carries as a hypothesis is the **trivialised single-degree case alone**: that `evaluationMap`
  is a quasi-isomorphism when its source vanishes outside one degree `k` and is isomorphic to
  the structure sheaf there.

  What that one case needs is a comparison of two complexes, and the obstruction is on the
  target side only. The source collapses sign-free:
  `AlgebraicGeometry.RingedSite.tensorTotalUnitFactorRightIso` identifies
  `Tot(SheafHom(L, M) ⊗_O K)` with `SheafHom(L, M)` reindexed by `-k`, and its description on
  local sections is now reachable, the right unit constraint of `⊗_O` having acquired one in
  `AlgebraicGeometry.RingedSite.sheafTensorUnitIsoRight_inv_apply`. On the target
  `AlgebraicGeometry.RingedSite.homUnitReindexIso` identifies the inner `SheafHom(K, L)` with
  `L` reindexed by `k`, leaving `SheafHom(reindexBy L k, M)`, and that complex is **not** a
  diagonal retwisting of `SheafHom(L, M)` reindexed by `-k`: reindexing the source of a Hom
  complex by `k` multiplies by `(-1)^k` the second of the two summands of the Hom-complex
  differential and not the first, which no sign `ε_n` on the terms can repair. The comparison
  that does exist is with the shift, `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso`, so a
  chain-level square has to be written with `CochainComplex.reindexByIsoShift` inserted on both
  sides, and closing it means reconciling three signs — the Koszul sign of
  `AlgebraicGeometry.RingedSite.evaluationSectionAt_applyOver`, the `(-1)^{kn}` of
  `reindexByIsoShift`, and the sign `Mathlib`'s `Cochain.leftShift` carries inside
  `sheafHomSourceShiftIso`.

  A **degreewise** argument avoids all three, and it is the natural starting point; the
  closing section of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationStrictlyPerfect` names the
  statements it would be assembled from.

The dévissage cannot instead be run in the derived category:
`Stacks.SheafOfModules.derivedSheafHom` carries no `CategoryTheory.Functor.CommShift` in the
**contravariant** variable, which is the one a dévissage in `K` varies; the covariant one is
`Stacks.SheafOfModules.commShift_derivedSheafHom` (see the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness`), so the
machinery of `Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated` does not
apply. That is why the argument is run on complexes throughout.

## Perfectness model

`AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5 is used, read at the ringed site
`Stacks.SheafOfModules.ringedSite Rc` of opens of the space. Being an `abbrev`, that site has
`SheafOfModules (ringedSite Rc).ringSheaf` equal to `Stacks.SheafOfModules.StructureSheafModules
Rc` by definition, so the predicate applies to the very objects the evaluation morphism of
Stacks 0A8U is defined on, with no bridge. Its local condition is phrased with
`AlgebraicGeometry.RingedSite.restrictComplex`, restriction to a slice site, which is the same
vocabulary as `SheafOfModules.overFunctor` and hence as the locality statements used here; the
competing ringed-space model of Stacks 08CM is phrased with restriction to an open *subspace*,
for which no comparison with the slice restriction is available.

## References

* [Stacks Project, Tag 0G40](https://stacks.math.columbia.edu/tag/0G40)
* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

/-- `K` acquires a **strictly perfect model over the open `V`**: some complex of `O_X`-modules
representing `K` restricts over `V` to a complex receiving a quasi-isomorphism from a strictly
perfect complex of `O_X|_V`-modules.

This is the local condition in the definition of a perfect object, Stacks 08G5, isolated at one
open; restriction is restriction to the slice site over `V`. -/
def HasStrictlyPerfectModelOver (K : DerivedCategory (StructureSheafModules Rc))
    (V : Opens X) : Prop :=
  ∃ E : CochainComplex (StructureSheafModules Rc) ℤ, Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
    ∃ P : CochainComplex
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O).over V)) ℤ,
      _root_.IsStrictlyPerfect
          ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O).over V) P ∧
        ∃ q : P ⟶ (ringedSite Rc).restrictComplex E V, QuasiIso q

/-- A perfect object acquires a strictly perfect model on a family of opens covering the space.

This is the globalizing half of Stacks 08G5 read off at the terminal open: the covering sieve of
`⊤` supplied by perfectness is turned into an honest family of opens whose supremum is `⊤`. -/
theorem exists_cover_hasStrictlyPerfectModelOver
    (K : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    ∃ (ι : Type u) (Y : ι → Opens X), (Opens.grothendieckTopology X).CoversTop Y ∧
      ∀ i, HasStrictlyPerfectModelOver Rc K (Y i) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨S, hS, hmodels⟩ := hE ⊤
  refine ⟨{ V : Opens X // ∃ f : V ⟶ (⊤ : Opens X), S f }, fun p ↦ p.1, ?_, ?_⟩
  · rw [Opens.coversTop_iff]
    refine TopologicalSpace.IsOpenCover.mk ?_
    refine le_antisymm le_top fun x _ ↦ ?_
    obtain ⟨V, f, hf, hxV⟩ :=
      (Opens.mem_grothendieckTopology (T := (X : Type u))).1 hS x trivial
    obtain ⟨W, g, h, hh, -⟩ := hf
    exact Opens.mem_iSup.2 ⟨⟨W, ⟨h, hh⟩⟩, leOfHom g hxV⟩
  · intro p
    obtain ⟨f, hf⟩ := p.2
    obtain ⟨P, hP, q, hq⟩ := hmodels f hf
    exact ⟨E, ⟨e⟩, P, hP, q, hq⟩

variable [∀ V : Opens X, (SheafOfModules.overFunctor.{u} (structureSheaf Rc) V).Additive]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

omit [∀ V : Opens X, (SheafOfModules.overFunctor.{u} (structureSheaf Rc) V).Additive] in
/-- **Stacks 0G40.** Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of
`D(O_X)` with `K` perfect. The evaluation morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

of Stacks 0A8U is an isomorphism, for every `L` and `M`.

This reads off the ringed-site statement
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_isPerfect` at the site of opens
of the space, for the canonical derived tensor product and the derived internal Hom of the ringed
space; the two notions of perfection agree because the predicate used here *is* the site-level
one of Stacks 08G5. -/
@[stacks 0G40]
theorem derivedSheafHomEvaluation_isIso_of_isPerfect
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (hK : (ringedSite Rc).IsPerfect K) :
    IsIso (derivedSheafHomEvaluation Rc K L M) :=
  RingedSite.isIso_derivedSheafHomEvaluation_of_isPerfect (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K L M hK

end Stacks.SheafOfModules

end
