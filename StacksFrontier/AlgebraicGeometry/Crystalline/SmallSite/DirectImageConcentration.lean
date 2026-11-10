module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HypercohomologyBound07QA
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.VanishingStatements
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDimensionVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus

/-!
# `Ru_{X/S, *}F` concentrated in degrees `≤ e`

Clause (1) of [Stacks, Tag 07MR] bounds `H^i(Cris(X/S), F)` by `d + e` with `d = dim X` and `e`
a bound on the embedding dimension of `X/S₀`.  The source's argument reduces that cohomology to
`H^i(X_Zar, Ru_{X/S, *}F)` and then needs two bounds: the vanishing of `H^j(X_Zar, -)` above `d`,
which is proved as
`...SmallSite.subsingleton_zariskiSheafH_of_topologicalKrullDim_le`
of `SmallSite/ZariskiDimensionVanishing.lean`, and the concentration of `Ru_{X/S, *}F` in degrees
`≤ e`.  This file is about the second.

The statement that `Ru_{X/S, *}F` lives in degrees `≤ e` as soon as `R^j u_{X/S, *}F = 0` for
`j > e` is the theorem `isLE_derivedZariskiDirectImage_obj`,
together with its converse — the two are the two directions
of the t-structure characterization of boundedness above, [Stacks, Tag 0118], at `D⁺(Ab(X_Zar))`.
So the reduction of the degreewise vanishing to the derived-category concentration costs nothing,
and what clause (1) is owed is the degreewise vanishing itself.

That vanishing is **not proved here, and is not proved anywhere in this library.**  It is carried
as the proposition `DirectImageVanishing07MR`, stated with the hypotheses clause (1) of
[Stacks, Tag 07MR] gives it — in particular `S.toClosedFiber.HasEmbeddingDimensionLE e`, the
predicate of `AlgebraicGeometry.Scheme.Hom.HasEmbeddingDimensionLE`.  The proposition is the
sheaf-level content of the clause, isolated so that what remains between it and the clause is
explicit.

**The point of this file is that nothing else remains**:
`abelianVanishing07MRClauseOne_of_directImageVanishing07MR` proves clause (1) of
`...SmallSite.AbelianVanishing07MR` from `DirectImageVanishing07MR` and from proved theorems
only.  So the degree-`e` concentration of `Ru_{X/S, *}F` is the *sole* remaining input of
clause (1): the Zariski-side dimension bound, the hypercohomology dévissage that combines the two
bounds into `d + e`, the Leray factorization of [Stacks, Tag 015M], and the identification of the
chapter's graded cohomology with the cohomology of `RΓ(Cris(X/S), -)` are all theorems here.

The combining step deserves a note, because the source's hint attributes it to part (4)
of [Stacks, Tag 07K7] and that is not the route taken.  The library's 07K7,
`CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived`, concludes about a right
derived functor on the *unbounded* `D(Ab(X_Zar))` together with its unit, and no such functor
exists for `Γ(X_Zar, -)` in this library — only `...SmallSite.derivedZariskiGlobalSectionsFunctor`
on `D⁺`.  The same bound out of `D⁺` is proved separately, as the Postnikov dévissage
`Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem` with
`...isLE_rightDerivedFunctorPlus_single`, and `isLE_derivedZariskiGlobalSections_obj` below is
that applied here.  Nothing is assumed in place of 07K7 and the numerical bound is identical.

## Why the vanishing is not proved

The source gets it from the affine local computation: on an affine open where `X` embeds in a
smooth `P` with relative embedding dimension `≤ e`, the crystalline cohomology of the sections is
computed by a de Rham complex supported in degrees `≤ e`, so the higher direct images vanish above
`e`.  Two separate inputs of that argument are missing from this library, and each is already
recorded as missing where it belongs:

* the envelopes `D_β` of the local situations, item 2 of the gap list of
  `SmallSite/CechCoverComplex.lean`.  The *rings* `D_β` are now built,
  `...SmallSite.CechPresentation.tupleEnvelope` of `SmallSite/CechTupleEnvelope.lean`, together
  with the presentations they are the envelopes of; what that item is still about is their
  transition morphisms along the Čech faces and their levels as objects of `Cris(X/S)`;
* the local completed de Rham complex of a general crystal, item 4 of the same list — the
  completed module of differentials is available ([Stacks, Tag 07KK],
  `Crystalline.dividedPowerDifferentialsCompletionComparison`), the *complex* is not built over
  the Čech rings, its differential being the connection of the pair of [Stacks, Tag 07JG]
  (`...SmallSite.crystalPairFunctor`, integrable by its item (07JD)) on each `D_β`.

The passage from `HasEmbeddingDimensionLE e` to a rank bound on those differentials is not
missing: the rank statement is
`Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials` of
`StacksFrontier/AlgebraicGeometry/Different/TheDifferent/SmoothFormula.lean`, and
`StacksFrontier/AlgebraicGeometry/Variety/Tangent/RelativeEmbeddingDimensionForms.lean` draws
the numerical consequence from it:
`AlgebraicGeometry.Scheme.Hom.exists_closedImmersion_isZero_relativeDifferentialForms` produces,
around each point of `X`, a closed immersion over `S` into a scheme whose relative differential
forms `Ω^m` vanish for every `m > e` — which is exactly the degree bound that gives the ambient
de Rham complex length `e`.  So the gap below `DirectImageVanishing07MR` is the de Rham complex
of the envelopes, not the dimension count.

The same two inputs block the Čech route:
`...SmallSite.isZero_cohomologyFunctor_of_computesOrdCechCohomology`
of `SmallSite/OrdCechDegreeBound.lean` reaches clause (2) from a hypothesis `hlen` which is
exactly `HasEmbeddingDimensionLE e` unpacked, and that file's own note says deriving `hlen` needs
the envelopes and [Stacks, Tag 07KK] at each of them.  So the two routes to clause (1) are blocked
by one and the same construction, and neither is a matter of assembling what is here.

## Main results

* `isLE_derivedZariskiDirectImage_obj`: **`Ru_{X/S, *}F` is concentrated in degrees `≤ e` as soon
  as `R^j u_{X/S, *}F = 0` for `j > e`.**
* `isZero_higherZariskiDirectImage_of_isLE`: the converse, so that the two formulations of the
  concentration agree.
* `isGE_zero_and_isLE_derivedZariskiDirectImage_obj`: with the lower bound
  `...SmallSite.isGE_derivedZariskiDirectImage_obj`, `Ru_{X/S, *}F` lives in the band `[0, e]`,
  which is the form the hypercohomology bound consumes.
* `DirectImageVanishing07MR`: **the proposition** that the degreewise vanishing holds under the
  hypotheses of clause (1) of [Stacks, Tag 07MR].  Nothing here proves it.
* `isLE_derivedZariskiGlobalSections_obj`: **the hypercohomology bound.**  On a Zariski site of
  Krull dimension at most `d`, `RΓ(X_Zar, -)` carries an object concentrated in `[0, e]` to one
  concentrated in degrees `≤ e + d`.  Proved.
* `AbelianVanishing07MRClauseOne` and `AbelianVanishing07MRClauseTwo` with
  `abelianVanishing07MR_of_clauses`: the two clauses of the abelian form of [Stacks, Tag 07MR],
  and the proof that they are together the whole of it.
* `abelianVanishing07MRClauseOne_of_directImageVanishing07MR`: **clause (1) from
  `DirectImageVanishing07MR` and nothing else.**

**No tag attribute is placed in this file.**  `isLE_derivedZariskiDirectImage_obj` and its
converse are [Stacks, Tag 0118] at this site rather than any part of [Stacks, Tag 07MR];
`isLE_derivedZariskiGlobalSections_obj` is the dévissage of [Stacks, Tag 07K7] applied here, not
that tag; and `abelianVanishing07MRClauseOne_of_directImageVanishing07MR` carries an unproved
proposition as a hypothesis, so it is not clause (1).

## References

* [Stacks Project, Proposition 60.22.4, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-! ### The two formulations of the concentration -/

/-- **`Ru_{X/S, *}F` is concentrated in degrees `≤ e` as soon as `R^j u_{X/S, *}F = 0` for
`j > e`.**

`R^j u_{X/S, *}` *is* the degree-`j` cohomology of `Ru_{X/S, *}` — that is
`...SmallSite.derivedZariskiDirectImage_comp_homologyFunctor`, which holds by `rfl` — so this is
one direction of the characterization of boundedness above for the canonical t-structure of
`D⁺(Ab(X_Zar))`, [Stacks, Tag 0118], as `DerivedCategory.Plus.isLE_iff`.

This is the step clause (1) of [Stacks, Tag 07MR] needs between the degreewise vanishing and the
hypercohomology bound of [Stacks, Tag 07K7].  It does not supply the vanishing: that is
`DirectImageVanishing07MR` below, and it is unproved. -/
theorem isLE_derivedZariskiDirectImage_obj
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (e : ℤ)
    (h : ∀ j : ℤ, e < j → IsZero ((higherZariskiDirectImage S j).obj F)) :
    ((derivedZariskiDirectImage S).obj F).IsLE e :=
  (DerivedCategory.Plus.isLE_iff ((derivedZariskiDirectImage S).obj F) e).2 h

/-- **`R^j u_{X/S, *}F = 0` for `j > e` when `Ru_{X/S, *}F` is concentrated in degrees `≤ e`**,
the converse of `isLE_derivedZariskiDirectImage_obj`.

Together the two say that the degreewise formulation of the concentration and the
derived-category one are the same statement, so that nothing is lost by stating the gap of
clause (1) of [Stacks, Tag 07MR] in either. -/
theorem isZero_higherZariskiDirectImage_of_isLE
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (e : ℤ)
    (h : ((derivedZariskiDirectImage S).obj F).IsLE e) (j : ℤ) (hj : e < j) :
    IsZero ((higherZariskiDirectImage S j).obj F) :=
  (DerivedCategory.Plus.isLE_iff ((derivedZariskiDirectImage S).obj F) e).1 h j hj

/-- **`Ru_{X/S, *}F` lives in the band `[0, e]`** once `R^j u_{X/S, *}F = 0` for `j > e`: the
lower bound is free, a right derived functor on `D⁺` applied to a sheaf placed in degree zero
moving cohomology to the right, and that is
`...SmallSite.isGE_derivedZariskiDirectImage_obj`.

This is the shape in which the hypercohomology bound consumes the concentration:
`isLE_derivedZariskiGlobalSections_obj` below takes an object in the band `[0, e]` to one in
degrees `≤ e + d`, which is the bound `d + e` of clause (1) of [Stacks, Tag 07MR]. -/
theorem isGE_zero_and_isLE_derivedZariskiDirectImage_obj
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (e : ℤ)
    (h : ∀ j : ℤ, e < j → IsZero ((higherZariskiDirectImage S j).obj F)) :
    ((derivedZariskiDirectImage S).obj F).IsGE 0 ∧
      ((derivedZariskiDirectImage S).obj F).IsLE e :=
  ⟨isGE_derivedZariskiDirectImage_obj S F, isLE_derivedZariskiDirectImage_obj S F e h⟩

/-! ### The sheaf-level gap of clause (1) of [Stacks, Tag 07MR] -/

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **The sheaf-level content of clause (1) of [Stacks, Tag 07MR]**: under the hypotheses of that
clause, `R^j u_{X/S, *}F = 0` for `j > e`, where `e` bounds the embedding dimension of `X/S₀`.

The hypotheses are those of `...SmallSite.AbelianVanishing07MR`, unchanged and in the same order,
with the dimension `d` of `X` dropped — it plays no part in this bound — and the degree `j`
ranging over `ℤ` rather than `ℕ`, which is the indexing of
`...SmallSite.higherZariskiDirectImage`.

**This is a proposition, not a theorem: nothing in this library proves it.**  The module
documentation above lists the three inputs of the source's argument for it that are missing, and
records that the same three block the Čech route of `SmallSite/OrdCechDegreeBound.lean` to clause
(2).  It is isolated here so that the passage from it to the clause is explicit: that passage is
`abelianVanishing07MRClauseOne_of_directImageVanishing07MR`. -/
def DirectImageVanishing07MR : Prop :=
  Subsingleton ↥(DividedPowerScheme.closedFiber S.S) →
    Nonempty ↥(DividedPowerScheme.closedFiber S.S) →
      LocallyOfFinitePresentation S.toClosedFiber → QuasiCompact S.toClosedFiber →
        QuasiSeparated S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
            ∀ e : ℕ, S.toClosedFiber.HasEmbeddingDimensionLE e →
              ∀ j : ℤ, (e : ℤ) < j →
                IsZero ((higherZariskiDirectImage S j).obj (abelianSheaf F))

/-! ### The Zariski hypercohomology bound -/

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})] in
/-- **`RΓ(X_Zar, K)` is concentrated in degrees `≤ e + d` for `K` concentrated in `[0, e]`**, on
the small Zariski site of an `X` of topological Krull dimension at most `d`.

This is the hypercohomology half of clause (1) of [Stacks, Tag 07MR], and it is the step the
source's hint attributes to part (4) of [Stacks, Tag 07K7].  It is proved
here from two results of the library and nothing else:

* `...SmallSite.isZero_rightDerivedZariskiGlobalSections_of_topologicalKrullDim_le` of
  `SmallSite/ZariskiDimensionVanishing.lean`, the vanishing `R^p Γ(X_Zar, -) = 0` for `p > d` on
  every abelian sheaf, which is [Stacks, Tag 0A3G] at the coefficient universe `u + 1`;
* the Postnikov dévissage of
  `Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem` together with
  `...isLE_rightDerivedFunctorPlus_single` of
  `StacksFrontier/Algebra/Homology/DerivedCategory/BoundedCohomologicalDimensionPlus.lean`, which
  turn a degreewise vanishing above `d` into a shift of the band by `d` for an object with a
  finite window of cohomology.

That route is taken rather than [Stacks, Tag 07K7] itself because the library's form of 07K7,
`CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived`, concludes about a right
derived functor on the *unbounded* `D(Ab(X_Zar))` together with its unit, and no such functor is
constructed for `Γ(X_Zar, -)` anywhere in this library — only
`...SmallSite.derivedZariskiGlobalSectionsFunctor` on `D⁺`.  The dévissage above is stated for a
functor out of `D⁺` and so applies directly.  The bound obtained is the same: `b = e` and
`n = d + 1` in 07K7's `b + n - 1`.

The weak Serre subcategory of the dévissage is taken to be everything, `⊤`: the Zariski bound
holds for an arbitrary abelian sheaf, so no condition on the cohomology sheaves of `K` is needed,
and none is imposed. -/
theorem isLE_derivedZariskiGlobalSections_obj [CompactSpace ↥S.X] [QuasiSeparatedSpace ↥S.X]
    (K : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})) (d e : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (d : WithBot ℕ∞))
    (hGE : K.IsGE 0) (hLE : K.IsLE (e : ℤ)) :
    ((derivedZariskiGlobalSectionsFunctor S).obj K).IsLE ((e : ℤ) + (d : ℤ)) := by
  let G := (zariskiGlobalSections S).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  have : G.IsTriangulated := by
    dsimp [G]
    infer_instance
  have hmain : (G.obj K).IsLE ((0 : ℤ) + (e : ℤ) + (d : ℤ)) :=
    Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem G ⊤ inferInstance
      (d : ℤ)
      (fun q M _ =>
        Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single
          (zariskiGlobalSections S) M (d : ℤ) q fun p hp =>
            isZero_rightDerivedZariskiGlobalSections_of_topologicalKrullDim_le S M d p hdim
              (by exact_mod_cast hp))
      0 e K hGE (by simpa using hLE) fun _ _ _ => trivial
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, show (e : ℤ) + d = 0 + e + d by ring]
  exact hmain

/-! ### Clause (1) of the abelian form of [Stacks, Tag 07MR], and its reduction -/

/-- **Clause (1) of `...SmallSite.AbelianVanishing07MR`**, verbatim: the `d + e` bound, with the
hypotheses of that proposition in the same order.  `abelianVanishing07MR_of_clauses` checks that
this and `AbelianVanishing07MRClauseTwo` are together the whole of it. -/
def AbelianVanishing07MRClauseOne : Prop :=
  Subsingleton ↥(DividedPowerScheme.closedFiber S.S) →
    Nonempty ↥(DividedPowerScheme.closedFiber S.S) →
      LocallyOfFinitePresentation S.toClosedFiber → QuasiCompact S.toClosedFiber →
        QuasiSeparated S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
            ∀ d e : ℕ, topologicalKrullDim ↥S.X = (d : WithBot ℕ∞) →
              S.toClosedFiber.HasEmbeddingDimensionLE e →
                ∀ i : ℕ, d + e < i → Subsingleton (cohomology S (abelianSheaf F) i)

/-- **Clause (2) of `...SmallSite.AbelianVanishing07MR`**, verbatim: the `q + e` bound for a
separated `X` covered by `q` affine opens.  Nothing in this file is about it; it is here so that
`abelianVanishing07MR_of_clauses` can exhibit the decomposition of the abelian form into its two
clauses, and so that `AbelianVanishing07MRClauseOne` is visibly a *part* of that form rather than
a weakening of it. -/
def AbelianVanishing07MRClauseTwo : Prop :=
  Subsingleton ↥(DividedPowerScheme.closedFiber S.S) →
    Nonempty ↥(DividedPowerScheme.closedFiber S.S) →
      LocallyOfFinitePresentation S.toClosedFiber → QuasiCompact S.toClosedFiber →
        QuasiSeparated S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
            ∀ q e : ℕ, Scheme.IsSeparated S.X →
              (∃ U : Fin q → S.X.Opens, (∀ k, IsAffineOpen (U k)) ∧ (⨆ k, U k) = ⊤) →
                S.toClosedFiber.HasEmbeddingDimensionLE e →
                  ∀ i : ℕ, q + e < i → Subsingleton (cohomology S (abelianSheaf F) i)

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
/-- **The abelian form of [Stacks, Tag 07MR] is exactly its two clauses.**  Both clauses carry the
same hypotheses, so the decomposition is by `fun … => ⟨_, _⟩` and no hypothesis is duplicated or
dropped; this is what makes `AbelianVanishing07MRClauseOne` a faithful reading of clause (1). -/
theorem abelianVanishing07MR_of_clauses (h₁ : AbelianVanishing07MRClauseOne S)
    (h₂ : AbelianVanishing07MRClauseTwo S) : AbelianVanishing07MR S :=
  fun hsub hne hfp hqc hqs F hqcoh =>
    ⟨h₁ hsub hne hfp hqc hqs F hqcoh, h₂ hsub hne hfp hqc hqs F hqcoh⟩

/-- **Clause (1) of the abelian form of [Stacks, Tag 07MR] follows from the sheaf-level vanishing
`DirectImageVanishing07MR`, and from nothing else.**

This is the reduction of clause (1), in the shape of
`...SmallSite.vanishing07MR_of_abelianVanishing07MR`: the target follows from one named
proposition and from proved theorems only.  Spelled out, the inputs are

* `...SmallSite.compactSpace_of_subsingleton_closedFiber` and
  `...quasiSeparatedSpace_of_subsingleton_closedFiber`, which derive the space hypotheses of the
  Zariski bound from the clause's own hypotheses rather than assuming them;
* `isLE_derivedZariskiGlobalSections_obj` above, the hypercohomology bound, itself proved from
  `...isZero_rightDerivedZariskiGlobalSections_of_topologicalKrullDim_le` and the
  dévissage of `Stacks.BoundedCohomologicalDimension`;
* `isLE_derivedZariskiDirectImage_obj` above, [Stacks, Tag 0118] at `D⁺(Ab(X_Zar))`, and the
  lower bound `...SmallSite.isGE_derivedZariskiDirectImage_obj`;
* `...SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImageObj`, [Stacks, Tag 015M] for
  `u_{X/S}`, which is where `H^i(Cris(X/S), -)` becomes `H^i(X_Zar, Ru_{X/S, *}-)`;
* `...SmallSite.homologyDerivedGlobalSectionsIso`,
  `...SmallSite.rightDerivedGlobalSectionsIso` and
  `...SmallSite.subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections`, which identify the
  cohomology of `RΓ(Cris(X/S), -)` with the chapter's graded `H^i(Cris(X/S), -)`.

**It is not a proof of the clause**, because `DirectImageVanishing07MR` is not discharged — that
is the missing mathematics, and the module documentation above says what it would take.  What it
does establish is that the degree-`e` concentration of `Ru_{X/S, *}F` is the *only* thing clause
(1) still wants: everything else the source's hint uses for that clause is now a theorem of this
library.  No tag attribute is placed. -/
theorem abelianVanishing07MRClauseOne_of_directImageVanishing07MR
    (hvan : DirectImageVanishing07MR S) : AbelianVanishing07MRClauseOne S := by
  intro hsub hne hfp hqc hqs F hqcoh d e hdim he i hi
  have := compactSpace_of_subsingleton_closedFiber S hsub hqc
  have := quasiSeparatedSpace_of_subsingleton_closedFiber S hsub hqs
  have hLE := isLE_derivedZariskiGlobalSections_obj S
    ((derivedZariskiDirectImage S).obj (abelianSheaf F)) d e hdim.le
    (isGE_derivedZariskiDirectImage_obj S (abelianSheaf F))
    (isLE_derivedZariskiDirectImage_obj S (abelianSheaf F) (e : ℤ)
      (hvan hsub hne hfp hqc hqs F hqcoh e he))
  have hstep : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S).obj
        ((derivedZariskiDirectImage S).obj (abelianSheaf F)))) :=
    (DerivedCategory.Plus.isLE_iff _ ((e : ℤ) + (d : ℤ))).1 hLE (i : ℤ) (by
      omega)
  have hRΓ : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedGlobalSections S).obj (abelianSheaf F))) :=
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).mapIso
      ((derivedGlobalSectionsIsoDerivedZariskiDirectImageObj S).app (abelianSheaf F))).isZero_iff.2
        hstep
  exact (subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections S (abelianSheaf F) i).2
    (((rightDerivedGlobalSectionsIso S i).app (abelianSheaf F)).isZero_iff.2
      (((homologyDerivedGlobalSectionsIso S i).app (abelianSheaf F)).isZero_iff.1 hRΓ))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
