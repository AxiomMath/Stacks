module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalenceUnconditional

/-!
# The small étale comparison `D(QCoh) ⥤ D_QCoh` is an equivalence exactly when Stacks 071Q holds

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the comparison of ringed sites
of Stacks 08H7/070R.  `AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule` —
Stacks 071Q, that `ε^* : D_QCoh(𝒪_S) ⟶ D_QCoh(S_étale, 𝒪)` is an equivalence — carries exactly
one hypothesis that is not proved, namely that the small étale analogue of the Stacks 06VT
comparison `D(QCoh(S_étale, 𝒪)) ⥤ D_QCoh(S_étale, 𝒪)`,
`AlgebraicGeometry.SmallEtale.derivedQcohOnSiteComparison`, is an equivalence.

**That hypothesis is not an input to Stacks 071Q; it is equivalent to it.**  This file proves the
implication that makes it so: over the *Zariski* half of the Stacks 06VT comparison being an
equivalence, Stacks 071Q *implies* that the small étale comparison is an equivalence, which is
the converse of the deduction `isEquivalence_derivedAssociatedModule` performs.  Both directions
pass through the one square
`AlgebraicGeometry.SmallEtale.derivedQuasicoherentComparisonSquare`, whose remaining two vertices
— the abelian equivalence of Stacks 03DX (2) at `τ = étale` on the derived categories of the
quasi-coherent modules, `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleDerivedQcoh'`,
and the Zariski comparison — are respectively proved unconditionally and proved at every affine
scheme.

The consequence is recorded here because it bounds what can be expected of that hypothesis.  The
module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean` says
only that the hypothesis "cannot be obtained from `derivedQuasicoherentComparisonSquare`, which
would need 071Q itself"; the statements below say the sharper thing, that over the Zariski
comparison the two are *interderivable*, so that discharging the hypothesis is neither easier
nor different from proving Stacks 071Q.  At an affine scheme — the only case the pseudo-coherence
applications of Stacks 0DII need — the Zariski binder is met by Stacks 06Z0,
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel`, so there
the equivalence of the two statements is unconditional; see the implementation notes for why that
specialization is left to the point of use rather than stated here.

## Why the route through the two comparison functors cannot reach Stacks 071Q

At a general scheme the small étale hypothesis is not merely unproved: it is *false*.  Granting
Stacks 071Q — a theorem of the source, with no hypothesis on `S` — the statements below make the
small étale comparison an equivalence if and only if the Zariski one is, and the Zariski one is
the conclusion of Stacks 08DB, which the source proves for a scheme that is quasi-compact with
affine diagonal and not in general.  So the route to Stacks 071Q through the two comparison
functors cannot be completed at the generality of Stacks 071Q, whatever is done to the small
étale side; and at an affine scheme, where both comparisons are equivalences, completing it is
the same problem as Stacks 071Q.  The source's own route is `Rε_*`, the derived direct image
along `ε`.

## Main results

* `isEquivalence_derivedQcohOnSiteComparison_of_isEquivalence_derivedAssociatedModule`: over
  the Zariski half of the Stacks 06VT comparison, Stacks 071Q implies that the small étale
  comparison `D(QCoh(S_étale, 𝒪)) ⥤ D_QCoh(S_étale, 𝒪)` is an equivalence.
* `isEquivalence_derivedQcohOnSiteComparison_iff`: hence, over the Zariski half, the small étale
  comparison is an equivalence if and only if Stacks 071Q holds.

## Implementation notes

No `@[stacks]` attribute is attached to anything here.  Neither statement is a clause of Stacks
071Q or of Stacks 06VT: each is an implication *between* two assertions, and a tag may not sit on
a declaration that assumes what the tag asserts.

**Why the affine specialization is not stated.**  Instantiating the Zariski binder by Stacks 06Z0
needs `StacksFrontier/AlgebraicGeometry/DerivedQCoh/ComparisonAffine.lean` imported, and importing
it makes the binders below fail to elaborate: the `Abelian` instance of
`SheafOfModules.{u} (structureSheaf B S hS)`, which the closure properties of `qcohOnSite` are
stated over, is then synthesized from a candidate that forces the module universe to be at least
the universe `u + 1` of the objects of the small étale site, and the resulting universe constraint
`u =?= max (u + 1) ?v` is unsolvable.  A consumer of
`isEquivalence_derivedQcohOnSiteComparison_iff` at an affine scheme supplies the binder itself and
meets no such obstruction, the binders of the `iff` being already fixed there.

Essential surjectivity of `ε^*` on quasi-coherent modules is not a hypothesis: it is supplied
throughout by `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`,
which is also the witness
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleDerivedQcoh'` is stated at, so the
two uses agree on the nose rather than up to an isomorphism of functors.

The binders are those of the `Equivalence` section of `SmallEtaleDerivedEquivalence.lean` with
its two `IsEquivalence` hypotheses removed: the weak-Serre closure of quasi-coherence on
`S_étale` (Stacks 06VE (5), (10) at `τ = étale`), the exactness of `ε^*` (the second assertion of
Stacks 08H8) and the four derived-category models.  All four of the first group are library
instances — in files that import `SmallEtaleDerivedEquivalence` and so are discharged by instance
search at any point of use — and they are carried rather than discharged here because they are
what pins the universe parameters of `AlgebraicGeometry.SmallEtale.qcohOnSite`, exactly as in
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleDerivedQcoh'`.  The
`HasDerivedCategory` instances are left free for the reason given there: pinning
`CategoryTheory.HasDerivedCategory.standard` would put the morphisms of `D(𝒪_S)` one universe
above its objects.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (qcohOnSite B S hS).FullSubcategory]
  [(qcohOnSite B S hS).IsClosedUnderKernels]
  [(qcohOnSite B S hS).IsClosedUnderCokernels]
  [(qcohOnSite B S hS).IsClosedUnderExtensions]
  [PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]

section Zariski

variable
  [(Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{w}
    S).IsEquivalence]

omit [(qcohOnSite B S hS).IsClosedUnderKernels]
  [(qcohOnSite B S hS).IsClosedUnderCokernels]
  [(qcohOnSite B S hS).IsClosedUnderExtensions]
  [PreservesFiniteLimits (associatedModuleOfSheaf B S hS)] in
/-- **Stacks 071Q implies the small étale half of the Stacks 06VT comparison**, over the Zariski
half of that comparison.

This is the converse of the deduction of
`AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule`, read off the same square
`AlgebraicGeometry.SmallEtale.derivedQuasicoherentComparisonSquare`: the left-hand composite
`i_S ⋙ ε^*_{D_QCoh}` is an equivalence because both of its factors are, so the right-hand
composite `ε^*_{D(QCoh)} ⋙ i_{S,étale}` is one too, and its left factor is the equivalence of
Stacks 03DX (2) at `τ = étale` on the derived categories of the quasi-coherent modules. -/
theorem isEquivalence_derivedQcohOnSiteComparison_of_isEquivalence_derivedAssociatedModule
    (h : (derivedAssociatedModule.{w} B S hS).IsEquivalence) :
    (derivedQcohOnSiteComparison.{w} B S hS).IsEquivalence := by
  have := h
  have := isEquivalence_associatedModuleDerivedQcoh'.{w} B S hS
  have : (associatedModuleDerivedQcoh.{w} B S hS
      (quasicoherentIsEssImageAssociatedModule B S hS) ⋙
        derivedQcohOnSiteComparison.{w} B S hS).IsEquivalence :=
    Functor.isEquivalence_of_iso (derivedQuasicoherentComparisonSquare.{w} B S hS
      (quasicoherentIsEssImageAssociatedModule B S hS))
  exact Functor.isEquivalence_of_comp_left
    (associatedModuleDerivedQcoh.{w} B S hS (quasicoherentIsEssImageAssociatedModule B S hS))
    (derivedQcohOnSiteComparison.{w} B S hS)

omit [(qcohOnSite B S hS).IsClosedUnderKernels]
  [(qcohOnSite B S hS).IsClosedUnderCokernels]
  [(qcohOnSite B S hS).IsClosedUnderExtensions]
  [PreservesFiniteLimits (associatedModuleOfSheaf B S hS)] in
/-- **The small étale half of the Stacks 06VT comparison and Stacks 071Q are interderivable**,
over the Zariski half of that comparison.

Forwards this is `AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule` with its
last hypothesis supplied, and backwards it is
`isEquivalence_derivedQcohOnSiteComparison_of_isEquivalence_derivedAssociatedModule`.  So the
hypothesis that declaration still carries is not an input to Stacks 071Q but a restatement of
it. -/
theorem isEquivalence_derivedQcohOnSiteComparison_iff :
    (derivedQcohOnSiteComparison.{w} B S hS).IsEquivalence ↔
      (derivedAssociatedModule.{w} B S hS).IsEquivalence := by
  refine ⟨fun h => ?_,
    isEquivalence_derivedQcohOnSiteComparison_of_isEquivalence_derivedAssociatedModule B S hS⟩
  have := h
  exact isEquivalence_derivedAssociatedModule.{w} B S hS
    (quasicoherentIsEssImageAssociatedModule B S hS)

end Zariski

end Comparison

end AlgebraicGeometry.SmallEtale

end
