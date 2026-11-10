module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.FactorSolutions
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TameConstantNumerator
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.WildLayerDescent
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.PrescribedFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TowerLevels
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.TowerInduction

/-!
# Per-factor packages over one shared base extension

`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`
(`EppDegreePrimeBridge.lean`) is the assembly step of the all-factor route to Tag 09F9: it turns a
weak solution at **every** conjugate factor of `(L ⊗[K] K₁) ⧸ nilradical`, all packaged over
**one shared** second extension `K₂`, into a weak solution for `A → B` — and, unlike the
amalgamating bridge beside it, assumes neither completeness nor an algebraically closed residue
field.

Its `hfactors` hypothesis is large: thirteen existentially quantified instances on the per-factor
rings, two compatibility squares, and then the weak solutions.  This file discharges all of it
except the weak solutions, by taking the per-factor ring to be `integralClosure B (E i)` and
citing `Stacks.EppTheorem` in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage` for each obligation.  What a
caller is left owing is exactly

  `∀ i, ∃ D, D.IsWeakSolution`

over one `K₂` fixed in advance — the synchronization, which is the remaining mathematics.

## Why `B` henselian

Over a general discrete valuation ring `integralClosure B (E i)` is only semilocal, so it is a
Dedekind domain and not a discrete valuation ring, and the combiner's instance list cannot be
met.  Henselianness makes it local.  This is not a weakening of the route: the finite-support
absorption that feeds the degree-`p` layer
(`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`) already
  requires
`B` henselian, and the completion step of the 09F9 chain is what arranges it.

## No factor is distinguished

`hfactors` is quantified over every index, and so is the hypothesis below.  The conjugate factors
are pairwise distinct (`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`) and the
  conjugate condition can
genuinely fail, so the step of the published proof
of Tag 09ET that descends along one embedding is unavailable, and nothing here uses it.

## Main results

* `Stacks.EppTheorem.exists_reducedFactorPackages`: from per-factor weak solutions over a shared
  `K₂`,
  the full `hfactors` payload with `S i = integralClosure B (E i)`.
* `Stacks.EppTheorem.algebraMap_reducedFactor_base_eq` and
  `Stacks.EppTheorem.algebraMap_reducedFactor_base_eq_of_tower`: the two routes from `A` into a
    conjugate
  factor agree — `A → L → E i` equals `A → K₁ → E i`, and likewise read through `B`.  This is the
  factor-level analogue of the `hA` hypothesis the combiner takes at `K₂`, and it is the one
  structure `exists_reducedFactorPackages` needs that is *not* a composite of what `hfactors`
  hands out: it is a genuine compatibility of the decomposition with `A`, obtained by projecting
  along `decomp` the fact that `includeLeft` and `includeRight` already agree on the image of `A`,
  since both are `K`-algebra maps and `A` acts through `K`.

* `Stacks.EppTheorem.FactorSolutions`: the per-factor obligation, named once in the instance
  context the
  combiner's data determines but does not hand over — the three composites `B → L → E i`,
  `A → B → E i`, `R → K₁ → E i` with their towers, the faithfulness of `R` on the factor, the
  factor square, and the five structures on `integralClosure B (E i)`.
* `Stacks.EppTheorem.isWeakSolution_of_forall_factorSolutions`: **the route, end to end.** If
  `FactorSolutions` holds for every decomposition, the caller's own base change `D₂` over `K₂` is
  a weak solution for `A → B`.
* `Stacks.EppTheorem.factorSolutions_of_tame`: **the tame case of `FactorSolutions`, discharged.**
  If
  every factor's extension `R → integralClosure B (E i)` is tamely ramified and the prescribed
  `K₂` has local ramification index over `R` divisible by each factor's, then `FactorSolutions`
  holds.  This is where the prescribed-extension form of Abhyankar's lemma
  (`IsDiscreteValuationRing.isWeakSolution_of_tame_of_ramificationIndex_dvd`) pays off: the
  weak-solution property is re-derived over the `K₂` the caller fixed, so one extension serves
  every factor.  Taking `K₂ = K₁(π₁^{1/e})` with `e` the lcm of the factors' ramification indices
  makes the divisibility automatic.
* `Stacks.EppTheorem.factorSolutions_of_isWeaklyUnramified`: **the carried case of
  `FactorSolutions`,
  discharged, with no completeness hypothesis.**  If the prescribed `K₂ / K₁` is totally ramified
  with respect to `R` and separable, every factor that is *already* weakly unramified over `R` is
  solved by that same `K₂`.  This is what lets a layer recursion carry its finished members
  through the shared base change instead of solving them separately and reconciling the results —
  which would be the very amalgamation the route forbids.  `htot` is a condition on `K₂ / K₁`
  alone, checked once rather than per factor, and the engine is Tag 09ER in package form
  (`IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`),
  which needs no completeness — unlike Abhyankar's lemma, so this case is strictly cheaper than
  the tame one.
* `Stacks.EppTheorem.factorSolutions_of_forall_isWeaklyUnramified_or_tame`: **a mixed family,
  carried and
  solved over one prescribed `K₂`.**  Each factor may independently be either already weakly
  unramified or tame, and one `K₂` discharges `FactorSolutions` for all of them.  This is the
  shape a layer recursion needs at every level, where some members are finished and some are not:
  the disjunction is resolved *inside* the `∀ i`, each branch consuming the same prescribed `K₂`
  through its own prescribed-extension engine, so the two kinds never have to be solved separately
  and reconciled.  That reconciliation is the amalgamation the route forbids, and it is what
  `∃ K₂` sitting outside `∀ i` exists to avoid.  The wild case is in neither branch and is still
  open.

* `Stacks.EppTheorem.exists_sharedExtension_factorSolutions_of_tame`: the tame case with the shared
  extension **constructed**, not prescribed.  For any `e ≥ 2` divisible by every factor's
  ramification index over `R`, the Kummer extension `K₂ = K₁(π₁^{1/e})` has local ramification
  index exactly `e` over `R`, so the divisibility holds at its unique maximal ideal.  Taking `e`
  to be a common multiple of the factors' indices makes the tame case unconditional: a single
  `K₂`, written down before any factor is examined, serves all of them.

* `EppTheorem.exists_sharedExtension_factorSolutions_of_prepared_wild_or_isWeaklyUnramified`:
  **the wild and carried cases together, over one produced `K₂`.**  Each factor is either wild —
  presented as `R → Bi i → integralClosure B (E i)` with `R → Bi i` weakly unramified, the top step
  a degree-`p` Artin--Schreier layer with a prepared Laurent presentation whose wild set is
  **nonempty** — or already weakly unramified over `R`; the choice is per factor and any mixture is
  allowed.  One finite `K₂ / K₁` is produced and discharges `FactorSolutions` for the whole family.
  The engine is
  `exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_wild_laurent` of
  `IsDiscreteValuationRing`
  (`EppWildFamilyPreparation.lean`), run on the wild sub-family, whose rings and fields are indexed
  by the member because the weakly unramified layer inside a factor differs from factor to factor.
  The conclusion **exposes** `IsGalois K₁ K₂` and `IsTotallyRamifiedWithRespectTo R K₁ K₂`, which
  is what makes the carried branch available at all: those are the inputs of
  `exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`, the engine of
  `factorSolutions_of_isWeaklyUnramified`.  The disjunction is resolved inside the `∀ i`, so the
  two kinds are never solved over different extensions and reconciled — that reconciliation is the
  amalgamation the route forbids.  Only `K₂` is shared; each wild factor keeps its own pole order,
  wild set, depths and maximising position, and the extension's parameters are fixed once from the
  whole prepared family before any per-factor proof.  Not covered: a factor that is genuinely
  ramified with an **empty** wild set.

## What remains

The **`J i = ∅` / all-perfect-core** case, precisely.  The tame case is `factorSolutions_of_tame`,
its shared extension built by `exists_sharedExtension_factorSolutions_of_tame`; the carried case is
`factorSolutions_of_isWeaklyUnramified` when `K₂` is prescribed, and is the second branch of
`exists_sharedExtension_factorSolutions_of_prepared_wild_or_isWeaklyUnramified` when `K₂` is
produced; the wild case with a nonempty wild set is the first branch of that same theorem, and
`IsDiscreteValuationRing.exists_prepared_wild_laurent_of_charP` produces every hypothesis of it
unconditionally **except** that nonemptiness.

A factor that is genuinely ramified with an empty wild set is in **neither** branch, and it cannot
be patched by a second construction: building one extension for those factors and another for the
wild ones, then reconciling, is exactly the amalgamation this route forbids.  It has to be folded
into the same construction, which is what the mixed shape of that theorem exists to be extended
to.

If `J i = ∅` then every Laurent coefficient of factor `i` lies in `perfectCore (κ_{Bi i}) p`, i.e.
is a `p ^ m`-th power for *every* `m`.  The wild construction cannot be repaired to cover it: it is
driven throughout by a coefficient with a **terminal** root — one that is not itself a `p`-th power
— and a perfect-core coefficient has no terminal root at any depth.  That case is the
constant-numerator branch, whose endgame produces an Artin--Schreier extension of `K₁` itself and
genuinely interrogates the *base* residue field.  It is where `Stacks.EppTheorem.EppCondition`
  enters, via
absorption of the deep roots into a finite étale base change
(`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`), and it is
  proved
nowhere in the tree.  Mixed characteristic and the removal of henselianness by completion descent
remain separate and also open.

`StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFamilySupport` supplies the step that
comes *before* it: one finite Galois residue extension covering the coefficient supports of
**every** factor at a prescribed Frobenius depth, obtained by unioning the minimal polynomials
across the whole family in the polynomial ring over the base residue field — the only place the
union can happen, since the factors' residue fields are pairwise different types.  Together with
this file, the route is complete at both ends and open in the middle: what is missing is a
per-factor degree-`p` endgame run against a **prescribed** `K₂`.  Every endgame in the tree instead
*produces* its own extension, and weak solutions are not stable under finite enlargement, so this
has to be a re-derivation rather than a transport.

That is genuine mathematics and
it is not proved here, so there is still no unconditional Tag 09F9 and nothing in this file is
tagged.  What has changed is that every structural obligation between the combiner and that
statement is now discharged.

## References

* [The Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/
