module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClassOfModule

/-!
# The constant-rank Chern classes on the rank loci

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℰ` be a finite locally free `O_X`-module whose rank need
not be constant. Stacks 0ESW builds the Chern classes of such a module out of the constant-rank
Chern classes of its restrictions `ℰ|_{X_r}` to the rank loci, and
`Stacks.Chow.chernClassArbitraryRank` carries that family of constant-rank classes as a
quantified argument.

This file supplies it. On the rank-`r` locus the module is finite locally free of constant rank
`r`, by `Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_rankLocus`, so the bivariant Chern classes
of Stacks 0B7H apply there and `Stacks.Chow.chernClass` is the family.

## Main definitions

* `Stacks.Chow.rankLocusChernClass` — the family `(c_j(ℰ|_{X_r}))_{r, j}` of constant-rank Chern
  classes on the rank loci, in the form `Stacks.Chow.chernClassArbitraryRank` consumes.

## Main results

* `Stacks.Chow.isChernClassBivariant_rankLocusChernClass` — each member of the family satisfies
  the characterization of Stacks 0B7H on its locus.
* `Stacks.Chow.pullbackPreservesRank_rankLocus` — the rank hypothesis that
  `Stacks.Chow.chernClassArbitraryRank` carries alongside the family is discharged, not assumed.
* `Stacks.Chow.rankLocus_eq_top`, `Stacks.Chow.rankLocus_eq_bot_of_ne` — on a module whose rank is
  globally constant and equal to `r₀`, the rank-`r₀` locus is the whole scheme and every other
  locus is empty, so the clopen decomposition of Stacks 0ESW has a single nonempty piece there.

## Implementation notes

The parameters carried are those of `Stacks.Chow.chernClass`, read on each rank locus: the Chern
cap products `caps` of Stacks 0B7G, the three naturality identities of Stacks 0B76 for them, and
the isomorphism clause `hiso` for the Gysin system. Nothing is added and nothing is weakened.
Stacks 0B7G rests on Stacks 02U5 and 02U7, neither of which is formalized here, so the cap
products are still data; what is no longer data is the family of classes read off them.

The rank instance on a locus is a `local instance` rather than a global one: it is keyed on the
shape `ℰ|_{X_r}` with the same `r`, so it is harmless here, but
`Stacks.Chow.pullbackPreservesRank_of_isFiniteLocallyFreeOfRank` is deliberately not an instance
upstream — a rank cannot in general be inferred — and this file does not change that.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- On its rank-`r` locus the module is finite locally free of constant rank `r`. Local to this
file, so that the constructions below can be stated without passing the instance by hand. -/
local instance isFiniteLocallyFreeOfRank_rankLocus (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r :=
  isFiniteLocallyFreeOfRank_pullback_rankLocus E r

/-- On a module of constant rank `r`, the rank at every point is `r`. -/
private theorem moduleRank_eq_of_isFiniteLocallyFreeOfRank (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    moduleRank E x = r :=
  (fiberRank_eq_moduleRank E x).symm.trans
    (AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank E r x)

/-- On a module whose rank is globally constant and equal to `r`, the rank-`r` locus is the whole
scheme: every point has fibre rank `r`, by Stacks 01C9, and the locus is cut out by exactly that
condition. -/
theorem rankLocus_eq_top (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    rankLocus E r = ⊤ := by
  ext x
  refine ⟨fun _ ↦ by simp, fun _ ↦ ?_⟩
  exact (mem_rankLocus E).2 (moduleRank_eq_of_isFiniteLocallyFreeOfRank E r x)

/-- On a module whose rank is globally constant and equal to `r₀`, every other rank locus is
empty, so the clopen decomposition of Stacks 0ESW has a single nonempty piece. -/
theorem rankLocus_eq_bot_of_ne (r₀ r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r₀] (h : r ≠ r₀) :
    rankLocus E r = ⊥ := by
  ext x
  exact ⟨fun hx ↦ absurd (((mem_rankLocus E).1 hx).symm.trans
    (moduleRank_eq_of_isFiniteLocallyFreeOfRank E r₀ x)) h, fun hx ↦ by simp at hx⟩

/-- **The rank hypothesis of Stacks 0ESW, discharged.** The pullback of the restriction
`ℰ|_{X_r}` along any morphism is again of rank `r`, so the hypothesis
`Stacks.Chow.chernClassArbitraryRank` carries beside the family of constant-rank classes need not
be assumed. -/
theorem pullbackPreservesRank_rankLocus (r : ℕ) :
    PullbackPreservesRank ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r :=
  pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r

variable (caps : ∀ r : ℕ, HigherChernCapRule C r)
  (hproper : ∀ (r : ℕ) (i : Fin (r + 1)),
    IdentityCapRule.ProperNaturality C ((rankLocus E r).ι ≫ sX) (i : ℤ)
      (chernIdentityCapRuleOfRank C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r (caps r) i))
  (hflat : ∀ (r : ℕ) (i : Fin (r + 1)),
    IdentityCapRule.FlatNaturality C ((rankLocus E r).ι ≫ sX) (i : ℤ)
      (chernIdentityCapRuleOfRank C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r (caps r) i))
  (hgysin : ∀ (r : ℕ) (i : Fin (r + 1)),
    IdentityCapRule.GysinNaturality C ((rankLocus E r).ι ≫ sX) (i : ℤ)
      (chernIdentityCapRuleOfRank C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r (caps r) i) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- The family `(c_j(ℰ|_{X_r}))_{r, j}` of constant-rank Chern classes on the rank loci, in the
form `Stacks.Chow.chernClassArbitraryRank` consumes: on the rank-`r` locus the module has constant
rank `r`, so its `j`-th Chern class is the bivariant class of Stacks 0B7H there. -/
def rankLocusChernClass (r : ℕ) (j : Fin (r + 1)) :
    chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) (j : ℤ) :=
  chernClass C ((rankLocus E r).ι ≫ sX)
    ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r G (caps r)
    (hproper r) (hflat r) (hgysin r) hiso j

/-- Each member of the family satisfies the characterization of Stacks 0B7H on its locus, so it is
a family of bivariant Chern classes of the restrictions and not assumed to be one. -/
theorem isChernClassBivariant_rankLocusChernClass (r : ℕ) (j : Fin (r + 1)) :
    IsChernClassBivariant C ((rankLocus E r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r G (caps r)
      (pullbackPreservesRank_rankLocus E r) j
      (rankLocusChernClass C G sX E caps hproper hflat hgysin hiso r j) :=
  isChernClassBivariant_chernClass C ((rankLocus E r).ι ≫ sX)
    ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r G (caps r)
    (hproper r) (hflat r) (hgysin r) hiso j

end Stacks.Chow

end
