module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.BaseSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local `n`-th roots of units on the big `τ`-sites of a scheme

Let `S` be a scheme of a chosen big fppf site `B`.  The big `τ`-site of `S` carrying the sheaf
of global functions, `AlgebraicGeometry.BigFppfOver.baseRingedSite`, is a ringed site, and the
hypothesis `Stacks.Cohomology.Torsors.Generators.LocalRoots` — every unit of the structure sheaf
has an `n`-th root of its inverse on a covering of every object — holds on it for the fppf and
the syntomic topology when `n` is positive, and for the étale topology when `n` is invertible on
`S`.

This is the last input of `AlgebraicGeometry.trivializationTorsor`, the torsor of
trivializations of a pair `(L, α)` of Tag 040Q, on those three sites: the torsor exists there
because the surjectivity half of the Kummer sequence of Tags 040N and 03PL holds there.

## Main results

* `AlgebraicGeometry.localRoots_baseRingedSite_fppf`,
  `AlgebraicGeometry.localRoots_baseRingedSite_syntomic` — **units have local `n`-th roots on the
  big fppf and big syntomic sites of `S`**, for `n` positive.
* `AlgebraicGeometry.localRoots_baseRingedSite_etale` — **units have local `n`-th roots on the
  big étale site of `S`**, when `n` is invertible on `S`.

## Implementation notes

Nothing is proved here that is not already proved: each of the three statements is the
corresponding local surjectivity theorem of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/BaseSites.lean` fed to
`Stacks.Cohomology.Torsors.Generators.localRoots_of_isLocallySurjective`.  What makes that
possible with no transport is a chain of definitional equalities.  The ringed site
`AlgebraicGeometry.BigFppfOver.baseRingedSite B S hS τ` *is*
`AlgebraicGeometry.schemeFunctionsRingedSite` on the localized topology and the functor to
schemes, by `AlgebraicGeometry.baseRingedSite_eq`; the sheaf of units written additively of such
a ringed site *is* the sheaf of units of the functor; and `n • 𝟙` on it *is*
`AlgebraicGeometry.powerPresheaf`, which is how that morphism is defined.  So the hypothesis of
`localRoots_of_isLocallySurjective` and the conclusion of, say,
`AlgebraicGeometry.fppf_power_isLocallySurjective_base` are one proposition, modulo the spelling
of the topology: `(BigFppfOver.baseRingedSite B S hS τ).J` versus
`BigFppfOver.baseOverTopology B S hS τ`, again the same term.

The two sheafification side conditions carried by the variable block of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Torsors/NormalizedGenerators.lean` are not needed
by `localRoots_of_isLocallySurjective` itself — neither
`Stacks.Cohomology.Torsors.Generators.LocalRoots` nor
`Stacks.Cohomology.Torsors.Generators.unitsAddSheaf` mentions sheafification — so no instance
binder appears here and the three statements are unconditional apart from their arithmetic
hypothesis on `n`.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors.Generators

namespace AlgebraicGeometry

universe u

/-- **Units have local `n`-th roots on the big fppf site of a scheme**, for `n` positive: every
unit of the sheaf of global functions has, on an fppf covering of every object of `(Sch/S)`, an
`n`-th root of its inverse.

This is `AlgebraicGeometry.fppf_power_isLocallySurjective_base`, the surjectivity half of the
fppf Kummer sequence, read through the identification of the `n`-th power map on the sheaf of
units of the ringed site with `AlgebraicGeometry.powerPresheaf`. -/
@[sga "7 IX 7.2.1.3" "special case"]
public theorem localRoots_baseRingedSite_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    LocalRoots (BigFppfOver.baseRingedSite B S hS .fppf) n :=
  localRoots_of_isLocallySurjective (BigFppfOver.baseRingedSite B S hS .fppf) n
    (fppf_power_isLocallySurjective_base B S hS n hn)

/-- **Units have local `n`-th roots on the big syntomic site of a scheme**, for `n` positive: a
unit acquires an `n`-th root of its inverse on a syntomic covering, by adjoining a root of
`X ^ n - a`.

This is `AlgebraicGeometry.syntomic_power_isLocallySurjective_base` read through the same
identification. -/
public theorem localRoots_baseRingedSite_syntomic (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : 0 < n) :
    LocalRoots (BigFppfOver.baseRingedSite B S hS .syntomic) n :=
  localRoots_of_isLocallySurjective (BigFppfOver.baseRingedSite B S hS .syntomic) n
    (syntomic_power_isLocallySurjective_base B S hS n hn)

/-- **Units have local `n`-th roots on the big étale site of a scheme**, when `n` is invertible
on `S`: the same polynomial `X ^ n - a` is étale over the base once `n` is a unit there.

This is `AlgebraicGeometry.etale_power_isLocallySurjective_base` read through the same
identification. -/
public theorem localRoots_baseRingedSite_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (n : ℕ) (hn : IsUnit (n : Scheme.Γ.obj (Opposite.op S))) :
    LocalRoots (BigFppfOver.baseRingedSite B S hS .etale) n :=
  localRoots_of_isLocallySurjective (BigFppfOver.baseRingedSite B S hS .etale) n
    (etale_power_isLocallySurjective_base B S hS n hn)

end AlgebraicGeometry

end
