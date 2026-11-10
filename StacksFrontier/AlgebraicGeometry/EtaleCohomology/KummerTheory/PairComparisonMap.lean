module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairAddCommGroup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairTransportIso

/-!
# The comparison map of Tag 040Q on the big `τ`-site

Tag 040Q identifies the isomorphism classes of pairs `(ℒ, α)` on a scheme `S` — an invertible
`𝒪_S`-module together with a trivialization `α : ℒ^{⊗ n} ≅ 𝒪_S` — with `H¹(S, μ_n)`.  This file
builds the map that the identification is supposed to be.

A pair on `S` is carried to the big `τ`-site by the associated-module functor of Descent,
Proposition 03DX (`AlgebraicGeometry.basePairSheaf`, `AlgebraicGeometry.basePairTriv`); there it
has a torsor of trivializations under `μ_n`
(`AlgebraicGeometry.trivializationTorsor`), and isomorphism classes of torsors are `H¹` by
Tag 03AJ (`Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1`).  That the composite does not see
the choice of pair inside its isomorphism class is
`AlgebraicGeometry.basePairClass_eq_of_pairIso`, so it descends to
`AlgebraicGeometry.PairClasses`.

## Main definitions

* `AlgebraicGeometry.basePairCohomologyClass`: **the comparison map
  `PairClasses S n → H¹((Sch/S)_τ, μ_n)` of Tag 040Q**, and
  `basePairCohomologyClass_pairClass`, its value on the class of a pair.

## What is not done here

**The map is not shown to be additive here.**  It is:
`AlgebraicGeometry.basePairCohomologyClassHom`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairComparisonHom`, is this map as a
homomorphism of abelian groups, the addition of the source being the tensor product of pairs
(`AlgebraicGeometry.instAddCommGroupPairClasses`) and that of the target the addition of `Ext¹`.

Injectivity and surjectivity are open for a nontrivial invertible sheaf; for the trivial one they
are
`AlgebraicGeometry.pairIso_iff_kummerBoundary_eq` and
`AlgebraicGeometry.forall_exists_kummerBoundary_iff`.  `Stacks.Kummer.bijective_of_comparison`
would deduce them from the comparison homomorphism together with two compatibilities that are not
proved anywhere yet: that the composite of the comparison with `H¹(μ_n) → H¹(𝒪^*) ≅ Pic(S)` is
`AlgebraicGeometry.pairSheafClassHom`, and that the comparison carries the class of a unit pair to
`AlgebraicGeometry.kummerBoundary`.  No `@[stacks 040Q]` attribute is added here: this is one of
the tag's constituents, not the tag.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.Torsors (torsorSetoid torsorIsoClassesEquivH1)

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind) (n : ℕ)

-- The two sheafification retypings that `AlgebraicGeometry.trivializationTorsor` needs at the
-- `(schemeFunctionsRingedSite _ _ _).J` spelling are declared `local` in
-- `StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/PairTransportIso.lean`, so they
-- are not in scope here; they are re-enabled rather than restated.
attribute [local instance] baseSchemeFunctions_hasWeakSheafify
  baseSchemeFunctions_wEqualsLocallyBijective

variable [HasSheafify (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{u})]

/-- **The comparison map of Tag 040Q on the big `τ`-site of `S`.**  The isomorphism class of a
pair `(ℒ, α)` on `S` is carried to the class in `H¹((Sch/S)_τ, μ_n)` of the torsor of
trivializations of the transported pair `(ℒ^a, α^a)`.

It is well defined on isomorphism classes by `AlgebraicGeometry.basePairClass_eq_of_pairIso`, and
the passage from torsor classes to `H¹` is Tag 03AJ.  The hypothesis that units have local
`n`-th roots is an argument, as it is there; it is discharged unconditionally by
`AlgebraicGeometry.localRoots_baseRingedSite_fppf` and its companions.

This map is **not** known to be additive; see the head of this file. -/
public def basePairCohomologyClass
    (hroot : Stacks.Cohomology.Torsors.Generators.LocalRoots
      (BigFppfOver.baseRingedSite B S hS τ) n) :
    PairClasses S n →
      Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n) 1 :=
  Quotient.lift
    (fun P : TrivializedPower S n =>
      torsorIsoClassesEquivH1 _ (Quotient.mk
        (torsorSetoid (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n))
        (trivializationTorsor (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
          (unitsPresheaf_isSheaf_base B S hS τ) n
          (baseRingedSite_isLocallyRinged B S hS τ) hroot (basePairSheaf B S hS τ n P)
          (basePairSheaf_isInvertible B S hS τ n P) (basePairTriv B S hS τ n P))))
    fun _ _ h =>
      congrArg (torsorIsoClassesEquivH1 _)
        (basePairClass_eq_of_pairIso B S hS τ n hroot _ _ h.some)

/-- The comparison map of Tag 040Q on the class of a pair is the `H¹`-class of the torsor of
trivializations of the transported pair. -/
public theorem basePairCohomologyClass_pairClass
    (hroot : Stacks.Cohomology.Torsors.Generators.LocalRoots
      (BigFppfOver.baseRingedSite B S hS τ) n) (P : TrivializedPower S n) :
    basePairCohomologyClass B S hS τ n hroot (pairClass P) =
      torsorIsoClassesEquivH1 _ (Quotient.mk
        (torsorSetoid (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n))
        (trivializationTorsor (BigFppfOver.baseOverTopology B S hS τ)
          (BigFppfOver.toScheme B S hS) (BigFppfOver.baseRingedSite B S hS τ).O.property
          (unitsPresheaf_isSheaf_base B S hS τ) n
          (baseRingedSite_isLocallyRinged B S hS τ) hroot (basePairSheaf B S hS τ n P)
          (basePairSheaf_isInvertible B S hS τ n P) (basePairTriv B S hS τ n P))) :=
  rfl

end AlgebraicGeometry

end
