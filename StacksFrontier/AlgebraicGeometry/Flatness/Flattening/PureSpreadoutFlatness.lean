module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutQuotient
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria

/-!
# A pure spreadout forces flatness over the base

In the finitely presented localized-module situation of Stacks 0AT6, the distinguished module
`N` is a localization of the spreadout module `N'` at a multiplicative subset of `B`, and `N'`
is projective over the base ring `A`.  Projective modules are flat and flatness over a base
ring is preserved by localizing at a multiplicative subset of the top ring, so `N` is flat over
`A`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.PureSpreadout.flat`: a pure spreadout makes `N` flat over `A`.
* `AlgebraicGeometry.flat_of_nonempty_pureSpreadout`: the same conclusion from mere existence.

## Implementation notes

The scalar tower `A → B → N'` is not a field of `PureSpreadout`, which records instead the two
towers through the coordinate ring `C`; it is recovered from the compatibility of the two
algebra maps out of `A`.

The conclusion is independent of the test-module universe of the universal injectivity packaged
in a pure spreadout, so that universe is left free.

## References

* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
* [Stacks Project, Tag 0AT7](https://stacks.math.columbia.edu/tag/0AT7)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

namespace PureSpreadout

/-- A pure spreadout of the distinguished module makes that module flat over the base ring:
it is a localization of an `A`-projective module at a multiplicative subset of `B`. -/
theorem flat {X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄}}
    (P : PureSpreadout.{u₁, u₂, u₃, u₄, u₅} X) : Module.Flat X.A X.N := by
  let : CommRing P.C := P.commRingC
  let : Algebra X.B P.C := P.algebraBC
  let : Algebra X.A P.C := P.algebraAC
  let : IsScalarTower X.A X.B P.C := P.isScalarTowerABC
  let : AddCommGroup P.N' := P.addCommGroupN'
  let : Module P.C P.N' := P.moduleCN'
  let : Module X.B P.N' := P.moduleBN'
  let : Module X.A P.N' := P.moduleAN'
  let : IsScalarTower X.B P.C P.N' := P.isScalarTowerBCN'
  let : IsScalarTower X.A P.C P.N' := P.isScalarTowerACN'
  let : IsScalarTower X.A X.B P.N' := IsScalarTower.of_algebraMap_smul fun a x => by
    rw [← IsScalarTower.algebraMap_smul P.C (algebraMap X.A X.B a) x,
      ← IsScalarTower.algebraMap_smul P.C a x]
    exact congrArg (fun c : P.C => c • x)
      (congrArg (fun f : X.A →+* P.C => f a)
        (IsScalarTower.algebraMap_eq X.A X.B P.C).symm)
  let : Module P.C X.N := P.moduleCN
  let : IsScalarTower X.B P.C X.N := P.isScalarTowerBCN
  let : Module.Projective X.A P.N' := P.projective
  have : Module.Flat X.A P.N' := Module.Flat.of_projective
  have := P.isLocalizedModule
  exact Module.Flat.of_isLocalizedModule_of_tower X.S (P.localizationMap.restrictScalars X.B)

end PureSpreadout

/-- Existence of a pure spreadout makes the distinguished module flat over the base ring. -/
theorem flat_of_nonempty_pureSpreadout
    {X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄}}
    (h : Nonempty (PureSpreadout.{u₁, u₂, u₃, u₄, u₅} X)) : Module.Flat X.A X.N :=
  h.elim PureSpreadout.flat

/-- What Stacks 0AT8 delivers, read through `flat_of_nonempty_pureSpreadout`: for each prime of
the base ring there is a finitely generated ideal of the local ring at that prime, contained in
the extension of the prime, over whose quotient the base-changed module is flat.

The flatness is over the new base ring, not over `A`: the pure spreadout produced by Stacks 0AT8
lives on the base change, so the flatness it forces is flatness of the base-changed module over
the local quotient. -/
theorem FinitelyPresentedLocalizedModuleSituation.exists_fg_ideal_flat_localQuotientBaseChange
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime] :
    ∃ I : Ideal (Localization.AtPrime p), I.FG ∧
      I ≤ p.map (algebraMap X.A (Localization.AtPrime p)) ∧
      ∃ Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂, max u₁ u₃,
          max u₁ (max u₃ u₄)},
        Nonempty (LocalQuotientBaseChange X Y p I) ∧ Module.Flat Y.A Y.N := by
  obtain ⟨I, hfg, hle, Y, hbc, hps⟩ :=
    X.exists_fg_ideal_localQuotientBaseChange_pureSpreadout.{_, _, _, _, 0} p
  exact ⟨I, hfg, hle, Y, hbc, flat_of_nonempty_pureSpreadout hps⟩

end AlgebraicGeometry

end
