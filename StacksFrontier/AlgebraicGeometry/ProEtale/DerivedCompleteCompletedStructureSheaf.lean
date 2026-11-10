module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimit

/-!
# The completion of the structure sheaf is derived complete

On a site every object of which has a covering by weakly contractible objects, the inverse limit
`𝒪^∧ = limₙ 𝒪/ℐⁿ` of the adic quotients of the structure sheaf along a sheaf of ideals is
derived complete along that sheaf of ideals.

Each term `𝒪/ℐⁿ` of the tower is derived complete because the `n`-th power of a local section
of `ℐ` kills it, so multiplication by that section is a nilpotent scalar on every restriction to
a slice; and an inverse limit of derived-complete sheaves is derived complete.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_limit_adicQuotientTower`: derived completeness
  of `limₙ 𝒪/ℐⁿ`.

## Implementation notes

As for the other parts of [Stacks, Tag 099Q] available in this library, the result is stated for
an arbitrary ringed site and an arbitrary sheaf of ideals. The source's `Λ^∧` is `limₙ Λ/Iⁿ` for
the constant sheaf `Λ̲` of a Noetherian coefficient ring and the ideal sheaf of `I ⊂ Λ`; the
structure sheaf of the ringed site plays the role of `Λ̲`, so `limₙ 𝒪/ℐⁿ` is `Λ^∧` in that
situation. Neither Noetherianity nor constancy of the coefficients enters: the tower of adic
quotients is derived complete for every sheaf of ideals, and the inverse-limit argument needs
only the weakly contractible objects, which are the source's hypothesis on `𝒞`.

Reading the object below *literally* as the source's `Λ^∧ = limₙ (Λ/Iⁿ)̲` on the constant
ringed site means identifying each term `𝒪/ℐⁿ` of the tower with the constant sheaf of
`Λ/Iⁿ`. That identification is [Stacks, Tag 093M], which this library has at a single power as
`Stacks.ConstantSheaf.constantSheaf_quotientByIdealAction`; carrying it to every power, and to
the sheaf-theoretic power `ℐⁿ` of the constant ideal sheaf, is not done here, and neither is
the construction of the constant ringed site at these universes — the library's
`AlgebraicGeometry.RingedSite.constantRingedSite` is built only at `RingedSite.{0, 0, 0}`.

The tower is `AlgebraicGeometry.RingedSite.adicQuotientTower`, which is indexed so that its
`n`-th term is `𝒪/ℐⁿ⁺¹`; that is the source's `limₙ Λ/Iⁿ` over `n ≥ 1`, and the term at `n = 0`
it omits is zero in any case, `Stacks.Sites.isZero_adicQuotientModule_zero`.

The three site universes are equal here, while the other parts of the tag allow the objects and
the morphisms of `𝒞` to live in independent universes. The restriction comes from the input
`AlgebraicGeometry.RingedSite.isDerivedComplete_adicQuotientObj`, which is available only at
`RingedSite.{u, u, u}`; nothing in the argument below depends on it. In particular this does not
reach the small pro-étale site of a scheme, which is a `RingedSite.{u + 1, u, _}`, so the
completed constant sheaf `AlgebraicGeometry.ProEtale.completedConstantSheaf` of [Stacks,
Tag 09BT] is not covered by this statement.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSite

/-- **The completion `limₙ 𝒪/ℐⁿ` of the structure sheaf is derived complete along `ℐ`.** Every
term of the tower of adic quotients is derived complete, and an inverse limit of derived-complete
sheaves of modules is derived complete. -/
@[stacks 099Q "completed_structure_sheaf"]
theorem isDerivedComplete_limit_adicQuotientTower
    (X : RingedSite.{u, u, u}) [Small.{u} X.C] [HasSheafify X.J (Type u)]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (limit (adicQuotientTower X I))) :=
  isDerivedComplete_limit X hX I (adicQuotientTower X I) fun n =>
    isDerivedComplete_adicQuotientObj X I (n + 1)

end AlgebraicGeometry.RingedSite

end
