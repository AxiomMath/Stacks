module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DegreewiseComparison

/-!
# Invertibility of the degreewise comparison in every degree at once

For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

and a quasi-coherent `𝒪_{S'}`-module `G` flat over `S`, [Stacks, Tag 0GN5] asserts that the
degreewise comparison

`cᵢ : Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

of `DegreewiseComparison.lean` is invertible for every `i`. This file records that the whole
family is invertible as soon as the single derived comparison

`RΦ(Rf_* F[0]) ⟶ Rf'_*(RΨ F[0])`

is invertible in the bounded below derived category: the degreewise comparison is, in every
degree, the degree-`i` cohomology of that one morphism read through two isomorphisms, so a
functor carries invertibility to all of them simultaneously. The quantifier over degrees is
therefore not part of what has to be proved.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_isIso`: **every
  degree at once.** If the derived comparison is invertible at `F[0]` then the degreewise
  comparison is invertible at `F` in every degree.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **Invertibility of the degreewise comparison of [Stacks, Tag 0GN5] in every degree, from the
single derived comparison.** The degreewise comparison in degree `i` is the degree-`i` cohomology
of the derived comparison, read through the two isomorphisms `comparisonSourceIso` and
`comparisonTargetIso`; so invertibility of the derived comparison at `F[0]` gives invertibility
of the degreewise comparison at `F` in every degree. -/
theorem isIso_degreewiseComparison_app_of_isIso (H : IsPullback g' f' f g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (h : IsIso ((derivedComparison G H.w hG).app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)))
    (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) := by
  rw [isIso_degreewiseComparison_app_iff H G hG i F]
  have := h
  infer_instance

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
