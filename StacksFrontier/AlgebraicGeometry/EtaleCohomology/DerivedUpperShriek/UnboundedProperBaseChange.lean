module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.UnboundedBaseChangeCompactifications
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChangeUnbounded
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeUnbounded
import StacksCore.Tactic.StacksAttribute

/-!
# Derived upper shriek commutes with derived direct image along a cartesian square

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of quasi-compact and quasi-separated schemes with `f` separated and of
finite type, and let `Λ` be a torsion ring. Then `Rf^! ∘ Rg_* = Rg'_* ∘ R(f')^!` as functors
`D(Y'_étale, Λ) ⥤ D(X_étale, Λ)`: this is [Stacks, Tag 0GLE].

Here `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` is the derived lower shriek
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` of a compactification `j` of `f`, and `Rf^!`
is its right adjoint, which exists by [Stacks, Tag 0G2C]
(`Stacks.EtaleCohomology.DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded`); likewise
`R(f')^!` for a compactification `j'` of `f'`. The compactifications are arbitrary, and the
functors they give are canonically independent of them by [Stacks, Tag 0F7I].

The proof is the source's: by uniqueness of adjoints the statement follows from base change for
derived lower shriek, `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` ([Stacks, Tag 0F7L]). That isomorphism
is `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso`, the base change map for `j`
and its base change, invertible by the unbounded proper base change theorem ([Stacks, Tag 0F0C]),
and it is carried to `j'` along [Stacks, Tag 0F7I] by
`Stacks.EtaleCohomology.derivedUpperShriekUnboundedBaseChangeIsoOfCompactifications`.

## Main results

* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedBaseChange`: **[Stacks, Tag 0GLE]**.

## Implementation notes

A torsion ring is a commutative ring `Λ` with `n = 0` in `Λ` for some integer `n ≥ 1`; it lives
in `Type`, the universe of the coefficient rings of the derived lower shriek functors of
[Stacks, Tags 0G2C and 0F7I] in this development. The schemes `X` and `X'` are quasi-compact and
quasi-separated because `f` and `f'` are, so only `Y` and `Y'` carry these hypotheses.

## References

* [Stacks Project, Tag 0GLE](https://stacks.math.columbia.edu/tag/0GLE)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g)
  (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
  (j : CompactificationOf (Over.mk f))

variable [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j' : CompactificationOf (Over.mk f'))

/-- **Stacks Project, Tag 0GLE.** Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of quasi-compact and quasi-separated schemes with `f` separated and of finite type, and let `Λ`
be a torsion ring (`n = 0` in `Λ` for some `n ≥ 1`). Let `Rf^!` and `R(f')^!` be the right
adjoints ([Stacks, Tag 0G2C]) of the derived lower shrieks `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)`
and `Rf'_! : D(X'_étale, Λ) ⥤ D(Y'_étale, Λ)` of arbitrary compactifications `j` of `f` and `j'`
of `f'`. Then `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!` as functors `D(Y'_étale, Λ) ⥤ D(X_étale, Λ)`. -/
@[stacks 0GLE]
def derivedUpperShriekUnboundedBaseChange :
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f' j'
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ g ⋙
        (derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint ≅
      (derivedLowerShriekUnbounded.{u, 0} f' j' Λ).rightAdjoint ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ g' :=
  derivedUpperShriekUnboundedBaseChangeIsoOfCompactifications sq Λ n hn hΛ j j'
    (derivedLowerShriekUnboundedBaseChangeIso Λ ⟨n, hn, hΛ⟩ sq j)

end Stacks.EtaleCohomology

end
