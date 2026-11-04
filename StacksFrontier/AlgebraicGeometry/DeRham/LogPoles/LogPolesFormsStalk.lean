module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsSheaf
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion

/-!
# The stalk of the sheaf of forms with a logarithmic pole along a divisor

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor, with
ideal sheaf `ℐ`. The sheaf `Ω^p_{X/S}(log Y) = SheafHom_{𝒪_X}(ℐ, 𝒦^p)` of
`AlgebraicGeometry.Scheme.Hom.logPolesForms` is an internal hom, so [Stacks, Tag 01CP] computes
its stalk as soon as the source is of finite presentation. This file supplies both halves and
reads off the stalk.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logPolesFormsSheafHom`: `Ω^p_{X/S}(log Y)` packaged as a
  `SheafHom` of [Stacks, Tag 01CO], which is the datum Tag 01CP consumes.
* `AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkEquiv`: **the stalk at `y` of
  `Ω^p_{X/S}(log Y)` is the module of `𝒪_{X,y}`-linear maps `ℐ_y ⟶ 𝒦^p_y`.**

## Main results

* `Stacks.Divisors.isFinitePresentation_negativeTwist`: the ideal sheaf of an effective Cartier
  divisor is of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.logPolesFormsSheafHom_obj`: the packaging is of `logPolesForms`
  on the nose.

## Implementation notes

**Where the finite presentation comes from.** An invertible sheaf of modules is of finite
presentation at the generality of an arbitrary site, by
`Stacks.SheafOfModules.isFinitePresentation_of_isInvertible`, which is the step of
[Stacks, Tag 0B8M]'s converse that the source attributes to [Stacks, Tag 0B8K]. The ideal sheaf
of an effective Cartier divisor is invertible by
`Stacks.Divisors.stacksIsInvertible_negativeTwist`, so nothing has to be proved here; the only
work is that the two are stated at different spellings of the structure sheaf of rings, and
Tag 01CP asks for the predicate at `structureSheaf X.sheaf` while the
invertibility is delivered at `structureSheafRing X.toRingedSpace`. The instance below states
the predicate at the first and is proved by the second; the two sheaves of rings are equal, but
instance search is syntactic, so the crossing is made once.

Effective Cartierness is the only hypothesis, and it is one of [Stacks, Tag 0FMW]'s own: the
source states that tag for an effective Cartier divisor. The definitions of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsSheaf` deliberately ask for no such
condition, so the binder appears here for the first time.

**Why the `SheafHom` datum is the general one.** The datum
`Stacks.AlgebraicGeometry.ReflexiveModules.sheafHomOfModules` is `SheafHom(F, G)` packaged in
the Tag 01CO shape for an arbitrary target; `logPolesFormsSheafHom`
is that at `F = ℐ` and `G = 𝒦^p`, and `logPolesFormsSheafHom_obj` records by `rfl` that its
underlying module is `logPolesForms`. The datum is not built again here, and in particular not
from `Stacks.SheafOfModules.internalHomSheafHom`, whose underlying module is
`AlgebraicGeometry.RingedSite.internalHomSheaf` — a different constant, as the note on that
declaration records.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (I : X.IdealSheafData) [IsEffectiveCartierDivisor I]

/-- **The ideal sheaf of an effective Cartier divisor is of finite presentation.** It is
invertible, and an invertible sheaf of modules is of finite presentation. Stated at the spelling
of the structure sheaf of rings that [Stacks, Tag 01CP] asks for. -/
instance isFinitePresentation_negativeTwist :
    SheafOfModules.IsFinitePresentation
      (R := structureSheaf X.sheaf) (negativeTwist I) :=
  Stacks.SheafOfModules.isFinitePresentation_of_isInvertible
    (structureSheafRing X.toRingedSpace).property (negativeTwist I)
    (stacksIsInvertible_negativeTwist I)

end Stacks.Divisors

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (p : ℕ)

/-- `Ω^p_{X/S}(log Y) = SheafHom_{𝒪_X}(ℐ, 𝒦^p)` packaged as a `SheafHom` of
[Stacks, Tag 01CO], the datum the stalk comparison of [Stacks, Tag 01CP] consumes. -/
abbrev logPolesFormsSheafHom :
    SheafHom X.sheaf (Stacks.Divisors.negativeTwist I) (formRestrictionKernelSheaf f I p) :=
  sheafHomOfModules (Stacks.Divisors.negativeTwist I) (formRestrictionKernelSheaf f I p)

/-- The module underlying the packaging is `Ω^p_{X/S}(log Y)` on the nose. -/
theorem logPolesFormsSheafHom_obj :
    (logPolesFormsSheafHom f I p).obj = logPolesForms f I p :=
  rfl

/-- **The stalk at `y` of the sheaf `Ω^p_{X/S}(log Y)` of relative `p`-forms with a logarithmic
pole along the divisor is `Hom_{𝒪_{X,y}}(ℐ_y, 𝒦^p_y)`**, the module of `𝒪_{X,y}`-linear maps
from the stalk of the ideal sheaf to the stalk of the sheaf of `p`-forms vanishing on the
divisor.

This is [Stacks, Tag 01CP] at `Ω^p_{X/S}(log Y)`, available because the ideal sheaf of an
effective Cartier divisor is of finite presentation. The `germ_apply` field of the result records
that the identification sends the germ of a local homomorphism, evaluated at the germ of a local
section of `ℐ`, to the germ of the value; by
`Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearMap_unique` that property determines
it. -/
def logPolesFormsStalkEquiv [Stacks.Divisors.IsEffectiveCartierDivisor I] (x : X) :
    SheafHomStalkLinearEquiv X.sheaf (Stacks.Divisors.negativeTwist I)
      (formRestrictionKernelSheaf f I p) (logPolesFormsSheafHom f I p) x :=
  sheafHomStalkLinearEquivOfFinitePresentation (logPolesFormsSheafHom f I p) x

end AlgebraicGeometry.Scheme.Hom

end
