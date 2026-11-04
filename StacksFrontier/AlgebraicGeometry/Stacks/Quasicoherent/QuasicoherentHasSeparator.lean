module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentBoundedSmall
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness

/-!
# `QCoh(𝒪_𝒳)` has a separator

For an essentially small category fibred in groupoids `𝒳` over the big fppf site of `S` — in
particular for an algebraic stack — the category `QCoh(𝒪_𝒳)` of quasi-coherent modules on its
fppf site has a separator.  This is the input of the special adjoint functor theorem which the
coherator of **Stacks 0778** and **Stacks 0781** part (2) needs, and which the source draws from
the Grothendieck property, **Stacks 0781** part (1).

It is the assembly of
`AlgebraicGeometry.FibredSite.hasSeparator_quasicoherentModules_of_essentiallySmall` (the bounded
quasi-coherent modules separate) with
`AlgebraicGeometry.FibredSite.essentiallySmall_isAffineBounded` (they form an essentially small
class).

## Main results

* `AlgebraicGeometry.FibredSite.hasSeparator_quasicoherentModules`: the separator, for an
  essentially small category fibred in groupoids.
* `AlgebraicGeometry.Stack.hasSeparator_quasicoherentModules`: the same for an algebraic stack.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **`QCoh(𝒪_𝒳)` has a separator**, for an essentially small category fibred in groupoids `𝒳`
over the big fppf site of `S`: the bounded quasi-coherent modules are separating and form an
essentially small class. -/
theorem hasSeparator_quasicoherentModules :
    HasSeparator (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  hasSeparator_quasicoherentModules_of_essentiallySmall B S hS p hp
    (essentiallySmall_isAffineBounded B S hS p hp)

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`QCoh(𝒪_𝒳)` has a separator for an algebraic stack `𝒳`**, at module universe `u`.  The fppf
site of an algebraic stack is essentially small
(`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`), so this is
`AlgebraicGeometry.FibredSite.hasSeparator_quasicoherentModules`. -/
theorem hasSeparator_quasicoherentModules (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :=
  FibredSite.hasSeparator_quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

end AlgebraicGeometry.Stack

end
