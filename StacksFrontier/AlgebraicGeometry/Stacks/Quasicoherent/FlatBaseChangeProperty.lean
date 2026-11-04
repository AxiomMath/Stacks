module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparison

/-!
# The flat base change property (Stacks 0762)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of Stacks 06TV. An object `x` of `𝒳` lying over a scheme `U`
gives the restriction `F|_{U_ét}` to the small étale site of `U`, the restriction of Stacks 06W1
on underlying abelian presheaves and of Stacks 06WJ as a module. An arrow `φ : x ⟶ y` of `𝒳`
lying over a morphism of schemes `f : U ⟶ V` gives the comparison map
`c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761**, which the source introduces as
Equation (96.9.4.1) of Sheaves on Stacks, that is Stacks 06WC.

**Stacks 0762** says that `F` *has the flat base change property* if and only if `c_φ` is an
isomorphism whenever `f` is flat.

## Main definitions

* `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`: **Stacks 0762**, the flat base change
  property.

## Implementation notes

Stacks 0761 is the comparison map itself, and the source gives it by pointing at Equation
(96.9.4.1) of Sheaves on Stacks: it is that same map, already available as
`AlgebraicGeometry.Stack.restrictModulePullbackComparison`, so the tag is recorded on that
declaration instead of being realized by a second copy.

The source states the definition for a sheaf of `𝒪_𝒳`-modules on `𝒳_étale`. The property speaks
only about the comparison maps, so it is stated here for a presheaf of modules over the
structure sheaf for an arbitrary topology `τ` coarser than the fppf one, as elsewhere in this
area; a sheaf condition is not part of it. Stacks 0765, for instance, asks for the property
together with local quasi-coherence (Stacks 06WJ), and it is the latter that carries the sheaf
condition.

Flatness of `f` is flatness of the morphism of schemes `B.inclusion.map (p.map φ).left`
underlying `φ`, the reading also used by
`AlgebraicGeometry.Stack.IsClosedUnderSitePullback`.

## References

* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

add_to_stacks 0761 "the comparison map `c_φ`" restrictModulePullbackComparison

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0762.** A presheaf of modules over the structure sheaf of a category fibred in
groupoids *has the flat base change property* when the comparison map `c_φ` of Stacks 0761 is an
isomorphism for every arrow `φ` of `𝒳` lying over a flat morphism of schemes.

The source calls the name nonstandard. -/
@[stacks 0762]
noncomputable abbrev HasFlatBaseChangeProperty {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)

end AlgebraicGeometry.Stack

end
