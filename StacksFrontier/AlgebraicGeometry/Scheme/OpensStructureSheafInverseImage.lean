module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Modules.Differentials

/-!
# The inverse image of the structure sheaf along the inclusion of an open subscheme

Let `X` be a scheme and `V ⊆ X` an open.  The open subscheme `V` carries its own structure
sheaf `𝒪_V`, obtained by restricting `𝒪_X`, while the inclusion `ι : V ⟶ X` has an inverse
image functor `ι^{-1}` on sheaves of commutative rings.  This file identifies the two:
`ι^{-1}𝒪_X ≅ 𝒪_V`.

The identification is what makes a sheaf on `X` restricted to `V` expressible as a sheaf *on
`V`*: statements produced by the general inverse-image machinery, such as
`Stacks.SheafOfModules.naiveCotangentComplexInverseImageIso`, speak of modules over
`ι^{-1}𝒪_X`, whereas a complex on the open subscheme is a complex of modules over `𝒪_V`.

## Main definitions

* `Stacks.OpensStructureSheaf.inverseImageIso`: the isomorphism `ι^{-1}𝒪_X ≅ 𝒪_V` of sheaves of
  commutative rings on `V`.
* `Stacks.OpensStructureSheaf.underlyingRingSheafIso`: the same isomorphism between the
  underlying sheaves of (not necessarily commutative) rings, which is the spelling over which
  sheaves of modules are taken.

## Main results

* `Stacks.OpensStructureSheaf.sheafPullback_obj_eq`: the *naive* inverse image along `ι` — the
  restriction `U ↦ 𝒪_X(ι(U))`, Mathlib's `Topology.IsOpenEmbedding.sheafPullback` — **is** the
  structure sheaf of the open subscheme, on the nose.  No transport is involved: both sides
  are `ι`'s image functor composed with `𝒪_X`, together with the sheaf condition.
* `Stacks.OpensStructureSheaf.nonempty_inverseImageIso`: the existence form of
  `inverseImageIso`.

## Implementation notes

All the mathematics is Mathlib's: `Topology.IsOpenEmbedding.sheafPullbackIso` identifies the
inverse image along an open embedding — defined as the sheafification of a left Kan extension —
with the naive restriction, and `Stacks.OpensStructureSheaf.sheafPullback_obj_eq` observes that
the naive restriction at `ι` is literally `AlgebraicGeometry.Scheme.Opens.toScheme`'s structure
sheaf, because `AlgebraicGeometry.Scheme.Opens.toScheme` is
`AlgebraicGeometry.Scheme.restrict` and the presheaf of a restricted presheafed space is by
definition the composite with the image functor on opens.

## References

* [Stacks Project, Tag 00A0](https://stacks.math.columbia.edu/tag/00A0), the inverse image of a
  sheaf along an open immersion.
* [Stacks Project, Tag 01I0](https://stacks.math.columbia.edu/tag/01I0), open subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

namespace Stacks.OpensStructureSheaf

variable (X : Scheme.{u}) (V : X.Opens)

/-- **The naive inverse image of `𝒪_X` along the inclusion of an open is `𝒪_V`.**  Mathlib's
`Topology.IsOpenEmbedding.sheafPullback`, the restriction `U ↦ 𝒪_X(ι(U))`, applied to the
structure sheaf of `X` is the structure sheaf of the open subscheme `V`, with no identification
in between: both are the image functor of `ι` on opens, composed with `𝒪_X`, bundled with the
sheaf condition. -/
theorem sheafPullback_obj_eq :
    (Topology.IsOpenEmbedding.sheafPullback CommRingCat.{u} V.ι.isOpenEmbedding).obj X.sheaf =
      V.toScheme.sheaf :=
  rfl

/-- **The inverse image of the structure sheaf along an open immersion: `ι^{-1}𝒪_X ≅ 𝒪_V`.**
For `V` an open of a scheme `X` and `ι : V ⟶ X` the inclusion, the inverse image of the
structure sheaf of `X` along `ι` is the structure sheaf of the open subscheme `V`. -/
def inverseImageIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} V.ι.base).obj X.sheaf ≅ V.toScheme.sheaf :=
  (Topology.IsOpenEmbedding.sheafPullbackIso CommRingCat.{u} V.ι.isOpenEmbedding).app X.sheaf

/-- The existence form of `Stacks.OpensStructureSheaf.inverseImageIso`. -/
theorem nonempty_inverseImageIso :
    Nonempty ((TopCat.Sheaf.pullback CommRingCat.{u} V.ι.base).obj X.sheaf ≅
      V.toScheme.sheaf) :=
  ⟨inverseImageIso X V⟩

/-- **`ι^{-1}𝒪_X ≅ 𝒪_V` between the underlying sheaves of rings.**  Sheaves of modules are
taken over a sheaf of not necessarily commutative rings, so this is the spelling of
`Stacks.OpensStructureSheaf.inverseImageIso` that transports modules. -/
def underlyingRingSheafIso :
    AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} V.ι.base).obj X.sheaf) ≅
      AlgebraicGeometry.SheafOfModules.underlyingRingSheaf V.toScheme.sheaf :=
  (CategoryTheory.sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    (inverseImageIso X V)

end Stacks.OpensStructureSheaf

end

end
