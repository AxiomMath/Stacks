module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf

/-!
# The localization equivalence preserves the structure sheaf (Stacks 06W9)

Let `p : 𝒳 ⥤ BigFppfOver B S hS` be a category fibred in groupoids and let `x` be an object of
`𝒳` lying over a scheme `U`. Stacks 06W0 gives a canonical equivalence `CategoryTheory.Over.post`
from the slice `Over x` to the schemes over `U`, identifying the localized associated topology
with the localized base topology. This file records that the equivalence also matches the two
structure sheaves: restricting the structure sheaf of `𝒳` to the slice at `x` gives the same
ring-valued presheaf as pulling the structure sheaf of the schemes over `U` back along the
equivalence. Together with Stacks 06W0 that makes it an equivalence of *ringed* sites
`(𝒳_τ/x, 𝒪_𝒳|_x) ≌ ((Sch/U)_τ, 𝒪)`, which is what lets a module on `𝒳` be tested one object at
a time, and the packaged form is here too.

The equality is an equality of functors, so it holds for the restriction maps and not only
objectwise; both sides are the sections functor `Scheme.Γ` precomposed with the same forgetful
functor to schemes, so it is definitional.

## Main definitions

* `AlgebraicGeometry.Stack.localizationEquivalence`: **Stacks 06W0** as an equivalence of
  categories `𝒳/x ≌ (Sch/U)`.

## Main results

* `AlgebraicGeometry.Stack.ringStructureSheafCore_overPost`: **Stacks 06W9**, the two structure
  presheaves agree.
* `AlgebraicGeometry.Stack.isDenseSubsite_localizationEquivalence` and
  `AlgebraicGeometry.Stack.isDenseSubsite_localizationEquivalence_inverse`: **Stacks 06W0** as an
  equivalence of sites, in both directions.
* `AlgebraicGeometry.Stack.sheafPushforwardContinuous_baseStructureSheaf` and
  `AlgebraicGeometry.Stack.sheafPushforwardContinuous_baseRingStructureSheaf`: **Stacks 06W9**,
  the equivalence of *ringed* sites — the direct image of the base structure sheaf along the
  localization equivalence is the restricted structure sheaf of `𝒳`, for the commutative
  structure sheaf and for its underlying sheaf of rings.

## Implementation notes

As elsewhere in this area the topology is a general `τ : GrothendieckTopology B.Schemes` with
`hτ : τ ≤ B.topology` rather than one of the five named topologies; see the "Generality of `τ`"
section of `StacksFrontier/AlgebraicGeometry/Stacks/StructureSheaf.lean`. Each named topology is an
instance of this, so the statement here is more general than the source's five cases.

The ringed-site packaging is an assembly of parts and proves nothing new: the equivalence of
categories and the identification of topologies are Stacks 06W0, and both structure-sheaf
equalities are `rfl` for the same reason that `ringStructureSheafCore_overPost` is. A morphism
of ringed sites in the sense of `AlgebraicGeometry.RingedSite.Hom` is not available here: that
structure asks for `AlgebraicGeometry.RingedSite.{u, u, w}`, with the objects and the morphisms
of the site in one universe, whereas `BigFppfOver B U hU` has `Type (u + 1)` objects and `Type u`
morphisms. The identification is therefore carried in the form the rest of the library uses for
an equivalence of ringed sites, a direct image of the structure sheaf equal to the restricted
one — the shape `Stacks.SheafOfModules.reindexRing` abbreviates and that
`Stacks.SheafOfModules.reindexEquivalence` consumes.

## References

* [Stacks Project, Tag 06W9](https://stacks.math.columbia.edu/tag/06W9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

/-- **Stacks 06W9.** The canonical localization equivalence of Stacks 06W0 carries the structure
sheaf of the schemes over `(p.obj x).left` to the restriction of the structure sheaf of `𝒳` to
the slice at `x`, including all restriction maps. -/
@[stacks 06W9]
theorem ringStructureSheafCore_overPost
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (x : 𝒳) :
    (Over.forget x).op ⋙ (ringStructureSheafCore B S hS p hp τ hτ).obj =
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙
        (baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 τ hτ).obj :=
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Stacks 06W0** as an equivalence of categories `𝒳/x ≌ (Sch/U)`, `U = p(x)`: the canonical
functor `CategoryTheory.Over.post` of `AlgebraicGeometry.Stack.isEquivalence_overPost`, with the
chosen inverse its `CategoryTheory.Functor.asEquivalence` supplies. -/
noncomputable def localizationEquivalence (x : 𝒳) :
    Over x ≌ BigFppfOver B (p.obj x).left.1 (p.obj x).left.2 :=
  letI := isEquivalence_overPost B S hS p hp x
  (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence

/-- The functor of `AlgebraicGeometry.Stack.localizationEquivalence` is `CategoryTheory.Over.post`
of the composite `p ⋙ Over.forget (B.obj hS)`. -/
@[simp]
theorem localizationEquivalence_functor (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).functor =
      Over.post (X := x) (p ⋙ Over.forget (B.obj hS)) :=
  rfl

/-- **Stacks 06W0 as an equivalence of sites.** The canonical localization functor is a dense
subsite inclusion from the localized associated topology to the localized base topology: it is
an equivalence of categories, hence cover dense, and the topology it induces from the localized
base topology is the localized associated topology, which is
`AlgebraicGeometry.Stack.inducedTopology_overPost`. -/
instance isDenseSubsite_localizationEquivalence
    (τ : GrothendieckTopology B.Schemes) (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).functor.IsDenseSubsite
      ((associatedTopology B S hS p τ).over x) (τ.over (B.obj (p.obj x).left.2)) := by
  let := isEquivalence_overPost B S hS p hp x
  have h : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsDenseSubsite
      ((associatedTopology B S hS p τ).over x) (τ.over (p.obj x).left) := by
    rw [← inducedTopology_overPost B S hS p hp τ x]
    infer_instance
  exact h

/-- The inverse of the localization equivalence is a dense subsite inclusion the other way, so
the correspondence of coverings holds in both directions. -/
instance isDenseSubsite_localizationEquivalence_inverse
    (τ : GrothendieckTopology B.Schemes) (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).inverse.IsDenseSubsite
      (τ.over (B.obj (p.obj x).left.2)) ((associatedTopology B S hS p τ).over x) :=
  letI : (localizationEquivalence B S hS p hp x).symm.inverse.IsDenseSubsite
      ((associatedTopology B S hS p τ).over x) (τ.over (B.obj (p.obj x).left.2)) :=
    isDenseSubsite_localizationEquivalence B S hS p hp τ x
  inferInstanceAs ((localizationEquivalence B S hS p hp x).symm.functor.IsDenseSubsite _ _)

/-- **Stacks 06W9.** The equivalence of Stacks 06W0 is an equivalence of *ringed* sites
`(𝒳_τ/x, 𝒪_𝒳|_x) ≌ ((Sch/U)_τ, 𝒪)`: the direct image along it of the structure sheaf of the big
`τ`-site of `U = p(x)` *is* the structure sheaf of `𝒳` restricted to the slice at `x`.

The two sites are identified by `AlgebraicGeometry.Stack.localizationEquivalence` and
`AlgebraicGeometry.Stack.isDenseSubsite_localizationEquivalence`, and the structure sheaves by
this equality, which is an equality and not merely an isomorphism. -/
@[stacks 06W9 "equivalence of ringed sites"]
theorem sheafPushforwardContinuous_baseStructureSheaf
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (x : 𝒳) :
    ((localizationEquivalence B S hS p hp x).functor.sheafPushforwardContinuous
        CommRingCat.{u} ((associatedTopology B S hS p τ).over x)
        (τ.over (B.obj (p.obj x).left.2))).obj
        (baseStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 τ hτ) =
      (structureSheaf B S hS p hp τ hτ).over x :=
  rfl

/-- **Stacks 06W9**, the same equivalence of ringed sites read on the underlying sheaves of
(not necessarily commutative) rings, which is the form the categories of sheaves of modules are
indexed by: the transport of the base sheaf of rings along the localization equivalence is the
restriction of the sheaf of rings of `𝒳` to the slice at `x`. -/
@[stacks 06W9 "equivalence of ringed sites, underlying sheaves of rings"]
theorem sheafPushforwardContinuous_baseRingStructureSheaf
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (x : 𝒳) :
    ((localizationEquivalence B S hS p hp x).functor.sheafPushforwardContinuous
        RingCat.{u} ((associatedTopology B S hS p τ).over x)
        (τ.over (B.obj (p.obj x).left.2))).obj
        (baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 τ hτ) =
      (ringStructureSheafCore B S hS p hp τ hτ).over x :=
  rfl

end AlgebraicGeometry.Stack

end
