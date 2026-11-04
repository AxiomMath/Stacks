module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectFullyFaithfulHeld
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomTorBridgeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# The Tor clause of Stacks 0DKN along an étale morphism, and over the identity

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `K` be an object of `D(𝒪_X)` of finite Tor dimension in the absolute
sense of Stacks 08FZ (2).  Then `K` satisfies the Tor clause of Stacks 0DKN along `f`: read in
`D(f⁻¹𝒪_Y)` through restriction of scalars along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, it *locally* has finite
Tor dimension, the local condition measured against
`AlgebraicGeometry.Space.canonicalSliceDerivedTensorProduct`.

The case `f = 𝟙 X` is what this is wanted for.  The identity is étale, so the Tor hypothesis of
Stacks 0DKV read over the identity — which is how the pseudo-coherent case of Stacks 09RI is
stated in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomAffineLeafReindex.lean` — follows
from the absolute finite Tor dimension that clause (2) of Stacks 09RI grants.  The stalkwise
characterisation
`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_derivedScalarRestriction_iff` is not used:
at an étale morphism, and in particular at an identity, the comparison is formal.

## Main results

* `AlgebraicGeometry.Space.hasLocallyFiniteTorDimensionAlong_of_hasFiniteTorDimension_of_isEtale`:
  the Tor clause of Stacks 0DKN along an étale morphism, from absolute finite Tor dimension.
* `AlgebraicGeometry.Space.hasLocallyFiniteTorDimensionAlong_id_of_hasFiniteTorDimension`: the
  same over the identity, which is the bridge between the two spellings of the Tor hypothesis of
  clause (2) of Stacks 09RI.

## The proof

Finite Tor dimension passes from `𝒪_X` to `f⁻¹𝒪_Y` by
`AlgebraicGeometry.Space.hasFiniteTorDimension_derivedScalarRestriction_of_isEtale`, and finite
Tor dimension on a site is locally finite Tor dimension on it: the restriction of the object to
*every* slice has finite Tor dimension, so the maximal covering of each chart witnesses the local
condition.  That last step is Stacks 08FZ (3) at the universe shape of the small étale site, an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, whose objects form a type one universe above its
morphisms.  The statement at that shape is
`Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse`'s
`locallyHasFiniteTorDimension_of_hasFiniteTorDimension`; the single-universe
`Stacks.SheafOfModules.DerivedTensorProduct`'s
`locallyHasFiniteTorDimension_of_hasFiniteTorDimension` cannot be instantiated here.

No `@[stacks ...]` attribute is placed here: the Tor clause of Stacks 0DKN is registered with
the clauses of that tag, and Stacks 08FZ where it is proved.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Lemma 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

section Etale

open Stacks.SheafOfModules.DerivedTensorProduct.FreeModuleUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

include hf in
/-- **The Tor clause of Stacks 0DKN along an étale morphism, from absolute finite Tor
dimension.**  If an object of `D(𝒪_X)` has finite Tor dimension in the absolute sense of
Stacks 08FZ (2), then along an étale `f` it satisfies the Tor clause of Stacks 0DKN: read in
`D(f⁻¹𝒪_Y)` through restriction of scalars along `f♯`, it locally has finite Tor dimension, the
local condition measured against
`AlgebraicGeometry.Space.canonicalSliceDerivedTensorProduct`.

The derived tensor product `T` against which the absolute hypothesis is measured is an arbitrary
one: only the vanishing of cohomology sheaves is transported. -/
theorem hasLocallyFiniteTorDimensionAlong_of_hasFiniteTorDimension_of_isEtale
    (T : Stacks.SheafOfModules.DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K) :
    HasLocallyFiniteTorDimensionAlong f K := by
  refine locallyHasFiniteTorDimension_of_hasFiniteTorDimension.{u + 1, u, u}
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (inverseImageRingedSite B S hS f))
    (canonicalSliceDerivedTensorProduct B S hS f) _ ?_
  exact hasFiniteTorDimension_derivedScalarRestriction_of_isEtale B S hS f hf T _ K h

end Etale

/-! ### The identity -/

/-- **The Tor clause of Stacks 0DKN over the identity is absolute finite Tor dimension.**  The
identity of an algebraic space is étale, by `AlgebraicGeometry.Space.isEtale_id`, so
`AlgebraicGeometry.Space.hasLocallyFiniteTorDimensionAlong_of_hasFiniteTorDimension_of_isEtale`
applies to it: an object of `D(𝒪_X)` of finite Tor dimension, read through restriction of
scalars along `𝟙⁻¹𝒪_X ⟶ 𝒪_X`, locally has finite Tor dimension.

This is the bridge between the two spellings of the Tor hypothesis of clause (2) of
Stacks 09RI: the tag's own, finite Tor dimension of `K₀` on the small étale ringed site of `X₀`,
and the one Stacks 0DKV carries, locally finite Tor dimension along the structure morphism, read
at the identity. -/
theorem hasLocallyFiniteTorDimensionAlong_id_of_hasFiniteTorDimension
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (T : Stacks.SheafOfModules.DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K) :
    HasLocallyFiniteTorDimensionAlong (𝟙 X) K :=
  hasLocallyFiniteTorDimensionAlong_of_hasFiniteTorDimension_of_isEtale B S hS (𝟙 X)
    (isEtale_id B S hS X.1) T K h

end AlgebraicGeometry.Space

end
