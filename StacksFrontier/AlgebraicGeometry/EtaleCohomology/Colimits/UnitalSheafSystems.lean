module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyIdentityLawTransport

/-!
# Unital systems of sheaves on an inverse system of schemes

Let `I` be a preordered set and let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes. A system
of sheaves `(𝓕_i, φ_{i'i})` on it in the sense of [Stacks, Tag 0EZL],
`Stacks.EtaleCohomology.EtaleSheafSystem`, is a sheaf `𝓕_i` on the small étale site of each `X_i`
together with maps `φ_{i'i} : f_{i'i}^{-1}𝓕_i ⟶ 𝓕_{i'}` for `i' ≥ i` satisfying the cocycle
condition `φ_{i''i} = φ_{i''i'} ∘ f_{i''i'}^{-1}φ_{i'i}` whenever `i'' ≥ i' ≥ i`. The source
imposes only the cocycle condition.

This file defines the unital variant, which also asks `φ_{ii} = id` for every `i`. Since `f_{ii}`
is the identity morphism of `X_i` but the inverse image along it is a chosen left adjoint,
`f_{ii}^{-1}𝓕_i` is not literally `𝓕_i`; the condition `φ_{ii} = id` is read through the
canonical identification `Stacks.EtaleCohomology.systemPullbackId` of the inverse image along an
identity transition with the identity functor.

## Main definitions

* `Stacks.EtaleCohomology.UnitalEtaleSheafSystem` — the unital variant of a system of sheaves on
  an inverse system of schemes: the data, the identity condition and the cocycle condition.
* `Stacks.EtaleCohomology.unitalDirectImageSystem` — the system of direct images of a sheaf
  along the projections of a cone, as a system satisfying both conditions.

## Implementation notes

The field `map_id` is the predicate `Stacks.EtaleCohomology.HasSheafIdentityLaw` of the
underlying system, written out. For the system of direct images it is supplied by
`Stacks.EtaleCohomology.hasSheafIdentityLaw_directImageSystem`.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- **The unital variant of a system of sheaves.** A system `(𝓕_i, φ_{i'i})` of sheaves on an
inverse system of schemes, `Stacks.EtaleCohomology.EtaleSheafSystem`, whose map at an identity
index is the identity: `φ_{ii} = id` for all `i`, read through the canonical identification
`Stacks.EtaleCohomology.systemPullbackId` of `f_{ii}^{-1}𝓕_i` with `𝓕_i`.

This is the unital variant; [Stacks, Tag 0EZL] itself (`Stacks.EtaleCohomology.EtaleSheafSystem`)
imposes only the cocycle condition. -/
public structure UnitalEtaleSheafSystem extends EtaleSheafSystem D A where
  /-- The identity condition: the map attached to an identity index is the identity, through
  the canonical identification of the inverse image along an identity transition. -/
  map_id : ∀ i : Iᵒᵖ, map (𝟙 i) = (systemPullbackId D A i).hom.app (obj i)

variable (c : Cone D) (F : Sheaf (smallEtaleTopology c.pt) A)

/-- The direct images `f_{i,*}𝓕` of a sheaf `𝓕` along the projections `f_i` of a cone over an
inverse system of schemes form a system of sheaves satisfying the identity condition as well as
the cocycle condition. -/
public def unitalDirectImageSystem : UnitalEtaleSheafSystem D A where
  toEtaleSheafSystem := directImageSystem D A c F
  map_id := hasSheafIdentityLaw_directImageSystem D A c F

end Stacks.EtaleCohomology

end
