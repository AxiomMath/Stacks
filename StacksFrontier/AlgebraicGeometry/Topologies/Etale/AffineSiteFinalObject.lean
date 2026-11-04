module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# The final object of the small affine étale site

For an affine scheme `S` the identity `S → S` is an affine étale object over `S`, so the small
affine étale site of `S` has a final object, namely `S` itself, and therefore has finite limits.

## Main definitions

* `AlgebraicGeometry.SmallAffineEtale.final`: the object `S / S` of the small affine étale
  category of `S`.
* `AlgebraicGeometry.SmallAffineEtale.finalIsTerminal`: `S / S` is a terminal object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object `S / S`, with identity structure morphism, in the small affine étale category of
an affine scheme `S`. -/
public def SmallAffineEtale.final [IsAffine S] : SmallAffineEtale B S hS :=
  ⟨SmallEtale.final B S hS, by
    dsimp [SmallEtale.IsAffine, SmallEtale.final]
    infer_instance⟩

/-- For an affine scheme the object `S / S` is final in the small affine étale category. -/
public noncomputable def SmallAffineEtale.finalIsTerminal [IsAffine S] :
    IsTerminal (SmallAffineEtale.final B S hS) :=
  IsTerminal.ofUniqueHom
    (fun Y ↦ (SmallAffineEtale.inclusion B S hS).preimage
      ((SmallEtale.finalIsTerminal B S hS).from
        ((SmallAffineEtale.inclusion B S hS).obj Y)))
    (fun _ _ ↦ (SmallAffineEtale.inclusion B S hS).map_injective
      ((SmallEtale.finalIsTerminal B S hS).hom_ext _ _))

/-- The small affine étale category of an affine scheme has a terminal object. -/
public instance hasTerminal_smallAffineEtale [IsAffine S] :
    HasTerminal (SmallAffineEtale B S hS) :=
  (SmallAffineEtale.finalIsTerminal B S hS).hasTerminal

/-- The small affine étale category of an affine scheme has finite limits. -/
public instance hasFiniteLimits_smallAffineEtale [IsAffine S] :
    HasFiniteLimits (SmallAffineEtale B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end AlgebraicGeometry

end
