module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward

/-!
# The projection of a base change on small étale sites

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `T` be an object of the
small étale site of `Y`.  The base change `X ×_Y T` of `T` along `a` (the object
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange B a` of the small étale site of `X`) comes with
the projection `X ×_Y T ⟶ T`, the base change of the underlying morphism of schemes of `a` along
the structure morphism of `T`.  This file records that this projection inherits
quasi-compactness and quasi-separatedness from `a`.

## Main results

* `AlgebraicGeometry.SmallEtale.quasiCompact_smallEtaleBaseChange_proj`: the projection
  `X ×_Y T ⟶ T` is quasi-compact as soon as the underlying morphism of schemes of `a` is.
* `AlgebraicGeometry.SmallEtale.quasiSeparated_smallEtaleBaseChange_proj`: the projection
  `X ×_Y T ⟶ T` is quasi-separated as soon as the underlying morphism of schemes of `a` is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The projection `X ×_Y T ⟶ T` of a base change on small étale sites is quasi-compact** as
soon as the underlying morphism of schemes of `a` is, being its base change along the structure
morphism of `T`. -/
theorem quasiCompact_smallEtaleBaseChange_proj [QuasiCompact (schemeHom B a)]
    (T : SmallEtale B Y.obj Y.property) :
    QuasiCompact (B.inclusion.map (pullback.fst T.obj.hom a)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (((IsPullback.of_hasPullback T.obj.hom a).map B.inclusion).flip) inferInstance

/-- **The projection `X ×_Y T ⟶ T` of a base change on small étale sites is quasi-separated** as
soon as the underlying morphism of schemes of `a` is, being its base change along the structure
morphism of `T`. -/
theorem quasiSeparated_smallEtaleBaseChange_proj [QuasiSeparated (schemeHom B a)]
    (T : SmallEtale B Y.obj Y.property) :
    QuasiSeparated (B.inclusion.map (pullback.fst T.obj.hom a)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (((IsPullback.of_hasPullback T.obj.hom a).map B.inclusion).flip) inferInstance

end AlgebraicGeometry.SmallEtale

end
