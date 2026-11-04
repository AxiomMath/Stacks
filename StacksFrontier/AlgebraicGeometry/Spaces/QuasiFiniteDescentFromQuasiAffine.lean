module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent

/-!
# Effective descent for separated quasi-finite morphisms, from effective descent for quasi-affine
ones

Effective descent for the quasi-affine morphisms of schemes implies effective descent for the
morphisms which are separated, locally quasi-finite, locally of finite type and quasi-compact, both
for the single-morphism predicate `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`
and for the covering-sieve predicate `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`
on the big fppf site of `S`. The link between the two properties is Stacks 02LR, that a separated
quasi-finite morphism of schemes is quasi-affine, in the form
`AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom`.

## Main results

* `isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite_of_isQuasiAffineHom`, in
  the namespace `AlgebraicGeometry.Space`: effective descent along the surjective étale
  morphisms of the big fppf site of `S` for the quasi-affine morphisms of schemes implies it for
  the separated quasi-finite morphisms.
* `isEffectiveDescentAlongCoveringSieve_isSeparated_inf_quasiFinite_of_isQuasiAffineHom`, in the
  same namespace: the same transfer for the covering-sieve predicate.
* `AlgebraicGeometry.isSeparated_inf_quasiFinite_isZariskiLocalAtTarget`: being separated, locally
  quasi-finite, locally of finite type and quasi-compact is Zariski local on the target.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Separatedness together with local quasi-finiteness, being locally of finite type and
quasi-compactness — the property of Stacks 02W8 together with quasi-compactness — is Zariski
local on the target. -/
theorem isSeparated_inf_quasiFinite_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact :
        MorphismProperty Scheme.{u}) :=
  have := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  MorphismProperty.IsLocalAtTarget.inf _ _

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Effective descent along the surjective étale morphisms of the big fppf site of `S` for the
quasi-affine morphisms of schemes implies effective descent for the separated quasi-finite ones. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite_of_isQuasiAffineHom
    (h0247 : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
  isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite
    isSeparated_inf_quasiFinite_le_isQuasiAffineHom h0247

/-- Effective descent along the covering sieves of the big fppf site of `S` for the quasi-affine
morphisms of schemes implies effective descent for the separated quasi-finite ones. -/
theorem isEffectiveDescentAlongCoveringSieve_isSeparated_inf_quasiFinite_of_isQuasiAffineHom
    (h0247 : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
  have _h1 := isSeparated_inf_quasiFinite_isZariskiLocalAtTarget.{u}
  have _h2 := isSeparated_inf_quasiFinite_descendsAlong_fppf.{u}
  isEffectiveDescentAlongCoveringSieve_of_le h0247
    isSeparated_inf_quasiFinite_le_isQuasiAffineHom

end Space

end AlgebraicGeometry

end
