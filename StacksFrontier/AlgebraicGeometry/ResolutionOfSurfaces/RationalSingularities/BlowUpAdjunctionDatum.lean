module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSupplement

/-!
# What the exceptional adjunction datum of the blowup contains

`AlgebraicGeometry.BlowUpDualizing.ExceptionalAdjunction` is the adjunction formula for the
exceptional curve, the input of the source's proof of clause (1) of [Stacks, Tag 0B64], packaged
as a datum: a normal sheaf `𝒩` of the exceptional curve `E ⊂ X`, invertible
and tensor-inverse to the conormal sheaf `ℐ_E|_E`, together with the adjunction formula
`ω_E ≅ ω_X|_E ⊗ 𝒩`.

This file measures that datum exactly. Three of its four fields are *already theorems* of
`BlowUpDualizing.lean`: `𝒪_E(-1)` is an invertible tensor inverse of the conormal sheaf
(`AlgebraicGeometry.BlowUpDualizing.conormalTensorTwistNegOneIso_unconditional`). So the datum is
*equivalent* to its formula field read at `𝒩 = 𝒪_E(-1)`, which is the conclusion of clause (1)
itself.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.exceptionalAdjunctionOfIso`: the formula
  `ω_E ≅ ω_X|_E(-1)` alone builds the whole datum, with no hypothesis on `A`, on `ω_X` or on
  `ω_E`.
* `AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalAdjunction_iff`: the datum exists if and
  only if `ω_E ≅ ω_X|_E(-1)`, the conclusion of clause (1): granting the datum is granting that
  conclusion.
* `AlgebraicGeometry.BlowUpDualizing.nonempty_iso_of_exceptionalAdjunction`: a datum over a fixed
  `ω_X` pins its second argument down up to isomorphism — two modules on `E` both admitting the
  datum over the same `ω_X` are isomorphic.

## Implementation notes

**Why the datum does not follow from dualizing hypotheses alone.** The last result above is an
obstruction to proving `Nonempty (ExceptionalAdjunction A ωX ωE)` from the hypotheses that `ω_X`
and `ω_E` are *some* dualizing modules (`Stacks.Duality.IsDualizingModule`): such a proof would
force any two dualizing modules on `E` to be isomorphic. They are not. The only uniqueness
available for dualizing complexes is up to shift and tensoring with an invertible object
([Stacks, Tag 0A7F], formalized over a ring as
`Dualizing.IsDualizingComplex.exists_iso_derivedTensorProduct_invertible`), and the converse
([Stacks, Tag 0A7F] read backwards,
`Dualizing.isDualizingComplex_tensor_of_isInvertible`) says that invertible twists of a dualizing
complex are dualizing again. Being a dualizing complex on a scheme is the local condition
`Stacks.Duality.IsDualizingComplex`, so on the exceptional curve of the blowup of a regular local
ring of dimension two — where `E ≅ 𝐏¹_κ` — every invertible module is a dualizing module, and
`𝒪_E` and `𝒪_E(-1)` are two non-isomorphic ones. Pinning `ω_E` down is exactly the normalization
that the source performs: its `ω_X` is the *normalized* dualizing module relative to a dualizing
module on `A` and its `ω_E` is the dualizing sheaf of `E` over the residue field, not arbitrary
dualizing modules.

**What normalizing `ω_X` alone does not give.** The normalization of `ω_X` relative to `ω_A` is
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule` of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities`
`/NormalizedDualizingModule.lean`; it pins `ω_X` down up to a unique trace-compatible
isomorphism, and it is what turns the datum of [Stacks, Tag 0BBU] into a theorem (clause (3) of
[Stacks, Tag 0B64], `AlgebraicGeometry.BlowUpDualizing.epi_dualizingPullbackMap_of_normalized`).
It says nothing about `E`. What clause (1) needs on top of it is the adjunction formula for the
effective Cartier divisor `E ⊂ X` — `ω_E = i^!ω_X^•` up to the shift, [Stacks, Tag 0A9X] and
[Stacks, Tag 0AA4] — which is the content of a different tag.

At [Stacks, Tag 0B4B] that formula is formalized in `D(𝒪_E)`, as the isomorphism
`R ℰom(𝒪_E, 𝒪_X) ≅ 𝒩[-1]` of
`Stacks.Divisors.normalSheafShiftIsoDerivedSheafHomExactSupport` and as the invertibility of the
*canonical* comparison morphism,
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport` of
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierCanonicalIso.lean`. With `ω_X` in place of
`𝒪_X` the computation is formalized *after* `Ri_*`, for an arbitrary complex `K` on `X`:
`Stacks.Divisors.pushforwardDerivedSheafHomExactSupportTensorIso` of
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDerivedSheafHomTensor.lean` is
`Ri_* R ℰom(𝒪_E, K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]`.

What is still owed is the descent of that computation from `X` to `E`. Derived pushforward along
the closed immersion reflects isomorphisms but is not full, so the isomorphism of the two
pushforwards does not by itself produce one in `D(𝒪_E)`; at `K = 𝒪_X` the descent is performed by
`CategoryTheory.Functor.isoSingleOfFullyFaithful`, both sides being concentrated in a single
degree there, and for a general `K` neither side is. Clause (1) for the normalized pair is
registered at `AlgebraicGeometry.BlowUpDualizing.nonempty_dualizingSheafOverField_iso_curveTwist`.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **The adjunction formula builds the adjunction datum.** Taking the normal sheaf to be
`𝒪_E(-1)`, its invertibility is that of a tensor power of an invertible module and its being a
tensor inverse of the conormal sheaf is `conormalTensorTwistNegOneIso_unconditional`, so an
isomorphism `ω_E ≅ ω_X|_E(-1)` is the only remaining field. -/
def exceptionalAdjunctionOfIso (ωX : (blowUpScheme A).Modules)
    (ωE : (exceptionalCurve A).Modules)
    (e : ωE ≅ curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1)) :
    ExceptionalAdjunction A ωX ωE where
  normal := curveTwistSheaf A (-1)
  isInvertible := inferInstance
  inverse := conormalTensorTwistNegOneIso_unconditional A
  formula := e

/-- **The exceptional adjunction datum is exactly clause (1) of [Stacks, Tag 0B64].** Forwards,
the normal sheaf of the datum is a tensor inverse of the conormal sheaf, so is isomorphic to
`𝒪_E(-1)` by uniqueness of tensor inverses. Backwards it is `exceptionalAdjunctionOfIso`. -/
theorem nonempty_exceptionalAdjunction_iff (ωX : (blowUpScheme A).Modules)
    (ωE : (exceptionalCurve A).Modules) :
    Nonempty (ExceptionalAdjunction A ωX ωE) ↔
      Nonempty (ωE ≅ curveTwist A
        ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1)) := by
  constructor
  · rintro ⟨D⟩
    have := D.isInvertible
    have := isInvertibleModule_conormalSheaf_unconditional A
    refine ⟨D.formula ≪≫ tensorModulesMapIso (exceptionalCurve A) (Iso.refl _) ?_⟩
    exact Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso (exceptionalCurve A)
      D.normal (curveTwistSheaf A (-1)) (conormalSheaf A) D.inverse
      (conormalTensorTwistNegOneIso_unconditional A)
  · rintro ⟨e⟩
    exact ⟨exceptionalAdjunctionOfIso A ωX ωE e⟩

/-- **The adjunction datum determines the module on the exceptional curve.** Two
`𝒪_E`-modules admitting the datum over the same `ω_X` are isomorphic, both being `ω_X|_E(-1)`. -/
theorem nonempty_iso_of_exceptionalAdjunction (ωX : (blowUpScheme A).Modules)
    (ωE ωE' : (exceptionalCurve A).Modules) (D : ExceptionalAdjunction A ωX ωE)
    (D' : ExceptionalAdjunction A ωX ωE') : Nonempty (ωE ≅ ωE') := by
  obtain ⟨e⟩ := (nonempty_exceptionalAdjunction_iff A ωX ωE).1 ⟨D⟩
  obtain ⟨e'⟩ := (nonempty_exceptionalAdjunction_iff A ωX ωE').1 ⟨D'⟩
  exact ⟨e ≪≫ e'.symm⟩

end AlgebraicGeometry.BlowUpDualizing

end
