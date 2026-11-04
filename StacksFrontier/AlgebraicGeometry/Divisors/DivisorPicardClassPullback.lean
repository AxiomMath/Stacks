module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback

/-!
# Pullback of the Picard class of an effective Cartier divisor

Let `f : X ⟶ Y` be a morphism of schemes and let `D ⊆ Y` be an effective Cartier divisor whose
pullback is defined, that is, whose scheme-theoretic inverse image `f^{-1}D` is again an
effective Cartier divisor. Then

`f^* [𝒪_Y(D)] = [𝒪_X(f^{-1}D)]`

in the Picard group of `X`: the assignment `D ↦ [𝒪(D)]` commutes with pullback.

## Main results

* `Stacks.Divisors.schemePullbackClass_picardClass` — the displayed identity.

## Implementation notes

This is the identification `f^* 𝒪_Y(D) ≅ 𝒪_X(f^{-1}D)` of
`Stacks.Divisors.invertibleSheafPullbackIso` read in the Picard group, where an isomorphism of
invertible modules is an equality of classes
(`Stacks.SheafOfModules.picardClass_eq_iff`). The move from the class to a representative is
`Stacks.Picard.pullbackClass_classOf`, which computes the pullback of a class on any
representative and not only on the one the skeleton chooses.

The same two-step computation is written out inline at three existing call sites —
`StacksFrontier/AlgebraicGeometry/Curves/Models/PicardSequenceExact.lean`,
`StacksFrontier/AlgebraicGeometry/Blowup/PicardGroup.lean` (where it is a private helper) and
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurvePicard.lean` (whose docstring records
that it is reproved there because the private one is not exported). Those sites are left
untouched; what is added here is the general statement, with the morphism and the divisor
arbitrary.

No `@[stacks]` attribute is attached. Tag 0C4U is the isomorphism of invertible sheaves together
with the identification of the canonical sections, and it is already registered on
`Stacks.Divisors.invertibleSheafPullbackIso` and
`Stacks.Divisors.invertibleSheafPullbackIso_canonicalSection`; the statement below forgets both
the isomorphism and the section, so it is a consequence of that tag and not its content.

## References

* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- **The Picard class of an effective Cartier divisor pulls back to the class of the
inverse-image divisor**, `f^* [𝒪_Y(D)] = [𝒪_X(f^{-1}D)]`.

The invertible sheaf of `D` pulls back to the invertible sheaf of `f^{-1}D` by Tag 0C4U, and an
isomorphism of invertible modules is an equality of Picard classes. -/
theorem schemePullbackClass_picardClass {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsPullbackDefined f D] :
    Stacks.Picard.schemePullbackClass f (picardClass D) = picardClass (D.comap f) :=
  (Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom (invertibleSheaf' D)
      (isInvertible_invertibleSheaf_picard D)).trans
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
        (isInvertible_invertibleSheaf_picard (D.comap f))).2
      ⟨invertibleSheafPullbackIso f D⟩)

end Stacks.Divisors

end
