module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion`

Further results complementing
`StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07VS**, in the form in which it is used below: an algebraic space over `S`
receiving a surjective *finite* morphism from an affine scheme of the site is an affine scheme.

It is the special case of the library's Stacks 07VS,
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, in which the source
is representable, and it is proved unconditionally as `AlgebraicGeometry.FormalSpace.is07VS`.

**This is strictly weaker than `AlgebraicGeometry.FormalSpace.Is07VT`.** A finite morphism of
algebraic spaces is universally closed by Stacks 0415
(`AlgebraicGeometry.Space.universallyClosed_of_isFinite`), so `Is07VT` implies it with nothing
granted — that is `AlgebraicGeometry.FormalSpace.is07VS_of_is07VT` below. The converse
direction is *not* available: recovering finiteness from universal closedness is affineness of
the morphism by Stacks 08GB followed by integrality by Stacks 0415, and then the passage from
an integral morphism to a limit of finite ones, which is the conclusion of Stacks 09YA that the
library's Stacks 07VT grants and the proof of Stacks 07VS does not need.

Every consumer in the formal-space tree takes this proposition rather than `Is07VT`, the one
application of the grant in that tree being to a closed immersion, which is finite outright.
`Is07VT`, which implies this proposition, also holds: it follows from Stacks 07VT, proved
outright as
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`. -/
abbrev Is07VS : Prop :=
  ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS} (c : yoneda.obj T ⟶ F),
    IsAlgebraicSpace B S hS F → IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    Space.IsSurjective B S hS c → Space.IsFinite B S hS c →
    Space.IsAffineSpace B S hS F

/-- **An algebraic space which is a thickening of an affine scheme of the site is affine**: an
algebraic space over `S` receiving a surjective closed immersion from an affine object of the
site is an affine space. This is the shape in which the formal-space tree consumes Stacks 07VS:
its one application there is to a thickening, a surjective closed immersion, so this is the
special case of `AlgebraicGeometry.FormalSpace.Is07VS` for closed immersions
(`AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion_of_is07VS`). -/
abbrev IsAffineOfSurjectiveClosedImmersion : Prop :=
  ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS} (c : yoneda.obj T ⟶ F),
    IsAlgebraicSpace B S hS F → IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    Space.IsSurjective B S hS c → Space.IsClosedImmersion B S hS c →
    Space.IsAffineSpace B S hS F

/-- `AlgebraicGeometry.FormalSpace.Is07VS` implies its closed-immersion case, a closed
immersion of algebraic spaces being finite (Stacks 081Y,
`AlgebraicGeometry.Space.isFinite_of_isClosedImmersion`). -/
theorem isAffineOfSurjectiveClosedImmersion_of_is07VS (h07VS : Is07VS B S hS) :
    IsAffineOfSurjectiveClosedImmersion B S hS :=
  fun c hF hT hsurj hci ↦ h07VS c hF hT hsurj (Space.isFinite_of_isClosedImmersion B S hS c hci)

/-- **`AlgebraicGeometry.FormalSpace.Is07VS` is weaker than
`AlgebraicGeometry.FormalSpace.Is07VT`**, with nothing granted: a finite morphism of algebraic
spaces over `S` is universally closed by Stacks 0415,
`AlgebraicGeometry.Space.universallyClosed_of_isFinite`, and the source of the morphism is an
algebraic space by Stacks 025Z.

So nothing is lost by stating the consumers in the formal-space tree with `Is07VS`: anything
that could supply `Is07VT` to the old form supplies `Is07VS` to the new one through this
implication. -/
theorem is07VS_of_is07VT (h07VT : Is07VT B S hS) : Is07VS B S hS :=
  fun {_ T} c hF hTaff hsurj hfin ↦
    h07VT c hF hTaff hsurj
      (Space.universallyClosed_of_isFinite B S hS (isAlgebraicSpace_yoneda B S hS T) hF hfin)

end AlgebraicGeometry.FormalSpace

end
