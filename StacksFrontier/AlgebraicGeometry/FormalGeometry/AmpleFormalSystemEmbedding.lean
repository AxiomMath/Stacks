module

public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.ImmersionClosedness
import StacksCore.Tactic.StacksAttribute

/-!
# The projective embedding of the closed member of an ample formal system

Grothendieck's algebraization theorem ([Stacks, Tag 089A]) starts from a Noetherian ring `A`
complete for an ideal `I`, the thickenings `Sₙ = Spec (A / Iⁿ)`, a tower of cartesian squares
`Xₙ ⟶ Sₙ` and a compatible system of invertible modules `(ℒₙ, φₙ)`, and assumes that
`X₁ ⟶ S₁` is proper and that `ℒ₁` is ample. Its proof begins by embedding the closed member:
it picks a degree `d` and global sections of `ℒ₁ ^⊗ d` inducing an immersion
`ψ₁ : X₁ ⟶ ℙᴺ_{S₁}` over `S₁` ([Stacks, Tag 01VT]), and then upgrades that immersion to a
closed immersion because `X₁` is proper over `S₁` ([Stacks, Tag 01W6]) and an immersion with
closed image is a closed immersion ([Stacks, Tag 01IQ]).

That step is what this file proves, with no hypothesis beyond the two the theorem makes. It is
proved first over an arbitrary affine base and then read at the thickening `S₁ = Spec (A / I)`,
which is the situation of the theorem.

## Main results

* `Stacks.AmpleFormalSystemEmbedding.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple`:
  a scheme proper over an affine base and carrying an ample invertible module admits, in some
  degree `d ≥ 1`, a closed immersion into a relative projective space over that base pulling the
  hyperplane sheaf back to the `d`-th tensor power of the module.
* `Stacks.AmpleFormalSystemEmbedding.isHProjective_of_isAmple`: the same read through
  `Stacks.HProjective.IsHProjective`.

## What the theorem still needs

The remaining steps of the proof of [Stacks, Tag 089A] are not carried here, and none of them is
a corollary of the above.

* The graded `𝒪_{X₁}`-algebra `𝓕 = ⨁_{n ≥ 0} Iⁿ𝒪_{X_{n+1}}` built from the kernels of
  `𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ}`, and the surjection onto it from the pullback of
  `B = ⨁ Iⁿ/Iⁿ⁺¹`, which is what makes `𝓕` a finite type graded module and so puts the system
  in the range of [Stacks, Tag 0897]. No such graded algebra is constructed anywhere in this
  repository.
* The vanishing `H¹(X₁, 𝓕ₙ ⊗ ℒ₁ ^⊗ d) = 0` for all `d ≥ d₀`, uniformly in `n`. This is
  [Stacks, Tag 0897] part (2), carried at
  `Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology` with the
  base change `X' = Spec B ×_{Spec A} X` and the comparison of cohomologies as hypotheses.
* The inductive lifting of the sections `s_{0,1}, …, s_{N,1}` of `ℒ₁ ^⊗ d` to sections of
  `ℒₙ ^⊗ d`, and the resulting cartesian tower `ψₙ : Xₙ ⟶ ℙᴺ_{Sₙ}`.
* The final appeal to [Stacks, Tag 0899], carried at
  `AlgebraicGeometry.exists_closedImmersion_algebraization_of_isPullback` with
  [Stacks, Tag 09ZT] and the uniqueness clause of [Stacks, Tag 0A42] as hypotheses — so that
  appeal is conditional on base already.
* The invertible module `ℒ` on the algebraized `X` with `ℒₙ ≅ ℒ|_{Xₙ}` compatible with the
  `φₙ`. The embedding only ever sees `ℒₙ ^⊗ d`, and the theorem's conclusion asks for `ℒₙ`
  itself; the source does not say how that `d`-th root is obtained. Its *ampleness* would be
  free once it exists, by [Stacks, Tag 01PT]
  (`Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule`); it is the module, not its
  ampleness, that is missing.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01IQ](https://stacks.math.columbia.edu/tag/01IQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.AmpleFormalSystemEmbedding

variable {X S : Scheme.{u}}

/-- **A scheme proper over an affine base with an ample invertible module embeds as a closed
subscheme of a relative projective space.** For `f : X ⟶ S` proper with `S` affine and `L` an
ample invertible `𝒪_X`-module there are a degree `d ≥ 1`, an `N` and a closed immersion
`ψ : X ⟶ ℙᴺ_S` over `S` with `ψ^* 𝒪(1) ≅ L ^⊗ d`.

[Stacks, Tag 01VT] — condition (5), which base carries — supplies an *immersion* with those
properties; `f` is proper, so `ψ` is proper by [Stacks, Tag 01W6] part (2) and its image is
closed by the final clause of that tag, and [Stacks, Tag 01IQ] turns an immersion with closed
image into a closed immersion. -/
@[ega "II 5.3.3" "special case", ega "III 5.4.5" "partial", sga "4½ Arcata 3.4.3" "special case"]
theorem exists_isClosedImmersion_projectiveSpaceOver_of_isAmple [IsAffine S] (f : X ⟶ S)
    [IsProper f] (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ (N : ℕ) (ψ : X ⟶ projectiveSpaceOver N S),
      IsClosedImmersion ψ ∧ ψ ≫ (projectiveSpaceOver N S ↘ S) = f ∧
      Nonempty (tensorPowModule X L (d : ℤ) ≅
        (Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf N S)) := by
  obtain ⟨d, hd, N, ψ, _, hover, he⟩ :=
    (Stacks.AmpleRelativeFiniteType.isAmple_iff_exists_hasImmersionTwistOver f L).1 hL
  refine ⟨d, hd, N, ψ, ?_, hover, he⟩
  exact (AlgebraicGeometry.isClosedImmersion_iff_isClosed_range ψ).2
    (AlgebraicGeometry.isClosed_range_of_universallyClosed_of_isSeparated ψ
      (projectiveSpaceOver N S ↘ S) f hover)

/-- **A scheme proper over an affine base with an ample invertible module is H-projective**, the
previous theorem read through `Stacks.HProjective.IsHProjective`. -/
@[ega "III 5.4.5" "partial"]
theorem isHProjective_of_isAmple [IsAffine S] (f : X ⟶ S) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) : Stacks.HProjective.IsHProjective f := by
  obtain ⟨_, _, N, ψ, hψ, hover, _⟩ :=
    exists_isClosedImmersion_projectiveSpaceOver_of_isAmple f L hL
  exact ⟨N, ψ, hψ, hover⟩

variable (A : Type u) [CommRing A] (I : Ideal A)

end Stacks.AmpleFormalSystemEmbedding

end
