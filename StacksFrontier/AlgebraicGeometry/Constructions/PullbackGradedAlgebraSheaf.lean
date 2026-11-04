module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Commutes
public import StacksFrontier.AlgebraicGeometry.Constructions.AffineGradedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent

/-!
# The algebra sheaf of a pulled-back sheaf of graded algebras

`Stacks.RelativeSpec.gradedAlgebraSheaf X A hc` reads a sheaf of graded `𝒪_X`-algebras with
commuting homogeneous multiplication as a sheaf of commutative `𝒪_X`-algebras, and
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` makes it quasi-coherent given two
further conditions: that the negative-degree pieces vanish and that the coproduct of the
nonnegative ones is quasi-coherent. This file supplies all three for a *pullback*
`Stacks.Conormal.gradedPullback g A`, and then for the algebra `f^* B̃` of
[Stacks, Tag 0897].

Of the three only the commutation `hc` is not formal. It quantifies over all homogeneous local
sections of `f^*A`, and the pullback-unit images of sections of `A` do not exhaust them, so the
condition on the pullback is strictly stronger than its restriction to pulled-back sections.
That gap is closed by `Stacks.RingedSpace.pullbackBilinear_heq_ext`, the heterogeneous form of
bilinear extensionality for pullbacks: the two sides of the commutation are bilinear in the two
sections, so agreement on pullback-unit images — which is
`Stacks.Conormal.gradedPullback_mul_pullbackSection` together with the commutation downstairs —
is enough. The two vanishing and quasi-coherence conditions are the pullback functor applied
piecewise, quasi-coherence of a coproduct being stable under colimits of any shape.

Commutativity of the homogeneous multiplication transfers along a pullback of schemes by
`Stacks.Conormal.gradedPullback_mul_comm` of
`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/GradedPullback.lean`.

## Main results

* `Stacks.Conormal.isQuasicoherent_coprod_gradedPullback_piece`: the coproduct of the
  nonnegative-degree pieces of a pullback is quasi-coherent.
* `Stacks.AffineGradedAlgebra.gradedTildePullback_mul_comm`,
  `Stacks.AffineGradedAlgebra.isZero_gradedTildePullback_piece` and
  `Stacks.AffineGradedAlgebra.isQuasicoherent_coprod_gradedTildePullback_piece`: the three
  conditions for `f^* B̃`.
* `Stacks.AffineGradedAlgebra.isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback`:
  **`f^* B̃`, read as a sheaf of commutative `𝒪_X`-algebras, is quasi-coherent** — the datum a
  relative spectrum requires of it.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (g : Z ⟶ X)
  (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-- **The coproduct of the nonnegative-degree pieces of a pulled-back graded algebra is
quasi-coherent** as soon as every piece of the original is: each piece of the pullback is
quasi-coherent by [Stacks, Tag 01BG], and quasi-coherence on a scheme is stable under colimits
of any shape. -/
theorem isQuasicoherent_coprod_gradedPullback_piece
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherent)
    [HasCoproduct fun n : ℕ => (gradedPullback g A).piece (n : ℤ)] :
    (∐ fun n : ℕ => (gradedPullback g A).piece (n : ℤ)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun n : ℕ => (gradedPullback g A).piece (n : ℤ))
    fun n => gradedPullback_isQuasicoherent g A hA (n.as : ℤ)

end Stacks.Conormal

namespace Stacks.AffineGradedAlgebra

variable {X : Scheme.{u}} (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜] (f : X ⟶ Spec (CommRingCat.of A))

/-- **Homogeneous multiplication in `f^* B̃` commutes**, in every pair of degrees: the hypothesis
`hc` of `Stacks.RelativeSpec.gradedAlgebraSheaf` for the graded algebra `𝓑` of
[Stacks, Tag 0897]. -/
theorem gradedTildePullback_mul_comm (i j : ℤ) (W : (Opens ↥X)ᵒᵖ)
    (a : ((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece i).val.obj W)
    (b : ((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece j).val.obj W) :
    HEq (((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).mul i j).app W a b)
      (((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).mul j i).app W b a) :=
  Stacks.Conormal.gradedPullback_mul_comm f (gradedTildeOf A 𝒜)
    (gradedTilde_mul_comm (R := CommRingCat.of A) 𝒜) i j W a b

/-- **The negative-degree pieces of `f^* B̃` vanish**: the hypothesis `hzero` of
`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` for the graded algebra `𝓑` of
[Stacks, Tag 0897]. -/
theorem isZero_gradedTildePullback_piece (n : ℤ) (hn : n < 0) :
    IsZero ((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece n) :=
  Stacks.Conormal.gradedPullback_isZero f (gradedTildeOf A 𝒜)
    (isZero_gradedTilde_piece (R := CommRingCat.of A) 𝒜 n hn)

/-- **The coproduct of the nonnegative-degree pieces of `f^* B̃` is quasi-coherent**: the
hypothesis `hqc` of `Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf` for the graded
algebra `𝓑` of [Stacks, Tag 0897]. -/
theorem isQuasicoherent_coprod_gradedTildePullback_piece
    [HasCoproduct fun n : ℕ =>
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece (n : ℤ)] :
    (∐ fun n : ℕ =>
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece (n : ℤ)).IsQuasicoherent :=
  Stacks.Conormal.isQuasicoherent_coprod_gradedPullback_piece f (gradedTildeOf A 𝒜)
    (gradedTilde_piece_isQuasicoherent (R := CommRingCat.of A) 𝒜)

/-- **`f^* B̃`, read as a sheaf of commutative `𝒪_X`-algebras, is quasi-coherent.** This is the
datum `Stacks.AffineAlgebraEquivalence.relativeSpec` requires of the graded algebra `𝓑` of
[Stacks, Tag 0897], and with `gradedTildePullback_mul_comm` it is everything the passage from a
graded `𝓑`-module to a module on the relative spectrum asks of `𝓑`. -/
theorem isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback
    [HasCoproduct fun n : ℕ =>
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece (n : ℤ)] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (Stacks.RelativeSpec.gradedAlgebraSheaf X
        (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
        (gradedTildePullback_mul_comm A 𝒜 f)) :=
  Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf X _ _
    (isZero_gradedTildePullback_piece A 𝒜 f)
    (isQuasicoherent_coprod_gradedTildePullback_piece A 𝒜 f)

end Stacks.AffineGradedAlgebra

end
