module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A disjoint union of separated schemes is separated

A coproduct of schemes in `AlgebraicGeometry.Scheme` is a disjoint union: the injections are
open immersions with pairwise disjoint images which jointly cover. This file proves that such a
disjoint union is a separated scheme as soon as each summand is, and in particular that a
disjoint union of affine schemes is separated.

Separatedness is *not* Zariski local on the source, so this is not a formality; what makes it
true is that the open cover of `(∐ Y) ×_{⊤} (∐ Y)` by the `Y a ×_{⊤} Y b` meets the diagonal
only in the pieces with `a = b`. The proof is exactly that observation, read through the
locality of `AlgebraicGeometry.IsClosedImmersion` on the target: the base change of the
diagonal of `∐ Y` along `Y a ×_{⊤} Y b ⟶ (∐ Y) ×_{⊤} (∐ Y)` is `Y a ×_{∐ Y} Y b`, which for
`a = b` is the diagonal of `Y a` — a closed immersion because `Y a` is separated — and for
`a ≠ b` is empty, so that the base change is a closed immersion for the trivial reason that a
morphism out of the empty scheme is one.

## Main results

* `AlgebraicGeometry.sigmaTerminalPullbackMap`: the canonical morphism
  `Y a ×_{⊤} Y b ⟶ (∐ Y) ×_{⊤} (∐ Y)`, a member of the open cover of the latter along which
  the diagonal is examined.
* `AlgebraicGeometry.Scheme.isSeparated_of_iso`: separatedness of a scheme is transported along
  an isomorphism.
* `AlgebraicGeometry.Scheme.isSeparated_sigma`: **a disjoint union of separated schemes is a
  separated scheme.**
* `AlgebraicGeometry.Scheme.isSeparated_sigma_of_isAffine`: a disjoint union of affine schemes
  is a separated scheme.

## Implementation notes

The two identifications of the base change are Mathlib's. For `a = b` it is
`CategoryTheory.Limits.pullback.diagonal_comp`, which factors the diagonal of `Y a ⟶ ⊤` as the
diagonal of `Y a ⟶ ∐ Y` — an isomorphism, the injection being a monomorphism — followed by that
base change; the two isomorphisms are cancelled with
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`. For `a ≠ b` it is
`CategoryTheory.Limits.pullbackDiagonalMapIdIso` together with
`AlgebraicGeometry.isEmpty_pullback_sigmaι_of_ne`.

The index type is allowed to live in any universe, subject only to the smallness that the
coproduct itself requires; no finiteness and no quasi-compactness is used.

No declaration here is tagged: the source of Stacks 0APL, which needs this statement for the
disjoint union of affine schemes supplied by Stacks 03FX, cites no tag for it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- The canonical morphism `Y a ×_{⊤} Y b ⟶ (∐ Y) ×_{⊤} (∐ Y)` induced by the two coproduct
injections. The family of these morphisms is the open cover of `(∐ Y) ×_{⊤} (∐ Y)` along which
the diagonal of `∐ Y` is examined in
`AlgebraicGeometry.Scheme.isSeparated_sigma`; it is the member of
`AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight` at `(a, b)`. -/
noncomputable def sigmaTerminalPullbackMap {σ : Type v} [Small.{u} σ] (Y : σ → Scheme.{u})
    (a b : σ) :
    pullback (Sigma.ι Y a ≫ terminal.from (∐ Y)) (Sigma.ι Y b ≫ terminal.from (∐ Y)) ⟶
      pullback (terminal.from (∐ Y)) (terminal.from (∐ Y)) :=
  pullback.map _ _ _ _ (Sigma.ι Y a) (Sigma.ι Y b) (𝟙 _) (Category.comp_id _) (Category.comp_id _)

namespace Scheme

/-- Separatedness of a scheme is transported along an isomorphism: the morphism to the terminal
object of the target factors through that of the source. -/
theorem isSeparated_of_iso {X X' : Scheme.{u}} (e : X ≅ X') (hX : X.IsSeparated) :
    X'.IsSeparated := by
  have := hX
  refine ⟨?_⟩
  rw [← terminal.comp_from e.inv]
  infer_instance

/-- **A disjoint union of separated schemes is a separated scheme.**

The open cover of `(∐ Y) ×_{⊤} (∐ Y)` by the `Y a ×_{⊤} Y b` reduces the claim, by locality of
`AlgebraicGeometry.IsClosedImmersion` on the target, to the base change of the diagonal along
each `AlgebraicGeometry.sigmaTerminalPullbackMap`. That base change is `Y a ×_{∐ Y} Y b`: the
diagonal of `Y a` when `a = b`, and empty otherwise. -/
theorem isSeparated_sigma {σ : Type v} [Small.{u} σ] (Y : σ → Scheme.{u})
    (hY : ∀ j, (Y j).IsSeparated) : (∐ Y).IsSeparated := by
  refine ⟨⟨?_⟩⟩
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover Y) (sigmaOpenCover Y)
      (terminal.from (∐ Y)) (terminal.from (∐ Y))) ?_
  rintro ⟨a, b⟩
  show IsClosedImmersion
    (pullback.snd (pullback.diagonal (terminal.from (∐ Y))) (sigmaTerminalPullbackMap Y a b))
  by_cases hab : a = b
  · subst hab
    have hoi : IsOpenImmersion (Sigma.ι Y a) := (sigmaOpenCover Y).map_prop a
    have hd : IsClosedImmersion (pullback.diagonal (terminal.from (Y a))) :=
      (hY a).isSeparated_terminal_from.isClosedImmersion_diagonal
    rw [← terminal.comp_from (Sigma.ι Y a), pullback.diagonal_comp,
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion] at hd
    exact hd
  · have he : IsEmpty ↑(pullback (pullback.diagonal (terminal.from (∐ Y)))
        (sigmaTerminalPullbackMap Y a b)) :=
      ⟨fun x ↦ (isEmpty_pullback_sigmaι_of_ne Y hab).elim
        ((pullbackDiagonalMapIdIso (Sigma.ι Y a) (Sigma.ι Y b) (terminal.from (∐ Y))).hom x)⟩
    infer_instance

/-- **A disjoint union of affine schemes is a separated scheme.** This is the form in which the
middle paragraph of Stacks 0APL needs `AlgebraicGeometry.Scheme.isSeparated_sigma`: Stacks 03FX
provides a surjective étale atlas whose underlying scheme is a disjoint union of affine schemes,
and Stacks 03FZ asks only that that scheme be separated. -/
theorem isSeparated_sigma_of_isAffine {σ : Type v} [Small.{u} σ] (Y : σ → Scheme.{u})
    (hY : ∀ j, IsAffine (Y j)) : (∐ Y).IsSeparated :=
  isSeparated_sigma Y fun j ↦ have := hY j; inferInstance

end Scheme

end AlgebraicGeometry

end
