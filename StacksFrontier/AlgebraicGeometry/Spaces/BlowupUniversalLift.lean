module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup

/-!
# The blowup of an algebraic space as a lifting property

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z ⊆ X` be a closed
subspace.  A morphism `b : X' ⟶ X` is the blowup of `X` in `Z` when it is a final object of the
category `𝒞` of algebraic spaces over `X` on which the inverse image of `Z` is an effective
Cartier divisor; this is `AlgebraicGeometry.Space.IsBlowupAlong`.

Finality in `𝒞` is restated here as the lifting property it is used by: for every `y : Y ⟶ X`
on which the inverse image of `Z` is an effective Cartier divisor there is exactly one
`l : Y ⟶ X'` over `X`.  Both directions are recorded, since the consumers need both — the
blowup is recognized by the lifting property, and once recognized it is applied through it.

## Main results

* `AlgebraicGeometry.Space.IsBlowupAlong.existsUnique_lift`: the blowup of `X` in `Z` admits a
  unique morphism from any algebraic space over `X` on which the inverse image of `Z` is an
  effective Cartier divisor, commuting with the morphisms to `X`.
* `AlgebraicGeometry.Space.isBlowupAlong_of_existsUnique_lift`: conversely, a morphism
  `b : X' ⟶ X` on which the inverse image of `Z` is an effective Cartier divisor and which has
  that unique-lifting property is the blowup of `X` in `Z`.
* `AlgebraicGeometry.Space.isBlowupAlong_iff_existsUnique_lift`: the two conditions agree.

## Implementation notes

An object of the category `𝒞 = AlgebraicGeometry.Space.CartierOver` is a pair of an object `Y`
of `Over X` and a proof that the inverse image of `Z` along `Y.hom` is an effective Cartier
divisor, and a morphism of `𝒞` is a morphism of `Over X`; so the datum of a morphism of `𝒞`
into the blowup is exactly a morphism `Y.left ⟶ X'` of algebraic spaces with `l ≫ b = Y.hom`,
and terminality is exactly its existence and uniqueness.  No property of `Z` beyond being a
closed subspace is used.

## References

* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X X' : AlgebraicSpaces B S hS}

/-- **The universal property of the blowup, Stacks 085U, as a lifting property.**

If `b : X' ⟶ X` is the blowup of `X` in the closed subspace `Z` and `y : Y ⟶ X` is a morphism of
algebraic spaces along which the inverse image of `Z` is an effective Cartier divisor on `Y`,
then there is exactly one morphism `l : Y ⟶ X'` with `l ≫ b = y`.

This is finality of `b` in the category `𝒞` of Stacks 085U read on objects and morphisms. -/
theorem IsBlowupAlong.existsUnique_lift {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b) {Y : AlgebraicSpaces B S hS} (y : Y ⟶ X)
    (hy : IsPullbackDefined B S hS y Z) :
    ∃! l : Y ⟶ X', l ≫ b = y := by
  obtain ⟨hb', ⟨t⟩⟩ := hb
  refine ⟨(t.from (⟨Over.mk y, hy⟩ : CartierOver B S hS Z)).hom.left, Over.w _, fun m hm => ?_⟩
  exact congrArg (fun φ : (⟨Over.mk y, hy⟩ : CartierOver B S hS Z) ⟶ ⟨Over.mk b, hb'⟩ =>
      φ.hom.left)
    (t.hom_ext (ObjectProperty.homMk (Over.homMk m hm)) (t.from _))

/-- **Recognizing the blowup by its lifting property.**

A morphism `b : X' ⟶ X` along which the inverse image of the closed subspace `Z` is an effective
Cartier divisor, and through which every morphism to `X` with that same property factors
uniquely, is the blowup of `X` in `Z`: it is a final object of the category `𝒞` of
Stacks 085U. -/
theorem isBlowupAlong_of_existsUnique_lift {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X}
    (hb : IsPullbackDefined B S hS b Z)
    (H : ∀ (Y : AlgebraicSpaces B S hS) (y : Y ⟶ X), IsPullbackDefined B S hS y Z →
      ∃! l : Y ⟶ X', l ≫ b = y) :
    IsBlowupAlong B S hS Z b := by
  refine ⟨hb, ⟨IsTerminal.ofUniqueHom (fun W => ObjectProperty.homMk
    (Over.homMk (H W.1.left W.1.hom W.2).choose
      (H W.1.left W.1.hom W.2).choose_spec.1)) ?_⟩⟩
  intro W m
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  exact (H W.1.left W.1.hom W.2).choose_spec.2 m.hom.left (Over.w m.hom)

/-- **Stacks 085U, in the form its consumers use.** A morphism `b : X' ⟶ X` is the blowup of `X`
in a closed subspace `Z` exactly when the inverse image of `Z` is an effective Cartier divisor on
`X'` and every morphism to `X` with that property factors uniquely through `b`. -/
theorem isBlowupAlong_iff_existsUnique_lift {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} :
    IsBlowupAlong B S hS Z b ↔
      IsPullbackDefined B S hS b Z ∧
        ∀ (Y : AlgebraicSpaces B S hS) (y : Y ⟶ X), IsPullbackDefined B S hS y Z →
          ∃! l : Y ⟶ X', l ≫ b = y :=
  ⟨fun hb => ⟨hb.isPullbackDefined, fun _ y hy => hb.existsUnique_lift y hy⟩,
    fun h => isBlowupAlong_of_existsUnique_lift h.1 h.2⟩

end AlgebraicGeometry.Space

end
