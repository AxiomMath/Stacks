module

public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.FrameSections
public import StacksFrontier.AlgebraicGeometry.SheafDescent.Basic

/-!
# A trivialization written as an isomorphism of sheaves is a sectionwise trivialization

Two spellings of "the invertible module `ℒ` is trivial over the open `U`" are in use in this
development. One is an isomorphism `ℒ|_U ≅ 𝒪_U` of sheaves of modules over the restricted
structure sheaf, which is what the local-freeness data of an invertible module produces
(`AlgebraicGeometry.exists_affine_frame_subset`) and what the local equation of a zero scheme is
read off from (`Stacks.Divisors.frameSections`). The other is
`Stacks.SheafDescent.Trivialization`, a compatible family of `Γ(X, W)`-linear isomorphisms
`Γ(ℒ, W) ≃ Γ(X, W)` for the opens `W` inside `U`, which is the spelling in which the stalk of
`ℒ` is known to be free of rank one (`Stacks.StalkJet.stalkEquiv`).

This file turns the first into the second. The over-site of `U` has one object for each open
`W` inside `U`, so an isomorphism of sheaves of modules over it is already a compatible family
of isomorphisms on sections; all that is needed is to read it as one.

## Main definitions

* `Stacks.Divisors.frameTrivialization`: the sectionwise trivialization of `ℒ` over `U`
  determined by an isomorphism `ℒ|_U ≅ 𝒪_U`.

## Main results

* `Stacks.Divisors.triv_frameTrivialization`: its trivializing map over `U` itself is
  `Stacks.Divisors.frameSections`, so the two formalisms assign the same local equation to a
  section.

## Implementation notes

The over-site of `U` is `Over U` for `U` an object of `X.Opens`, whose objects are morphisms
`h : W ⟶ U`, that is, inclusions `W ≤ U`. Restriction of a sheaf of modules along
`Over.forget U` leaves the modules of sections unchanged, so `Γ(ℒ|_U, (W, h)) = Γ(ℒ, W)` holds
definitionally and no transport appears below; the naturality of the trivialization is the
naturality of the isomorphism at the morphisms of `Over U`.

No `@[stacks]` attribute is attached: this is a change of spelling.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} {L : X.Modules} {U : X.Opens}

/-- **A trivialization `ℒ|_U ≅ 𝒪_U` read as a sectionwise trivialization over `U`**: evaluating
the isomorphism at the object `h : W ⟶ U` of the over-site of `U` gives the `Γ(X, W)`-linear
isomorphism `Γ(ℒ, W) ≃ Γ(X, W)`. -/
def frameTrivialization (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Stacks.SheafDescent.Trivialization X.presheaf L.val U where
  θ W h := ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk h))).mapIso eU).toLinearEquiv
  θ_naturality {W W'} h h' m :=
    PresheafOfModules.naturality_apply
      ((_root_.SheafOfModules.forget (X.ringCatSheaf.over U)).map eU.hom)
      (op (Over.homMk h' (by simp) : Over.mk (h' ≫ h) ⟶ Over.mk h)) m

/-- **The trivializing map of `Stacks.Divisors.frameTrivialization` over `U` is
`Stacks.Divisors.frameSections`**: the two spellings of a trivialization assign the same local
equation to a section. -/
theorem triv_frameTrivialization (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (u : Γ(L, U)) :
    (frameTrivialization eU).θ U (𝟙 U) u = frameSections X L eU u :=
  rfl

end Stacks.Divisors

end
