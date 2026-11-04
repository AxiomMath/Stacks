module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# Quasi-coherent modules on a spectrum, read on the algebraic space it represents

Let `B` be a big fppf site over a scheme `S` and let `U` be an object of `B` whose underlying
scheme is the spectrum of a ring `R`.  Then the quasi-coherent `𝒪`-modules on the small étale
site of the algebraic space `yoneda.obj U` are exactly the `R`-modules.

This is the composite of two comparisons that the development already has and never put
together:

* `AlgebraicGeometry.tildeEquiv`, the affine case of the description of quasi-coherent modules
  in terms of modules — `M ↦ M̃` is an equivalence `Mod(R) ≌ QCoh(𝒪_{Spec R})` on the *Zariski*
  site of `Spec R`; and
* `AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence`, which carries the
  quasi-coherent modules on the Zariski site of the scheme underlying `U` to the quasi-coherent
  modules on the small étale site of `yoneda.obj U`.  That one is itself the composite of
  Stacks 03DX (2) at `τ = étale` with the equivalence of small étale sites of a represented
  algebraic space, and it is unconditional.

## Main definitions

* `AlgebraicGeometry.Space.representedSpecQuasicoherentSheavesEquivalence`: **the equivalence
  `Mod(R) ≌ QCoh(𝒪_{yoneda.obj U})`** for an object `U` of the big fppf site whose underlying
  scheme is `Spec R`.

## Main results

* `AlgebraicGeometry.Space.representedSpecQuasicoherentSheavesEquivalence_functor` and
  `AlgebraicGeometry.Space.representedSpecQuasicoherentSheavesEquivalence_inverse`: the two
  halves of the equivalence are the two composites of the halves of its two factors.  They pin
  the equivalence down: a functor built from `M ↦ M̃` followed by the reading on the represented
  algebraic space is this one, which is what lets a *named* functor — rather than an abstract
  equivalence — be transported across it.

## Implementation notes

The hypothesis is an **equality** `(BigFppfOver.toScheme B S hS).obj U = Spec R`, not an
isomorphism, and that is deliberate.  The categories of quasi-coherent modules on the two sides
depend on the scheme through its structure sheaf, so an isomorphism of schemes would have to be
turned into an equivalence of module categories by inverse image, and the only version of that
transport in the tree is private to
`StacksFrontier/AlgebraicGeometry/FunctorsAndMorphisms/IntegralTransformQcoh/Equivalence.lean`.
With an equality the transport is `Eq.mpr` and costs nothing.  The equality is also the shape in
which the hypothesis actually arises: in the affine case of formal glueing the two spaces *are*
`Spec R` and `Spec S`, and each `D(f_i)` *is* the spectrum of a localization, so nothing has to
be transported along an isomorphism of schemes to use this.

No `stacks` attribute is claimed.  Both factors carry their own registrations — Stacks 01I7 for
the affine description of quasi-coherent modules and Stacks 03DX for the passage to the small
étale site — and their composite is a convenience for the consumers below, not a further result
of the Stacks project.

## References

* [Stacks Project, Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quasi-coherent modules on the algebraic space represented by a spectrum are modules
over the ring.**  If the scheme underlying an object `U` of the big fppf site is `Spec R`, then
`QCoh(𝒪_{yoneda.obj U})` is equivalent to `Mod(R)`.

The equivalence is `M ↦ M̃` on the Zariski site of `Spec R`, followed by the reading of a
quasi-coherent module on the small étale site of the represented algebraic space. -/
def representedSpecQuasicoherentSheavesEquivalence (R : CommRingCat.{u})
    (U : BigFppfOver B S hS) (hU : (BigFppfOver.toScheme B S hS).obj U = Spec R) :
    ModuleCat.{u} R ≌ QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  (hU ▸ AlgebraicGeometry.tildeEquiv (R := R)).trans
    (representedQuasicoherentSheavesEquivalence B S hS U)

/-- The functor of `AlgebraicGeometry.Space.representedSpecQuasicoherentSheavesEquivalence` is
`M ↦ M̃` followed by the reading on the represented algebraic space. -/
theorem representedSpecQuasicoherentSheavesEquivalence_functor (R : CommRingCat.{u})
    (U : BigFppfOver B S hS) (hU : (BigFppfOver.toScheme B S hS).obj U = Spec R) :
    (representedSpecQuasicoherentSheavesEquivalence B S hS R U hU).functor =
      (hU ▸ AlgebraicGeometry.tildeEquiv (R := R)).functor ⋙
        (representedQuasicoherentSheavesEquivalence B S hS U).functor :=
  rfl

/-- The inverse of
`AlgebraicGeometry.Space.representedSpecQuasicoherentSheavesEquivalence` takes global sections on
the represented algebraic space and reads the result as an `R`-module. -/
theorem representedSpecQuasicoherentSheavesEquivalence_inverse (R : CommRingCat.{u})
    (U : BigFppfOver B S hS) (hU : (BigFppfOver.toScheme B S hS).obj U = Spec R) :
    (representedSpecQuasicoherentSheavesEquivalence B S hS R U hU).inverse =
      (representedQuasicoherentSheavesEquivalence B S hS U).inverse ⋙
        (hU ▸ AlgebraicGeometry.tildeEquiv (R := R)).inverse :=
  rfl

end AlgebraicGeometry.Space

end
