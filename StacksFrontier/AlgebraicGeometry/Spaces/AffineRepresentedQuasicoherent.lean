module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# Quasi-coherent modules on an affine representable algebraic space

Let `U` be an object of the big fppf site over a scheme `S` whose underlying scheme `T` is
affine. Modules over the ring `Γ(T, ⊤)` of global functions are the quasi-coherent `𝒪`-modules
on the small étale site of the algebraic space `yoneda.obj U`. This is the affine case of
[Stacks, Tag 03DX] part (2) read on the small étale site of an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.affineRepresentedQuasicoherentModulesEquivalence` is the equivalence
  `Mod(Γ(T, ⊤)) ≌ QCoh(𝒪_{yoneda.obj U})`.

## Implementation notes

The equivalence is the composite of the affine reconstruction
`AlgebraicGeometry.affineQuasicoherentModulesEquiv` with
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)

/-- **Modules over the ring of global functions of an affine representable algebraic space are
its quasi-coherent `𝒪`-modules.**  Let `U` be an object of the big fppf site over `S` whose
underlying scheme `T` is affine.  Then `Mod(Γ(T, ⊤)) ≌ QCoh(𝒪_{yoneda.obj U})`, with modules in
the scheme universe `u` on both sides. -/
noncomputable def affineRepresentedQuasicoherentModulesEquivalence
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ≌
      Space.QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  letI := hU
  (_root_.AlgebraicGeometry.affineQuasicoherentModulesEquiv
      ((BigFppfOver.toScheme B S hS).obj U)).trans
    (representedQuasicoherentSchemeEquivalence B S hS U)

end AlgebraicGeometry.Space

end
