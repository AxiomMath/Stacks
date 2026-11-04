module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Quasi-coherence of the pullback of an algebra sheaf, from one isomorphism

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`.
Its pullback `AlgebraicGeometry.Space.algebraPullback` is the `𝒪_Y`-algebra
`𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A`, built as a pushout of sheaves of commutative rings.

Quasi-coherence of an algebra sheaf is quasi-coherence of its underlying sheaf of modules
(`AlgebraicGeometry.Space.AlgebraSheaf.IsQuasicoherent`), and the pullback of a quasi-coherent
module along an arbitrary morphism of algebraic spaces is quasi-coherent (Stacks 03GA). So the
pullback of a quasi-coherent algebra sheaf is quasi-coherent as soon as the `𝒪_Y`-module underlying
the pushout is identified with the module pullback of the `𝒪_X`-module underlying `A`. Stacks 03GA
concerns modules only; the algebra case enters the relative spectrum of Stacks 081V and, for
schemes, of Stacks 01SA.

This is the space-level analogue of
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso`, the same
statement for a morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_algebraPullback_of_underlyingModuleIso`: if the module
  underlying `g^*A` is isomorphic to the module pullback of the module underlying `A`, the
  pullback of a quasi-coherent algebra sheaf `A` is quasi-coherent.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Quasi-coherence of the pullback of a quasi-coherent algebra sheaf.**  If the
`𝒪_Y`-module underlying the algebra `𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A` is the pullback along `g` of the
`𝒪_X`-module underlying a quasi-coherent `A`, then that algebra is quasi-coherent. -/
theorem isQuasicoherent_algebraPullback_of_underlyingModuleIso (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    (e : (modulePullback B S hS g).obj (AlgebraSheaf.underlyingModule A) ≅
      AlgebraSheaf.underlyingModule ((algebraPullback B S hS g).obj A)) :
    ((algebraPullback B S hS g).obj A).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso e
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g
      (AlgebraSheaf.underlyingModule A) hA)

end AlgebraicGeometry.Space

end
