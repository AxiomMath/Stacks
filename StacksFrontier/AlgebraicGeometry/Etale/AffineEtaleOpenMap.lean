module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import StacksFrontier.AlgebraicGeometry.Etale.AffineReducedFibre

/-!
# An étale morphism of affine schemes is open on prime spectra

For `f : E' ⟶ S` étale with `E'` and `S` affine, the map of prime spectra induced by the pullback
of global functions along `f` is open.

The map in question is `PrimeSpectrum \Gamma(E', ⊤) ⟶ PrimeSpectrum \Gamma(S, ⊤)`, the map of
prime spectra of the rings of global functions, as opposed to the map of underlying topological
spaces of the schemes.

## Main results

* `AlgebraicGeometry.isOpenMap_comap_appTop_of_etale`: for `f : E' ⟶ S` étale between affine
  schemes, the map of prime spectra induced by `f.appTop` is open.

## Implementation notes

The proof is algebraic: for affine source and target, `f` being étale makes the map on global
functions an étale ring map (`AlgebraicGeometry.HasRingHomProperty.appTop` and
`RingHom.etale_algebraMap`), an étale algebra is flat and of finite presentation, flatness gives
going down (`Algebra.HasGoingDown.of_flat`), and going down together with finite presentation
gives openness by Stacks 00I1,
`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`. Passing instead through
openness of the morphism of schemes would need the comparison of the scheme's space with the
prime spectrum of its ring of functions, which this route avoids.

No `stacks` tag is claimed: Stacks 00I1 is tagged in Mathlib at the lemma used, and the
specialisation to the étale case adds no clause of a tag.

## References

* [Stacks Project, Tag 00I1](https://stacks.math.columbia.edu/tag/00I1)
* [Stacks Project, Tag 02GH](https://stacks.math.columbia.edu/tag/02GH)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **An étale morphism of affine schemes is open on prime spectra.** For `f : E' ⟶ S` étale
with `E'` and `S` affine, the map of prime spectra induced by the pullback of global functions
along `f` is an open map. -/
theorem isOpenMap_comap_appTop_of_etale {E' S : Scheme.{u}} [IsAffine E'] [IsAffine S]
    (f : E' ⟶ S) [Etale f] :
    letI : Algebra Γ(S, ⊤) Γ(E', ⊤) := f.appTop.hom.toAlgebra
    IsOpenMap (PrimeSpectrum.comap (algebraMap Γ(S, ⊤) Γ(E', ⊤))) := by
  let : Algebra Γ(S, ⊤) Γ(E', ⊤) := f.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(S, ⊤) Γ(E', ⊤) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.appTop (P := @Etale) f inferInstance)
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end AlgebraicGeometry

end
