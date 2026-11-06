module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# The conormal module of a morphism of first-order thickenings of algebraic spaces

Let
```
X --⊆--→ X'
|        |
f        f'
↓        ↓
Y --⊆--→ Y'
```
be a morphism of first-order thickenings of algebraic spaces over a scheme `S` contained in a
big fppf site `B`. If `f'` is flat and `X = Y ×_{Y'} X'`, then the canonical map
`f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of conormal modules is an isomorphism.

Here `X = Y ×_{Y'} X'` is expressed by taking the upper closed subspace to be the inverse image
`g⁻¹(Y) ⊆ X'` and the vertical morphism to be the projection. Flatness of `f'` is flatness of the
induced morphism of small étale ringed topoi, `AlgebraicGeometry.RingedToposHom.IsFlat`. The
statement takes both first-order thickening conditions, on `Y ⊆ Y'` and on `g⁻¹(Y) ⊆ X'`, as
hypotheses, and does not assume `f` flat.

## Main results

* `AlgebraicGeometry.Space.isIso_conormalMap_preimage_iff_mono`: at a fibre product square the
  canonical map of conormal modules is an isomorphism exactly when it is a monomorphism.
* `AlgebraicGeometry.Space.isIso_conormalMap_firstOrderThickening_of_isFlat`: for a flat
  morphism of first-order thickenings with cartesian square, the canonical map of conormal modules
  is an isomorphism.

## References

* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') (Y : ClosedSubspaces B S hS Y'.1)

/-- At the fibre product square of a morphism `g : X' ⟶ Y'` and a closed subspace `Y ⊆ Y'`, the
canonical map of conormal modules `f^*𝒞_{Y/Y'} ⟶ 𝒞_{g⁻¹(Y)/X'}` is an isomorphism exactly when it
is a monomorphism. -/
theorem isIso_conormalMap_preimage_iff_mono :
    IsIso (conormalMap B S hS (preimageSubspace B S hS g Y) Y g
        (preimageProjection B S hS g Y)
        (conormalEtaleRestrictionSquare B S hS g Y)) ↔
      Mono (conormalMap B S hS (preimageSubspace B S hS g Y) Y g
        (preimageProjection B S hS g Y)
        (conormalEtaleRestrictionSquare B S hS g Y)) := by
  have := epi_conormalMap B S hS g Y
  exact ⟨fun _ => IsIso.mono_of_iso _, fun _ => isIso_of_mono_of_epi _⟩

/-- Let `(f, f') : (X ⊆ X') → (Y ⊆ Y')` be a morphism of first-order thickenings of algebraic
spaces in which `X = Y ×_{Y'} X'`, that is in which the upper closed subspace is the inverse image
`g⁻¹(Y)` of the lower one along `g = f'` and `f` is the projection. If `f'` is flat, as a morphism
of small étale ringed topoi, then the canonical map of conormal modules `f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}`
is an isomorphism. The first-order thickening conditions on `Y ⊆ Y'` and on `g⁻¹(Y) ⊆ X'` are
taken as hypotheses. -/
@[stacks 06BH "(1) implies (2), with f' flat as a morphism of small etale ringed topoi"]
theorem isIso_conormalMap_firstOrderThickening_of_isFlat
    (_hY : IsFirstOrderThickening B S hS Y' Y.1)
    (_hX : IsFirstOrderThickening B S hS X' (preimageSubspace B S hS g Y).1)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    IsIso (conormalMap B S hS (preimageSubspace B S hS g Y) Y g
      (preimageProjection B S hS g Y)
      (conormalEtaleRestrictionSquare B S hS g Y)) :=
  isIso_conormalMap_of_isFlat B S hS g Y hg

end AlgebraicGeometry.Space

end
