module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversallyClosed.IntegralPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The intermediate scheme of the Stein factorization is a relative spectrum

Let `f : X ⟶ S` be a universally closed, quasi-separated morphism of schemes, so that `f`
factors as `X --f'--> S' --π--> S` with `S' = f.normalization` the normalization of `S` in `X`.
This module identifies `S'`, as a scheme over `S`, with the relative spectrum
`Spec_S(f_* 𝒪_X)` of the pushed-forward structure sheaf, and identifies the first factor `f'`
with the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` of [Stacks, Tag 01LY].

## Main results

* `Stacks.SteinFactorization.overIsoPushforwardSpectrum`: the identification over `S` of the
  intermediate scheme with `Spec_S(f_* 𝒪_X)`.
* `Stacks.SteinFactorization.toNormalization_overIsoPushforwardSpectrum_hom_left`: that
  identification carries the first factor to the canonical morphism.
* `Stacks.SteinFactorization.overIsoPushforwardSpectrum_of_isProper` and
  `Stacks.SteinFactorization.toNormalization_overIsoPushforwardSpectrum_hom_left_of_isProper`:
  the same two statements for a proper morphism.

## Implementation notes

The identification of the schemes is `AlgebraicGeometry.normalizationIsoPushforwardSpectrum`,
[Stacks, Tag 03GQ]; what is added here is that it is an isomorphism *over* `S`, which is what
turns it into a comparison of factorizations rather than of bare schemes.  Being an isomorphism
in `CategoryTheory.Over S` says exactly that it carries `π` to the structure morphism of the
relative spectrum, and the accompanying equation says that it carries `f'` to the canonical
morphism; together these say that the factorization of `f` through the normalization *is* its
factorization through `Spec_S(f_* 𝒪_X)`.

## References

* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 03GQ](https://stacks.math.columbia.edu/tag/03GQ)
* [Stacks Project, Tag 01LY](https://stacks.math.columbia.edu/tag/01LY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.RelativeSpec (canonicalMorphism pushforwardSpectrum)

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}} (f : X ⟶ S)

section UniversallyClosed

variable [UniversallyClosed f] [QuasiSeparated f]

/-- **Stacks Project, Tag 03GY (relative_spectrum).**  Clause (4) of the factorization of a
universally closed, quasi-separated morphism `f : X ⟶ S`: the intermediate scheme `S'` of the
factorization is, as a scheme over `S`, the relative spectrum `Spec_S(f_* 𝒪_X)` of the
pushed-forward structure sheaf.  Being an isomorphism over `S` is the statement that the second
factor `π : S' ⟶ S` becomes the structure morphism of the relative spectrum. -/
@[stacks 03GY "relative_spectrum",
  ega "III 7.8.10" "partial",
  sga "1 X 1.2" "Y′ ≅ Spec f_*O_X over Y",
  sga "6 XII 2.5" "partial"]
public noncomputable def overIsoPushforwardSpectrum :
    Over.mk f.fromNormalization ≅ Over.mk (pushforwardSpectrum f).toBase :=
  Over.isoMk (normalizationIsoPushforwardSpectrum f)
    (normalizationIsoPushforwardSpectrum_hom_comp_toBase f)

/-- **Stacks Project, Tag 03GY (relative_spectrum).**  Under the identification of the
intermediate scheme of the factorization with `Spec_S(f_* 𝒪_X)`, the first factor
`f' : X ⟶ S'` becomes the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` of [Stacks, Tag 01LY]. -/
@[stacks 03GY "relative_spectrum",
  ega "III 7.8.10" "partial",
  sga "1 X 1.2" "Under Y′ ≅ Spec f_*O_X",
  sga "6 XII 2.5" "partial"]
public theorem toNormalization_overIsoPushforwardSpectrum_hom_left :
    f.toNormalization ≫ (overIsoPushforwardSpectrum f).hom.left = canonicalMorphism f :=
  toNormalization_normalizationIsoPushforwardSpectrum_hom f

end UniversallyClosed

section Proper

variable [IsProper f]

/-- **Stacks Project, Tag 03H2 (relative_spectrum).**  Clause (4) of the factorization of a
proper morphism `f : X ⟶ S`: the intermediate scheme `S'` of the factorization is, as a scheme
over `S`, the relative spectrum `Spec_S(f_* 𝒪_X)` of the pushed-forward structure sheaf. -/
@[stacks 03H2 "relative_spectrum",
  ega "III 7.8.10" "partial",
  sga "1 X 1.2" "Y′ ≅ Spec f_*O_X over Y",
  sga "6 XII 2.5" "partial"]
public noncomputable def overIsoPushforwardSpectrum_of_isProper :
    Over.mk f.fromNormalization ≅ Over.mk (pushforwardSpectrum f).toBase :=
  overIsoPushforwardSpectrum f

/-- **Stacks Project, Tag 03H2 (relative_spectrum).**  Under the identification of the
intermediate scheme of the factorization of a proper morphism with `Spec_S(f_* 𝒪_X)`, the first
factor `f' : X ⟶ S'` becomes the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` of
[Stacks, Tag 01LY]. -/
@[stacks 03H2 "relative_spectrum",
  ega "III 7.8.10" "partial",
  sga "1 X 1.2" "Under Y′ ≅ Spec f_*O_X",
  sga "6 XII 2.5" "partial"]
public theorem toNormalization_overIsoPushforwardSpectrum_hom_left_of_isProper :
    f.toNormalization ≫ (overIsoPushforwardSpectrum_of_isProper f).hom.left =
      canonicalMorphism f :=
  toNormalization_overIsoPushforwardSpectrum_hom_left f

end Proper

end Stacks.SteinFactorization
