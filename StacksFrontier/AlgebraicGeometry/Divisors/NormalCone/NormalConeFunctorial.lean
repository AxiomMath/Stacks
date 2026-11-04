module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalPushforward
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic

/-!
# The morphism of normal cones over a commutative square of immersions

Let `i : Z ⟶ X` and `i' : Y ⟶ X'` be immersions and let `f : Z ⟶ Y` carry a morphism of conormal
graded algebras `AlgebraicGeometry.ConormalAlgebraHom i i' f` — produced over a commutative square
by `AlgebraicGeometry.conormalAlgebraHom` of [Stacks, Tag 0634]. This file builds from it the
morphism of normal cones

`C_ZX ⟶ C_{Y}X'`

over `f`, and identifies its composite with the projection of `C_{Y}X'`.

For a nested pair `Z ⊆ Y ⊆ X` inside one ambient scheme, taking `i` the composite immersion, `i'`
the immersion of `Y`, `f` the immersion of `Z` into `Y` and `g := 𝟙 X`,
`Stacks.Conormal.normalConeMapOfFactorization` is the resulting `C_ZX ⟶ C_YX`.

## Main definitions

* `Stacks.Conormal.normalConeSituation`: the relative-spectrum situation of `𝒞_{Z/X,*}` on `Z`,
  whose glued spectrum is `C_ZX` on the nose.
* `Stacks.Conormal.normalConePushforwardHom`: the algebra map
  `𝒞_{Y/X',*} ⟶ (C_ZX ⟶ Y)_* 𝒪_{C_ZX}` that the universal property of `C_{Y}X'` consumes.
* `Stacks.Conormal.normalConeMap`: **the morphism `C_ZX ⟶ C_{Y}X'`** attached to a morphism of
  conormal graded algebras along `f`.
* `Stacks.Conormal.normalConeMapOfSquare`: **the canonical morphism of normal cones over a
  commutative square of immersions**, the previous one at the canonical map of graded algebras of
  [Stacks, Tag 0634].
* `Stacks.Conormal.normalConeMapOfFactorization`: the square at `g := 𝟙 X`, i.e. **the canonical
  `C_ZX ⟶ C_YX` of a nested pair of immersions** in one ambient scheme.

## Main results

* `Stacks.Conormal.normalConeMap_toBase`, `normalConeMapOfSquare_toBase` and
  `normalConeMapOfFactorization_toBase`: **the morphism of normal cones lies over `f`** — its
  composite with the projection `C_{Y}X' ⟶ Y` is the projection `C_ZX ⟶ Z` followed by `f`.

## Implementation notes

**The universal property, not a map on relative spectra.** The relative spectrum of this library
has no functorial action on morphisms of algebra sheaves over *different* bases;
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom` compares two algebras on one base. What is
available is representability, [Stacks, Tag 01LV]: a morphism `T ⟶ C_YX` is a pair of a morphism
`T ⟶ Y` and an algebra map `𝒞_{Y/X,*} ⟶ (T ⟶ Y)_* 𝒪_T`, and the base morphism is *data* in that
pair, so nothing forces `T` to lie over `Y` beforehand. Taking `T := C_ZX` and the base morphism
to be the projection followed by `f`, the algebra map required is exactly
`Stacks.Conormal.conormalAlgebraSheafPushforwardHom` once `𝒪_{C_ZX}` pushed to `Z` is identified
with `𝒞_{Z/X,*}`, which is [Stacks, Tag 01LX] part (3)
(`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`).

**No transport appears.** The direct image along `f` of the direct image along the projection is
the direct image along the composite,
`Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra`, by `rfl`; and `C_ZX` and
its projection are the scheme and the structure morphism of the glued spectrum of
`Stacks.Conormal.normalConeSituation` by `rfl`. So the two ends of the composite below meet on the
nose and no comparison isomorphism is inserted anywhere.

**Two ambient schemes, and the one-ambient pitfall.** The construction never mentions the ambient
scheme, so it is stated for `i : Z ⟶ X` and `i' : Y ⟶ X'` throughout, matching
`AlgebraicGeometry.ConormalAlgebraHom`. The hazard is mixing the two conventions: feeding an
`i' : Y ⟶ X'` to a lemma stated at one ambient forces the elaborator to unify `X'` with `X`
underneath `Stacks.Conormal.conormalAlgebraSheaf`, and that does not fail cleanly — it runs out of
heartbeats in `whnf`. `Stacks.Conormal.conormalAlgebraSheafPushforwardHom` is therefore stated at
two ambients as well, and no declaration on this path is stated at one.

## References

* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Conormal

open Stacks.RelativeSpec

variable {Z X Y X' : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X') (f : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i']

section

variable [hci : (conormalAlgebraSheaf i).IsQuasicoherent]

/-- The relative-spectrum situation of the conormal algebra `𝒞_{Z/X,*}` on `Z`. Its glued
spectrum is the normal cone `C_ZX` and its structure morphism the projection `C_ZX ⟶ Z`, both by
`rfl`. -/
abbrev normalConeSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  { base := Z, algebra := conormalAlgebraSheaf i }

/-- **The normal cone is the glued spectrum of its situation.** -/
theorem normalCone_eq_gluedSpectrum :
    normalCone i = (gluedSpectrum (normalConeSituation i)).scheme := rfl

/-- **The projection of the normal cone is the structure morphism of its glued spectrum.** -/
theorem normalConeToBase_eq_gluedSpectrum_toBase :
    normalConeToBase i = (gluedSpectrum (normalConeSituation i)).toBase := rfl

end

/-! ### The algebra map the universal property consumes -/

variable (H : ConormalAlgebraHom i i' f)
  [hci : (conormalAlgebraSheaf i).IsQuasicoherent]

/-- **The algebra map `𝒞_{Y/X,*} ⟶ (C_ZX ⟶ Y)_* 𝒪_{C_ZX}`.** It is the bridge
`Stacks.Conormal.conormalAlgebraSheafPushforwardHom` followed by the direct image along `f` of
the identification of `𝒞_{Z/X,*}` with the pushed-forward structure sheaf of `C_ZX`, which is
[Stacks, Tag 01LX] part (3). The target is the direct image along the composite because the
direct image of a direct image is the direct image of the composite by `rfl`. -/
def normalConePushforwardHom :
    conormalAlgebraSheaf i' ⟶ pushforwardAlgebra (normalConeToBase i ≫ f) :=
  conormalAlgebraSheafPushforwardHom i i' f H ≫
    (algebraPushforward f).map (pushforwardAlgebraIso (conormalAlgebraSheaf i)).inv

/-! ### The morphism of normal cones -/

variable [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- **The morphism of normal cones `C_ZX ⟶ C_YX`** attached to a morphism of conormal graded
algebras along `f : Z ⟶ Y`.

By representability of the relative-spectrum functor ([Stacks, Tag 01LV]) a morphism into `C_YX`
is a morphism to `Y` together with an algebra map out of `𝒞_{Y/X,*}` into its direct image; here
the morphism to `Y` is the projection `C_ZX ⟶ Z` followed by `f`, and the algebra map is
`Stacks.Conormal.normalConePushforwardHom`. -/
def normalConeMap : normalCone i ⟶ normalCone i' :=
  pairToHom (s := normalConeSituation i')
    ⟨normalConeToBase i ≫ f,
      (conormalAlgebraSheaf i').pairHomEquiv (normalConeToBase i ≫ f)
        (normalConePushforwardHom i i' f H)⟩

/-- **The morphism of normal cones lies over `f`**: its composite with the projection
`C_YX ⟶ Y` is the projection `C_ZX ⟶ Z` followed by `f`. This is the base clause of the pair that
defines it, `Stacks.RelativeSpec.pairToHom_toBase`. -/
theorem normalConeMap_toBase :
    normalConeMap i i' f H ≫ normalConeToBase i' = normalConeToBase i ≫ f :=
  pairToHom_toBase (s := normalConeSituation i') _

end Stacks.Conormal

namespace Stacks.Conormal

/-! ### The canonical morphism over a commutative square -/

section Square

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
  [IsImmersion i] [IsImmersion i']
  [(conormalAlgebraSheaf i).IsQuasicoherent] [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- **The canonical morphism of normal cones over a commutative square of immersions**: the
morphism `C_ZX ⟶ C_{Z'}X'` over `f` induced by the canonical map of conormal graded algebras of
[Stacks, Tag 0634]. -/
def normalConeMapOfSquare (comm : f ≫ i' = i ≫ g) : normalCone i ⟶ normalCone i' :=
  normalConeMap i i' f (conormalAlgebraHom i i' f g comm).hom

/-- **The canonical morphism of normal cones lies over `f`.** -/
theorem normalConeMapOfSquare_toBase (comm : f ≫ i' = i ≫ g) :
    normalConeMapOfSquare i i' f g comm ≫ normalConeToBase i' = normalConeToBase i ≫ f :=
  normalConeMap_toBase i i' f _

end Square

/-! ### The canonical morphism of a nested pair `Z ⊆ Y ⊆ X` -/

section Nested

variable {Z Y X : Scheme.{u}} (i : Z ⟶ X) (i' : Y ⟶ X) (f : Z ⟶ Y)
  [IsImmersion i] [IsImmersion i']
  [(conormalAlgebraSheaf i).IsQuasicoherent] [(conormalAlgebraSheaf i').IsQuasicoherent]

/-- **The canonical morphism `C_ZX ⟶ C_YX` of normal cones of a nested pair of immersions**
`Z ⟶ Y ⟶ X` in one ambient scheme, where the immersion of `Z` factors through that of `Y`. This
is `Stacks.Conormal.normalConeMapOfSquare` at `g := 𝟙 X`.

This is the input the normal line cone of [Stacks, Tag 0FEB] needs: for `Z ⊆ Y ⊆ X` it is the
morphism along which the normal cone of the smaller subscheme maps into that of the larger.

The other morphism of cones that tag asks for, `C_ZY ⟶ C_ZX` for one `Z` and two ambients, is
`Stacks.Conormal.normalConeMapOfSquare` at `f := 𝟙 Z` and `g := j`; it is not given a name here
because it is that square with no factorization hypothesis to discharge. -/
def normalConeMapOfFactorization (hf : f ≫ i' = i) : normalCone i ⟶ normalCone i' :=
  normalConeMapOfSquare i i' f (𝟙 X) (hf.trans (Category.comp_id i).symm)

/-- **The canonical morphism `C_ZX ⟶ C_YX` lies over `f`.** -/
theorem normalConeMapOfFactorization_toBase (hf : f ≫ i' = i) :
    normalConeMapOfFactorization i i' f hf ≫ normalConeToBase i' = normalConeToBase i ≫ f :=
  normalConeMapOfSquare_toBase i i' f (𝟙 X) _

end Nested

end Stacks.Conormal

end
