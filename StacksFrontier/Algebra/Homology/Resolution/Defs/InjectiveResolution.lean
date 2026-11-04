module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injective resolutions of cochain complexes

Let `C` be a category with zero morphisms in which every short complex has homology. An
*injective resolution* of a cochain complex `K` of `C` is a bounded below cochain complex `I` of
injective objects of `C` together with a quasi-isomorphism `K ⟶ I`:
```
... ⟶ Kⁿ⁻¹ ⟶ Kⁿ   ⟶ Kⁿ⁺¹ ⟶ ...
        |      |      |
        v      v      v
... ⟶ Iⁿ⁻¹ ⟶ Iⁿ   ⟶ Iⁿ⁺¹ ⟶ ...
```
An injective resolution of an *object* `X` of `C`, i.e. a complex `I` with `Iⁿ = 0` for `n < 0`,
with each `Iⁿ` injective, with `X ⟶ I⁰` an isomorphism onto `ker d⁰` and with `Hⁱ(I) = 0` for
`i > 0`, is Mathlib's `CategoryTheory.InjectiveResolution X`; it is almost the same thing as an
injective resolution of the complex `X[0]`, the two conditions on `X ⟶ I⁰` and on `Hⁱ(I)`
together saying exactly that `X[0] ⟶ I` is a quasi-isomorphism.

## Main definitions

* `CochainComplex.InjectiveResolution K`: an injective resolution of a cochain complex `K`,
  bundling the resolving complex, the map from `K`, degreewise injectivity, boundedness below and
  the quasi-isomorphism condition.

## References

* [Stacks, Tag 013I](https://stacks.math.columbia.edu/tag/013I)
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]

/-- An injective resolution of a cochain complex `K` in a category `C`: a bounded below cochain
complex `cocomplex` of injective objects of `C`, together with a quasi-isomorphism
`ι : K ⟶ cocomplex`. -/
@[stacks 013I, sga "2 VIII 1.3", sga "4½ Etat_0 3.1.8" "injective case"]
public structure InjectiveResolution (K : CochainComplex C ℤ) where
  /-- the cochain complex involved in the resolution -/
  cocomplex : CochainComplex C ℤ
  /-- the cochain complex must be bounded below -/
  boundedBelow : CochainComplex.plus C cocomplex
  /-- the cochain complex must be degreewise injective -/
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  /-- the morphism from the complex which is being resolved -/
  ι : K ⟶ cocomplex
  /-- the morphism from the complex which is being resolved is a quasi-isomorphism -/
  quasiIso : QuasiIso ι := by infer_instance

attribute [instance] InjectiveResolution.injective InjectiveResolution.quasiIso

end CochainComplex
