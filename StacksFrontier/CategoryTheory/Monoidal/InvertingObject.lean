module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Monoidal.TensorPow

/-!
# Inverting an object of a symmetric monoidal category

Let `K : 𝒜 ⥤ ℳ` be a fully faithful braided functor between symmetric monoidal categories, let
`L` be an object of `𝒜` and `T` an object of `ℳ` with `K(L) ⊗ T ≅ 𝟙`, such that the symmetry
of `T ⊗ T` is the identity and every object of `ℳ` is isomorphic to some `K(A) ⊗ T^{⊗ n}`. Then
`ℳ` is obtained from `𝒜` by inverting `L`: a braided functor `F : 𝒜 ⥤ 𝒞` into a symmetric
monoidal category for which `F(L)` is invertible extends to a braided functor `G : ℳ ⥤ 𝒞`
along `K`, uniquely up to unique monoidal isomorphism, and `G` is additive and `ℚ`-linear as
soon as `K` and `F` are additive.

In Stacks 0FGH, `𝒜` is the category of correspondences of degree zero (made Karoubian), `ℳ` the
category of Chow motives, `L` the Lefschetz motive and `T` the Tate motive.

This file states the three assertions (E), (U) and (L) as propositions.

## Main definitions

* `CategoryTheory.InvertingObject.Existence`: (E), existence of the braided extension.
* `CategoryTheory.InvertingObject.Uniqueness`: (U), its uniqueness up to unique monoidal
  isomorphism compatible with the identifications on `𝒜`.
* `CategoryTheory.InvertingObject.LinearExistence`: (L), existence of an additive and `ℚ`-linear
  braided extension when `K` and `F` are additive.

## Implementation notes

In (L) the hypothesis that `K` is additive cannot be dropped: on the one-object category with
endomorphisms `ℚ` and tensor product given by multiplication, the multiplicative bijection of
`ℚ` exchanging the primes `2` and `3` is a fully faithful braided functor `K`, and with
`F = 𝟭`, `L = 𝟙`, `T = 𝟙` every extension is that bijection's inverse, which is not additive.

In (L) the hypotheses that the tensor products of `ℳ` and `𝒞` are additive
(`MonoidalPreadditive`) are what make the whiskerings by the invertible objects used to present
morphisms additive; an autoequivalence `- ⊗ T` of a preadditive monoidal category need not be
additive (on the category with objects `ℤ`, endomorphisms `ℚ` and `f ⊗ g = σⁿ(f) σᵐ(g)` for
`f ∈ End m`, `g ∈ End n`, with `σ` that bijection, `f ↦ f ▷ 1` is `σ`).

## References

* [Stacks Project, Tag 0FGH](https://stacks.math.columbia.edu/tag/0FGH)
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory

namespace InvertingObject

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [SymmetricCategory 𝒜]
  {ℳ : Type u₂} [Category.{v₂} ℳ] [MonoidalCategory ℳ] [SymmetricCategory ℳ]
  (𝒞 : Type u₃) [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] [K.Full] [K.Faithful] (L : 𝒜) (T : ℳ)

/-- **(E) Existence of the extension.** If `K(L) ⊗ T ≅ 𝟙`, the symmetry of `T ⊗ T` is the
identity and every object of `ℳ` is isomorphic to some `K(A) ⊗ T^{⊗ n}`, then every braided
functor `F : 𝒜 ⥤ 𝒞` with `F(L)` invertible extends along `K` to a braided functor
`G : ℳ ⥤ 𝒞`, by a monoidal isomorphism `K ⋙ G ≅ F`. -/
def Existence : Prop :=
  ∀ (_ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (_ : (β_ T T).hom = 𝟙 _)
    (_ : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))
    (F : 𝒜 ⥤ 𝒞) [F.Braided] (_ : IsInvertible (F.obj L)),
    ∃ (G : ℳ ⥤ 𝒞) (_ : G.Braided) (φ : K ⋙ G ≅ F), NatTrans.IsMonoidal φ.hom

/-- **(U) Uniqueness of the extension.** Two braided extensions `G₁`, `G₂` of `F` along `K`,
with monoidal isomorphisms `φᵢ : K ⋙ Gᵢ ≅ F`, are related by a unique monoidal isomorphism
`θ : G₁ ≅ G₂` compatible with the `φᵢ`. -/
def Uniqueness : Prop :=
  ∀ (_ : K.obj L ⊗ T ≅ 𝟙_ ℳ)
    (_ : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))
    (F : 𝒜 ⥤ 𝒞) [F.Braided] (G₁ G₂ : ℳ ⥤ 𝒞) [G₁.Braided] [G₂.Braided]
    (φ₁ : K ⋙ G₁ ≅ F) (φ₂ : K ⋙ G₂ ≅ F) [NatTrans.IsMonoidal φ₁.hom]
    [NatTrans.IsMonoidal φ₂.hom],
    ∃! θ : G₁ ≅ G₂, NatTrans.IsMonoidal θ.hom ∧ Functor.whiskerLeft K θ.hom ≫ φ₂.hom = φ₁.hom

/-- **(L) Existence of an additive, `ℚ`-linear extension.** Under the hypotheses of (E), if
moreover `𝒜`, `ℳ`, `𝒞` are preadditive, `ℳ` and `𝒞` are `ℚ`-linear with additive tensor products,
and `K` and `F` are additive, then the extension can be chosen additive and `ℚ`-linear. -/
def LinearExistence [Preadditive 𝒜] [Preadditive ℳ] [Linear ℚ ℳ] [MonoidalPreadditive ℳ]
    [Preadditive 𝒞] [Linear ℚ 𝒞] [MonoidalPreadditive 𝒞] [K.Additive] : Prop :=
  ∀ (_ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (_ : (β_ T T).hom = 𝟙 _)
    (_ : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))
    (F : 𝒜 ⥤ 𝒞) [F.Braided] [F.Additive] (_ : IsInvertible (F.obj L)),
    ∃ (G : ℳ ⥤ 𝒞) (_ : G.Braided) (_ : G.Additive) (_ : Functor.Linear ℚ G)
      (φ : K ⋙ G ≅ F), NatTrans.IsMonoidal φ.hom

end InvertingObject

end CategoryTheory
