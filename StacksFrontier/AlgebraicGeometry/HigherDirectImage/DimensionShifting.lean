module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Dimension shifting for the higher direct images of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes. The higher direct images
`R ᵍ f_* = (Scheme.Modules.pushforward f).rightDerivedPlus q` are the higher right derived
functors of the direct image on sheaves of modules, and the category `X.Modules` is Grothendieck
abelian, so it has enough injectives; the long exact sequence of [Stacks, Tag 010Q] is therefore
available for them. This file records that long exact sequence at `f_*` and extracts from it the
one consequence a resolution argument needs:

**if `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` is short exact and `ℱ₂` has vanishing higher direct image in the
two degrees `q` and `q + 1`, then the connecting morphism**

`R ᵍ f_* ℱ₃ ⟶ R ᵍ⁺¹ f_* ℱ₁`

**is an isomorphism.**

Iterating this along an exact complex whose intermediate terms have no higher direct image at
all moves the top degree of a left-hand end of the complex down to the degree zero of its
right-hand end; that is the standard dimension-shifting computation.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImage.pushforwardDeltaFunctor`: **the higher direct
  images along `f` as a cohomological `δ`-functor** — the long exact sequence
  `0 ⟶ f_* ℱ₁ ⟶ f_* ℱ₂ ⟶ f_* ℱ₃ ⟶ R ¹ f_* ℱ₁ ⟶ ⋯`.
* `Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPlusShiftIso`: **the dimension-shifting
  isomorphism** `R ᵍ f_* ℱ₃ ≅ R ᵍ⁺¹ f_* ℱ₁`, in the `ℤ`-indexing
  `CategoryTheory.Functor.rightDerivedPlus`.

## Main results

* `Stacks.DeltaFunctorShift.isIso_δ_of_isZero`: in a cohomological `δ`-functor, the connecting
  morphism of a short exact sequence is invertible in a degree where the middle term is silent in
  that degree and the next.
* `Stacks.AlgebraicGeometry.HigherDirectImage.isIso_pushforwardδ`: that criterion at the higher
  direct images.

## Implementation notes

The abstract criterion is proved for an arbitrary `CategoryTheory.DeltaFunctor` into an abelian
category: the exactness of `Fᵍ(ℱ₂) ⟶ Fᵍ(ℱ₃) ⟶ Fᵍ⁺¹(ℱ₁)` makes `δ` a monomorphism when the first
term is zero, the exactness of `Fᵍ(ℱ₃) ⟶ Fᵍ⁺¹(ℱ₁) ⟶ Fᵍ⁺¹(ℱ₂)` makes it an epimorphism when the
last term is zero, and in an abelian category the two give invertibility.

The `δ`-functor itself is `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`,
which needs nothing of `f` beyond additivity of the direct image and enough injectives in
`X.Modules`; both are found by instance search.

`pushforwardDeltaFunctor` is **a public form of a `private` declaration**:
`StacksFrontier/AlgebraicGeometry/CoherentTwoOutOfThree/Basic.lean:220` builds the
same `δ`-functor, by the same one-line application, as a `private` definition, and uses it for the
two-out-of-three property of coherence of the higher direct images. `private` declarations are
per-module mangled, so there is neither shadowing nor collision — but there is also no way for
another module to use it, and the application has to be written again.

The functors of the `δ`-functor are Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, so the statement in the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` of the rest of the development is obtained by
conjugating with `Stacks.DerivedIndexing.rightDerivedIso`.

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance at priority `2000`,
as in the modules that state vanishing of higher direct images of the twists on projective space,
so that `rightDerivedPlus` here elaborates in the same model as there; at the default priority
the globally declared locally small model is preferred, whose morphisms live one universe lower.

No `stacks` attribute is attached: the long exact sequence of [Stacks, Tag 010Q] carries its
attribute on the structure `CategoryTheory.DeltaFunctor`, and what is below is one instance of it
together with a corollary.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.DeltaFunctorShift

/-- **The connecting morphism of a cohomological `δ`-functor is invertible where the middle term
of the sequence is silent.** If `Fᵍ(ℱ₂) = 0` then `δ : Fᵍ(ℱ₃) ⟶ Fᵍ⁺¹(ℱ₁)` is a monomorphism, by
exactness of `Fᵍ(ℱ₂) ⟶ Fᵍ(ℱ₃) ⟶ Fᵍ⁺¹(ℱ₁)`; if `Fᵍ⁺¹(ℱ₂) = 0` then it is an epimorphism, by
exactness of `Fᵍ(ℱ₃) ⟶ Fᵍ⁺¹(ℱ₁) ⟶ Fᵍ⁺¹(ℱ₂)`. -/
theorem isIso_δ_of_isZero {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : CategoryTheory.DeltaFunctor A B) {S : ShortComplex A} (hS : S.ShortExact) (q : ℕ)
    (h₁ : IsZero ((F.functor q).obj S.X₂))
    (h₂ : IsZero ((F.functor (q + 1)).obj S.X₂)) :
    IsIso (F.δ hS q) := by
  have hmono : Mono (F.δ hS q) :=
    (F.exact_δ₁ hS q).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi (F.δ hS q) :=
    (F.exact_δ₂ hS q).epi_f (h₂.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Stacks.DeltaFunctorShift

namespace Stacks.AlgebraicGeometry.HigherDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The higher direct images along a morphism of schemes form a cohomological `δ`-functor**
([Stacks, Tag 010Q]): a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of sheaves of modules on `X`
gives rise to the long exact sequence

`0 ⟶ f_* ℱ₁ ⟶ f_* ℱ₂ ⟶ f_* ℱ₃ ⟶ R ¹ f_* ℱ₁ ⟶ R ¹ f_* ℱ₂ ⟶ ⋯`,

whose connecting morphisms are natural in the sequence. The direct image is additive and
`X.Modules` is Grothendieck abelian, hence has enough injectives, which is all that
[Stacks, Tag 05TE] requires. -/
def pushforwardDeltaFunctor : CategoryTheory.DeltaFunctor X.Modules Y.Modules :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.Modules.pushforward f)

/-- The `q`-th functor of `pushforwardDeltaFunctor f` is the `q`-th right derived functor of the
direct image along `f`. -/
@[simp] theorem pushforwardDeltaFunctor_functor (q : ℕ) :
    (pushforwardDeltaFunctor f).functor q = (Scheme.Modules.pushforward f).rightDerived q :=
  rfl

/-- **The connecting morphism of the long exact sequence of higher direct images is invertible
where the middle term of the sequence has no higher direct image.** -/
theorem isIso_pushforwardδ {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    (h₁ : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj S.X₂))
    (h₂ : IsZero (((Scheme.Modules.pushforward f).rightDerived (q + 1)).obj S.X₂)) :
    IsIso ((pushforwardDeltaFunctor f).δ hS q) :=
  Stacks.DeltaFunctorShift.isIso_δ_of_isZero (pushforwardDeltaFunctor f) hS q h₁ h₂

/-- **Dimension shifting for the higher direct images**, in Mathlib's `ℕ`-indexing: for a short
exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` whose middle term has vanishing higher direct image in the
degrees `q` and `q + 1`,

`R ᵍ f_* ℱ₃ ≅ R ᵍ⁺¹ f_* ℱ₁`. -/
def rightDerivedShiftIso {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    (h₁ : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj S.X₂))
    (h₂ : IsZero (((Scheme.Modules.pushforward f).rightDerived (q + 1)).obj S.X₂)) :
    ((Scheme.Modules.pushforward f).rightDerived q).obj S.X₃ ≅
      ((Scheme.Modules.pushforward f).rightDerived (q + 1)).obj S.X₁ :=
  @asIso _ _ _ _ _ (isIso_pushforwardδ f hS q h₁ h₂)

/-- **Dimension shifting for the higher direct images**, in the `ℤ`-indexing
`CategoryTheory.Functor.rightDerivedPlus`: for a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of sheaves of modules on `X` whose middle term has vanishing higher direct
image in the degrees `q` and `q + 1`,

`R ᵍ f_* ℱ₃ ≅ R ᵍ⁺¹ f_* ℱ₁`.

This is `rightDerivedShiftIso` read through `Stacks.DerivedIndexing.rightDerivedIso`, the
comparison of the two indexings. -/
def rightDerivedPlusShiftIso {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    (h₁ : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj S.X₂))
    (h₂ : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus ((q + 1 : ℕ) : ℤ)).obj
      S.X₂)) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj S.X₃ ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus ((q + 1 : ℕ) : ℤ)).obj S.X₁ :=
  ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app S.X₃).symm ≪≫
    rightDerivedShiftIso f hS q
      (h₁.of_iso
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app S.X₂))
      (h₂.of_iso ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward f) (q + 1)).app S.X₂)) ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) (q + 1)).app S.X₁

end Stacks.AlgebraicGeometry.HigherDirectImage

end
