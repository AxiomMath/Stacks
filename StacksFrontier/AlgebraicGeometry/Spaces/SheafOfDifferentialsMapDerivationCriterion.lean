module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of Stacks 04CX is invertible exactly when restriction of derivations is

Let

```
X' --f--> X
|         |
p'        p
v         v
Y' --q--> Y
```

be a commutative square of algebraic spaces over `S` and let
`c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` be its comparison map of Stacks 04CX.  Equation 0619
(`AlgebraicGeometry.Space.derivationDirectImageEquiv`) turns a morphism out of `f^*Ω_{X/Y}` into
a `Y`-derivation of `𝒪_X` with values in a direct image, and the universal property of Stacks
04CT (`AlgebraicGeometry.Space.differentialsHomEquiv`) turns a morphism out of `Ω_{X'/Y'}` into a
`Y'`-derivation of `𝒪_{X'}`.  Reading precomposition with `c_f` through the two of them gives the
map

> `Θ_C : (Ω_{X'/Y'} ⟶ C) ⟶ (Y-derivations of 𝒪_X with values in f_*C)`,
> `g ↦ (f_*d_{X'/Y'} ∘ f♯)` postcomposed with `f_*g`,

which is **restriction of derivations along `f`** and mentions neither `f^*` nor `c_f`.  By the
Yoneda lemma `c_f` is an isomorphism exactly when `Θ_C` is a bijection for every `𝒪_{X'}`-module
`C`.

The point of the reformulation is what it removes.  Invertibility of `c_f` is a statement about
the inverse image `f^*Ω_{X/Y}`, so proving it for a square of schemes of the site — the one
statement `AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso` that Stacks 05ZC and
Stacks 05ZD still need — through the invertibility clause of Stacks 04CS needs the base change
`(k^*𝓕)^a ≅ ε_k^*(𝓕^a)` of Stacks 03LC (1)
(`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`,
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`) *compatibly with the universal
derivations*, and that compatibility is not in the tree: both sides of the base change are left
adjoints and the only thing pinning it is the conjugacy
`AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv`.  Bijectivity of
`Θ_C` mentions no inverse image of modules at all: only direct images, for which the comparison
of the two routes round the square of small étale ringed sites of a morphism of schemes of the
site is computed over the opens of the base
(`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`).

## Main definitions

* `AlgebraicGeometry.Space.restrictDerivation`: `Θ_C`, restriction of derivations along the top
  edge of the square — the composite `Y`-derivation `f_*(d_{X'/Y'} ∘ g) ∘ f♯` of a morphism
  `g : Ω_{X'/Y'} ⟶ C`.

## Main results

* `derivationDirectImageEquiv_sheafOfDifferentialsMap_comp_eq_restrictDerivation`:
  `Θ_C` is precomposition with the comparison map of Stacks 04CX, read through Equation 0619.
* `AlgebraicGeometry.Space.isIso_of_bijective_restrictDerivation`: **the comparison map of
  Stacks 04CX is an isomorphism as soon as `Θ_C` is a bijection for every `C`.**
* `AlgebraicGeometry.Space.bijective_restrictDerivation_of_isIso`: the converse, so the two
  formulations are interchangeable.

## Implementation notes

The Yoneda step is carried out by hand rather than through a representability API: from
surjectivity of `Θ` at `C = f^*Ω_{X/Y}` comes a right inverse of `c_f`, and injectivity at
`C = Ω_{X'/Y'}` turns it into a two-sided one.  Only `Θ` being a bijection *for every* `C` is
used, which is what the Yoneda lemma needs.

`AlgebraicGeometry.Space.restrictDerivation` is defined as the postcomposition of
`AlgebraicGeometry.Space.pushforwardUniversalDerivation` — the `Y`-derivation
`f_*d_{X'/Y'} ∘ f♯` of Stacks 04CX — with the direct image of `g`, rather than by writing out a
derivation of its own.  That spares the construction of a direct image of an arbitrary
derivation: the only derivation on `X'` that enters is the universal one, and every other value
of `Θ` is obtained from it by postcomposition.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the bijection between
  maps out of `f^*Ω_{X/Y}` and derivations into a direct image.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials and its universal derivation.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **Restriction of derivations along the top edge of a commutative square.**  For a morphism
`g : Ω_{X'/Y'} ⟶ C` of `𝒪_{X'}`-modules, the `Y`-derivation of `𝒪_X` with values in `f_*C`
obtained by composing the structure map `f♯ : 𝒪_X ⟶ f_*𝒪_{X'}` with the direct image of
`d_{X'/Y'}` followed by `g`.

This is the `Y`-derivation `f_*d_{X'/Y'} ∘ f♯` of Stacks 04CX, postcomposed with the direct
image of `g`. -/
def restrictDerivation (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y') (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) (C : Modules.{u, u} B S hS X'.1 X'.2)
    (g : sheafOfDifferentials B S hS p' ⟶ C) :
    PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS f).obj C).val
      (structureSharpInverseImage B S hS p).hom :=
  (pushforwardUniversalDerivation B S hS f p p' q hcomm).postcomp
    ((modulePushforward B S hS f).map g).val

/-- The `Y`-derivation `f_*d_{X'/Y'} ∘ f♯` of Stacks 04CX is the universal `Y`-derivation
followed by the transpose of the comparison map of Stacks 04CX, as derivations.

This is `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap` — a
statement about the values on local sections — read as an equality of derivations. -/
theorem postcomp_homEquiv_sheafOfDifferentialsMap (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) :
    (universalDerivation B S hS p).postcomp
        (((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS p')
          (sheafOfDifferentialsMap B S hS f p p' q hcomm)).val) =
      pushforwardUniversalDerivation B S hS f p p' q hcomm :=
  by
    ext U t
    exact isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f p p' q hcomm U t

/-- **Restriction of derivations along `f` is precomposition with the comparison map of
Stacks 04CX**, read through Equation 0619.

The transpose along `f^* ⊣ f_*` is natural in its right argument, so the derivation attached to
`c_f ≫ g` is the derivation attached to `c_f` postcomposed with `f_*g`; and the derivation
attached to `c_f` is `f_*d_{X'/Y'} ∘ f♯` by the characterizing property of Stacks 04CX. -/
theorem derivationDirectImageEquiv_sheafOfDifferentialsMap_comp_eq_restrictDerivation
    (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y') (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q)
    (C : Modules.{u, u} B S hS X'.1 X'.2) (g : sheafOfDifferentials B S hS p' ⟶ C) :
    derivationDirectImageEquiv B S hS f p C
        (sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ g) =
      restrictDerivation B S hS f p p' q hcomm C g := by
  rw [derivationDirectImageEquiv_apply, Adjunction.homEquiv_naturality_right]
  rw [restrictDerivation, ← postcomp_homEquiv_sheafOfDifferentialsMap B S hS f p p' q hcomm]
  rfl

/-- Restriction of derivations is bijective exactly when precomposition with the comparison map of
Stacks 04CX is. -/
private theorem bijective_restrictDerivation_iff (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) (C : Modules.{u, u} B S hS X'.1 X'.2) :
    Function.Bijective (restrictDerivation B S hS f p p' q hcomm C) ↔
      Function.Bijective
        (fun g : sheafOfDifferentials B S hS p' ⟶ C ↦
          sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ g) := by
  rw [← Equiv.comp_bijective _ (derivationDirectImageEquiv B S hS f p C)]
  exact Iff.of_eq (congrArg _ (funext fun g ↦
    (derivationDirectImageEquiv_sheafOfDifferentialsMap_comp_eq_restrictDerivation
      B S hS f p p' q hcomm C g).symm))

/-- **Restriction of derivations along `f` is a bijection for every `C` as soon as the comparison
map of Stacks 04CX is an isomorphism.** -/
theorem bijective_restrictDerivation_of_isIso (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q)
    (h : IsIso (sheafOfDifferentialsMap B S hS f p p' q hcomm))
    (C : Modules.{u, u} B S hS X'.1 X'.2) :
    Function.Bijective (restrictDerivation B S hS f p p' q hcomm C) := by
  refine (bijective_restrictDerivation_iff B S hS f p p' q hcomm C).2
    ⟨fun g₁ g₂ hg ↦ (cancel_epi (sheafOfDifferentialsMap B S hS f p p' q hcomm)).1 hg,
      fun θ ↦ ⟨inv (sheafOfDifferentialsMap B S hS f p p' q hcomm) ≫ θ, by simp⟩⟩

/-- **The comparison map of Stacks 04CX is an isomorphism as soon as restriction of derivations
along its top edge is a bijection for every `𝒪_{X'}`-module.**

By `derivationDirectImageEquiv_sheafOfDifferentialsMap_comp_eq_restrictDerivation` the hypothesis
says that precomposition with the comparison map is a bijection on the morphisms into every
`𝒪_{X'}`-module, which is the Yoneda criterion for an isomorphism: surjectivity at
`C = f^*Ω_{X/Y}` gives a right inverse, and injectivity at `C = Ω_{X'/Y'}` makes it a left inverse
as well. -/
theorem isIso_of_bijective_restrictDerivation (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q)
    (h : ∀ C : Modules.{u, u} B S hS X'.1 X'.2,
      Function.Bijective (restrictDerivation B S hS f p p' q hcomm C)) :
    IsIso (sheafOfDifferentialsMap B S hS f p p' q hcomm) := by
  set c := sheafOfDifferentialsMap B S hS f p p' q hcomm with hc
  have hpre := fun C ↦ (bijective_restrictDerivation_iff B S hS f p p' q hcomm C).1 (h C)
  obtain ⟨d, hd⟩ := (hpre ((modulePullback B S hS f).obj
    (sheafOfDifferentials B S hS p))).surjective (𝟙 _)
  have hd' : c ≫ d = 𝟙 _ := hd
  refine ⟨d, hd', (hpre (sheafOfDifferentials B S hS p')).injective ?_⟩
  change c ≫ d ≫ c = c ≫ 𝟙 _
  rw [← Category.assoc, hd', Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Space

end
