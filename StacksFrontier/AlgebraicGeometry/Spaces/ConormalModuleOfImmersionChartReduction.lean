module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionBaseChange

/-!
# The canonical map of conormal modules restricted to étale charts

Let
```
Z --f--→ Z'
|i       |i'
X --g--→ X'
```
be a commutative square of algebraic spaces over `S` whose vertical morphisms are immersions,
and let `φ : U ⟶ X`, `ψ : V ⟶ X'` be étale, with `Z_U = U ×_X Z` and `Z_V = V ×_{X'} Z'` the
inverse images of the two immersions and `g_U : U ⟶ V` a morphism over `g` carrying `Z_U` into
`Z_V`.  If the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is an
isomorphism, so is the canonical map `f_U^*𝒞_{Z_V/V} ⟶ 𝒞_{Z_U/U}` of the square of charts.

This is the step of the proof of [Stacks Project, Tag 06BH] that passes condition (2) from the
morphism of first-order thickenings of algebraic spaces to the induced morphism of its étale
charts, where the scheme-level [Stacks Project, Tag 063Y] applies.  The source states it as "the
map `f^*𝒞_{Y/Y'} → 𝒞_{X/X'}` is an isomorphism if and only if `g^*𝒞_{V/V'} → 𝒞_{U/U'}` is an
isomorphism"; the implication proved here is the one the direction (2) ⟹ (1) uses.

## Main results

* `AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_chart_of_isIso`: the implication above.

## Route

The two ways of factoring the outer rectangle of charts,
`(Z_U ⊆ U) → (Z ⊆ X) → (Z' ⊆ X')` and `(Z_U ⊆ U) → (Z_V ⊆ V) → (Z' ⊆ X')`, have the same
canonical map, by the composition law of [Stacks Project, Tag 04G2] part (3).  The two étale
squares have invertible canonical maps by [Stacks Project, Tag 04CO]
(`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isPullback_of_isEtale`), so the
first factorisation is invertible when the given square is, and the second then forces the
square of charts to be invertible.

## References

* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X Z' X' ZU U ZV V : AlgebraicSpaces B S hS}

/-- **Condition (2) of Stacks 06BH passes to étale charts.**  For a commutative square of
immersions `i : Z ⟶ X`, `i' : Z' ⟶ X'` over `g : X ⟶ X'`, étale morphisms `φ : U ⟶ X` and
`ψ : V ⟶ X'` with cartesian squares `Z_U = U ×_X Z` and `Z_V = V ×_{X'} Z'`, and a commutative
square of charts `(f_U, g_U) : (Z_U ⊆ U) → (Z_V ⊆ V)` lying over `(f, g)`, invertibility of the
canonical map of [Stacks Project, Tag 04CP] of the given square implies invertibility of the one
of the square of charts. -/
theorem isIso_conormalMapOfImmersions_chart_of_isIso
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom) (hsq : i ≫ g = f ≫ i')
    (iU : ZU ⟶ U) (pU : ZU ⟶ Z) (φ : U ⟶ X) (sqU : IsPullback pU iU i φ)
    (hφ : IsEtale B S hS φ.hom)
    (iV : ZV ⟶ V) (pV : ZV ⟶ Z') (ψ : V ⟶ X') (sqV : IsPullback pV iV i' ψ)
    (hψ : IsEtale B S hS ψ.hom)
    (fU : ZU ⟶ ZV) (gU : U ⟶ V) (hsqU : iU ≫ gU = fU ≫ iV)
    (hf : fU ≫ pV = pU ≫ f) (hg : gU ≫ ψ = φ ≫ g)
    (hiU : IsImmersion B S hS iU.hom) (hiV : IsImmersion B S hS iV.hom)
    (h : IsIso (conormalMapOfImmersions B S hS i i' f g hi hi' hsq)) :
    IsIso (conormalMapOfImmersions B S hS iU iV fU gU hiU hiV hsqU) := by
  have hU := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS iU i hiU hi pU φ
    sqU hφ
  have hV := isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS iV i' hiV hi' pV ψ
    sqV hψ
  have hrect₁ : iU ≫ φ ≫ g = (pU ≫ f) ≫ i' := by
    rw [← Category.assoc, ← sqU.w, Category.assoc, hsq, Category.assoc]
  have hrect₂ : iU ≫ gU ≫ ψ = (fU ≫ pV) ≫ i' := by
    rw [← Category.assoc, hsqU, Category.assoc, ← sqV.w, Category.assoc]
  have houter₁ := isIso_conormalMapOfImmersions_outer B S hS iU i i' pU φ f g hiU hi hi'
    sqU.w.symm hsq hrect₁ hU h
  have houter₂ := isIso_conormalMapOfImmersions_congr B S hS iU i' hiU hi' hf.symm hg.symm
    hrect₁ hrect₂ houter₁
  exact isIso_conormalMapOfImmersions_upper B S hS iU iV i' fU gU pV ψ hiU hiV hi' hsqU
    sqV.w.symm hrect₂ houter₂ hV

end AlgebraicGeometry.Space

end
