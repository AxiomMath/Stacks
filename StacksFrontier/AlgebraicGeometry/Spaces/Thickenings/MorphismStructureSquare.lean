module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap

/-!
# The structure map of a morphism of thickenings over a base

Let `B` be an algebraic space over a scheme `S` (written `T` below, `B` being the big fppf site)
and let `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a morphism of thickenings over `T`: so
`f' : X' ⟶ Y'` is a morphism over `T` with `f' ∘ i_X = i_Y ∘ f`.  The running text of
Section 05ZJ of the Stacks project ("Thickenings", More on Morphisms of Spaces) observes that

* in the square of small étale topoi formed by `f`, `f'`, `i_X` and `i_Y`, the vertical arrows
  are equivalences, so that `f` and `f'` define the same morphism of topoi; and
* the structure map `(f')^♯ : f^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` is then a map of sheaves of
  `𝒪_T`-algebras which fits into a commutative square with `f^♯`, `i_X^♯` and `i_Y^♯`.

These are exactly the hypotheses under which Lemma 05ZN recovers a morphism of thickenings from a
map `α` of structure sheaves, so the observation says that `α = (f')^♯` meets them.  This file
proves it, in the presentation used by
`AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged` (the library's carrier of
05ZN).

## Main results

* `AlgebraicGeometry.Space.thickeningHom_structureSharp_compatible`: **Section 05ZJ**, the
  paragraph on a morphism of thickenings over a base.
* `AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening`
  (from `EtaleSite.lean`, registered there under Equation 05ZL) is additionally registered under
  Section 05ZJ for the sentence it formalizes, "if `X ⊂ X'` is a thickening, then `X → X'` is
  integral and universally bijective", which is what makes the vertical arrows equivalences.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/MorphismFromStructureMap.lean`, the map
`(f')^♯` together with the morphism of topoi underlying it is the morphism of small étale ringed
topoi `AlgebraicGeometry.Space.smallEtaleRingedToposHom` of `f'`, from the small étale ringed
topos of `X'` to that of `Y'`.  The source's commuting square is read there as a 2-isomorphism
between the two composites `(Sh(X_étale), 𝒪_X) ⟶ (Sh(Y'_étale), 𝒪_{Y'})`, namely
`(f')_small ∘ (i_X)_small` and `(i_Y ∘ f)_small`, and the `𝒪_T`-algebra condition as a
2-isomorphism between `(p_{Y'})_small ∘ (f')_small` and `(p_{X'})_small`.  Both come from the
functoriality 2-isomorphism of Stacks 03G2, part (3)
(`AlgebraicGeometry.Space.smallEtaleRingedToposHomCompTwoIso`), at the two equations defining a
morphism of thickenings over `T`.  The equivalence of the vertical arrows is the sheaf-of-sets
half of Equation 05ZM,
`AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_of_isThickening`; the source's
`X_{spaces,étale}` and `X_étale` give the same topos (Stacks 03G1), and the small étale form is
the one in which the structure maps are stated.

## References

* [Stacks Project, Tag 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04KJ](https://stacks.math.columbia.edu/tag/04KJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1} {H : Subfunctor Y'.1}

/-- **Section 05ZJ: the structure map of a morphism of thickenings over a base.** Let
`G ⊂ X'` and `H ⊂ Y'` be thickenings of algebraic spaces over `T` (structure morphisms `pX'`,
`pY'`), and let `(f, f')` be a morphism of thickenings over `T`: `f : G ⟶ H`, `f' : X' ⟶ Y'`,
`f' ∘ i_X = i_Y ∘ f` and `pY' ∘ f' = pX'`.  Then

1. the direct images along `i_X` and `i_Y` of the small étale topoi are equivalences (the
   vertical arrows of the source's square of topoi);
2. `(f')_small` is a morphism of locally ringed topoi;
3. `(f')^♯` fits into the source's commuting square with `f^♯`, `i_X^♯` and `i_Y^♯`:
   `(f')_small ∘ (i_X)_small` is 2-isomorphic to `(i_Y ∘ f)_small`;
4. `(f')^♯` is a map of `𝒪_T`-algebras: `(p_{Y'})_small ∘ (f')_small` is 2-isomorphic to
   `(p_{X'})_small`.

Clauses 3 and 4 are the hypotheses `hsquare` and `halgebra`, and clause 2 the hypothesis
`hlocal`, of `AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged` at
`Φ = (f')_small`. -/
@[stacks 05ZJ "the paragraph on a morphism (f, f') : (X ⊂ X') -> (Y ⊂ Y') of thickenings over \
B: the vertical arrows of the square of etale topoi are equivalences, and (f')^# : \
f^{-1}O_{Y'} -> O_{X'} is a map of O_B-algebras fitting into the commutative square with f^#, \
i_X^# and i_Y^#, read as 2-isomorphisms of morphisms of small etale ringed topoi (the form of \
the hypotheses of Lemma 05ZN); (f')_small is moreover locally ringed"]
theorem thickeningHom_structureSharp_compatible (hG : IsThickening B S hS X' G)
    (hH : IsThickening B S hS Y' H) (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (f : IsThickening.space B S hS hG ⟶ IsThickening.space B S hS hH) (f' : X' ⟶ Y')
    (hsq : IsThickening.inclusion B S hS hG ≫ f' = f ≫ IsThickening.inclusion B S hS hH)
    (hT : f' ≫ pY' = pX') :
    (smallToposMorphismTypeU B S hS
        (IsThickening.inclusion B S hS hG)).pushforward.IsEquivalence ∧
      (smallToposMorphismTypeU B S hS
        (IsThickening.inclusion B S hS hH)).pushforward.IsEquivalence ∧
      (smallEtaleRingedToposHom B S hS f').IsLocallyRinged ∧
      Nonempty (SmallEtaleTwoIso B S hS
        (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS f')
          (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hG)))
        (smallEtaleRingedToposHom B S hS (f ≫ IsThickening.inclusion B S hS hH))) ∧
      Nonempty (SmallEtaleTwoIso B S hS
        (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS pY')
          (smallEtaleRingedToposHom B S hS f'))
        (smallEtaleRingedToposHom B S hS pX')) := by
  refine ⟨isEquivalence_smallEtalePushforward_of_isThickening B S hS hG,
    isEquivalence_smallEtalePushforward_of_isThickening B S hS hH,
    smallEtaleRingedToposHom_isLocallyRinged B S hS f', ?_, ?_⟩
  · rw [← hsq]
    exact ⟨smallEtaleRingedToposHomCompTwoIso B S hS (IsThickening.inclusion B S hS hG) f'⟩
  · rw [← hT]
    exact ⟨smallEtaleRingedToposHomCompTwoIso B S hS f' pY'⟩

add_to_stacks 05ZJ "the sentence opening 'The fundamental equivalence': if X ⊂ X' is a \
thickening, then X -> X' is integral and universally bijective (universally injective and \
surjective)"
  AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening

end AlgebraicGeometry.Space

end
