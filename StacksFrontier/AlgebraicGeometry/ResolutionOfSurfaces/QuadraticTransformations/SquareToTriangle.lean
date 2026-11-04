module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.TwistEndomorphism

/-!
# From the conormal square map of Tag 01R4 to the first arrow of Tag 067L

Let `i : E ⟶ X'` and `i' : E' ⟶ Y'` be immersions, and let `g : E ⟶ E'` and `f' : X' ⟶ Y'` make
the square

```
E  --i-->  X'
|          |
g          f'
|          |
v          v
E' --i'--> Y'
```

commute, through an immersion `j : E ⟶ Y'` equal to both composites. The comparison map
`Stacks.Immersion.immersionConormalSheafMap` of [Stacks, Tag 01R4] attached to the square is a
composite whose last factor is the first arrow
`Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap` of the conormal sequence of
[Stacks, Tag 067L] for the triangle `i ≫ f' = j`: the square is the stack of the triangle square
`(𝟙_E, f')` over the square `(g, 𝟙_{Y'})`, and comparison maps compose along stacked squares
([Stacks, Tag 04G2] part (3)). So an epimorphic square map gives an epimorphic first arrow.

For exceptional curves of the first kind `E ⊆ X'` and `E' ⊆ Y'`, this gives `i^* Ω_{X'/Y'} = 0`
when the comparison map of the square is nonzero, a step of the proof of [Stacks, Tag 0C5R],
under the hypothesis `Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow` on the second arrow
of the conormal sequence of [Stacks, Tag 067L].

## Main results

* `Stacks.ResolutionOfSurfaces.epi_conormalTransitivityMap_of_epi_immersionConormalSheafMap` —
  an epimorphic comparison map of the square of [Stacks, Tag 01R4] makes the first arrow of the
  conormal sequence of [Stacks, Tag 067L] for the triangle an epimorphism.
* `Stacks.ResolutionOfSurfaces.isZero_pullback_relativeDifferentials_of_exceptionalCurvePair` —
  for two exceptional curves of the first kind `E ⊆ X'` and `E' ⊆ Y'` with compatible
  presentations as `𝐏¹_k`, a morphism `g : E ⟶ E'` and a morphism `f' : X' ⟶ Y'` making the
  square commute, a nonzero conormal comparison map forces `i^* Ω_{X'/Y'} = 0`.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The square map and the first arrow of the conormal sequence -/

/-- Let `i : E ⟶ X'` and `i' : E' ⟶ Y'` be immersions, let `g : E ⟶ E'` and `f' : X' ⟶ Y'`, and let
`j : E ⟶ Y'` be an immersion equal both to `i ≫ f'` and to `g ≫ i'`, so that the square
`i ≫ f' = g ≫ i'` commutes and factors through `j`. If the comparison map
`g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}` of the square is an epimorphism then so is the first arrow
`𝒞_{E/Y'} ⟶ 𝒞_{E/X'}` of the conormal sequence of the triangle `i ≫ f' = j`. -/
public theorem epi_conormalTransitivityMap_of_epi_immersionConormalSheafMap
    {E E' X' Y' : Scheme.{u}} (i : E ⟶ X') (i' : E' ⟶ Y') [IsImmersion i] [IsImmersion i']
    (g : E ⟶ E') (f' : X' ⟶ Y') (j : E ⟶ Y') [IsImmersion j]
    (h : i ≫ f' = j) (hj : g ≫ i' = j)
    (hepi : Epi (Stacks.Immersion.immersionConormalSheafMap i i' g f'
      (Stacks.Immersion.toShHom_square (h.trans hj.symm)))) :
    Epi (Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap i j f' h) := by
  have comm₁ : i ≫ f' = 𝟙 E ≫ j := h.trans (Category.id_comp j).symm
  have comm₂ : j ≫ 𝟙 Y' = g ≫ i' := (Category.comp_id j).trans hj.symm
  have key :=
    Stacks.Immersion.immersionConormalSheafMap_comp i j i' (𝟙 E) f' comm₁ g (𝟙 Y') comm₂
  rw [← Stacks.ConormalSequenceTwoImmersions.pullbackIdIso_hom_comp_conormalTransitivityMap
    i j f' h] at key
  simp only [← Category.assoc] at key
  have hstack : Epi (Stacks.Immersion.immersionConormalSheafMap i i' (𝟙 E ≫ g) (f' ≫ 𝟙 Y')
      (Stacks.Immersion.toShHom_square (Stacks.Immersion.square_comp comm₁ comm₂))) := hepi
  rw [key] at hstack
  exact @epi_of_epi _ _ _ _ _ _ _ hstack

/-! ### Vanishing of the relative differentials along an exceptional curve -/

/-- Assume `Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`. Let `E ⊆ X'` and `E' ⊆ Y'`
be exceptional curves of the first kind with compatible presentations `e : 𝐏¹_k ≅ E` and
`e' : 𝐏¹_k ≅ E'`, let `g : E ⟶ E'` satisfy `e ≫ g = e'`, let `j : E ⟶ Y'` be an immersion equal
to `g ≫ i'` and to `i ≫ f'`, and suppose the conormal comparison map `g^* 𝒞_{E'/Y'} ⟶ 𝒞_{E/X'}`
of [Stacks, Tag 01R4] is nonzero. Then `i^* Ω_{X'/Y'}` is a zero object. -/
public theorem isZero_pullback_relativeDifferentials_of_exceptionalCurvePair (k : Type u)
    [Field k] (hsec : ConormalSequenceSecondArrow.{u})
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') {D : X'.IdealSheafData} {D' : Y'.IdealSheafData}
    {e : projectiveLineProj k ≅ D.subscheme} {e' : projectiveLineProj k ≅ D'.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) (hE' : D'.IsExceptionalCurveOfFirstKind k e')
    (g : D.subscheme ⟶ D'.subscheme) (he : e.hom ≫ g = e'.hom)
    (j : D.subscheme ⟶ Y') [IsImmersion j] (hj : g ≫ D'.subschemeι = j)
    (h : D.subschemeι ≫ f' = j)
    (hne : Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0) :
    IsZero ((Scheme.Modules.pullback D.subschemeι).obj
      (Scheme.Hom.relativeDifferentials f')) := by
  have := isIso_immersionConormalSheafMap_of_exceptionalCurvePair k f' hE hE' g he
    (h.trans hj.symm) hne
  exact isZero_pullback_relativeDifferentials_of_epi hsec D.subschemeι j f' h
    (epi_conormalTransitivityMap_of_epi_immersionConormalSheafMap D.subschemeι D'.subschemeι g f'
      j h hj inferInstance)

end Stacks.ResolutionOfSurfaces

end
