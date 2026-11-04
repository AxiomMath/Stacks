module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpecOfGlobalFunctions

/-!
# A morphism out of an algebraic space is determined on its étale charts

A morphism from an algebraic space over `S` into a sheaf on the big fppf site of `S` is determined
by its restrictions to the étale scheme charts of the source: a chosen surjective étale atlas is an
epimorphism of sheaves, by the coequalizer presentation of Stacks 0262 part (3), and it is one of
the charts.

In particular the canonical morphism `X ⟶ Spec A` of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom` is *the* morphism with its chart formula, so
that formula may be used to identify it with any other morphism satisfying it.

## Main results

* `AlgebraicGeometry.Space.hom_ext_of_charts`: two morphisms from an algebraic space into a sheaf
  which agree on every étale chart are equal.
* `AlgebraicGeometry.Space.specMapOfGlobalHom_unique`: the canonical morphism to the spectrum of a
  ring of functions is determined by its chart formula.

## Implementation notes

The chosen atlas is `AlgebraicGeometry.Space.chosenAtlasKernelPair`, and
`AlgebraicGeometry.Space.chartFromEtaleHom` reads it as an object of the small étale site, so the
hypothesis quantified over all charts applies to it. That it is an epimorphism of sheaves is
`CategoryTheory.Limits.Cofork.IsColimit.epi` applied to
`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`, exactly as in the proof of
`AlgebraicGeometry.Space.affineMapOfPullback`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism from an algebraic space into a sheaf is determined on the étale charts.** -/
theorem hom_ext_of_charts (X : AlgebraicSpaces B S hS)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) {p p' : X.1 ⟶ Q}
    (h : ∀ V : SmallEtale B S hS X.1, V.1.hom ≫ p = V.1.hom ≫ p') : p = p' := by
  let J := BigFppfOver.topology B S hS
  let D := chosenAtlasKernelPair B S hS X
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS D.f D.t D.s D.pullback
    X.property D.surjective D.etale
  let UF : Sheaf J (Type u) := ⟨yoneda.obj D.U, hUsh⟩
  let XF : Sheaf J (Type u) := ⟨X.1, X.property.isSheaf⟩
  let QF : Sheaf J (Type u) := ⟨Q, hQ⟩
  let ff : UF ⟶ XF := ⟨D.f⟩
  have _ : Epi ff := Cofork.IsColimit.epi (Classical.choice hc)
  have hsheaf : ff ≫ (⟨p⟩ : XF ⟶ QF) = ff ≫ (⟨p'⟩ : XF ⟶ QF) :=
    Sheaf.hom_ext (h (chartFromEtaleHom B S hS X D.U D.f D.etale))
  exact congrArg (fun q => q.hom) ((cancel_epi ff).1 hsheaf)

/-- **The canonical morphism to the spectrum of a ring of functions is determined by its chart
formula.** This is the uniqueness half of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom`. -/
theorem specMapOfGlobalHom_unique (X : AlgebraicSpaces B S hS) (A : Type u) [CommRing A]
    (φ : A →+* globalFunctions B S hS X.1)
    {p p' : X.1 ⟶ schemePoints B S hS (Spec (CommRingCat.of A))}
    (hp : ∀ V : SmallEtale B S hS X.1, yonedaEquiv (V.1.hom ≫ p) =
      specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp φ))
    (hp' : ∀ V : SmallEtale B S hS X.1, yonedaEquiv (V.1.hom ≫ p') =
      specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp φ)) :
    p = p' :=
  hom_ext_of_charts B S hS X (isSheaf_schemePoints B S hS _) fun V =>
    yonedaEquiv.injective ((hp V).trans (hp' V).symm)

end AlgebraicGeometry.Space

end
