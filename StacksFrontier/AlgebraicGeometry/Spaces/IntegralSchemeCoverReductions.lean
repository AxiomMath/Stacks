module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable

/-!
# The opening reductions of Stacks 09YB

Stacks 09YB asserts, for a quasi-compact quasi-separated algebraic space `X` over a scheme
`S`, that (1) there is a surjective integral morphism `Y ⟶ X` with `Y` a scheme, and that (2)
given a surjective étale `U ⟶ X` the cover `Y` may be chosen so that every point of `Y` has an
open neighbourhood over which `Y ⟶ X` factors through `U`.

Two steps of that proof need nothing beyond what is already in the library, and both are proved
here:

* its first sentence, "part (1) is the special case of part (2) where `U = X`"; and
* its third sentence, "since `X` is quasi-separated, hence reasonable, there exists an integer
  `d` bounding the degree of the geometric fibres of `U ⟶ X`", which is the input the proof's
  induction on `d` is started from.

Neither is the tag, so nothing here is tagged. The refined assertion (2) is taken as an
explicit named hypothesis.

## Main results

* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_etale_refinement` derives
  clause (1) of Stacks 09YB from clause (2), by refining along the identity.
* `AlgebraicGeometry.Space.isReasonableSpace_of_isAbsolutelyQuasiSeparated` is the implication
  `(η) ⇒ (δ)` of Stacks 03JX: a quasi-separated algebraic space is reasonable.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_isAbsolutelyQuasiSeparated` is that
  implication in the shape Stacks 09YB consumes it: an étale chart of a quasi-separated
  algebraic space by an affine scheme has universally bounded fibres.

## Implementation notes

*The reduction of (1) to (2).* A presheaf is a surjective étale cover of itself, so taking the
prescribed cover to be the identity turns clause (2) into clause (1), the local factorizations
being discarded. Surjectivity and étaleness of the identity are proved inline, as they are in
`AlgebraicGeometry.Space.exists_finite_surjective_scheme_cover_of_etale_refinement`, the same
reduction for Stacks 09YC: the library's `AlgebraicGeometry.Space.isSurjective_id` and
`AlgebraicGeometry.Space.isEtale_id` are stated only for the identity of a *representable*
presheaf, whereas the space being covered here is arbitrary.

*The degree bound.* `AlgebraicGeometry.Space.IsReasonableSpace` is by definition the assertion
that every étale chart by an affine scheme has universally bounded fibres, so once
reasonableness is in hand the bound is a matter of unfolding; the only step is converting the
étaleness of the chart between the two spellings `AlgebraicGeometry.Space.IsEtale` and the
`MorphismProperty.presheaf` form, which is
`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`. Reasonableness itself is the composite of
three implications of Stacks 03JX — `(η) ⇒ (ζ)`, `(ζ) ⇒ (ε)` and `(ε) ⇒ (δ)` — which
the library proves separately but never chains from quasi-separatedness. It chains them from
*separatedness over an affine base* in
`AlgebraicGeometry.Space.isReasonableSpace_of_isSeparated_toBase`, which is a different and
stronger hypothesis than the one Stacks 09YB has.

*What is not proved here.* Neither clause of the tag is proved here; both are proved, clause (1)
by the induction of `StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction` and
clause (2) from it in `StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence`, where
the tag is registered. The relative compactification the induction starts from is not a blocker:
the proof factors `U ⟶ X` as a quasi-compact open immersion `U ⟶ Y` followed by an integral `Y ⟶ X`
with `Y` the normalization of `X` in `U`, the normalization enters this library as the datum
`AlgebraicGeometry.Space.NormalizationInData`, and terms of that datum now exist unconditionally —
`AlgebraicGeometry.Space.zariskiMainTheorem` (Stacks 0ABS) produces one, with the open immersion
and the integral morphism, for any quasi-finite separated morphism of algebraic spaces, by glueing
the chart normalizations along a surjective étale chart of the target.

The normalization `Y` is an *algebraic space*, while the tag asks for a cover by an object of
the site, that is by a *scheme*, and turning it into one is what the induction on the
fibre-degree bound does. That `Y` is not a subfunctor of `X`: in the inductive step the proof
uses the decomposition `U ×_X Y = U ⨿ W` with `W` non-empty, so `Y ⟶ X` is not a monomorphism.
The step's Stacks 0G2D, the decomposition, the scheme-theoretic closure and the closed
complement are all in the library, and
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence` records where.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09YB, clause (1) from clause (2).** Suppose that every quasi-compact
quasi-separated algebraic space over `S` has a surjective integral morphism from a scheme
which factors Zariski locally through any prescribed surjective étale cover of the space.
Then every quasi-compact quasi-separated algebraic space over `S` has a surjective integral
morphism from a scheme.

Refine along the identity of the space, which is a surjective étale cover of it, and forget
the local factorizations. -/
theorem existsIntegralSurjectiveSchemeCover_of_etale_refinement
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (H : ∀ X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS U →
      IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS hZ X →
      ∀ p : U ⟶ X, IsSurjective B S hS p → IsEtale B S hS p →
      ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
        IsSurjective B S hS f ∧ IsIntegralHom B S hS f ∧
        ∀ y : points B S hS (yoneda.obj Y),
          ∃ W : Subfunctor (yoneda.obj Y),
            IsOpenSubspace B S hS W ∧
            W.toFunctor.IsRepresentable ∧
            y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
            ∃ g : W.toFunctor ⟶ U, W.ι ≫ f = g ≫ p)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ExistsIntegralSurjectiveSchemeCover B S hS X := by
  have hid : IsSurjective B S hS (𝟙 X) := by
    rw [IsSurjective, pointsMap_id]
    exact Function.surjective_id
  have hide : IsEtale B S hS (𝟙 X) := fun _ φ hφ => by simpa using hφ
  obtain ⟨Y, f, hsurj, hint, -⟩ := H X X hX hX hqc hqs (𝟙 X) hid hide
  exact ⟨Y, f, hsurj, hint⟩

/-- **Stacks 03JX, `(η) ⇒ (δ)`.** A quasi-separated algebraic space over `S` is reasonable.

This is the composite of the three implications `(η) ⇒ (ζ)`, `(ζ) ⇒ (ε)` and
`(ε) ⇒ (δ)`. It is the form in which Stacks 09YB uses Stacks 03JX. -/
theorem isReasonableSpace_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    IsReasonableSpace B S hS X :=
  isReasonableSpace_of_isVeryReasonableSpace B S hS X hX
    (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X hX
      (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS X hZ hX
        hqs))

/-- **The degree bound starting the induction of Stacks 09YB.** An étale chart by an affine
scheme of a quasi-separated algebraic space over `S` has universally bounded fibres: there is
one integer bounding the degrees of all of its geometric fibres. -/
theorem hasUniversallyBoundedFibers_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (φ : yoneda.obj U ⟶ X) (hφ : IsEtale B S hS φ) :
    HasUniversallyBoundedFibers B S hS U φ :=
  isReasonableSpace_of_isAbsolutelyQuasiSeparated B S hS hZ X hX hqs U hU φ
    (presheaf_etale_of_isEtale B S hS hφ)

end AlgebraicGeometry.Space

end
