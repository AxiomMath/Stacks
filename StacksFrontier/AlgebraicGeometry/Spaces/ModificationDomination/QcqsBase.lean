module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple

/-!
# A proper modification is dominated by an admissible blowup

Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `U ⊆ Y`
be an open subspace. Assume that `Y` is quasi-compact and quasi-separated, that `U` is
quasi-compact, that `f` is proper and that `f⁻¹(U) ⟶ U` is an isomorphism. Then there is a
`U`-admissible blowup `Y' ⟶ Y` which dominates `X`: the blowup morphism factors as
`Y' ⟶ X ⟶ Y`. This is Stacks 087G.

## The proof

The source deduces Stacks 087G from Stacks 0GUW, which rests on the flattening theorem for
algebraic spaces, Stacks 087C, and through it on Zariski's main theorem for algebraic spaces
(Stacks 0874, through 087B). The proof here avoids both: it runs the induction principle for
quasi-compact quasi-separated algebraic spaces, Stacks 08GP
(`AlgebraicGeometry.Space.qcqs_induction_on_self`), on the property
`AlgebraicGeometry.Space.DominatesModifications`, with

* the affine case `AlgebraicGeometry.Space.dominatesSections_schemeSpace`: over a quasi-compact
  quasi-separated scheme the strict transform of an affine étale chart is flattened by a blowup,
  by the flatness half of Stacks 081R (a scheme-level form of Stacks 087E), and the closure of the
  open part of the modification is then flat, finite (Stacks 0B4J) and an open immersion
  (Stacks 0879), hence the base (the second half of the proof of Stacks 0GUW);
* the step `AlgebraicGeometry.Space.dominatesModifications_of_isElementaryDistinguishedSquare`
  across an elementary distinguished square, through Stacks 086D, 086C, 085S and 0DVI.

## Main results

* `AlgebraicGeometry.Space.dominatesModifications_of_isQuasiCompactSpace`.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isProper`: **Stacks 087G**.

## References

* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An affine algebraic space dominates modifications. -/
theorem dominatesModifications_of_isAffineSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (h : IsAffineSpace B S hS F) :
    DominatesModifications (⟨F, hF⟩ : AlgebraicSpaces B S hS) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := h
  let e' : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ≅ schemeSpace T :=
    { hom := ObjectProperty.homMk e.hom
      inv := ObjectProperty.homMk e.inv
      hom_inv_id := ObjectProperty.hom_ext _ e.hom_inv_id
      inv_hom_id := ObjectProperty.hom_ext _ e.inv_hom_id }
  exact (DominatesSections.of_iso e'
    (dominatesSections_schemeSpace B.contains_terminal T)).dominatesModifications

/-- **Every quasi-compact quasi-separated algebraic space dominates modifications**, by the
induction principle of Stacks 08GP. -/
theorem dominatesModifications_of_isQuasiCompactSpace (Y : AlgebraicSpaces B S hS)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1) :
    DominatesModifications Y := by
  have h := qcqs_induction_on_self B S hS B.contains_terminal Y hYqc hYqs
    (fun F _ => ∀ hF : IsAlgebraicSpace B S hS F, DominatesModifications ⟨F, hF⟩)
    (fun V hVa hF => dominatesModifications_of_isAffineSpace hF hVa)
    (fun W V U φ _ hsq hWqc hWqs hUqc hVa hPU _ _ _ =>
      dominatesModifications_of_isElementaryDistinguishedSquare (W := ⟨W.1.left.1, _⟩) U φ hsq
        hWqc hWqs hUqc hVa (hPU _))
  exact h Y.2

/-- **Stacks 087G.** Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S` and let `U ⊆ Y` be an open subspace. Assume that `Y` is quasi-compact and quasi-separated,
that `U` is quasi-compact, that `f` is proper and that `f⁻¹(U) ⟶ U` is an isomorphism. Then
there is a `U`-admissible blowup `b : Y' ⟶ Y` which dominates `X`, that is, there is a
factorization `Y' ⟶ X ⟶ Y` of the blowup morphism.

Being a `U`-admissible blowup is Stacks 086B, `AlgebraicGeometry.Space.IsAdmissibleBlowup`;
quasi-separatedness of `Y` is absolute quasi-separatedness; and `f⁻¹(U) ⟶ U` is the projection
`X ×_Y U ⟶ U`. -/
@[stacks 087G]
theorem exists_isAdmissibleBlowup_dominating_of_isProper {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (U : OpenSubspaces B S hS Y.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hf : IsProper B S hS f.hom) (hfU : IsIso (pullback.snd f.hom U.1.ι)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), IsAdmissibleBlowup B S hS U b ∧
      ∃ g : Y' ⟶ X, g ≫ f = b :=
  dominatesModifications_of_isQuasiCompactSpace Y hYqc hYqs U hUqc X f hf hfU

end AlgebraicGeometry.Space

end
