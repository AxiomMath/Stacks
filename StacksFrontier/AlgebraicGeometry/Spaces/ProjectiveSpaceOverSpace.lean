module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartProperImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation

/-!
# Projective space over an algebraic space

Let `Y` be an algebraic space over `S`. Projective `n`-space over `Y` is the product of `Y` with
the functor of points of `ℙⁿ_S`; it is an algebraic space, its projection to `Y` is proper (the
base change of `ℙⁿ_S ⟶ S`), and the standard affine chart `𝔸ⁿ_S ⟶ ℙⁿ_S` makes relative affine
`n`-space over `Y` (`AlgebraicGeometry.Space.affineSpaceOver`) an open subspace of it, over `Y`.
This is the compactification of `𝔸ⁿ_Y` used in the proof of Chow's lemma for algebraic stacks
(Stacks 0CQ8), after Stacks 088N.

## Main results

* `AlgebraicGeometry.Space.exists_isProper_isOpenImmersion_affineSpaceOver`: `𝔸ⁿ_Y` is an open
  subspace of an algebraic space proper over `Y`, compatibly with the projections to `Y`.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 088N](https://stacks.math.columbia.edu/tag/088N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`𝔸ⁿ_Y` is an open subspace of `ℙⁿ_Y`, which is proper over `Y`.** For an algebraic space
`Y` over `S` there are an algebraic space `P` (the product of `Y` with `ℙⁿ_S`), a proper
morphism `q : P ⟶ Y` and an open immersion `k : 𝔸ⁿ_Y ⟶ P` with `k ≫ q` the projection of
`𝔸ⁿ_Y` to `Y`.

The projection `ℙⁿ_S × Y ⟶ Y` is the base change of the proper morphism `ℙⁿ_S ⟶ S`, and `k` is
the base change of the standard affine chart `𝔸ⁿ_S ⟶ ℙⁿ_S` along it. -/
theorem exists_isProper_isOpenImmersion_affineSpaceOver
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (n : ℕ) :
    ∃ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS P) (q : P ⟶ Y)
      (k : affineSpaceOver B S hS Y n ⟶ P),
      IsProper B S hS q ∧ IsOpenImmersion B S hS k ∧ k ≫ q = prod.fst := by
  let F := Over.post (X := B.obj hS) B.inclusion
  let E : BigFppfOver B S hS := Over.mk (ObjectProperty.homMk
    (X := B.obj (B.contains_affineSpace hS n)) (Y := B.obj hS)
    (AffineSpace.over (ULift.{u} (Fin n)) S).hom)
  have hPpr := isProper_projectiveSpaceOver n S
  have hPn : B.Contains (projectiveSpaceOver n S) :=
    @contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Over.mk (𝟙 (B.obj hS))) _
      (projectiveSpaceOver n S ↘ S) inferInstance inferInstance
  let Pₛ : BigFppfOver B S hS := BigFppfOver.mk B S hS hPn (projectiveSpaceOver n S ↘ S)
  let e := Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (n + 1)))
  let α : E ⟶ Pₛ := BigFppfOver.homMk B S hS hPn _ (projectiveSpaceOver.affineChart n 0 e S)
    (projectiveSpaceOver.affineChart_over n 0 e S)
  have hterm : ∀ T : BigFppfOver B S hS,
      (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from T) = B.inclusion.map T.hom := by
    intro T
    simp
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    ((@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}).inverseImage
      (BigFppfOver.toScheme B S hS))
  have hk₀ : IsOpenImmersion B S hS (prod.map (yoneda.map α) (𝟙 Y)) :=
    hbc.of_isPullback (IsPullback.of_prod_fst_with_id (yoneda.map α) Y)
      (isOpenImmersion_yoneda_map B S hS α
        (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
          (projectiveSpaceOver.affineChart n 0 e S))))
  let eR := (restrictedYonedaIso F).app E
  let d : affineSpaceOver B S hS Y n ≅ yoneda.obj E ⨯ Y :=
    prod.braiding _ _ ≪≫ prod.mapIso eR (Iso.refl Y)
  have hQ : IsAlgebraicSpace B S hS (yoneda.obj Pₛ ⨯ Y) := isAlgebraicSpace_prod_yoneda_obj Pₛ hY
  have : (MorphismProperty.presheaf ((@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}).inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨yoneda.obj Pₛ ⨯ Y, hQ, prod.snd, d.hom ≫ prod.map (yoneda.map α) (𝟙 Y), ?_,
    MorphismProperty.RespectsIso.precomp _ d.hom _ hk₀, ?_⟩
  · exact (presheaf_isProper_iff B S hS prod.snd hQ hY (relativelyRepresentable_prod_snd Pₛ Y)).2
      (presheaf_prod_snd inferInstance Pₛ Y (by rw [hterm]; exact hPpr))
  · simp [d, prod.mapIso]

end AlgebraicGeometry.Space

end
