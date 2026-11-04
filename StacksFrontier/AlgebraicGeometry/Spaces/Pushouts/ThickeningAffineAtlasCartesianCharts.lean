module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Pushouts.ThickeningAffineAtlasOfChartLift

/-!
# The charts of a pushout of algebraic spaces along a thickening are cartesian

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over `S`,
and let `Y' = P/Rel` be the pushout built in Stacks 07VX from a compatible pair of étale scheme
charts: `P = U' ⨿_U V` and `Rel = R' ⨿_{R₀} T` for the kernel pairs. This file proves that the
two chart squares

```text
U' ⟶ P        V ⟶ P
↓     ↓        ↓    ↓
X' ⟶ Y'       Y ⟶ Y'
```

are cartesian, when the kernel pair `R₀` of the chart of `X` is the common base change of the
kernel pairs of the charts of `X'` and `Y` along the first projections — which is how the atlas
of `AlgebraicGeometry.Space.C1573.exists_thickeningAffineAtlas_of_isPullback` is built.

The scheme-level input is that the two relation squares over the first projections of `Rel` are
cartesian (Stacks 07RV, `Stacks.Pushout.C1573.isPullback_of_isPushout_of_isPullback`), and
Stacks 07S3 on charts (`AlgebraicGeometry.Space.isPullback_chart_of_isPullback_source`) passes
from those to the quotient sheaves.

## Main results

* `AlgebraicGeometry.Space.exists_isPushout_isPullback_charts_of_isPullback`: the pushout of a
  span with a lifted chart, together with its chart, both of whose chart squares are cartesian.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfOver.hasSheafify_type

/-- **The pushout of Stacks 07VX with both chart squares cartesian.** Let `i : X ⟶ X'` be a
thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over `S`, let `q : V ⟶ Y` be a
surjective étale chart and `p' : U' ⟶ X'` an étale chart restricting along `i` to the base change
`p : U ⟶ X` of `q` along `f`. Then the span has a pushout `Y'` in the algebraic spaces over `S`,
with a surjective étale chart `P ⟶ Y'` by the scheme pushout `P = U' ⨿_U V`, and both squares
`U' ⟶ P` over `X' ⟶ Y'` and `V ⟶ P` over `Y ⟶ Y'` are cartesian. -/
theorem exists_isPushout_isPullback_charts_of_isPullback
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {U U' V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ Y.1) (p : yoneda.obj U ⟶ X.1)
    (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U') (g : U ⟶ V)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hpbf : IsPullback p (yoneda.map g) f.hom q)
    (hpbi : IsPullback (yoneda.map k) p p' i.hom) :
    ∃ (A : ThickeningAffineAtlas B S hS i f) (E : AlgebraicSpaces B S hS) (a : X' ⟶ E)
      (b : Y ⟶ E), IsPushout i f a b ∧ ∃ qm : yoneda.obj A.P ⟶ E.1,
        IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) qm ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) qm ∧
        IsPullback (yoneda.map A.a) A.p' qm a.hom ∧ IsPullback (yoneda.map A.b) A.q qm b.hom ∧
        ∃ (hU : A.U = U) (hU' : A.U' = U') (hV : A.V = V),
          A.p = yoneda.map (eqToHom hU) ≫ p ∧ A.p' = yoneda.map (eqToHom hU') ≫ p' ∧
          A.q = yoneda.map (eqToHom hV) ≫ q ∧ A.k = eqToHom hU ≫ k ≫ eqToHom hU'.symm ∧
          A.g = eqToHom hU ≫ g ≫ eqToHom hV.symm := by
  obtain ⟨A, s₀, t₀, hR₀, hkRs, hgRs, hK₁, hG₁, hfields⟩ :=
    C1573.exists_thickeningAffineAtlas_of_isPullback B S hS hi hf q p p' k g hqS hqE hp'E hpbf hpbi
  obtain ⟨E, a, b, hpush, qm, hqm, hqmS, hqmE, ha₀, hb₀⟩ :=
    isPushout_quotient_of_thickeningAffineAtlas B S hS A
  set Φ := BigFppfOver.toScheme B S hS with hΦ
  have := A.isAffineHom_g
  have hw₁ : Φ.map A.aR ≫ Φ.map A.s = Φ.map A.s' ≫ Φ.map A.a := by
    rw [← Φ.map_comp, ← Φ.map_comp, A.aR_s]
  have hw₂ : Φ.map A.bR ≫ Φ.map A.s = Φ.map A.sY ≫ Φ.map A.b := by
    rw [← Φ.map_comp, ← Φ.map_comp, A.bR_s]
  obtain ⟨hcartA, hcartB, -⟩ := Stacks.Pushout.C1573.isPullback_of_isPushout_of_isPullback
    A.isThickening_k A.isPushout_chart hK₁ hG₁ A.isPushout_relation hw₁ hw₂
  have hcA : IsPullback A.aR A.s' A.s A.a := IsPullback.of_map_of_faithful Φ hcartA
  have hcB : IsPullback A.bR A.sY A.s A.b := IsPullback.of_map_of_faithful Φ hcartB
  refine ⟨A, E, a, b, hpush, qm, hqm, hqmS, hqmE, ?_, ?_, hfields⟩
  · exact isPullback_chart_of_isPullback_source B S hS X'.property.isSheaf E.property.isSheaf
      A.p' qm a.hom A.surjective_p' A.etale_p' hqmS hqmE A.kernelPair_X' hqm
      A.aR_s A.aR_t hcA ha₀
  · exact isPullback_chart_of_isPullback_source B S hS Y.property.isSheaf E.property.isSheaf
      A.q qm b.hom A.surjective_q A.etale_q hqmS hqmE A.kernelPair_Y hqm
      A.bR_s A.bR_t hcB hb₀

end AlgebraicGeometry.Space
