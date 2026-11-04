module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalDenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# A dense open immersion becomes an isomorphism where the composite is finite

Let `j : V ⟶ Y` be an open immersion of algebraic spaces over `S` whose point range is dense,
let `π : Y ⟶ X` be integral, and let `ι : U ⟶ X` be an open immersion. Write `W = U ×_X Y` and
`A = W ×_Y V = U ×_X V`. If the base change `A ⟶ U` of `j ≫ π` along `ι` is **finite**, then the
base change `A ⟶ W` of `j` is an **isomorphism**, and consequently the base change `W ⟶ U` of
`π` has whatever properties `A ⟶ U` has — in particular it is finite étale as soon as `A ⟶ U`
is.

This is the input the proof of [Stacks, Tag 0GUL] needs, and the reason that proof's appeal to
the normalization of `X` in `V` can be dispensed with. The source takes `Y` to be the
normalization of `X` in `V` and quotes the two lemmas saying that a relative normalization is an
isomorphism over the open where the morphism is already finite, in order to conclude that
`π` is finite étale over `U`. But the conclusion needs no property of `Y` beyond integrality of
`π` and density of the range of `j`, and those are exactly what the factorization of
[Stacks, Tag 0ABS] followed by the replacement of `Y` by the scheme-theoretic closure of
`j(V)` already supplies — see
`AlgebraicGeometry.Space.exists_isSchemeTheoreticallyDense_isIntegralHom_factorization`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isOpenImmersion_of_denseRange_of_universallyClosed`: an
  open immersion with dense point range which is universally closed over a separated base is an
  isomorphism.
* `AlgebraicGeometry.Space.denseRange_pointsMap_of_isPullback_of_denseRange`: a base change of a
  morphism with dense point range along an open immersion again has dense point range.
* `AlgebraicGeometry.Space.isFinite_isEtale_of_isPullback_of_denseRange`: the conclusion above,
  that `W ⟶ U` is finite étale.

## Implementation notes

The argument is the one indicated by [Stacks, Tag 04NX] and [Stacks, Tag 03H4]:

* the comparison morphism `m : A ⟶ W` is a base change of `j`, hence an open immersion
  (Stacks 02YW);
* the point range of `m` is **closed**, because `m` composed with `W ⟶ U` is the base change
  `A ⟶ U` of `j ≫ π`, which is finite and so universally closed, while `W ⟶ U` is a base change
  of the integral `π` (Stacks 03ZS) and so separated — this is part (1) of Stacks 04NX,
  `AlgebraicGeometry.Space.isClosed_range_of_comp_of_isSeparated`;
* the point range of `m` is **dense**, being the preimage of the dense point range of `j` along
  the point map of `W ⟶ Y`, which is an open map because `W ⟶ Y` is a base change of the open
  immersion `ι`; that the range is exactly that preimage is Stacks 03H4,
  `AlgebraicGeometry.Space.exists_points_of_isPullback`;
* a closed dense subset is everything, so `m` is surjective on points, and a surjective open
  immersion is an isomorphism.

Nothing in the argument asks `A`, `W` or `V` to be a scheme, and no hypothesis beyond the four
`IsAlgebraicSpace` ones is carried.

## References

* [Stacks Project, Tag 0GUL](https://stacks.math.columbia.edu/tag/0GUL)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 0ABS](https://stacks.math.columbia.edu/tag/0ABS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open immersion with dense point range which is universally closed over a separated
base is an isomorphism.** Its point range is closed by part (1) of [Stacks, Tag 04NX] and
dense by hypothesis, hence everything; a surjective open immersion is an isomorphism. -/
theorem isIso_of_isOpenImmersion_of_denseRange_of_universallyClosed
    {A W U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hW : IsAlgebraicSpace B S hS W)
    (hU : IsAlgebraicSpace B S hS U)
    (m : A ⟶ W) (hm : IsOpenImmersion B S hS m) (w : W ⟶ U)
    (hw : IsSeparated B S hS w)
    (hclosed : UniversallyClosed B S hS (m ≫ w))
    (hdense : DenseRange (pointsMap B S hS A m)) :
    IsIso m := by
  have hcl : _root_.IsClosed (Set.range (pointsMap B S hS A m)) :=
    isClosed_range_of_comp_of_isSeparated B S hS hA hW hU m w hclosed hw
  have huniv : Set.range (pointsMap B S hS A m) = Set.univ := by
    rw [← hcl.closure_eq]
    exact hdense.closure_range
  exact isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS m hm
    (Set.range_eq_univ.1 huniv)

/-- **A base change of a morphism with dense point range along an open immersion again has
dense point range.** The point range of the base change is the preimage of that of the morphism
along the point map of the other leg — the containment that needs proving is [Stacks, Tag 03H4]
— and the preimage of a dense set under an open map is dense. -/
theorem denseRange_pointsMap_of_isPullback_of_denseRange
    {A W V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {m : A ⟶ W} {a : A ⟶ V} {w : W ⟶ Y} {j : V ⟶ Y}
    (sq : IsPullback m a w j) (hw : IsOpenImmersion B S hS w)
    (hdense : DenseRange (pointsMap B S hS V j)) :
    DenseRange (pointsMap B S hS A m) := by
  refine Dense.mono (fun x hx => ?_)
    (Dense.preimage hdense (isOpenMap_pointsMap_of_isOpenImmersion B S hS w hw))
  obtain ⟨v, hv⟩ := hx
  obtain ⟨z, hz, -⟩ := exists_points_of_isPullback B S hS sq x v hv.symm
  exact ⟨z, hz⟩

/-- **The base change of an integral morphism along an open immersion is finite étale as soon
as the base change of its restriction to a dense open subspace is.**

Let `ι : U ⟶ X` be an open immersion, let `π : Y ⟶ X` be integral and let `j : V ⟶ Y` be an
open immersion whose point range is dense. Let `W = U ×_X Y` with legs `w₁ : W ⟶ U` and
`w₂ : W ⟶ Y`, and let `A = W ×_Y V` with legs `m : A ⟶ W` and `a : A ⟶ V`, so that `m ≫ w₁` is
the base change of `j ≫ π` along `ι`. If `m ≫ w₁` is finite and étale then so is `w₁`.

The comparison `m` is an isomorphism: it is an open immersion whose point range is closed
(Stacks 04NX, the composite being finite hence universally closed and `w₁` integral hence
separated) and dense (Stacks 03H4). So `w₁ = m⁻¹ ≫ (m ≫ w₁)`, a composite of an isomorphism
with a finite étale morphism. -/
theorem isFinite_isEtale_of_isPullback_of_denseRange
    {X Y V U W A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hW : IsAlgebraicSpace B S hS W) (hA : IsAlgebraicSpace B S hS A)
    {ι : U ⟶ X} (hι : IsOpenImmersion B S hS ι)
    {π : Y ⟶ X} (hπ : IsIntegralHom B S hS π)
    {j : V ⟶ Y} (hj : IsOpenImmersion B S hS j)
    (hjdense : DenseRange (pointsMap B S hS V j))
    {w₁ : W ⟶ U} {w₂ : W ⟶ Y} (sqW : IsPullback w₁ w₂ ι π)
    {m : A ⟶ W} {a : A ⟶ V} (sqA : IsPullback m a w₂ j)
    (hfin : IsFinite B S hS (m ≫ w₁)) (het : IsEtale B S hS (m ≫ w₁)) :
    IsFinite B S hS w₁ ∧ IsEtale B S hS w₁ := by
  have hEid : MorphismProperty.ContainsIdentities (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) := by
    have _ : MorphismProperty.ContainsIdentities
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    exact MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have hEiso : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) := by
    have _ : MorphismProperty.RespectsIso
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  have hw₂ : IsOpenImmersion B S hS w₂ :=
    isOpenImmersion_of_isPullback B S hS (isPullback_homMk B S hS hU hY hX hW sqW) hι
  have hm : IsOpenImmersion B S hS m :=
    isOpenImmersion_of_isPullback B S hS (isPullback_homMk B S hS hV hW hY hA sqA.flip) hj
  have hw₁int : IsIntegralHom B S hS w₁ := isIntegralHom_of_isPullback B S hS sqW.flip hπ
  have hw₁sep : IsSeparated B S hS w₁ := isSeparated_of_isIntegralHom B S hS w₁ hW hU hw₁int
  have hdense : DenseRange (pointsMap B S hS A m) :=
    denseRange_pointsMap_of_isPullback_of_denseRange B S hS sqA hw₂ hjdense
  have hiso : IsIso m :=
    isIso_of_isOpenImmersion_of_denseRange_of_universallyClosed B S hS hA hW hU m hm w₁
      hw₁sep (universallyClosed_of_isFinite B S hS hA hU hfin) hdense
  have _ := hiso
  have hfac : inv m ≫ m ≫ w₁ = w₁ := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← hfac]
  exact ⟨isFinite_comp B S hS
      (isFinite_of_isClosedImmersion B S hS (inv m)
        (isClosedImmersion_of_isIso B S hS (inv m))) hfin,
    isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS (MorphismProperty.presheaf_of_isIso _ _)) het⟩

end AlgebraicGeometry.Space

end
