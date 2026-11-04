module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeOfRepresented
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantQuotientSchemes

/-!
# The morphism from a well-nigh affine stack to its moduli space

Let `𝒳` be a well-nigh affine algebraic stack with a chart `x : U ⟶ 𝒳` and relation
`s, t : R ⟶ U` (`AlgebraicGeometry.Stack.WellNighAffineChart`). The proof of Stacks 0DUP takes the
ring `C` of `R`-invariant functions on `U` (Stacks, Groupoids, Section 03BE), sets `M = Spec C`,
and lets `f : 𝒳 ⟶ M` be the 1-morphism corresponding by Stacks 0DUH to the `R`-invariant morphism
`U ⟶ M`. This file carries out that construction.

## Main definitions

* `AlgebraicGeometry.Stack.WellNighAffineChart.groupoidScheme`: the groupoid scheme
  `(U, R, s, t, c)` over `S`.
* `AlgebraicGeometry.Stack.WellNighAffineChart.moduliObject`: `M = Spec C`, an affine object of
  the big fppf site over `S`, its structure morphism being the descent of that of `U`
  (`AlgebraicGeometry.GroupoidScheme.invariantSpectrumToBase`).
* `AlgebraicGeometry.Stack.WellNighAffineChart.quotientMap`: the morphism `U ⟶ M` of the site.
* `AlgebraicGeometry.Stack.WellNighAffineChart.moduliSpace`: `M` as an algebraic space.
* `AlgebraicGeometry.Stack.WellNighAffineChart.moduliMap`: the 1-morphism `f : 𝒳 ⟶ M`.

## Main results

* `AlgebraicGeometry.Stack.WellNighAffineChart.chart_comp_moduliMap`: `f ∘ x` is the 1-morphism
  attached to `U ⟶ M`, on the nose.

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
* [Stacks Project, Tag 03BE](https://stacks.math.columbia.edu/tag/03BE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Morphisms

namespace AlgebraicGeometry.Stack.WellNighAffineChart

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)

/-- The groupoid scheme `(U, R, s, t, c)` of the chart, over `S`. -/
noncomputable abbrev groupoidScheme : Stacks.Groupoids.GroupoidScheme S :=
  Space.representedGroupoidScheme K.s K.t K.c K.pointwise

/-- The object scheme `U` of the groupoid scheme is affine. -/
instance isAffine_groupoidScheme_objects : IsAffine K.groupoidScheme.objects.left :=
  K.isAffine_U

/-- The arrow scheme `R` of the groupoid scheme is affine. -/
instance isAffine_groupoidScheme_arrows : IsAffine K.groupoidScheme.arrows.left :=
  K.isAffine_V

/-- The source morphism `s : R ⟶ U` of the groupoid scheme is finite locally free. -/
instance isFiniteLocallyFree_groupoidScheme_source :
    IsFiniteLocallyFree K.groupoidScheme.source.left :=
  K.isFiniteLocallyFree_s

/-- The target morphism `t : R ⟶ U` of the groupoid scheme is finite locally free. -/
instance isFiniteLocallyFree_groupoidScheme_target :
    IsFiniteLocallyFree K.groupoidScheme.target.left :=
  K.isFiniteLocallyFree_t

/-- The spectrum of the ring of invariant functions lies in the site: it is no larger than the
affine scheme `U`. -/
theorem contains_invariantSpectrum :
    B.Contains (Spec (.of (invariantRing K.groupoidScheme))) := by
  refine lt_of_le_of_lt ?_ K.U.left.2
  rw [Scheme.size_Spec]
  show _ ≤ Scheme.size K.groupoidScheme.objects.left
  rw [Scheme.size_of_isAffine K.groupoidScheme.objects.left]
  exact max_le_max le_rfl (Cardinal.mk_le_of_injective Subtype.val_injective)

/-- **The moduli space `M = Spec C`** as an object of the big fppf site over `S`, its structure
morphism being the descent of that of `U` along `U ⟶ Spec C`. -/
noncomputable abbrev moduliObject : BigFppfOver B S hS :=
  Space.schemeSiteObject B hS
    (X := Over.mk (GroupoidScheme.invariantSpectrumToBase K.groupoidScheme))
    K.contains_invariantSpectrum

/-- The underlying scheme of `M = Spec C` is affine. -/
instance isAffine_moduliObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj K.moduliObject) :=
  inferInstanceAs (IsAffine (Spec (.of (invariantRing K.groupoidScheme))))

/-- **The quotient map `U ⟶ M`** as a morphism of the site. -/
noncomputable abbrev quotientMap : K.U ⟶ K.moduliObject :=
  (Space.siteToOver B hS).preimage
    (Over.homMk (GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme)
      (GroupoidScheme.objectsToInvariantSpectrum_comp_invariantSpectrumToBase K.groupoidScheme) :
      K.groupoidScheme.objects ⟶ Over.mk (GroupoidScheme.invariantSpectrumToBase K.groupoidScheme))

/-- The quotient map, as a morphism over `S`, is `U ⟶ Spec C` over the base. -/
theorem siteToOver_map_quotientMap :
    (Space.siteToOver B hS).map K.quotientMap =
      Over.homMk (GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme)
        (GroupoidScheme.objectsToInvariantSpectrum_comp_invariantSpectrumToBase
          K.groupoidScheme) :=
  Functor.map_preimage _ _

/-- The quotient map, on underlying schemes, is `U ⟶ Spec C`. -/
theorem toScheme_map_quotientMap :
    (BigFppfOver.toScheme B S hS).map K.quotientMap =
      GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme :=
  congrArg Over.Hom.left K.siteToOver_map_quotientMap

/-- **The quotient map identifies the source and the target.** -/
theorem s_comp_quotientMap : K.s ≫ K.quotientMap = K.t ≫ K.quotientMap := by
  apply (Space.siteToOver B hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, siteToOver_map_quotientMap]
  exact Over.OverMorphism.ext
    (GroupoidScheme.target_comp_objectsToInvariantSpectrum K.groupoidScheme).symm

/-- **The moduli space `M`**, as an algebraic space over `S`. -/
noncomputable abbrev moduliSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj K.moduliObject, isAlgebraicSpace_yoneda B S hS K.moduliObject⟩

/-- `M` is an affine algebraic space. -/
theorem isAffineSpace_moduliSpace : Space.IsAffineSpace B S hS K.moduliSpace.obj :=
  Space.isAffineSpace_yoneda B S hS K.moduliObject inferInstance

/-- The quotient map is invariant as a morphism of represented presheaves. -/
theorem yoneda_s_comp_quotientMap :
    yoneda.map K.s ≫ yoneda.map K.quotientMap = yoneda.map K.t ≫ yoneda.map K.quotientMap := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, s_comp_quotientMap]

/-- The descent of the quotient map along the chart, as a 1-morphism of categories fibred in
groupoids. -/
noncomputable def moduliBasedFunctor :
    𝒳.val.val ⥤ᵇ (fibredCategory B S hS K.moduliSpace.obj).val :=
  (K.descend K.moduliSpace (yoneda.map K.quotientMap) K.yoneda_s_comp_quotientMap).choose

/-- **The 1-morphism `f : 𝒳 ⟶ M`.** -/
noncomputable def moduliMap :
    𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS K.moduliSpace.obj K.moduliSpace.property :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom K.moduliBasedFunctor)

/-- The based functor underlying `f : 𝒳 ⟶ M` is `moduliBasedFunctor`. -/
theorem moduliMap_hom_hom : K.moduliMap.hom.hom = K.moduliBasedFunctor := rfl

/-- **`f ∘ x` is the 1-morphism attached to the quotient map `U ⟶ M`.** -/
theorem chart_comp_moduliMap :
    BasedFunctor.comp K.chart.hom.hom K.moduliMap.hom.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS K.U)
        (associatedMap B S hS (yoneda.map K.quotientMap)).1.hom :=
  (K.descend K.moduliSpace (yoneda.map K.quotientMap) K.yoneda_s_comp_quotientMap).choose_spec

end AlgebraicGeometry.Stack.WellNighAffineChart

end
