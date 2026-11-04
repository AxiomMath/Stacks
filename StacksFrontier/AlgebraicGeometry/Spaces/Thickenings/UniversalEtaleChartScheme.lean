module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalRepresentableConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# The universal first-order thickening over an étale chart, at the level of schemes

Let `Z ⟶ W` be a morphism of the big fppf category over `S` whose underlying morphism of schemes
is a first-order thickening. Suppose the represented algebraic space of `W`, with a structure
morphism `y : W ⟶ X'` to an algebraic space `X'`, is a universal first-order thickening of `Z`
over `X'`. Let `v : V' ⟶ X'` be an étale chart, `W_V = W ×_{X'} V'` and `Z_V = Z ×_W W_V`, all
three represented by objects of the site. Then `Z_V ⟶ W_V` is a universal first-order thickening
of `Z_V` over `V'` *in the sense of schemes*, with structure morphism the projection
`W_V ⟶ V'`.

This is the input of the scheme-level argument for **Stacks 06D8** through an étale chart of the
target. That argument works with scheme-level universal first-order thickenings, while the
thickening is given at the level of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_scheme_of_etaleChart`: the statement
  above.

## Implementation notes

There are two steps. First, `yoneda.map b : W_V ⟶ W` is étale as a base change of `v`, so
clause (2) of **Stacks 060D**,
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalization`, makes the range of
`yoneda.map jV` a space-level universal first-order thickening of `Z_V` over `V'`. The cartesian
square it asks for is the Yoneda image of the given square `Z_V = Z ×_W W_V`, with the two
represented closed subspaces replaced by their ranges; Yoneda images of closed immersions of the
site are monomorphisms (`AlgebraicGeometry.Space.mono_of_isClosedImmersion`). Second, the
space-level and scheme-level notions agree for a first-order thickening of the site
(`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map_iff`). That
`Z_V ⟶ W_V` is a first-order thickening is **Stacks 09ZU**, applied to the image of the square in
schemes.

## References

* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The universal first-order thickening over an étale chart is a scheme-level one.** Let
`j : Z ⟶ W` be a morphism of the big fppf category over `S` whose underlying morphism of schemes
is a first-order thickening. Suppose the range of `yoneda.map j` is a universal first-order
thickening of `Z` over an algebraic space `X'` with structure morphism `y`. Let
`v : V' ⟶ X'` be étale from an object of the site, let `W_V = W ×_{X'} V'` (the square `hWV`),
and let `Z_V = Z ×_W W_V` (the square `hZV`, in the site). Then the underlying morphisms of
schemes make `Z_V ⟶ W_V` a universal first-order thickening of `Z_V` over `V'`, with structure
morphism `W_V ⟶ V'`. -/
theorem isUniversalFirstOrderThickening_scheme_of_etaleChart
    {X' : AlgebraicSpaces B S hS} {Z W V' ZV WV : BigFppfOver B S hS}
    (j : Z ⟶ W)
    (hj : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map j))
    (y : schemeSpace W ⟶ X')
    (huniv : IsUniversalFirstOrderThickening B S hS (Subfunctor.range (yoneda.map j)) y)
    (v : yoneda.obj V' ⟶ X'.1)
    (hv : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v)
    (b : WV ⟶ W) (gV : WV ⟶ V') (hWV : IsPullback (yoneda.map b) (yoneda.map gV) y.hom v)
    (a : ZV ⟶ Z) (jV : ZV ⟶ WV) (hZV : IsPullback jV a b j) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (jV ≫ gV)) ((BigFppfOver.toScheme B S hS).map jV)
      ((BigFppfOver.toScheme B S hS).map gV) := by
  -- `Z_V ⟶ W_V` is a first-order thickening of schemes, by Stacks 09ZU.
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hjV : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map jV) :=
    Stacks.Thickenings.isFirstOrderThickening_of_isPullback
      (hZV.map (BigFppfOver.toScheme B S hS)) hj
  refine (isUniversalFirstOrderThickening_range_yoneda_map_iff B S hS jV gV hjV).1 ?_
  -- The chart and its base change, as morphisms of algebraic spaces, are étale.
  let φ : schemeSpace V' ⟶ X' := ObjectProperty.homMk v
  have hφ : IsEtale B S hS φ.hom := isEtale_of_presheaf_etale B S hS hv
  have hb : IsEtale B S hS (schemeSpaceMap b).hom :=
    isEtale_of_presheaf_etale B S hS (presheaf_of_isPullback B S hS hWV.flip hv)
  have hr : schemeSpaceMap gV ≫ φ = schemeSpaceMap b ≫ y := ObjectProperty.hom_ext _ hWV.w.symm
  -- The square of ranges is the Yoneda image of `Z_V = Z ×_W W_V`.
  have hmono {P Q : BigFppfOver B S hS} (f : P ⟶ Q) :
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) →
        Mono (yoneda.map f) :=
    mono_of_isClosedImmersion B S hS _ ∘
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ f).2
  have := hmono j hj.1
  have := hmono jV hjV.1
  let c : (Subfunctor.range (yoneda.map jV)).toFunctor ⟶
      (Subfunctor.range (yoneda.map j)).toFunctor :=
    inv (Subfunctor.toRange (yoneda.map jV)) ≫ yoneda.map a ≫ Subfunctor.toRange (yoneda.map j)
  have hsq : IsPullback c (Subfunctor.range (yoneda.map jV)).ι
      (Subfunctor.range (yoneda.map j)).ι (schemeSpaceMap b).hom := by
    refine IsPullback.of_iso (hZV.flip.map yoneda)
      (asIso (Subfunctor.toRange (yoneda.map jV)))
      (asIso (Subfunctor.toRange (yoneda.map j))) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [c]
    · simp
    · simp
    · simp [schemeSpaceMap_hom]
  exact IsUniversalFirstOrderThickening.etaleLocalization (X := X') (U := schemeSpace V')
    (Z' := schemeSpace W) (V' := schemeSpace WV) B S hS _ y huniv φ hφ (schemeSpaceMap b) hb
    (schemeSpaceMap gV) hr _ c hsq

end AlgebraicGeometry.Space

end
