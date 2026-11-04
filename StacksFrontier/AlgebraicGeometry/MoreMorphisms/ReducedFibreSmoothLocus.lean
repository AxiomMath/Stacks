module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization is smooth over the base above the smooth locus

Let `q : W ⟶ S` be locally of finite presentation with `S` normal, and let `ν : Y ⟶ W` be the
normalization of `W`. The smooth locus `V ⊂ W` of `q` is an open subscheme smooth over `S`,
hence normal, so `ν` is an isomorphism over `V`. **Therefore `ν ≫ q` is smooth at every point
of `ν⁻¹(V)`.** The scheme `W` is not assumed reduced: the normalization is insensitive to
nilpotents, and a normal open is reduced on the nose.

This is the first half of the last paragraph of the proof of the reduced fibre theorem: with
`W = X_B` the base change and `V = U_B` the smooth locus, the points of the normalized base
change lying over `U_B` are handled outright, and only the points outside it have to be reached
through the elimination of ramification.

## Main results

* `InfinitesimalLifting.smoothAt_of_smooth_opens`: a morphism smooth after restriction to an open
  subscheme is smooth at every point of that open.
* `AlgebraicGeometry.smooth_smoothLocus_ι_comp`: the restriction of a morphism to its smooth
  locus is smooth.
* `AlgebraicGeometry.Scheme.smoothAt_normalization_comp_of_mem_preimage_smoothLocus`: the
  normalization composed with the structure morphism is smooth at every point lying over the
  smooth locus.

## Implementation notes

`InfinitesimalLifting.SmoothAt` is defined through `AlgebraicGeometry.Scheme.Hom.resLE` to the
whole target, so smoothness of the composite `U.ι ≫ q` is converted to it by cancelling the
isomorphism `(⊤ : S.Opens).ι`.

Smoothness of `q` restricted to its smooth locus is read off from
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff` together with
`AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_eq`, which identify the smooth locus of the
restriction with the preimage of the smooth locus, that is, with everything.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-- **Smoothness at a point from smoothness on an open neighbourhood.** If the restriction of `f`
to an open subscheme `U` is smooth, then `f` is smooth at every point of `U`. -/
theorem InfinitesimalLifting.smoothAt_of_smooth_opens {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) {x : X} (hx : x ∈ U) (h : Smooth (U.ι ≫ f)) :
    InfinitesimalLifting.SmoothAt f x := by
  refine ⟨U, hx, ?_⟩
  have he : (U.ι ≫ f) ≫ (Scheme.topIso S).inv = f.resLE ⊤ U le_top := by
    rw [← Scheme.Hom.resLE_comp_ι (f := f) (U := (⊤ : S.Opens)) (V := U) le_top]
    simp
  rw [← he]
  exact MorphismProperty.comp_mem _ _ _ h inferInstance

namespace AlgebraicGeometry

/-- **A morphism is smooth after restriction to its smooth locus.** The smooth locus of the
restriction is the preimage of the smooth locus, which is the whole of it. -/
@[sga "3 X 8.9" "G'"]
theorem smooth_smoothLocus_ι_comp {W S : Scheme.{u}} (q : W ⟶ S)
    [LocallyOfFinitePresentation q] : Smooth (q.smoothLocus.ι ≫ q) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact q.smoothLocus.ι_preimage_self

namespace Scheme

/-- **The normalization is smooth over the base above the smooth locus.** Let `q : W ⟶ S` be
locally of finite presentation with `S` normal, and let `ν` be the normalization of `W`. Then
`ν ≫ q` is smooth at every point of the preimage of the smooth locus of `q`. No reducedness of
`W` is assumed.

The smooth locus is smooth over the normal scheme `S`, hence is a normal open subscheme of `W`,
and the normalization is an isomorphism over a normal open. Composing that isomorphism with the
smooth restriction of `q` gives smoothness over the whole preimage.

This is the first half of the last paragraph of the proof of Tag 09IL; the generic points of
fibres lying outside the smooth locus are the other half. The full statement of that tag is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`. -/
theorem smoothAt_normalization_comp_of_mem_preimage_smoothLocus {W S : Scheme.{u}}
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (q : W ⟶ S) [LocallyOfFinitePresentation q] [IsNormal S]
    (y : W.normalizationScheme hW) (hy : y ∈ W.normalization hW ⁻¹ᵁ q.smoothLocus) :
    InfinitesimalLifting.SmoothAt (W.normalization hW ≫ q) y := by
  have hsmooth : Smooth (q.smoothLocus.ι ≫ q) := smooth_smoothLocus_ι_comp q
  have _ : IsNormal q.smoothLocus.toScheme := isNormal_of_smooth (q.smoothLocus.ι ≫ q)
  have _ : IsIso (W.normalization hW ∣_ q.smoothLocus) :=
    W.isIso_normalization_restrict_of_isNormal hW q.smoothLocus inferInstance
  refine InfinitesimalLifting.smoothAt_of_smooth_opens _
    (W.normalization hW ⁻¹ᵁ q.smoothLocus) hy ?_
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  exact MorphismProperty.comp_mem _ _ _ inferInstance hsmooth

end Scheme

end AlgebraicGeometry

end
