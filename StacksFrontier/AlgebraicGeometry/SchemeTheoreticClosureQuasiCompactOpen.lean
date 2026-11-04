module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageOverOpen
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure

/-!
# The scheme-theoretic closure of a quasi-compact open subscheme

Let `W` be an open subscheme of a scheme `Y` whose inclusion `W.ι` is a quasi-compact morphism.
Its *scheme-theoretic closure* is the closed subscheme `T = W.ι.image` of `Y` cut out by the
kernel ideal sheaf `W.ι.ker`, with closed immersion `W.ι.imageι : T ⟶ Y` and canonical map
`W.ι.toImage : W ⟶ T`. This file proves that

1. `|T| = closure |W|` as subsets of `|Y|`;
2. restricting `T` back over `W` recovers `W` as a scheme: `W.ι.imageι ∣_ W` is an isomorphism,
   and `W.ι.toImage` is an open immersion onto the part of `T` lying over `W`;
3. `W ⟶ T` has dense range.

## Main definitions

* `AlgebraicGeometry.Scheme.Opens.isoPreimageImageι`: the identification of the part of the
  scheme-theoretic closure lying over `W` with `W`.

## Main results

* `AlgebraicGeometry.Scheme.Opens.range_imageι_ι`: the underlying set of the scheme-theoretic
  closure of `W` is `closure (W : Set Y)`.
* `AlgebraicGeometry.Scheme.Opens.coe_support_ker_ι`: the support of the kernel ideal sheaf of
  `W.ι` is `closure (W : Set Y)`.
* `AlgebraicGeometry.Scheme.Opens.preimage_imageι_ι_self`: the open of the scheme-theoretic
  closure lying over `W` is the range of `W.ι.toImage`.
* `AlgebraicGeometry.Scheme.Opens.denseRange_toImage_ι`: `W ⟶ T` has dense range.
* `AlgebraicGeometry.Scheme.Opens.exists_schemeTheoreticClosure`: there are a closed immersion
  `i : T ⟶ Y` and an open immersion `j : W ⟶ T` over `Y` with these properties.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Opens

variable {Y : Scheme.{u}} (W : Y.Opens)

/-- The underlying set of the scheme-theoretic closure of a quasi-compact open subscheme `W` is
the topological closure of `W`. -/
theorem range_imageι_ι [QuasiCompact W.ι] :
    Set.range W.ι.imageι = closure (W : Set Y) := by
  rw [Scheme.Hom.range_imageι, Scheme.Opens.range_ι]

/-- The support of the kernel ideal sheaf of the inclusion of a quasi-compact open subscheme `W`
is the closure of `W`. -/
theorem coe_support_ker_ι [QuasiCompact W.ι] :
    (W.ι.ker.support : Set Y) = closure (W : Set Y) := by
  rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι]

/-- A quasi-compact open subscheme has dense range in its scheme-theoretic closure. -/
theorem denseRange_toImage_ι [QuasiCompact W.ι] : DenseRange W.ι.toImage :=
  W.ι.toImage.denseRange

/-- The part of the scheme-theoretic closure of `W` lying over `W` is the range of
`W.ι.toImage`. -/
theorem preimage_imageι_ι_self [QuasiCompact W.ι] :
    W.ι.imageι ⁻¹ᵁ W = W.ι.toImage.opensRange := by
  have h : closure (Set.range W.ι) ∩ (W : Set Y) = Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.inter_eq_right.mpr subset_closure
  exact TopologicalSpace.Opens.ext (by
    simpa using (AlgebraicGeometry.range_toImage_eq_preimage W.ι h).symm)

/-- The part of the scheme-theoretic closure of an open subscheme `W` lying over `W` is
isomorphic to `W`, via the restriction `W.ι.imageι ∣_ W`. -/
def isoPreimageImageι : (W.ι.imageι ⁻¹ᵁ W).toScheme ≅ W.toScheme :=
  haveI := Stacks.SchemeTheoreticImage.isIso_imageι_restrict W
  asIso (W.ι.imageι ∣_ W)

/-- The forward map of `AlgebraicGeometry.Scheme.Opens.isoPreimageImageι` is the restriction
`W.ι.imageι ∣_ W`. -/
@[simp]
lemma isoPreimageImageι_hom : (isoPreimageImageι W).hom = W.ι.imageι ∣_ W := rfl

/-- The identification of `AlgebraicGeometry.Scheme.Opens.isoPreimageImageι` is compatible with
the two inclusions into `Y`. -/
@[reassoc]
lemma isoPreimageImageι_hom_ι :
    (isoPreimageImageι W).hom ≫ W.ι = (W.ι.imageι ⁻¹ᵁ W).ι ≫ W.ι.imageι :=
  morphismRestrict_ι _ _

/-- For a quasi-compact open subscheme `W` of a scheme `Y`, there are a scheme `T`, a closed
immersion `i : T ⟶ Y` and an open immersion `j : W ⟶ T` with `j ≫ i = W.ι` such that the
underlying set of `T` is the closure of `W`, `j` has dense range, the open of `T` lying over `W`
is the range of `j`, and the restriction of `i` over `W` is an isomorphism. -/
theorem exists_schemeTheoreticClosure [QuasiCompact W.ι] :
    ∃ (T : Scheme.{u}) (i : T ⟶ Y) (j : W.toScheme ⟶ T),
      IsClosedImmersion i ∧ IsOpenImmersion j ∧ j ≫ i = W.ι ∧
        Set.range i = closure (W : Set Y) ∧ DenseRange j ∧
          ((i ⁻¹ᵁ W : T.Opens) : Set T) = Set.range j ∧ IsIso (i ∣_ W) := by
  refine ⟨W.ι.image, W.ι.imageι, W.ι.toImage, inferInstance, inferInstance, W.ι.toImage_imageι,
    range_imageι_ι W, denseRange_toImage_ι W, ?_,
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict W⟩
  rw [preimage_imageι_ι_self W, Scheme.Hom.coe_opensRange]

end AlgebraicGeometry.Scheme.Opens

end
