module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1H01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1OpenSubstack

/-!
# `Curves^{grc,1} ⊂ Curves^{h0,1}` as open substacks of `Curves`

The substack `Curves^{grc,1}` of families of curves whose geometric fibres are reduced, connected
and of dimension `1` is contained in the substack `Curves^{h0,1}` of families with
`f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1`, both are open substacks of `Curves`, and
for a family of curves `f : X → S` in `Curves^{grc,1}` the module `R¹f_*𝒪_X` is a finite locally
free `𝒪_S`-module whose formation commutes with arbitrary base change.

## Main results

* `AlgebraicGeometry.curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage_of`:
  `Curves^{grc,1}` and `Curves^{h0,1}` are open substacks of `Curves`, the first is contained in
  the second, and for a family of curves in the first `R¹f_*𝒪_X` is finite locally free and
  commutes with arbitrary base change.

## Implementation notes

The result takes as hypotheses:

* `hconst`: for a proper, geometrically reduced and geometrically connected algebraic space `X`
  over a field `k`, the map `k → Γ(X, 𝒪_X)` is bijective;
* `hopen`: the families of curves with bijective global functions on their fibres over fields
  form an open locus;
* `hpush`: such a family has `f_*𝒪_X = 𝒪_S` universally;
* `hR1`, `hR1bc`: for a family of curves whose fibres have the residue fields as global functions,
  `R¹f_*𝒪_X` is finite locally free, and its formation commutes with base change.

## References

* [Stacks Project, Tag 0E6L](https://stacks.math.columbia.edu/tag/0E6L)
* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`Curves^{grc,1} ⊂ Curves^{h0,1}` as open substacks of `Curves`.** The strictly full
subcategories `Curves^{grc,1}` of families of curves whose geometric fibres are reduced, connected
and of dimension `1` and `Curves^{h0,1}` of families with `f_*𝒪_X = 𝒪_S` universally and fibres of
dimension `1` are open substacks of `Curves` — each is closed under isomorphisms and its inclusion
is representable by algebraic spaces and an open immersion — the first is contained in the second,
and for every family of curves in the first the module `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module whose formation commutes with arbitrary base change.

This takes as hypotheses `hconst` (global functions of a proper, geometrically reduced and
geometrically connected algebraic space over a field `k` are `k`), `hopen` and `hpush` (bijectivity
of global functions on fibres over fields is an open condition, and implies `f_*𝒪_X = 𝒪_S`
universally), and `hR1`, `hR1bc` (`R¹f_*𝒪_X` is finite locally free and commutes with base change
for families whose fibres have the residue fields as global functions). -/
theorem curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage_of
    (hconst : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
      (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))), Space.IsProper B (Spec (.of k)) hk f →
        Space.IsGeometricallyReduced k B hk X hX → Space.IsGeometricallyConnected B k hk X →
        Function.Bijective (algebraMap k (Space.globalFunctions B (Spec (.of k)) hk X)))
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hR1 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (hR1bc : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsGrc1CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom)) ∧
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom)) ∧
    IsGrc1CurveFamily B hZ ≤ IsH01CurveFamily B hZ ∧
    ∀ X : CurveFamily B hZ, IsGrc1CurveFamily B hZ X →
      X.HasFiniteLocallyFreeFirstHigherDirectImage ∧
        X.FirstHigherDirectImageCommutesWithBaseChange :=
  ⟨(curvesGrc1_isOpenSubstack_and_factors_iff B hZ).1,
    (curvesH01_isOpenSubstack_and_factors_iff_of hopen hpush).1,
    isGrc1CurveFamily_le_isH01CurveFamily_of hconst hpush,
    fun _ hX =>
      CurveFamily.firstHigherDirectImage_of_isGrc1CurveFamily_of hconst hpush hR1 hR1bc hX⟩

end AlgebraicGeometry

end
