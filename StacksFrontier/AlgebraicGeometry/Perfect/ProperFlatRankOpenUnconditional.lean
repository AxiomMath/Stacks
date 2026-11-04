module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Assembly
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian

/-!
# Stacks 0B9S

Let `f : X ⟶ S` be proper and of finite presentation and let `ℱ` be an `𝒪_X`-module of finite
presentation, flat over `S`. For an integer `i` and a natural number `r` there is an open `U ⊆ S`
such that a morphism `g : T ⟶ S` factors through `U` exactly when `Rf_{T,*}ℱ_T` is a finite
locally free module of rank `r` placed in degree `i` ([Stacks, Tag 0B9S]).

Both halves of [Stacks, Tag 0B91] — perfectness of `Rf_*ℱ` and the base change isomorphism
`Lg^*Rf_*ℱ ≅ Rf_{T,*}ℱ_T` — hold for `f` proper of finite presentation and `ℱ` of finite
presentation and flat over `S`, so the statement holds with no further hypotheses.

## Main results

* `exists_opens_factorsThrough_iff_hasDerivedPushforwardRank`: [Stacks, Tag 0B9S].

## Implementation notes

The rank is a natural number where the source writes `r ∈ ℤ`: no module is locally free of
negative rank, so for `r < 0` the source's open is empty and the statement has no content beyond
that.

## References

* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- **[Stacks, Tag 0B9S].** Let `π : Y ⟶ T` be proper and of finite presentation, `ℱ` an
`𝒪_Y`-module of finite presentation flat over `T`, `i` an integer and `r` a natural number. There
is an open `U ⊆ T` such that a morphism `h : T' ⟶ T` factors through `U` exactly when
`Rπ'_*(h'^*ℱ)` is a finite locally free `𝒪_{T'}`-module of rank `r` placed in degree `i`, for the
base change `π' : Y' ⟶ T'` of `π` along `h` (any cartesian square). -/
@[stacks 0B9S "the rank r is a natural number: no module is locally free of negative rank, so \
for r < 0 the source's open is empty"]
theorem exists_opens_factorsThrough_iff_hasDerivedPushforwardRank {Y T : Scheme.{u}}
    (π : Y ⟶ T) (hfp : FinitePresentation π) [IsProper π] (F : Y.Modules)
    (hF : F.IsFinitePresentation) (hflat : IsFlatOver π.toLRSHom.toShHom F) (i : ℤ) (r : ℕ) :
    ∃ U : T.Opens, ∀ {Y' T' : Scheme.{u}} (h : T' ⟶ T) (π' : Y' ⟶ T') (h' : Y' ⟶ Y),
      IsPullback h' π' π h →
      ((∃ g : T' ⟶ U.toScheme, g ≫ U.ι = h) ↔
        HasDerivedPushforwardRank π' ((Scheme.Modules.pullback h').obj F) i r) :=
  exists_opens_factorsThrough_iff_of_baseChange
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward π hfp F hF hflat i r

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
