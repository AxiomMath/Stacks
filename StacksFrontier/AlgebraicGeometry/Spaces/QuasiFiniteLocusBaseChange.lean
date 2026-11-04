module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange

/-!
# Formation of the quasi-finite locus commutes with base change

For a cartesian square of algebraic spaces over `S` with `f` locally of finite type, the locus in
the source of the base change `f'` where `f'` is quasi-finite is the preimage of the locus in the
source of `f` where `f` is quasi-finite.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero`: a morphism locally of
  finite type is quasi-finite at a point exactly when its relative dimension there is zero.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_iff_of_isPullback`: the base change of `f` is
  quasi-finite at a point exactly when `f` is quasi-finite at its image.
* `AlgebraicGeometry.Space.setOf_isQuasiFiniteAt_eq_preimage_of_isPullback'`: the quasi-finite
  locus of the base change is the preimage of the quasi-finite locus of `f`.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-finiteness at a point is relative dimension zero -/

/-- A morphism of algebraic spaces over `S` which is locally of finite type is quasi-finite at a
point of its source exactly when its relative dimension there is zero. -/
theorem isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS X) :
    IsQuasiFiniteAt B S hS f x ↔ HasRelativeDimensionAt 0 B S hS f x := by
  constructor
  · rintro ⟨U, hU, x', rfl, hqf⟩
    have hι : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf U.ι :=
      presheaf_etale_of_isOpenImmersion B S hS hU.2
    refine (hasRelativeDimensionAt_comp_iff B S hS 0 U.ι f hι hU.1 hY x').mp ?_
    exact (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS (U.ι ≫ f)
      fun U₀ V₀ a b h ha hb hcomm ↦ (hqf U₀ V₀ a b h ha hb hcomm).1).mp hqf x'
  · intro hd
    obtain ⟨x', hx'⟩ : x ∈ Set.range (pointsMap B S hS
        (relativeDimensionZeroLocus B S hS f).toFunctor
        (relativeDimensionZeroLocus B S hS f).ι) := by
      rwa [range_pointsMap_relativeDimensionZeroLocus B S hS f]
    exact ⟨relativeDimensionZeroLocus B S hS f,
      isOpenSubspace_relativeDimensionZeroLocus B S hS hX hY f hf, x', hx',
      isLocallyQuasiFinite_relativeDimensionZeroLocus B S hS hX hY f hf⟩

/-! ### Part (2) of Tag 0ABM -/

/-- In a cartesian square of algebraic spaces over `S` with `f` locally of finite type, the base
change of `f` is quasi-finite at a point of its source exactly when `f` is quasi-finite at the
image of that point.

The square is the one with `p` over `f` and `q` over `g`, so `p : W ⟶ Z` is the base change of
`f : X ⟶ Y` and `q : W ⟶ X` is the projection. -/
theorem isQuasiFiniteAt_iff_of_isPullback
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hf : IsLocallyOfFiniteType B S hS f)
    (x' : points B S hS W) :
    IsQuasiFiniteAt B S hS p x' ↔
      IsQuasiFiniteAt B S hS f (pointsMap B S hS W q x') := by
  have hW : IsAlgebraicSpace B S hS W :=
    (isAlgebraicSpace_pullback B S hS g f hZ hX hY).of_iso sq.isoPullback.symm
  have hp : IsLocallyOfFiniteType B S hS p :=
    IsLocallyOfFiniteType.of_isPullback B S hS sq hX hY hf
  rw [isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hW hZ p hp x',
    isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hX hY f hf
      (pointsMap B S hS W q x'),
    hasRelativeDimensionAt_iff_of_isPullback' B S hS 0 sq hX hY hZ hf x']

/-- In a cartesian square of presheaves over `S` whose corners `X`, `Y` and `Z` are algebraic
spaces, with `f` locally of finite type, the locus in the source of the base change of `f` where
that base change is quasi-finite is the preimage, under the projection on points, of the locus in
the source of `f` where `f` is quasi-finite.

The square is the one with `p` over `f` and `q` over `g`, so `p : W ⟶ Z` is the base change of
`f : X ⟶ Y` and `q : W ⟶ X` is the projection. -/
@[stacks 0ABM "part (2): the quasi-finite locus commutes with base change"]
theorem setOf_isQuasiFiniteAt_eq_preimage_of_isPullback'
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hf : IsLocallyOfFiniteType B S hS f) :
    {x' | IsQuasiFiniteAt B S hS p x'} =
      pointsMap B S hS W q ⁻¹' {x | IsQuasiFiniteAt B S hS f x} :=
  Set.ext fun x' ↦ isQuasiFiniteAt_iff_of_isPullback B S hS sq hX hY hZ hf x'

end AlgebraicGeometry.Space

end
