module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension

/-!
# Composing flat morphisms of good algebraic spaces of given relative dimension

A morphism of algebraic spaces which is locally of finite type is *flat of relative dimension
`r`* when it is flat and the fibre dimension and the transcendence degree of the residue field
extension add up to `r` at every point of its source. Let `X/B`, `Y/B` and `Z/B` be good
algebraic spaces over a base and let `f : X ⟶ Y` and `g : Y ⟶ Z` be flat of relative dimensions
`r` and `s` over the base. Then the composite `f ≫ g` is flat of relative dimension `r + s`.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimension_comp_of_isFlat`: the relative dimension of a
  composite of morphisms locally of finite type of relative dimensions `r` and `s`, the first of
  them flat, is `r + s`.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_comp`: the composite of flat morphisms
  of good algebraic spaces over the base of relative dimensions `r` and `s` is flat of relative
  dimension `r + s`.

## References

* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces over `S` which are
locally of finite type and have relative dimensions `r` and `s`, with `f` flat, the composite has
relative dimension `r + s`. -/
theorem hasRelativeDimension_comp_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfft : IsLocallyOfFiniteType B S hS f) (hgft : IsLocallyOfFiniteType B S hS g)
    (hflat : IsFlat B S hS f) (r s : ℕ) (hr : HasRelativeDimension r B S hS f)
    (hs : HasRelativeDimension s B S hS g) :
    HasRelativeDimension (r + s) B S hS (f ≫ g) := by
  intro x
  have hsum := hasRelativeDimensionAt_comp_of_isFlatAt B S hS hX hY hZ f g x hfft hgft
    (r : ℕ∞) (s : ℕ∞) (hr x) (hs (pointsMap B S hS X f x))
    ((isFlat_iff_forall_isFlatAt B S hS f).mp hflat x)
  rwa [← Nat.cast_add] at hsum

/-- Let `X/B`, `Y/B` and `Z/B` be good algebraic spaces over the base of `D` and let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms over the base which are flat of relative dimensions `r`
and `s`. Then the composite `f ≫ g` is flat of relative dimension `r + s`: it is locally of
finite type, flat, and of relative dimension `r + s`. -/
@[stacks 0EPA "the composite is flat of relative dimension r + s"]
theorem isFlat_and_hasRelativeDimension_comp (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (r s : ℕ)
    (hff : IsFlat D.site D.base D.base_mem f)
    (hfr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgs : HasRelativeDimension s D.site D.base D.base_mem g) :
    IsLocallyOfFiniteType D.site D.base D.base_mem (f ≫ g) ∧
      IsFlat D.site D.base D.base_mem (f ≫ g) ∧
        HasRelativeDimension (r + s) D.site D.base D.base_mem (f ≫ g) := by
  have hfft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f sY
      (by rw [hfbase]; exact hX.2.2)
  have hgft : IsLocallyOfFiniteType D.site D.base D.base_mem g :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hY.1 hZ.1 D.isAlgebraicSpace g sZ
      (by rw [hgbase]; exact hY.2.2)
  exact ⟨isLocallyOfFiniteType_comp' D.site D.base D.base_mem f g hY.1 hZ.1 hfft hgft,
    isFlat_comp D.site D.base D.base_mem hX.1 hY.1 hZ.1 f g hff hgf,
    hasRelativeDimension_comp_of_isFlat D.site D.base D.base_mem hX.1 hY.1 hZ.1 f g hfft hgft
      hff r s hfr hgs⟩

end AlgebraicGeometry.Space

end
