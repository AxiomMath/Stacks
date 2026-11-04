module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of quasi-compactness along surjections

Quasi-compactness of a morphism of schemes descends along a surjection in two ways. In a
commutative triangle whose first morphism is surjective, quasi-compactness of the composite
gives quasi-compactness of the second morphism, because every compact preimage downstairs is the
image of a compact preimage upstairs. Along an *open* surjection of base schemes one may instead
descend quasi-compactness from the base change, by shrinking a compact open of the base to a
compact open upstairs with the same image.

## Main results

* `AlgebraicGeometry.quasiCompact_of_comp_surjective`: quasi-compactness of a composite descends
  along a surjective first morphism.
* `AlgebraicGeometry.quasiCompact_of_isOpenMap_surjective_baseChange`: quasi-compactness
  descends along an open, surjective morphism of target schemes.

## References

* [Stacks Project, Tag 04ZD](https://stacks.math.columbia.edu/tag/04ZD)
* [Stacks Project, Tag 04ZE](https://stacks.math.columbia.edu/tag/04ZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If `f` is surjective and `f ≫ q` is quasi-compact, then `q` is quasi-compact. -/
@[stacks 04ZD, ega "IV 1.1.3"]
public theorem quasiCompact_of_comp_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ q)] :
    QuasiCompact q := by
  refine ⟨fun U hU hc => ?_⟩
  simpa [Scheme.Hom.comp_base, Set.preimage_comp, Set.image_preimage_eq_inter_range,
    range_eq_univ] using
    (QuasiCompact.isCompact_preimage (f := f ≫ q) U hU hc).image f.continuous

/-- Quasi-compactness of a morphism of schemes descends along an open,
surjective morphism of target schemes. -/
@[stacks 04ZE]
public theorem quasiCompact_of_isOpenMap_surjective_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hopen : IsOpenMap g.base) [Surjective g]
    [QuasiCompact (pullback.snd f g)] : QuasiCompact f := by
  refine ⟨fun V hVopen hVcompact => ?_⟩
  obtain ⟨W, hWcompact, hWimage⟩ :=
    hopen.exists_opens_image_eq_of_prespectralSpace g.continuous (fun y _ => g.surjective y)
      hVopen hVcompact
  rw [← hWimage, ← Scheme.image_preimage_eq_of_isPullback
    (IsPullback.of_isLimit (pullbackIsPullback f g)).flip]
  exact (QuasiCompact.isCompact_preimage (f := pullback.snd f g) W W.2 hWcompact).image
    (pullback.fst f g).continuous

end AlgebraicGeometry
