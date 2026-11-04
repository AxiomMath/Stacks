module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Base change of a closed subset proper over the base

Let

```
X' ⟶ X
↓     ↓
Y' ⟶ Y
```

be a cartesian square of algebraic spaces over a scheme `S` whose right vertical morphism is
locally of finite type, and let `T` be a closed subset of the points of `X` which is proper over
`Y`. Then the inverse image of `T` in the points of `X'` is closed and proper over `Y'`.

Closedness needs nothing from the square: the map on points of any morphism of algebraic spaces
is continuous, which is Stacks 0EP6, already proved in this library as
`AlgebraicGeometry.Space.isClosed_preimage_pointsMap`.

For properness, the reduced induced closed subspace `Z` on `T` is pulled back along the upper
horizontal morphism. Its inverse image is again an algebraic space, its set of points is the
inverse image of `T` by Stacks 03H4, and it is proper over `Y'` because pasting the Cartesian
square of the inverse image onto the given one exhibits it as a base change of `Z ⟶ Y`,
properness being stable under base change by Stacks 04WP. The reduced induced subspace on the
inverse image of `T` maps to `Z`, by the unconditional form of Stacks 03JJ at a reduced induced
subspace, hence into the inverse image of `Z` by the universal property of the Cartesian square;
and that morphism is proper, so properness over `Y'` of the inverse image of `Z` gives
properness of the inverse image of `T` as a closed subset.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_ι_preimage`: **Stacks 03H4**, the point set of the
  inverse image of a subspace, for arbitrary presheaves.
* `AlgebraicGeometry.Space.isProperOver_preimage`: **Stacks 0CZF**, the properness assertion.

The closedness assertion of Stacks 0CZF is recorded on the Stacks 0EP6 declaration
`AlgebraicGeometry.Space.isClosed_preimage_pointsMap` rather than restated here.

## Implementation notes

No statement here needs the reduced induced subspace to be a *closed* subspace, which in this
library is the one clause of Stacks 03IQ that waits on effective descent. The inverse image of
the reduced induced subspace is an algebraic space because it is a fibre product of algebraic
spaces, and properness of a morphism out of a reduced induced subspace is
`AlgebraicGeometry.Space.isProper_of_comp_eq_ι_reducedClosedSubspace`; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/Properness/ProperClosedSubset.lean`.

The square is taken in `AlgebraicGeometry.AlgebraicSpaces`, the category of algebraic spaces
over `S`, because that is where properness is known to be stable under base change; the
Cartesian square of an inverse image of a subfunctor is transported into that category along
`AlgebraicGeometry.AlgebraicSpaces`' faithful inclusion into presheaves.

## References

* [Stacks Project, Tag 0CZF](https://stacks.math.columbia.edu/tag/0CZF)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

add_to_stacks 0CZF "closedness" AlgebraicGeometry.Space.isClosed_preimage_pointsMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point set of the inverse image of a subspace -/

/-- **The set of points of the inverse image of a subspace is the inverse image of its set of
points.** The inclusion of the inverse image sits in a cartesian square over the inclusion of
the subspace, so Stacks 03H4 produces a point of the inverse image above any point of the source
whose image lies in the subspace, and conversely the projection to the subspace witnesses the
containment. -/
theorem range_pointsMap_ι_preimage {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (Z : Subfunctor Y) (hZ : IsAlgebraicSpace B S hS Z.toFunctor) :
    Set.range (pointsMap B S hS (Z.preimage f).toFunctor (Z.preimage f).ι) =
      pointsMap B S hS X f ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  have hsqZ : IsPullback (Z.fromPreimage f) (Z.preimage f).ι Z.ι f :=
    Subfunctor.isPullback_preimage f Z
  have hP : IsAlgebraicSpace B S hS (Z.preimage f).toFunctor :=
    isAlgebraicSpace_of_isPullback hZ hX hY.isSheaf hY.diagonal_representable hsqZ
  have hpull : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f) :
        (⟨(Z.preimage f).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ⟩)
      (ObjectProperty.homMk (Z.preimage f).ι) (ObjectProperty.homMk Z.ι)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsqZ
  ext x
  refine ⟨?_, fun ⟨z, hz⟩ => (exists_point_of_isPullback B S hS hpull z x hz).imp fun _ h => h.2⟩
  rintro ⟨w, rfl⟩
  refine Set.mem_preimage.2
    ⟨pointsMap B S hS (Z.preimage f).toFunctor (Z.fromPreimage f) w, ?_⟩
  rw [← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  exact pointsMap_comp_apply B S hS (Z.preimage f).ι f w

/-- **The set of points of the inverse image of a subspace is the inverse image of its set of
points.** The inclusion of the inverse image sits in a cartesian square over the inclusion of
the subspace, and for a cartesian square of presheaves the preimage of the image of a set of
points is the image of its preimage, which is Stacks 03H4.

Nothing here needs any of the three presheaves to be an algebraic space. -/
theorem range_pointsMap_ι_preimage' {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (Z : Subfunctor Y) :
    Set.range (pointsMap B S hS (Z.preimage f).toFunctor (Z.preimage f).ι) =
      pointsMap B S hS X f ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  simpa only [Set.image_univ, Set.preimage_univ] using
    (preimage_image_pointsMap_of_isPullback B S hS
      (Subfunctor.isPullback_preimage f Z) Set.univ).symm

/-! ### Stacks 0CZF -/

/-- **Stacks 0CZF, properness.** In a cartesian square of algebraic spaces over `S` whose right
vertical morphism is locally of finite type, the inverse image of a closed subset proper over
the base is proper over the new base. -/
@[stacks 0CZF "properness"]
theorem isProperOver_preimage {X' X Y' Y : AlgebraicSpaces B S hS}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hproper : IsProperOver B S hS X.property Y.property f.hom hf T hT) :
    IsProperOver B S hS X'.property Y'.property f'.hom
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hf)
      (pointsMap B S hS X'.1 g'.hom ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT) := by
  set Z := reducedClosedSubspace B S hS X.1 X.property T hT with hZdef
  have hZalg : IsAlgebraicSpace B S hS Z.toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS X.1 X.property T hT
  set Q := Z.preimage g'.hom with hQdef
  have hsqQ : IsPullback (Z.fromPreimage g'.hom) Q.ι Z.ι g'.hom :=
    Subfunctor.isPullback_preimage g'.hom Z
  have hQalg : IsAlgebraicSpace B S hS Q.toFunctor :=
    isAlgebraicSpace_of_isPullback hZalg X'.property X.property.isSheaf
      X.property.diagonal_representable hsqQ
  have hpull : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage g'.hom) :
        (⟨Q.toFunctor, hQalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZalg⟩)
      (ObjectProperty.homMk Q.ι) (ObjectProperty.homMk Z.ι) g' :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsqQ
  have hQproper : IsProper B S hS (Q.ι ≫ f'.hom) :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback (hpull.paste_vert sq) hproper
  -- the reduced induced subspace on the inverse image of `T` maps to the one on `T`
  have hrange : Set.range (pointsMap B S hS
      (reducedClosedSubspace B S hS X'.1 X'.property (pointsMap B S hS X'.1 g'.hom ⁻¹' T)
        (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT)).toFunctor
      ((reducedClosedSubspace B S hS X'.1 X'.property (pointsMap B S hS X'.1 g'.hom ⁻¹' T)
        (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT)).ι ≫
          g'.hom)) ⊆ T := by
    rw [pointsMap_comp, Set.range_comp, range_pointsMap_ι_reducedClosedSubspace]
    exact Set.image_preimage_subset _ _
  obtain ⟨u, hu⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS
    X.1 X.property T hT
    (isAlgebraicSpace_reducedClosedSubspace B S hS X'.1 X'.property _
      (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT))
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X'.1 X'.property _
      (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT))
    ((reducedClosedSubspace B S hS X'.1 X'.property (pointsMap B S hS X'.1 g'.hom ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT)).ι ≫
        g'.hom)).2 hrange
  exact isProperOver_of_isProper_ι_comp B S hS X'.property Y'.property f'.hom _ _
    (isClosed_preimage_pointsMap B S hS X'.property X.property g'.hom hT) Q hQalg hQproper
    (hsqQ.lift u _ hu) (hsqQ.lift_snd u _ hu)

end AlgebraicGeometry.Space

end
