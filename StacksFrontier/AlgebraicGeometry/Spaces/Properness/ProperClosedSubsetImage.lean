module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Images and inverse images of closed subsets proper over the base

Let `X` and `Y` be algebraic spaces over a scheme `S`, both locally of finite type over an
algebraic space `A`, and let `f : X ⟶ Y` be a morphism over `A`. Stacks 0CZG collects three
statements about a closed subset `T` of the points of `X` or of `Y` which is proper over `A`:

* if `f` is universally closed, the image of `T` is closed in the points of `Y` and proper
  over `A`;
* if `Y` is separated over `A`, the image of `T` is closed in the points of `Y` and proper
  over `A`;
* if `f` is proper, the inverse image of a closed subset of `Y` proper over `A` is closed in the
  points of `X` and proper over `A`.

The two image statements have the same proof, isolated here as
`AlgebraicGeometry.Space.isProper_ι_comp_of_universallyClosed_ι_comp`: all that either needs of
its hypotheses is that the restriction `Z ⟶ Y` of `f` to the reduced induced closed subspace `Z`
on `T` is **universally closed**. In the first case that holds because `Z ⟶ X` is universally
closed and `f` is universally closed; in the second because `Z` is proper, hence universally
closed, over `A` and `Y ⟶ A` is separated, so Stacks 04NX cancels `Y ⟶ A`.

Granted that, the image of `T` is the image of the whole of `Z`, hence closed because a
universally closed morphism is closed (Stacks 03HI). The reduced induced subspace `Z'` on it
receives `Z` by Stacks 03JJ, surjectively on points; the receiving morphism is universally closed,
again by Stacks 04NX, since `Z' ⟶ Y` is a monomorphism and so separated. Properness of `Z`
over `A` then makes `Z'` separated over `A` by Stacks 05Z2 and quasi-compact over `A` by
Stacks 040W, while the inclusion of `Z'` is locally of finite type and so Stacks 03XG makes it
locally of finite type over `A`; Stacks 08AJ assembles these into properness of `Z'` over `A`.

The inverse image statement is a base change instead: the inverse image of `Z` along a proper
`f` is proper over `Z`, by Stacks 04WP, hence proper over `A`; and the reduced induced subspace
on the inverse image of `T` factors through that inverse image, by the unconditional form of
Stacks 03JJ at a reduced induced subspace together with the universal property of the Cartesian
square. Closedness of the inverse image is Stacks 0EP6, continuity of the map on points.

## Main results

* `AlgebraicGeometry.Space.isClosed_image_of_universallyClosed`: **Stacks 0CZG**, closedness of
  the image under a universally closed morphism.
* `AlgebraicGeometry.Space.isProperOver_image_of_universallyClosed`: **Stacks 0CZG**, properness
  over the base of that image.
* `AlgebraicGeometry.Space.isClosed_image_of_isProperOver`: **Stacks 0CZG**, closedness of the
  image in a target separated over the base.
* `AlgebraicGeometry.Space.isProperOver_image_of_isSeparated`: **Stacks 0CZG**, properness over
  the base of that image.
* `AlgebraicGeometry.Space.isProperOver_preimage_of_isProper`: **Stacks 0CZG**, properness over
  the base of the inverse image along a proper morphism.

Closedness of the inverse image is recorded on the Stacks 0EP6 declaration
`AlgebraicGeometry.Space.isClosed_preimage_pointsMap` rather than restated here.

## Implementation notes

No statement here needs the reduced induced subspace on a closed set of points to be a *closed*
subspace, which in this library is the one clause of Stacks 03IQ that waits on effective
descent. Where the source uses that the inclusion of a reduced induced subspace is a closed
immersion, this file uses instead that it is a monomorphism, that it is locally of finite type
and that it is universally closed, all of which hold unconditionally; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/Properness/ProperClosedSubset.lean`.

For the universally closed morphism and for the inverse image the structure morphism of `X` is
written as the composite of `f` with the structure morphism of `Y`; for the separated target it
is a morphism of its own together with a commutativity hypothesis, as in the source.

## References

* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

add_to_stacks 0CZG AlgebraicGeometry.Space.isClosed_preimage_pointsMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Images of a closed subset along a universally closed restriction -/

section Image

variable {X Y A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of a closed set of points is the image of the whole reduced induced subspace on
it**, the set of points of that subspace being the closed set one started with. -/
theorem range_pointsMap_ι_comp_reducedClosedSubspace (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T) (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
        ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f)) = pointsMap B S hS X f '' T := by
  rw [pointsMap_comp, Set.range_comp, range_pointsMap_ι_reducedClosedSubspace]

/-- **If the restriction of `f` to the reduced induced subspace on `T` is universally closed, the
image of `T` is closed.** A universally closed morphism of algebraic spaces over `S` is closed by
Stacks 03HI, and the image of `T` is the image of the whole subspace. -/
theorem isClosed_image_of_universallyClosed_ι_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hk : UniversallyClosed B S hS ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f)) :
    IsClosed (pointsMap B S hS X f '' T) := by
  have h := isClosed_of_universallyClosed B S hS hY _ hk Set.univ isClosed_univ
  rwa [Set.image_univ, range_pointsMap_ι_comp_reducedClosedSubspace] at h

/-- **If the restriction of `f` to the reduced induced subspace on `T` is universally closed and
`T` is proper over `A`, then the image of `T` is proper over `A`.**

This is the common content of the two image statements of Stacks 0CZG. The reduced induced
subspace `Z'` on the image receives the reduced induced subspace `Z` on `T` by Stacks 03JJ, and
the receiving morphism `p` is surjective on points because the points of `Z'` are exactly the
image of the points of `Z`, while the inclusion of `Z'` is injective on points by Stacks 06RV.
Universal closedness of `p` follows from that of `Z ⟶ Y` by Stacks 04NX, the inclusion of `Z'`
being a monomorphism and hence separated. Properness of `Z` over `A` then transfers to `Z'`
by Stacks 05Z2, Stacks 040W, Stacks 03XG and Stacks 08AJ. -/
theorem isProper_ι_comp_of_universallyClosed_ι_comp (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (g : Y ⟶ A) (hg : IsLocallyOfFiniteType B S hS g)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hk : UniversallyClosed B S hS ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f))
    (hT' : IsClosed (pointsMap B S hS X f '' T))
    (hTproper : IsProper B S hS
      ((reducedClosedSubspace B S hS X hX T hT).ι ≫ (f ≫ g))) :
    IsProper B S hS
      ((reducedClosedSubspace B S hS Y hY (pointsMap B S hS X f '' T) hT').ι ≫ g) := by
  set Z := reducedClosedSubspace B S hS X hX T hT with hZdef
  set Z' := reducedClosedSubspace B S hS Y hY (pointsMap B S hS X f '' T) hT' with hZ'def
  have hZalg : IsAlgebraicSpace B S hS Z.toFunctor :=
    hZdef ▸ isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT
  have hZ'alg : IsAlgebraicSpace B S hS Z'.toFunctor :=
    hZ'def ▸ isAlgebraicSpace_reducedClosedSubspace B S hS Y hY _ hT'
  have hZkrange : Set.range (pointsMap B S hS Z.toFunctor (Z.ι ≫ f)) =
      pointsMap B S hS X f '' T :=
    hZdef ▸ range_pointsMap_ι_comp_reducedClosedSubspace B S hS hX T hT f
  have hZ'range : Set.range (pointsMap B S hS Z'.toFunctor Z'.ι) =
      pointsMap B S hS X f '' T :=
    hZ'def ▸ range_pointsMap_ι_reducedClosedSubspace B S hS Y hY _ hT'
  -- the reduced induced subspace on `T` maps to the one on the image
  obtain ⟨p, hp⟩ :=
    (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS Y hY _ hT' hZalg
      (hZdef ▸ hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT)
      (Z.ι ≫ f)).2 (by rw [hZkrange])
  -- and does so surjectively on points
  have hpSurj : IsSurjective B S hS p := by
    intro z'
    obtain ⟨z, hz⟩ : pointsMap B S hS Z'.toFunctor Z'.ι z' ∈
        Set.range (pointsMap B S hS Z.toFunctor (Z.ι ≫ f)) :=
      hZkrange.trans hZ'range.symm ▸ ⟨z', rfl⟩
    refine ⟨z, pointsMap_injective_of_mono B S hS Z'.ι ?_⟩
    rw [← pointsMap_comp_apply, hp]
    exact hz
  -- `p` is universally closed, the inclusion of the image being a monomorphism
  have hpUC : UniversallyClosed B S hS p :=
    universallyClosed_of_comp_of_isSeparated B S hS hZalg hZ'alg hY p Z'.ι
      (by rw [hp]; exact hk) (isSeparated_of_mono B S hS Z'.ι inferInstance)
  have hpq : p ≫ (Z'.ι ≫ g) = Z.ι ≫ (f ≫ g) := by
    rw [← Category.assoc, hp, Category.assoc]
  have hqsep : IsSeparated B S hS (Z'.ι ≫ g) :=
    isSeparated_of_isSurjective_of_universallyClosed B S hS hZalg hZ'alg hA p (Z'.ι ≫ g)
      hpSurj hpUC (by rw [hpq]; exact hTproper.1)
  have hqftLocal : IsLocallyOfFiniteType B S hS (Z'.ι ≫ g) :=
    isLocallyOfFiniteType_comp B S hS hZ'alg hY hA Z'.ι g
      (isLocallyOfFiniteType_ι_reducedClosedSubspace B S hS Y hY _ hT') hg
  have hqqc : IsQuasiCompact B S hS (Z'.ι ≫ g) :=
    isQuasiCompact_of_comp_surjective B S hS hZalg hZ'alg hA p (Z.ι ≫ (f ≫ g)) (Z'.ι ≫ g)
      hpq.symm hpSurj hTproper.2.1.2
  exact isProper_of_isSurjective_comp B S hS hZalg hZ'alg hA p (Z'.ι ≫ g)
    (by rw [hpq]; exact hTproper.2.2) hpSurj hqsep ⟨hqftLocal, hqqc⟩

/-! #### A universally closed morphism -/

/-- **Stacks 0CZG, closedness of the image under a universally closed morphism.** A universally
closed morphism of algebraic spaces over `S` carries closed subsets of its space of points to
closed subsets: it is closed, by Stacks 03HI. -/
@[stacks 0CZG "image_universally_closed"]
theorem isClosed_image_of_universallyClosed (_hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : UniversallyClosed B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsClosed (pointsMap B S hS X f '' T) :=
  isClosed_of_universallyClosed B S hS hY f hf T hT

/-- **Stacks 0CZG, properness of the image under a universally closed morphism.** The image of a
closed subset proper over the base under a universally closed morphism is proper over the base.

The restriction of a universally closed morphism to the reduced induced subspace is universally
closed, the inclusion of that subspace being universally closed, so
`AlgebraicGeometry.Space.isProper_ι_comp_of_universallyClosed_ι_comp` applies. -/
@[stacks 0CZG "image_universally_closed"]
theorem isProperOver_image_of_universallyClosed (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (g : Y ⟶ A) (hf : UniversallyClosed B S hS f)
    (hXft : IsLocallyOfFiniteType B S hS (f ≫ g))
    (hYft : IsLocallyOfFiniteType B S hS g)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hTproper : IsProperOver B S hS hX hA (f ≫ g) hXft T hT) :
    IsProperOver B S hS hY hA g hYft (pointsMap B S hS X f '' T)
      (isClosed_image_of_universallyClosed B S hS hX hY f hf T hT) :=
  isProper_ι_comp_of_universallyClosed_ι_comp B S hS hX hY hA f g hYft T hT
    (universallyClosed_comp B S hS hX hY _ f
      (universallyClosed_ι_reducedClosedSubspace B S hS X hX T hT) hf)
    _ hTproper

/-! #### A target separated over the base -/

/-- **The restriction of `f` to the reduced induced subspace on a closed set `T` proper over `A`
is universally closed when `Y` is separated over `A`**, by Stacks 04NX. -/
private theorem universallyClosed_ι_comp_of_isProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (pX : X ⟶ A) (pY : Y ⟶ A) (hcomm : f ≫ pY = pX)
    (hpX : IsLocallyOfFiniteType B S hS pX) (hsep : IsSeparated B S hS pY)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hproper : IsProperOver B S hS hX hA pX hpX T hT) :
    UniversallyClosed B S hS ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f) :=
  universallyClosed_of_comp_of_isSeparated B S hS
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT) hY hA _ pY
    (by rw [Category.assoc, hcomm]; exact hproper.2.2) hsep

/-- **Stacks 0CZG, closedness of the image in a separated target.** If the structure morphism of
`Y` is separated and the closed subset `T` of the points of `X` is proper over the base, then the
image of `T` in the points of `Y` is closed.

The reduced induced subspace on `T` is universally closed over the base, so its morphism to `Y`
is universally closed by Stacks 04NX, the structure morphism of `Y` being separated. -/
@[stacks 0CZG "image_separated"]
theorem isClosed_image_of_isProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (pX : X ⟶ A) (pY : Y ⟶ A) (hcomm : f ≫ pY = pX)
    (hpX : IsLocallyOfFiniteType B S hS pX) (_hpY : IsLocallyOfFiniteType B S hS pY)
    (hsep : IsSeparated B S hS pY)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hproper : IsProperOver B S hS hX hA pX hpX T hT) :
    IsClosed (pointsMap B S hS X f '' T) :=
  isClosed_image_of_universallyClosed_ι_comp B S hS hX hY f T hT
    (universallyClosed_ι_comp_of_isProperOver B S hS hX hY hA f pX pY hcomm hpX hsep T hT hproper)

/-- **Stacks 0CZG, properness of the image in a separated target.** The image in `Y` of a closed
subset of `X` proper over the base is proper over the base when the structure morphism of `Y` is
separated.

As for closedness, the reduced induced subspace on `T` is universally closed over `Y` by
Stacks 04NX, so `AlgebraicGeometry.Space.isProper_ι_comp_of_universallyClosed_ι_comp` applies. The
closedness of the image is an explicit hypothesis, as `AlgebraicGeometry.Space.IsProperOver` is a
predicate on closed subsets. -/
@[stacks 0CZG "image_separated"]
theorem isProperOver_image_of_isSeparated (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (pX : X ⟶ A) (pY : Y ⟶ A) (hcomm : f ≫ pY = pX)
    (hpX : IsLocallyOfFiniteType B S hS pX) (hpY : IsLocallyOfFiniteType B S hS pY)
    (hsep : IsSeparated B S hS pY)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hproper : IsProperOver B S hS hX hA pX hpX T hT)
    (hImage : IsClosed (pointsMap B S hS X f '' T)) :
    IsProperOver B S hS hY hA pY hpY (pointsMap B S hS X f '' T) hImage :=
  isProper_ι_comp_of_universallyClosed_ι_comp B S hS hX hY hA f pY hpY T hT
    (universallyClosed_ι_comp_of_isProperOver B S hS hX hY hA f pX pY hcomm hpX hsep T hT hproper)
    hImage (by rw [hcomm]; exact hproper)

end Image

/-! ### Inverse images under a proper morphism -/

section Preimage

variable {X Y A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CZG, properness of the inverse image.** The inverse image of a closed subset
proper over the base under a proper morphism is proper over the base. -/
@[stacks 0CZG "inverse_image_proper"]
theorem isProperOver_preimage_of_isProper (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (g : Y ⟶ A) (hf : IsProper B S hS f)
    (hXft : IsLocallyOfFiniteType B S hS (f ≫ g))
    (hYft : IsLocallyOfFiniteType B S hS g)
    (T : Set (points B S hS Y)) (hT : IsClosed T)
    (hTproper : IsProperOver B S hS hY hA g hYft T hT) :
    IsProperOver B S hS hX hA (f ≫ g) hXft (pointsMap B S hS X f ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS hX hY f hT) := by
  set Z := reducedClosedSubspace B S hS Y hY T hT with hZdef
  have hZalg : IsAlgebraicSpace B S hS Z.toFunctor :=
    hZdef ▸ isAlgebraicSpace_reducedClosedSubspace B S hS Y hY T hT
  set W := Z.preimage f with hWdef
  have hsqW : IsPullback (Z.fromPreimage f) W.ι Z.ι f := Subfunctor.isPullback_preimage f Z
  have hWalg : IsAlgebraicSpace B S hS W.toFunctor :=
    isAlgebraicSpace_of_isPullback hZalg hX hY.isSheaf hY.diagonal_representable hsqW
  have hsq : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f) :
        (⟨W.toFunctor, hWalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZalg⟩)
      (ObjectProperty.homMk W.ι) (ObjectProperty.homMk Z.ι)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsqW
  have hbase : IsProper B S hS (Z.fromPreimage f) :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hf
  have hWproper : IsProper B S hS (W.ι ≫ (f ≫ g)) := by
    have hcomp := isProper_comp B S hS hWalg hZalg hA (Z.fromPreimage f) (Z.ι ≫ g)
      hbase hTproper
    rwa [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc] at hcomp
  -- the reduced induced subspace on the inverse image of `T` maps to the one on `T`
  have hT' := isClosed_preimage_pointsMap B S hS hX hY f hT
  set V := reducedClosedSubspace B S hS X hX (pointsMap B S hS X f ⁻¹' T) hT'
  obtain ⟨u, hu⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS Y hY
    T hT (isAlgebraicSpace_reducedClosedSubspace B S hS X hX _ hT')
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _ hT') (V.ι ≫ f)).2
    (by rw [range_pointsMap_ι_comp_reducedClosedSubspace]; exact Set.image_preimage_subset _ _)
  exact isProperOver_of_isProper_ι_comp B S hS hX hA (f ≫ g) hXft _ hT' W hWalg hWproper
    (hsqW.lift u _ hu) (hsqW.lift_snd u _ hu)

end Preimage

end AlgebraicGeometry.Space

end
