module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldFibreTopologicalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent

/-!
# A finite set-theoretic fibre has a finite field fibre, for decent spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, let `y` be the point
of `|Y|` it represents, let `F = f^{-1}({y}) ⊂ |X|` be the set-theoretic fibre and let
`X_k = X ×_Y Spec(k)` be the field fibre. The last assertion of Stacks 0ACK is that when both
`X` and `Y` are decent, condition (1) — that `F` is finite — implies all the other conditions
of the tag. This file proves the one of them that does not already follow from the equivalences
already proved, namely condition (4): the point set of `X_k` is finite.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.finite_preimage_pointsMap_of_mono_of_isQuasiFiniteAt` is Stacks
  0AC7 read for one fibre of the upper horizontal morphism of a cartesian square of Tag 0AC1
  whose lower-left corner has at most one point.
* `AlgebraicGeometry.Space.finite_fibre_pointsMap_fst_fieldFibre`: the fibre of the comparison
  map `|X_k| → |X|` over a point at which `f` is quasi-finite is finite, for a decent target.
* `AlgebraicGeometry.Space.finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent` is
  Stacks 0ACK, condition (1) implies condition (4) for decent source and target.

## Implementation notes

The comparison map `|X_k| → |X|` is surjective onto `F` by Tag 03H4
(`AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`), so a finite `F` leaves exactly one
thing to prove: that each of its fibres is finite. Discreteness of `|X_k|` is *not* enough for
that — a discrete space surjecting onto a finite set may well be infinite — which is why the
implication needs an input beyond the already proved equivalences of the tag.

That input is Stacks 0AC7,
`AlgebraicGeometry.Space.finite_fibrePoints_of_mono_of_isQuasiFiniteAt`, read against the
*reflected* square. The set of Tag 0AC2 of the reflected square at the pair `(z, x)` is the
same set as that of the original square at `(x, z)`
(`AlgebraicGeometry.Space.fibrePoints_flip`), and reflecting exchanges the roles of the tag's
two hypotheses, so what they ask for here is a monomorphic representative of `y`, which
decency of `Y` supplies, and quasi-finiteness of `f` at `x`. The lower-left corner of the
square is `Spec(k)`, which has exactly one point, so the set of Tag 0AC2 at `(x, z)` *is* the
fibre of `|X_k| → |X|` over `x` and nothing is lost in passing to it; when `|Spec(k)|` carries
no point compatible with `x` the fibre is empty, because the square is cartesian.

Quasi-finiteness of `f` at the points of `F` is not an extra hypothesis: it is condition (8),
which
`AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint`
derives from condition (5) for any representative of `y`, and condition (5) for the
quasi-compact monomorphic representative `q` that decency of `Y` supplies follows from a
finite `F` in two steps: Lemma 0AC8 (`AlgebraicGeometry.Space.homeomorphSetFibre`) identifies
`|X_q|` with `F`, making it finite, and the already proved "condition (4) implies condition (5) for
a decent morphism" then makes it discrete.

That last step is where decency of the *source* enters, and it enters through Stacks 03KF.
`AlgebraicGeometry.Space.discreteTopology_points_fieldFibre_of_finite_of_isDecent` asks for
`AlgebraicGeometry.Space.IsDecent`, decency of the morphism in the sense of Stacks 03KZ, which
decency of `X` supplies by
`AlgebraicGeometry.Space.isDecent_of_isDecentSpace_source` (Stacks 0ABX, the decent case):
every representable base change `Spec(T) ×_Y X ⟶ X` of a morphism into an algebraic space is
relatively representable, so `AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`
turns decency of `X` into decency of all of them at once. The hypothesis is phrased as decency
of the source rather than of the morphism because the former is the stronger of the two.

Neither the fibre finiteness nor Stacks 0AC7 behind it uses decency of `X`, or local finite
type of `f`: `AlgebraicGeometry.Space.finite_fibre_pointsMap_fst_fieldFibre` needs only
decency of the target and quasi-finiteness at the one point.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_fieldFibreFiniteDecent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_fieldFibreFiniteDecent
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_fieldFibreFiniteDecent B S hS).has_limit _

/-! ### Stacks 0AC7 as a statement about one fibre of the upper horizontal morphism -/

/-- **Stacks 0AC7, read for a fibre of the upper horizontal morphism.** Let `D` be a cartesian
square of Tag 0AC1 whose lower-left corner `Z` has at most one point. If the image in `|Y|` of
a point `x` of `|X|` is represented by a monomorphism from the spectrum of a field and the
right vertical morphism `f` is quasi-finite at `x`, then the fibre of `|W| → |X|` over `x` is
finite.

With `|Z|` a subsingleton, the fibre of `|W| → |X|` over `x` coincides with the set of Tag
0AC2 attached to `x` and the unique point of `|Z|`, as soon as `|Z|` has one compatible with
`x`; and if it has none then the fibre is empty, because the square is cartesian. The set of
Tag 0AC2 is finite by Stacks 0AC7 applied to the reflected square
`AlgebraicGeometry.Space.PointsFibresDiagram.flip`, in which the roles of the two prescribed
points — and hence of the two hypotheses of that tag — are exchanged. -/
theorem finite_preimage_pointsMap_of_mono_of_isQuasiFiniteAt (D : PointsFibresDiagram B S hS)
    (hZ : Subsingleton (points B S hS D.Z)) (x : points B S hS D.X)
    (hy : HasMonomorphicFieldRepresentative B S hS D.Y (pointsMap B S hS D.X D.f x))
    (hx : IsQuasiFiniteAt B S hS D.f x) :
    (pointsMap B S hS D.W D.p ⁻¹' {x}).Finite := by
  by_cases hex : ∃ z : points B S hS D.Z,
      pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z
  · obtain ⟨z, h⟩ := hex
    have hy' : HasMonomorphicFieldRepresentative B S hS D.Y
        (pointsMap B S hS D.Z D.g z) := by rw [← h]; exact hy
    have heq : pointsMap B S hS D.W D.p ⁻¹' {x} = fibrePoints D x z h := by
      ext w
      exact ⟨fun hw ↦ ⟨hw, hZ.elim _ _⟩, fun hw ↦ hw.1⟩
    rw [heq, ← fibrePoints_flip D x z h]
    exact finite_fibrePoints_of_mono_of_isQuasiFiniteAt D.flip z x h.symm hy' hx
  · have hempty : pointsMap B S hS D.W D.p ⁻¹' {x} = (∅ : Set (points B S hS D.W)) := by
      ext w
      refine ⟨fun hw ↦ hex ⟨pointsMap B S hS D.W D.q w, ?_⟩, fun hw ↦ hw.elim⟩
      rw [show x = pointsMap B S hS D.W D.p w from hw.symm, ← pointsMap_comp_apply,
        ← pointsMap_comp_apply, D.isPullback.w]
    rw [hempty]
    exact Set.finite_empty

/-- **Each fibre of the comparison map `|X_k| → |X|` is finite.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` with `Y` decent, and let `p` be a field-valued point of
`Y`. If `f` is quasi-finite at a point `x` of `|X|`, then the set of points of the field fibre
`X_k` above `x` is finite.

This is `AlgebraicGeometry.Space.finite_preimage_pointsMap_of_mono_of_isQuasiFiniteAt` for the
cartesian square `X_k = X ×_Y Spec(k)` of Tag 0AC1, whose lower-left corner `Spec(k)` is a
one-point scheme; decency of `Y` provides the monomorphic representative of the image of `x`,
which is condition (4) of Stacks 03JU. Neither local finite type of `f` nor decency of `X` is
used. -/
theorem finite_fibre_pointsMap_fst_fieldFibre (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (x : points B S hS X)
    (hx : IsQuasiFiniteAt B S hS f x) :
    (pointsMap B S hS (fieldFibre B S hS f p)
      (pullback.fst f (fieldMorphism B S hS Y p)) ⁻¹' {x}).Finite :=
  have hsub : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
      subsingleton_toScheme_siteObject B S hS Y p
    (pointsEquivScheme B S hS p.siteObject).subsingleton
  finite_preimage_pointsMap_of_mono_of_isQuasiFiniteAt B S hS
    { W := fieldFibre B S hS f p
      Z := yoneda.obj p.siteObject
      X := X
      Y := Y
      W_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p) hX
        (isAlgebraicSpace_yoneda B S hS p.siteObject) hY
      Z_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS p.siteObject
      X_isAlgebraicSpace := hX
      Y_isAlgebraicSpace := hY
      q := pullback.snd f (fieldMorphism B S hS Y p)
      p := pullback.fst f (fieldMorphism B S hS Y p)
      f := f
      g := fieldMorphism B S hS Y p
      isPullback := IsPullback.of_hasPullback f (fieldMorphism B S hS Y p) }
    hsub x (hYdec.hasMonomorphicFieldRepresentative B S hS Y _) hx

/-! ### Condition (1) implies condition (4) for decent spaces -/

/-- **Stacks 0ACK, condition (1) implies condition (4) for decent spaces.** Let `f : X ⟶ Y` be
a morphism of algebraic spaces over `S` which is locally of finite type, let `p` be a
field-valued point of `Y` with set-theoretic fibre `F`, and let both `X` and `Y` be decent. If
`F` is finite, then the point set of the field fibre `X_k` is finite.

The comparison map `|X_k| → |X|` has image `F` by Tag 03H4, so `|X_k|` is the union of its
fibres over the finitely many points of `F`, and each of those is finite by
`AlgebraicGeometry.Space.finite_fibre_pointsMap_fst_fieldFibre` once `f` is known to be
quasi-finite at every point of `F`. That is condition (8) of the tag, and it follows from a
finite `F`: decency of `Y` supplies a quasi-compact monomorphic representative `q` of the same
point of `|Y|`, Lemma 0AC8 identifies `|X_q|` with `F` and so makes it finite, decency of `X`
makes `f` a decent morphism and hence `|X_q|` discrete, and condition (5) for `q` is condition
(8) for `q`, which is condition (8) for `p` because condition (8) is representative-free. -/
@[stacks 0ACK "condition (1) implies condition (4) for decent spaces"]
theorem finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hft : IsLocallyOfFiniteType B S hS f)
    (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (hfinite : (setFibre B S hS f p).Finite) :
    (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite := by
  classical
  -- Decency of `Y` supplies a quasi-compact monomorphic representative of the same point.
  obtain ⟨q, hqclass, hmono, hqc⟩ := hYdec (p.class B S hS Y)
  have hset : setFibre B S hS f q = setFibre B S hS f p :=
    setFibre_eq_of_class_eq B S hS f p q hqclass
  -- Lemma 0AC8 makes the point set of `X_q` finite, and decency of `X` makes it discrete.
  have hfinq : (Set.univ : Set (points B S hS (fieldFibre B S hS f q))).Finite :=
    have : Finite (setFibre B S hS f q) := by rw [hset]; exact hfinite
    have : Finite (points B S hS (fieldFibre B S hS f q)) :=
      Finite.of_equiv _ (homeomorphSetFibre B S hS hX hY f q hmono hqc).toEquiv.symm
    Set.finite_univ
  have hdisc : IsDiscreteFieldFibrePoints B S hS f q :=
    discreteTopology_points_fieldFibre_of_finite_of_isDecent B S hS hX hY f q hft
      (isDecent_of_isDecentSpace_source B S hS hX hY f hXdec) hfinq
  -- Condition (5) for `q` is condition (8), which does not depend on the representative.
  have h8 : IsQuasiFiniteAboveFieldValuedPoint B S hS f p :=
    (isQuasiFiniteAboveFieldValuedPoint_iff_of_class_eq B S hS f p q hqclass).mp
      ((isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft
        q).mp hdisc)
  -- The point set of `X_k` is the union of the fibres over the finitely many points of `F`.
  refine Set.Finite.subset (hfinite.biUnion fun x hx ↦
    finite_fibre_pointsMap_fst_fieldFibre B S hS hX hY f p hYdec x (h8 x hx)) ?_
  intro w _
  exact Set.mem_biUnion
    (show pointsMap B S hS (fieldFibre B S hS f p)
        (pullback.fst f (fieldMorphism B S hS Y p)) w ∈ setFibre B S hS f p from by
      rw [← range_pointsMap_fst_fieldFibre B S hS f p]
      exact Set.mem_range_self w) rfl

end AlgebraicGeometry.Space

end
