module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Dimension zero of the field fibre, and quasi-finiteness above the point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, let `y` be the point
of `|Y|` it represents, and let `X_k = X ×_Y Spec(k)` be the field fibre. Stacks 0ACK compares
eight conditions on this data; `StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreConditions.lean`
states them and proves two of the eight implications of the source's diagram.

This file adds the implications that Lemma 0ACA
(`StacksFrontier/AlgebraicGeometry/Spaces/DimensionZeroOverField.lean`) and part (2) of Lemma
0ABM supply: condition (7) implies conditions (5), (6) and (8), and conditions (8) implies
conditions (7) and (5). The hinge is that condition (7), `dim(X_k) = 0`, is equivalent to
local quasi-finiteness of the structure morphism `X_k ⟶ Spec(k)`, and that condition (8) is
equivalent to that same local quasi-finiteness.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_snd_fieldFibre`: **Stacks 03XH** for the
  field fibre, that the structure morphism `X_k ⟶ Spec(k)` is locally of finite type.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_snd_fieldFibre_iff_dimension_le_zero`: the
  structure morphism `X_k ⟶ Spec(k)` is locally quasi-finite exactly when `dim(X_k) ≤ 0`.
* `isLocallyQuasiFinite_snd_fieldFibre_of_isQuasiFiniteAboveFieldValuedPoint` and
  `isQuasiFiniteAboveFieldValuedPoint_of_isLocallyQuasiFinite_snd_fieldFibre`, in
  `AlgebraicGeometry.Space`: condition (8) is local quasi-finiteness of `X_k ⟶ Spec(k)`.
* `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibre` is
  Stacks 0ACK, condition (7) implies condition (5).
* `AlgebraicGeometry.Space.isZeroDimensionalFieldFibrePoints_of_isZeroDimensionalFieldFibre`
  is Stacks 0ACK, condition (7) implies condition (6).
* `AlgebraicGeometry.Space.isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibre`
  is Stacks 0ACK, condition (7) implies condition (8).
* `AlgebraicGeometry.Space.isZeroDimensionalFieldFibre_of_isQuasiFiniteAboveFieldValuedPoint`
  is Stacks 0ACK, condition (8) implies condition (7).
* `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_of_isQuasiFiniteAboveFieldValuedPoint`
  is Stacks 0ACK, condition (8) implies condition (5).

## Implementation notes

The field fibre is `CategoryTheory.Limits.pullback f (yonedaEquiv.symm p.value)`, so its
structure morphism to `Spec(k)` is `CategoryTheory.Limits.pullback.snd`, and the cartesian
square used throughout is the flip of `CategoryTheory.IsPullback.of_hasPullback`: in the
orientation that Tag 0ABM and Tag 03XH expect, the base change of `f` is the projection to
`Spec(k)` and the projection to `X` sits over `Spec(k) ⟶ Y`.

Condition (7) is `dim(X_k) = 0` for the dimension of Tag 04N6, which is a supremum in
`WithBot ℕ∞`. Lemma 0ACA is therefore available here only in the `≤ 0` form, which is what
`AlgebraicGeometry.Space.isLocallyQuasiFinite_snd_fieldFibre_iff_dimension_le_zero` states; the
`= 0` form of condition (7) is strictly stronger, since it also forces `|X_k|` to be nonempty.
That is why the implications *out of* condition (7) need no nonemptiness hypothesis — they get
it for free from `AlgebraicGeometry.Space.nonempty_points_of_dimension_eq_zero` — while
condition (8) implies condition (7) only for a nonempty field fibre. Condition (8) implies
condition (5) with no nonemptiness hypothesis at all, because that route goes through local
quasi-finiteness of `X_k ⟶ Spec(k)` and never through the dimension: the empty space is
discrete, and has dimension `⊥`.

The arrows back into condition (7) from the topological conditions live further along. From
condition (5) it is
`AlgebraicGeometry.Space.isZeroDimensionalFieldFibre_of_isDiscreteFieldFibrePoints`
(`Spaces/FieldFibreDiscreteDecent.lean`); from condition (6) it is in
`Spaces/FieldFibreZeroDimensionalDecent.lean`, where a decency hypothesis repairs the arrow of
Lemma 0ACA from `dim(|X_k|) = 0` to discreteness of `|X_k|`, which is false without one.

## References

* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}


/-- **Stacks 03XH** for the field fibre. The structure morphism `X_k ⟶ Spec(k)` of the field
fibre of a morphism locally of finite type is locally of finite type, being a base change of
that morphism. -/
theorem isLocallyOfFiniteType_snd_fieldFibre (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS Y) :
    IsLocallyOfFiniteType B S hS (pullback.snd f (yonedaEquiv.symm p.value)) :=
  IsLocallyOfFiniteType.of_isPullback B S hS
    (IsPullback.of_hasPullback f (yonedaEquiv.symm p.value)).flip hX hY hf

/-! ### Condition (7) is local quasi-finiteness of the structure morphism of the fibre -/

/-- **Condition (7) of Stacks 0ACK is local quasi-finiteness over `Spec(k)`.** The structure
morphism `X_k ⟶ Spec(k)` of the field fibre of a morphism locally of finite type is locally
quasi-finite exactly when the field fibre has dimension at most zero.

This is Lemma 0ACA, conditions (4) and (5), applied to `X_k` over `Spec(k)`: the spectrum of a
field has one point, which is all that
`AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero` needs of the base. -/
theorem isLocallyQuasiFinite_snd_fieldFibre_iff_dimension_le_zero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p)) :
    IsLocallyQuasiFinite B S hS (pullback.snd f (yonedaEquiv.symm p.value)) ↔
      dimension B S hS (fieldFibre B S hS f p) hXk ≤ 0 :=
  isLocallyQuasiFinite_iff_dimension_le_zero B S hS hXk
    (subsingleton_toScheme_siteObject B S hS Y p) _
    (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hf p)

/-! ### Condition (7) implies conditions (5) and (6) -/

/-- **Stacks 0ACK, condition (7) implies condition (5).** If the field fibre `X_k` has
dimension zero as an algebraic space, then its point space `|X_k|` is discrete.

By Lemma 0ACA the structure morphism `X_k ⟶ Spec(k)` is then locally quasi-finite, and a space
locally quasi-finite over a one-point base has discrete point space. -/
@[stacks 0ACK "condition (7) implies condition (5)"]
theorem isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsZeroDimensionalFieldFibre B S hS f p hXk) :
    IsDiscreteFieldFibrePoints B S hS f p :=
  discreteTopology_points_of_isLocallyQuasiFinite B S hS hXk
    (subsingleton_toScheme_siteObject B S hS Y p) _
    ((isLocallyQuasiFinite_snd_fieldFibre_iff_dimension_le_zero B S hS hX hY hf p hXk).mpr
      h.le)

/-- **Stacks 0ACK, condition (7) implies condition (6).** If the field fibre `X_k` has
dimension zero as an algebraic space, then its point space `|X_k|` has dimension zero.

No nonemptiness hypothesis is needed: the dimension of Tag 04N6 is a supremum over the points,
so condition (7) already forces `|X_k|` to have a point. -/
@[stacks 0ACK "condition (7) implies condition (6)"]
theorem isZeroDimensionalFieldFibrePoints_of_isZeroDimensionalFieldFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsZeroDimensionalFieldFibre B S hS f p hXk) :
    IsZeroDimensionalFieldFibrePoints B S hS f p :=
  isZeroDimensionalFieldFibrePoints_of_isDiscreteFieldFibrePoints B S hS f p
    (isDiscreteFieldFibrePoints_of_isZeroDimensionalFieldFibre B S hS hX hY hf p hXk h)
    (nonempty_points_of_dimension_eq_zero B S hS hXk h)

/-! ### Condition (8) and local quasi-finiteness of the structure morphism -/

/-- Condition (8) of Stacks 0ACK says `X_k ⟶ Spec(k)` is quasi-finite at every point of `|X_k|`. -/
private theorem isQuasiFiniteAboveFieldValuedPoint_iff_forall_isQuasiFiniteAt_snd
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f p ↔
      ∀ w, IsQuasiFiniteAt B S hS (pullback.snd f (yonedaEquiv.symm p.value)) w := by
  rw [IsQuasiFiniteAboveFieldValuedPoint, ← range_pointsMap_fst_fieldFibre B S hS f p,
    Set.forall_mem_range]
  exact forall_congr' fun w ↦ (isQuasiFiniteAt_iff_of_isPullback B S hS
    (IsPullback.of_hasPullback f (yonedaEquiv.symm p.value)).flip hX hY
    (isAlgebraicSpace_yoneda B S hS p.siteObject) hf w).symm

/-- **Condition (8) of Stacks 0ACK gives local quasi-finiteness over `Spec(k)`.** If `f` is
quasi-finite at every point of `|X|` above the point represented by `p`, then the structure
morphism `X_k ⟶ Spec(k)` of the field fibre is locally quasi-finite.

Part (2) of Tag 0ABM turns condition (8) into quasi-finiteness of the structure morphism at
every point of `|X_k|`, and the pointwise form of Tag 04NV assembles those into local
quasi-finiteness. -/
theorem isLocallyQuasiFinite_snd_fieldFibre_of_isQuasiFiniteAboveFieldValuedPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsQuasiFiniteAboveFieldValuedPoint B S hS f p) :
    IsLocallyQuasiFinite B S hS (pullback.snd f (yonedaEquiv.symm p.value)) := by
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj p.siteObject) :=
    isAlgebraicSpace_yoneda B S hS p.siteObject
  have hpr := isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hf p
  refine (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _ hpr).mpr
    fun w ↦ (isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hXk hZ _ hpr w).mp ?_
  exact (isQuasiFiniteAboveFieldValuedPoint_iff_forall_isQuasiFiniteAt_snd B S hS hX hY hf p).mp
    h w

/-- **Local quasi-finiteness over `Spec(k)` gives condition (8) of Stacks 0ACK.** If the
structure morphism `X_k ⟶ Spec(k)` of the field fibre is locally quasi-finite, then `f` is
quasi-finite at every point of `|X|` above the point represented by `p`.

A locally quasi-finite morphism is quasi-finite at every point of its source, and part (2) of
Tag 0ABM transports that along the projection `|X_k| → |X|`, whose image is exactly the
fibre. -/
theorem isQuasiFiniteAboveFieldValuedPoint_of_isLocallyQuasiFinite_snd_fieldFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (hqf : IsLocallyQuasiFinite B S hS (pullback.snd f (yonedaEquiv.symm p.value))) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f p := by
  exact (isQuasiFiniteAboveFieldValuedPoint_iff_forall_isQuasiFiniteAt_snd B S hS hX hY hf p).mpr
    (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hXk hqf)

/-! ### Conditions (7) and (8) are equivalent -/

/-- **Stacks 0ACK, condition (7) implies condition (8).** If the field fibre `X_k` has
dimension zero as an algebraic space, then `f` is quasi-finite at every point of `|X|` above
the point represented by `p`.

By Lemma 0ACA the structure morphism `X_k ⟶ Spec(k)` is locally quasi-finite, hence
quasi-finite at every point of `|X_k|`; part (2) of Tag 0ABM transports that along the
projection `|X_k| → |X|`, whose image is exactly the fibre. -/
@[stacks 0ACK "condition (7) implies condition (8)"]
theorem isQuasiFiniteAboveFieldValuedPoint_of_isZeroDimensionalFieldFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsZeroDimensionalFieldFibre B S hS f p hXk) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f p :=
  isQuasiFiniteAboveFieldValuedPoint_of_isLocallyQuasiFinite_snd_fieldFibre B S hS hX hY hf p
    hXk ((isLocallyQuasiFinite_snd_fieldFibre_iff_dimension_le_zero B S hS hX hY hf p hXk).mpr
      h.le)

/-- **Stacks 0ACK, condition (8) implies condition (7).** If `f` is quasi-finite at every point
of `|X|` above the point represented by `p`, and the field fibre `X_k` has a point, then `X_k`
has dimension zero as an algebraic space.

Condition (8) makes the structure morphism `X_k ⟶ Spec(k)` locally quasi-finite, and Lemma
0ACA converts that into the dimension statement. The nonemptiness hypothesis is what upgrades
`dim(X_k) ≤ 0` to `dim(X_k) = 0`: the dimension of Tag 04N6 is a supremum, so the empty space
has dimension `⊥`. -/
@[stacks 0ACK "condition (8) implies condition (7), nonempty fibre"]
theorem isZeroDimensionalFieldFibre_of_isQuasiFiniteAboveFieldValuedPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsQuasiFiniteAboveFieldValuedPoint B S hS f p)
    (hne : Nonempty (points B S hS (fieldFibre B S hS f p))) :
    IsZeroDimensionalFieldFibre B S hS f p hXk :=
  dimension_eq_zero_of_isLocallyQuasiFinite B S hS hXk
    (subsingleton_toScheme_siteObject B S hS Y p) _
    (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hf p)
    (isLocallyQuasiFinite_snd_fieldFibre_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hf p
      hXk h) hne

/-! ### Condition (8) implies condition (5) -/

/-- **Stacks 0ACK, condition (8) implies condition (5).** If `f` is quasi-finite at every point
of `|X|` above the point represented by `p`, then the point space `|X_k|` of the field fibre is
discrete.

Condition (8) makes the structure morphism `X_k ⟶ Spec(k)` locally quasi-finite, and a space
locally quasi-finite over a one-point base has discrete point space. No nonemptiness hypothesis
intervenes: the empty space is discrete, and the route taken avoids the dimension of Tag 04N6,
whose value on the empty space is `⊥` rather than `0`. -/
@[stacks 0ACK "condition (8) implies condition (5)"]
theorem isDiscreteFieldFibrePoints_of_isQuasiFiniteAboveFieldValuedPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsQuasiFiniteAboveFieldValuedPoint B S hS f p) :
    IsDiscreteFieldFibrePoints B S hS f p :=
  discreteTopology_points_of_isLocallyQuasiFinite B S hS hXk
    (subsingleton_toScheme_siteObject B S hS Y p) _
    (isLocallyQuasiFinite_snd_fieldFibre_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hf p
      hXk h)

end AlgebraicGeometry.Space

end
