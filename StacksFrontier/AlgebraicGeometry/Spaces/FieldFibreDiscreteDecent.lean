module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverFieldSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreInducing

/-!
# The two fibres are simultaneously discrete, over a decent target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, let `y` be the point
of `|Y|` it represents, let `F = f^{-1}({y}) ⊂ |X|` be the set-theoretic fibre and let
`X_k = X ×_Y Spec(k)` be the field fibre. Stacks 0ACK compares eight conditions on this data,
and asserts among other things that when `Y` is decent its conditions (2) and (5) — that `F` is
discrete, and that `|X_k|` is discrete — are equivalent. This file proves that statement.

`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreConditions.lean` states the eight conditions,
and that file together with
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreQuasiFinite.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreEquivalences.lean` proves the implications which
run *out of* conditions (4) and (7). What was missing was the arrow back *into* the dimension
condition, from the topological condition (5); that arrow is Stacks 0ACA, condition (2) implies
condition (4), now available as
`AlgebraicGeometry.Space.dimension_le_zero_of_discreteTopology_points`. This file supplies it in
the form the tag needs and then draws the decent-target equivalence from it.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.setFibre_eq_of_class_eq`: the set-theoretic fibre depends only on
  the point of `|Y|` that the field-valued point represents, and not on the representative.
* `AlgebraicGeometry.Space.isZeroDimensionalFieldFibre_of_isDiscreteFieldFibrePoints` is
  Stacks 0ACK, condition (5) implies condition (7) for a nonempty fibre.
* `AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint`
  is Stacks 0ACK, conditions (5) and (8) are equivalent.
* `AlgebraicGeometry.Space.discreteTopology_setFibre_iff_discreteTopology_points_fieldFibre`
  is Stacks 0ACK, conditions (2) and (5) are equivalent for a decent target.

## Implementation notes

The source proves the decent-target statements by choosing a quasi-compact monomorphism
`Spec(k') ⟶ Y` in the equivalence class of `y`, which decency of `Y` provides, and invoking
Lemma 0AC8 to identify `|X_{k'}|` with `F` as topological spaces. That identification is proved
in full, as `AlgebraicGeometry.Space.homeomorphSetFibre`, so condition (2) is equivalent to
condition (5) *for the chosen representative* `k'` outright. The work is in comparing the chosen
representative with the given one.

The comparison is made through condition (8), `f` is quasi-finite at every point of `F`, which
is the only condition in the chain that mentions no field fibre and is therefore
representative-free by construction: `AlgebraicGeometry.Space.IsQuasiFiniteAboveFieldValuedPoint`
quantifies over `AlgebraicGeometry.Space.setFibre`, and that set is literally defined by the
class of its argument, so `AlgebraicGeometry.Space.setFibre_eq_of_class_eq` transports it between
representatives. Condition (5) is equivalent to condition (8) for *every* representative of `y`,
and the two equivalences compose with the homeomorphism of Lemma 0AC8 to give the tag.

Making condition (5) equivalent to condition (8) is where the new arrow is used. The direction
(8) ⟹ (5) is proved in `StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreQuasiFinite.lean`. The
direction (5) ⟹ (8) is Stacks 0ACA, condition (2) implies condition (4), applied to `X_k` over
`Spec(k)`: the field fibre is an algebraic space, its structure morphism is a base change of `f`
and so is locally of finite type by Tag 03XH, and its base is presented by the field `k` on the
nose, since `AlgebraicGeometry.Space.FieldValuedPoint.siteObject` *is*
`AlgebraicGeometry.BigFppfOver.mk B S hS p.contained p.toBase`, so that lemma's presentation
hypothesis is discharged by `rfl`. It yields `dim(X_k) ≤ 0`, and that inequality already *is*
local quasi-finiteness of `X_k ⟶ Spec(k)`, which is condition (8); so neither
`AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint` nor
the decent-target equivalence drawn from it needs a nonempty fibre, and the source asks for
none. Only the `= 0` form of the dimension of Tag 04N6 does, that dimension being a supremum in
`WithBot ℕ∞` whose value on the empty space is `⊥`; that is why
`AlgebraicGeometry.Space.isZeroDimensionalFieldFibre_of_isDiscreteFieldFibrePoints`, which
states condition (7), keeps the hypothesis.

**Conditions (3) and (6) need a decency hypothesis on `f` beyond the one the source states.**
The source asserts that conditions (2) and (3) are equivalent for a decent target, and that
conditions (5), (6) and (7) are equivalent with no hypothesis at all. Those two claims are false
as stated: the arrows out of conditions (3) and (6) are instances of Stacks 0ACA, condition (3)
implies condition (2), which fails for the point space of `𝔸¹_k/ℤ`, an indiscrete topology on
infinitely many points. The counterexample is
`Stacks.Examples.DimensionVersusPointSet.exists_zeroTopologicalDimension_not_discretePoints`
(`StacksFrontier/Examples/Spaces/ZeroDimensionalPointsNotDiscrete.lean`), and taking `Y = Spec(k)`
— a scheme, hence a decent algebraic space — with that space as `X` turns it into a
counterexample to both claims at once, since then `X_k = X` and `F = |X|`. Decency of `Y` alone
does not make `|X|` or `|X_k|` a `T₀` space, so it does not repair them; decency of `f` does,
because the field fibre of a decent morphism is a decent algebraic space and the point space of
a decent algebraic space is Kolmogorov by Stacks 03K3. The repaired arrows are in
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreZeroDimensionalDecent.lean`. Nothing in this
file depends on them.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
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

/-! ### The set-theoretic fibre depends only on the point -/

/-- **The set-theoretic fibre is representative-free.** Two field-valued points of `Y` which
represent the same point of `|Y|` have the same set-theoretic fibre, since
`AlgebraicGeometry.Space.setFibre` is defined as a preimage of the class of its argument. -/
theorem setFibre_eq_of_class_eq (f : X ⟶ Y) (p q : FieldValuedPoint B S hS Y)
    (h : q.class B S hS Y = p.class B S hS Y) :
    setFibre B S hS f q = setFibre B S hS f p := by
  ext x
  change _ = q.class B S hS Y ↔ _
  rw [h]
  exact Iff.rfl

/-- Condition (8) of Stacks 0ACK is representative-free: it quantifies over the set-theoretic
fibre, which `AlgebraicGeometry.Space.setFibre_eq_of_class_eq` shows depends only on the point
of `|Y|` represented. -/
theorem isQuasiFiniteAboveFieldValuedPoint_iff_of_class_eq (f : X ⟶ Y)
    (p q : FieldValuedPoint B S hS Y) (h : q.class B S hS Y = p.class B S hS Y) :
    IsQuasiFiniteAboveFieldValuedPoint B S hS f q ↔
      IsQuasiFiniteAboveFieldValuedPoint B S hS f p := by
  change (∀ x ∈ setFibre B S hS f q, _) ↔ (∀ x ∈ setFibre B S hS f p, _)
  rw [setFibre_eq_of_class_eq B S hS f p q h]

/-! ### Condition (5) implies condition (7) -/

/-- The field fibre of a morphism locally of finite type has dimension at most zero as soon as
its point space is discrete. This is the unconditional half of "condition (5) implies condition
(7)" of Stacks 0ACK, and it is Stacks 0ACA, condition (2) implies condition (4), applied to the
field fibre over `Spec(k)`.

The base of the field fibre is presented by the field `k` on the nose, so the presentation
hypothesis of `AlgebraicGeometry.Space.dimension_le_zero_of_discreteTopology_points` holds by
`rfl`; its structure morphism is locally of finite type because it is a base change of `f`, by
Tag 03XH. -/
theorem dimension_fieldFibre_le_zero_of_isDiscreteFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsDiscreteFieldFibrePoints B S hS f p) :
    dimension B S hS (fieldFibre B S hS f p) hXk ≤ 0 :=
  dimension_le_zero_of_discreteTopology_points B S hS hXk p.contained p.toBase rfl
    (pullback.snd f (fieldMorphism B S hS Y p))
    (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hft p) h

/-- The structure morphism of a field fibre with discrete point space is locally quasi-finite. -/
private theorem isLocallyQuasiFinite_snd_fieldFibre_of_isDiscreteFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsDiscreteFieldFibrePoints B S hS f p) :
    IsLocallyQuasiFinite B S hS (pullback.snd f (fieldMorphism B S hS Y p)) :=
  (isLocallyQuasiFinite_snd_fieldFibre_iff_dimension_le_zero B S hS hX hY hft p hXk).mpr
    (dimension_fieldFibre_le_zero_of_isDiscreteFieldFibrePoints B S hS hX hY hft p hXk h)

/-- **Stacks 0ACK, condition (5) implies condition (7)** for a nonempty fibre. If the point
space of the field fibre `X_k` is discrete and nonempty, then `X_k` has dimension zero as an
algebraic space.

The inequality `dim(X_k) ≤ 0` is
`AlgebraicGeometry.Space.dimension_fieldFibre_le_zero_of_isDiscreteFieldFibrePoints`; it makes
the structure morphism `X_k ⟶ Spec(k)` locally quasi-finite, and nonemptiness then upgrades the
inequality to the equation, since the dimension of Tag 04N6 is a supremum in `WithBot ℕ∞` and
the empty space has dimension `⊥`. -/
@[stacks 0ACK "condition (5) implies condition (7), nonempty fibre"]
theorem isZeroDimensionalFieldFibre_of_isDiscreteFieldFibrePoints
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p))
    (h : IsDiscreteFieldFibrePoints B S hS f p)
    (hne : Nonempty (points B S hS (fieldFibre B S hS f p))) :
    IsZeroDimensionalFieldFibre B S hS f p hXk :=
  dimension_eq_zero_of_isLocallyQuasiFinite B S hS hXk
    (subsingleton_toScheme_siteObject B S hS Y p)
    (pullback.snd f (fieldMorphism B S hS Y p))
    (isLocallyOfFiniteType_snd_fieldFibre B S hS hX hY hft p)
    (isLocallyQuasiFinite_snd_fieldFibre_of_isDiscreteFieldFibrePoints B S hS hX hY hft p hXk h)
    hne

/-! ### Conditions (5) and (8) are equivalent -/

/-- **Stacks 0ACK, conditions (5) and (8).** For a morphism locally of finite type and a
field-valued point of its target, the point space of the field fibre `X_k` is discrete exactly
when `f` is quasi-finite at every point of `|X|` above the point represented.

Both directions run through local quasi-finiteness of the structure morphism `X_k ⟶ Spec(k)`,
which `isLocallyQuasiFinite_snd_fieldFibre_of_isQuasiFiniteAboveFieldValuedPoint` and its
converse identify with condition (8). Forward,
`AlgebraicGeometry.Space.dimension_fieldFibre_le_zero_of_isDiscreteFieldFibrePoints` gives
`dim(X_k) ≤ 0`, which is that local quasi-finiteness. No nonemptiness hypothesis is needed,
exactly as the source makes none: the two conditions compared are a topological property and a
pointwise property of the fibre, both of which hold vacuously for an empty fibre, and the route
taken passes only through the `≤ 0` form of the dimension of Tag 04N6 and never through its
`= 0` form, whose value on the empty space is `⊥`. -/
@[stacks 0ACK "conditions (5) and (8)"]
theorem isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hft : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y) :
    IsDiscreteFieldFibrePoints B S hS f p ↔
      IsQuasiFiniteAboveFieldValuedPoint B S hS f p := by
  have hXk : IsAlgebraicSpace B S hS (fieldFibre B S hS f p) :=
    isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS Y p) hX
      (isAlgebraicSpace_yoneda B S hS p.siteObject) hY
  refine ⟨fun h ↦ isQuasiFiniteAboveFieldValuedPoint_of_isLocallyQuasiFinite_snd_fieldFibre
      B S hS hX hY hft p hXk
      (isLocallyQuasiFinite_snd_fieldFibre_of_isDiscreteFieldFibrePoints B S hS hX hY hft p hXk
        h),
    fun h ↦ isDiscreteFieldFibrePoints_of_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft p
      hXk h⟩

/-! ### Conditions (2) and (5) are equivalent for a decent target -/

/-- **Stacks 0ACK, conditions (2) and (5) for a decent target.** Let `f : X ⟶ Y` be a morphism
of algebraic spaces locally of finite type, let `p` be a field-valued point of `Y` with
set-theoretic fibre `F`, and let `Y` be decent. Then `F` is discrete exactly when the point space
of the field fibre `X_k` is discrete.

Decency of `Y` supplies a field-valued point `q` representing the same point of `|Y|` whose
presenting morphism is a quasi-compact monomorphism, which is condition (4) of Stacks 03JV. For
that representative Lemma 0AC8 identifies `|X_q|` with `F` as topological spaces
(`AlgebraicGeometry.Space.homeomorphSetFibre`), and `F` is the same set for `q` as for `p` by
`AlgebraicGeometry.Space.setFibre_eq_of_class_eq`. So condition (2) is equivalent to condition
(5) for `q`. Condition (5) is equivalent to condition (8) for either representative by
`AlgebraicGeometry.Space.isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint`, and
condition (8) is representative-free, which closes the chain back to condition (5) for `p`. -/
@[stacks 0ACK "conditions (2) and (5) for a decent target"]
theorem discreteTopology_setFibre_iff_discreteTopology_points_fieldFibre
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hft : IsLocallyOfFiniteType B S hS f)
    (hdecent : IsDecentSpace B S hS Y) :
    DiscreteTopology (setFibre B S hS f p) ↔
      DiscreteTopology (points B S hS (fieldFibre B S hS f p)) := by
  obtain ⟨q, hqclass, hmono, hqc⟩ := hdecent (p.class B S hS Y)
  have hset : setFibre B S hS f q = setFibre B S hS f p :=
    setFibre_eq_of_class_eq B S hS f p q hqclass
  have hhomeo : points B S hS (fieldFibre B S hS f q) ≃ₜ setFibre B S hS f p :=
    (homeomorphSetFibre B S hS hX hY f q hmono hqc).trans (Homeomorph.setCongr hset)
  have h8 := isQuasiFiniteAboveFieldValuedPoint_iff_of_class_eq B S hS f p q hqclass
  have hq5 := isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY
    hft q
  have hp5 := isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY
    hft p
  refine ⟨fun hd ↦ ?_, fun hd ↦ ?_⟩
  · have := hd
    exact hp5.mpr (h8.mp (hq5.mp hhomeo.symm.discreteTopology))
  · have hdq : DiscreteTopology (points B S hS (fieldFibre B S hS f q)) :=
      hq5.mpr (h8.mpr (hp5.mp hd))
    have := hdq
    exact hhomeo.discreteTopology

end AlgebraicGeometry.Space

end
