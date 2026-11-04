module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions

/-!
# Decency along a morphism of algebraic spaces

Decency of an algebraic space over a scheme `S` is a condition at each of its points, and the
condition is about a field-valued representative of that point. A morphism of algebraic spaces
moves points forwards and field-valued representatives with them, so the two natural
comparisons are: decency of the target together with decency of the morphism gives decency of
the source, which is Stacks 0ABY; and decency of the source together with surjectivity on
points and quasi-compactness of the morphism gives decency of the target, which is the decent
case of Stacks 03L2.

The condition at a point that this file's results produce is
`AlgebraicGeometry.Space.HasQuasiCompactFieldRepresentative`, condition (5) of Stacks 03JV:
some field-valued representative of the point presents it by a quasi-compact morphism, with no
condition of being a monomorphism. It is defined in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactPointsConditions.lean`, which this file
imports, together with the implication from condition (4).

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_of_isDecent`: **Stacks 0ABY** for decency — if a
  morphism of algebraic spaces and its target are decent, so is its source.
* `AlgebraicGeometry.Space.hasQuasiCompactFieldRepresentative_of_isDecentSpace`: along a
  quasi-compact morphism which is surjective on points, decency of the source gives condition
  (5) of Stacks 03JV at every point of the target.
* `AlgebraicGeometry.Space.isDecentSpace_of_surjective_isQuasiCompact`: **Stacks 03L2** for
  decency — along a quasi-compact morphism which is surjective on points, decency of the
  source gives decency of the target.

## Implementation notes

For Stacks 0ABY the field-valued representative of a point `x` of the source is built in two
steps, as in the source. A representative `Spec k ⟶ Y` of the image of `x` is given by decency
of the target; the point `x` lifts to a point of the fibre product `Spec k ×_Y X`, which is
decent because the morphism is, so that point has a representative `Spec k' ⟶ Spec k ×_Y X`
which is a quasi-compact monomorphism; and the composite with the projection to `X` is again a
quasi-compact monomorphism, the projection being a base change of `Spec k ⟶ Y`.

Decency of the target, in the sense of Stacks 03I8, asks at every point for a representative
which is a quasi-compact **monomorphism**. The composite of the quasi-compact monomorphism
representing a preimage point with the given morphism is quasi-compact, but there is no reason
for it to be a monomorphism; the monomorphism is recovered from the implication from condition
(5) to condition (4) of Stacks 03JV, which says that a point with a quasi-compact field-valued
representative has a quasi-compact *monomorphic* one. So the argument is split in two, the
first step producing condition (5) at every point of the target and the second upgrading it.

Only the case "decent" of Stacks 0ABY is proved here. Its case `(β)`, in the form of condition
(4) of Stacks 03JU, is
`AlgebraicGeometry.Space.hasMonomorphicFieldRepresentative_of_target_of_baseChange` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/RelativeConditions.lean`.

Neither statement uses étaleness, although Stacks 03L2 assumes it; quasi-compactness of the
morphism is what the composition argument needs. Surjectivity on points is surjectivity of the
induced map on equivalence classes of field-valued points, which is the meaning of
surjectivity of `|X| → |Y|` by Stacks 03H5.

## References

* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03L2](https://stacks.math.columbia.edu/tag/03L2)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Morphism

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Decency of the source of a decent morphism -/

/-- **Stacks 0ABY, decent.** If a morphism of algebraic spaces over `S` is decent and its
target is decent, then its source is decent.

A point `x` of the source maps to a point of the target, which decency of the target presents
by a quasi-compact monomorphism `g : Spec k ⟶ Y`. The point `x` and the tautological point of
`Spec k` have the same image in `Y`, so they come from a point of `Spec k ×_Y X`; that fibre
product is decent because the morphism is, so that point is presented by a quasi-compact
monomorphism, and composing it with the projection to `X` — a base change of `g`, hence again a
quasi-compact monomorphism — presents `x`. -/
@[stacks 0ABY "decent"]
theorem isDecentSpace_of_isDecent (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hYdecent : IsDecentSpace B S hS Y) (hfdecent : IsDecent B S hS f) :
    IsDecentSpace B S hS X := by
  intro x
  obtain ⟨r, hr, hrmono, hrqc⟩ := hYdecent (pointsMap B S hS X f x)
  set T := r.siteObject with hT
  set g : yoneda.obj T ⟶ Y := fieldMorphism B S hS Y r with hg
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hPalg : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hTalg hX hY
  -- the two points lying over the same point of `Y` come from a point of `Spec k ×_Y X`
  have hcompat : pointsMap B S hS (yoneda.obj T) g
      ((r.tautologicalPoint B S hS Y).class B S hS (yoneda.obj T)) =
        pointsMap B S hS X f x := by
    rw [pointsMap_fieldMorphism_tautologicalPoint]
    exact hr
  obtain ⟨w, -, hwX⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g f)
    ((r.tautologicalPoint B S hS Y).class B S hS (yoneda.obj T)) x hcompat
  -- the projection to `X` is a base change of `g`, so a quasi-compact monomorphism
  have _ : Mono g := hrmono
  have hprojmono : Mono (pullback.snd g f) := pullback.snd_of_mono
  have hprojqc : IsQuasiCompact B S hS (pullback.snd g f) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f) hrqc
  -- a representative of the point of the fibre product, pushed to `X`
  obtain ⟨s, hs, hsmono, hsqc⟩ := hfdecent T g w
  refine ⟨FieldValuedPoint.map B S hS (pullback g f) (pullback.snd g f) s, ?_, ?_, ?_⟩
  · rw [← pointsMap_class, hs]
    exact hwX
  · rw [fieldMorphism_map]
    exact mono_comp' hsmono hprojmono
  · rw [fieldMorphism_map]
    exact isQuasiCompact_comp B S hS hPalg hX _ _ hsqc hprojqc

/-! ### Quasi-compact field-valued representatives on the target -/

/-- **Stacks 03L2, condition (5) of Stacks 03JV at every point of the target.** Let `f` be a
quasi-compact morphism of algebraic spaces over `S` which is surjective on points. If the
source is decent, then every point of the target has a quasi-compact field-valued
representative.

A point of the target is the image of a point of the source, which decency of the source
presents by a quasi-compact morphism from the spectrum of a field; composing it with `f` again
gives a quasi-compact morphism, and it presents the chosen point of the target.

Decency of the target asks for a representative which is in addition a monomorphism, and
obtaining one from this is the equivalence of conditions (4) and (5) of Stacks 03JV. Étaleness
of `f`, which Stacks 03L2 also assumes, is not used. -/
@[stacks 03L2 "condition (5) of Stacks 03JV at every point of the target"]
theorem hasQuasiCompactFieldRepresentative_of_isDecentSpace (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (hsurj : Function.Surjective (pointsMap B S hS X f))
    (hXdecent : IsDecentSpace B S hS X) (y : points B S hS Y) :
    HasQuasiCompactFieldRepresentative B S hS Y y := by
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨p, hp, -, hpqc⟩ := hXdecent x
  refine ⟨FieldValuedPoint.map B S hS X f p, ?_, ?_⟩
  · rw [← pointsMap_class, hp]
  · rw [fieldMorphism_map]
    exact isQuasiCompact_comp B S hS hX hY _ _ hpqc hf

/-- **Stacks 03L2, decent.** Let `f` be a quasi-compact morphism of algebraic spaces over `S`
which is surjective on points. If its source is decent, then so is its target.

Every point of the target acquires a quasi-compact field-valued representative by pushing one
forward along `f`, and the implication from condition (5) to condition (4) of Stacks 03JV
makes that representative a monomorphism. Étaleness of `f`, which Stacks 03L2 also assumes,
is not used. -/
@[stacks 03L2 "decent"]
theorem isDecentSpace_of_surjective_isQuasiCompact (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (hsurj : Function.Surjective (pointsMap B S hS X f))
    (hXdecent : IsDecentSpace B S hS X) :
    IsDecentSpace B S hS Y := fun y ↦
  hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative
    B S hS Y hY
    (hasQuasiCompactFieldRepresentative_of_isDecentSpace B S hS hX hY f hf hsurj hXdecent y)

end Morphism

end AlgebraicGeometry.Space

end
