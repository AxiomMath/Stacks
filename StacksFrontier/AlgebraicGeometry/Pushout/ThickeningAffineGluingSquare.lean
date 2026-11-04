module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# Gluing across a thickening, on an arbitrary cocartesian square

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of schemes, let `Y'` carry
the pushout square of the two, and let `V'` carry the pushout square of a triple `(V, U', φ)`
over it, with `V' ⟶ Y'` the induced morphism.  [Stacks Project, Tag 07RX] says that `V' ⟶ Y'`
is locally of finite type, flat, flat and locally of finite presentation, smooth or étale
exactly when both `V ⟶ Y` and `U' ⟶ X'` are.

`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing` proves the five clauses for a
`AlgebraicGeometry.ThickeningAffinePushoutSituation`, which carries the identification of the
sections of `Y'` as a fibre product as a hypothesis.  That identification is the fourth
assertion of [Stacks Project, Tag 07RT], and it is a theorem of this library for a thickening
of any order — `Stacks.Pushout.pushout_structureSheaf_isPullback'`, which discharges the
[Stacks Project, Tag 06AD] hypothesis of Tag 07RT from
`Stacks.Thickenings.forall_isAffine_of_isThickening`.  This file transports that theorem from
Mathlib's canonical pushout to an arbitrary cocartesian square along
`CategoryTheory.Limits.IsPushout.isoPushout`, and so states the five clauses for two arbitrary
cocartesian squares with no hypothesis beyond the thickening and the affine morphism.

## Main definitions

* `AlgebraicGeometry.ThickeningAffinePushoutSituation.ofIsThickening`: a cocartesian square on
  a thickening and an affine morphism, as a situation.
* `AlgebraicGeometry.ThickeningAffineGluing.triple`: the triple `(V, U', φ)` of
  [Stacks Project, Tag 07RV] carried by a second cocartesian square and the two cartesian
  squares that identify `U` with `V ×_Y X` and with `U' ×_{X'} X`.

## Main results

* `AlgebraicGeometry.ThickeningAffinePushoutSituation.sections_isPullback_of_isPushout`: the
  fourth assertion of [Stacks Project, Tag 07RT] on an arbitrary cocartesian square.
* `AlgebraicGeometry.ThickeningAffineGluing.locallyOfFiniteType_induced_iff_of_isPushout`,
  `flat_induced_iff_of_isPushout`,
  `flat_and_locallyOfFinitePresentation_induced_iff_of_isPushout`,
  `smooth_induced_iff_of_isPushout` and `etale_induced_iff_of_isPushout`: the five clauses of
  [Stacks Project, Tag 07RX] on two arbitrary cocartesian squares.

## References

* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

universe u

namespace AlgebraicGeometry

/-! ### The situation of Tag 07RV on an arbitrary cocartesian square -/

namespace ThickeningAffinePushoutSituation

/-- **The fourth assertion of [Stacks Project, Tag 07RT] for an arbitrary cocartesian square.**
On every open of a scheme carrying the pushout square of a thickening `i : X ⟶ X'` and an affine
morphism `f : X ⟶ Y`, the sections form the fibre product of the sections on `Y` and on `X'`
over those on `X`.  This is
`Stacks.Pushout.pushout_structureSheaf_isPullback'` transported along
`CategoryTheory.Limits.IsPushout.isoPushout`. -/
theorem sections_isPullback_of_isPushout {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y}
    {inX' : X' ⟶ Y'} {inY : Y ⟶ Y'} (hi : IsThickening i) [IsAffineHom f]
    (hpo : IsPushout i f inX' inY) (O : Y'.Opens) :
    IsPullback (inY.app O) (inX'.app O) (f.app (inY ⁻¹ᵁ O))
      (i.app (inX' ⁻¹ᵁ O) ≫ eqToHom (congrArg (fun W ↦ Γ(X, W))
        (congrArg (fun k : X ⟶ Y' ↦ k ⁻¹ᵁ O) hpo.w))) := by
  have : HasPushout i f := hpo.hasPushout
  obtain ⟨e, hl, hr⟩ : ∃ e : pushout i f ≅ Y',
      pushout.inl i f ≫ e.hom = inX' ∧ pushout.inr i f ≫ e.hom = inY :=
    ⟨hpo.isoPushout.symm, by
      rw [Iso.symm_hom, ← hpo.inl_isoPushout_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id], by
      rw [Iso.symm_hom, ← hpo.inr_isoPushout_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]⟩
  have hpb := Stacks.Pushout.pushout_structureSheaf_isPullback' i f hi (e.hom ⁻¹ᵁ O)
  have key : ∀ hw : i ≫ (pushout.inl i f ≫ e.hom) = f ≫ (pushout.inr i f ≫ e.hom),
      IsPullback ((pushout.inr i f ≫ e.hom).app O) ((pushout.inl i f ≫ e.hom).app O)
        (f.app ((pushout.inr i f ≫ e.hom) ⁻¹ᵁ O))
        (i.app ((pushout.inl i f ≫ e.hom) ⁻¹ᵁ O) ≫ eqToHom (congrArg (fun W ↦ Γ(X, W))
          (congrArg (fun k : X ⟶ Y' ↦ k ⁻¹ᵁ O) hw))) := by
    intro _
    refine hpb.of_iso' (asIso (e.hom.app O)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals simp [Scheme.Hom.comp_app]
  rw [hl, hr] at key
  exact key hpo.w

/-- A cocartesian square on a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is a
`AlgebraicGeometry.ThickeningAffinePushoutSituation`: the affineness of its two other legs and
the description of its sections are the assertions of [Stacks Project, Tag 07RT]. -/
def ofIsThickening {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    (inX' : X' ⟶ Y') (inY : Y ⟶ Y') (hi : IsThickening i) [IsAffineHom f]
    (hpo : IsPushout i f inX' inY) : ThickeningAffinePushoutSituation.{u} where
  X := X
  X' := X'
  Y := Y
  Y' := Y'
  i := i
  f := f
  inX' := inX'
  inY := inY
  isClosedImmersion_i := hi.1
  isAffineHom_f := inferInstance
  isAffineHom_inX' := Stacks.Pushout.isAffineHom_of_isPushout_of_isThickening hpo hi
  isAffineHom_inY :=
    haveI : AlgebraicGeometry.IsClosedImmersion inY :=
      (Stacks.Pushout.isThickening_of_isPushout_of_isThickening hpo hi).1
    inferInstance
  isPushout := hpo
  sections_isPullback := fun O ↦ sections_isPullback_of_isPushout hi hpo O

end ThickeningAffinePushoutSituation

/-! ### The five clauses of Tag 07RX on arbitrary cocartesian squares -/

namespace ThickeningAffineGluing

variable {X X' Y Y' U U' V V' : Scheme.{u}}
  {i : X ⟶ X'} {f : X ⟶ Y} {inX' : X' ⟶ Y'} {inY : Y ⟶ Y'}
  {iT : U ⟶ U'} {fT : U ⟶ V} {inU' : U' ⟶ V'} {inV : V ⟶ V'}
  {toX : U ⟶ X} {toX' : U' ⟶ X'} {toY : V ⟶ Y} {g : V' ⟶ Y'}

/-- The triple `(V, U', φ)` of [Stacks Project, Tag 07RV] carried by two cocartesian squares and
the two cartesian squares identifying `U` with `V ×_Y X` and with `U' ×_{X'} X`. -/
def triple (hi : IsThickening i) [IsAffineHom f] (hpo : IsPushout i f inX' inY)
    (hpoT : IsPushout iT fT inU' inV) (hpbi : IsPullback iT toX toX' i)
    (hpbf : IsPullback fT toX toY f) :
    (ThickeningAffinePushoutSituation.ofIsThickening i f inX' inY hi hpo).Triple :=
  haveI : IsAffineHom fT := MorphismProperty.of_isPullback hpbf.flip inferInstance
  { T := ThickeningAffinePushoutSituation.ofIsThickening iT fT inU' inV
      (isThickening_of_isPullback hpbi hi) hpoT
    toX' := toX'
    toY := toY
    toX := toX
    isPullback_i := hpbi
    isPullback_f := hpbf }

/-- The morphism `V' ⟶ Y'` of a triple is the one induced by the universal property of the
pushout `V' = V ⨿_U U'`. -/
theorem triple_induced (hi : IsThickening i) [IsAffineHom f] (hpo : IsPushout i f inX' inY)
    (hpoT : IsPushout iT fT inU' inV) (hpbi : IsPullback iT toX toX' i)
    (hpbf : IsPullback fT toX toY f) (hl : inU' ≫ g = toX' ≫ inX')
    (hr : inV ≫ g = toY ≫ inY) :
    (triple hi hpo hpoT hpbi hpbf).induced = g :=
  hpoT.hom_ext
    (((triple hi hpo hpoT hpbi hpbf).inX'_comp_induced).trans hl.symm)
    (((triple hi hpo hpoT hpbi hpbf).inY_comp_induced).trans hr.symm)

/-- **[Stacks Project, Tag 07RX], clause (1), on arbitrary cocartesian squares.**  The morphism
`V' ⟶ Y'` glued from a triple is locally of finite type if and only if both `V ⟶ Y` and
`U' ⟶ X'` are. -/
theorem locallyOfFiniteType_induced_iff_of_isPushout (hi : IsThickening i) [IsAffineHom f]
    (hpo : IsPushout i f inX' inY) (hpoT : IsPushout iT fT inU' inV)
    (hpbi : IsPullback iT toX toX' i) (hpbf : IsPullback fT toX toY f)
    (hl : inU' ≫ g = toX' ≫ inX') (hr : inV ≫ g = toY ≫ inY) :
    LocallyOfFiniteType g ↔ LocallyOfFiniteType toY ∧ LocallyOfFiniteType toX' := by
  exact triple_induced hi hpo hpoT hpbi hpbf hl hr ▸
    (triple hi hpo hpoT hpbi hpbf).locallyOfFiniteType_induced_iff

/-- **[Stacks Project, Tag 07RX], clause (2), on arbitrary cocartesian squares.**  The morphism
`V' ⟶ Y'` glued from a triple is flat if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem flat_induced_iff_of_isPushout (hi : IsThickening i) [IsAffineHom f]
    (hpo : IsPushout i f inX' inY) (hpoT : IsPushout iT fT inU' inV)
    (hpbi : IsPullback iT toX toX' i) (hpbf : IsPullback fT toX toY f)
    (hl : inU' ≫ g = toX' ≫ inX') (hr : inV ≫ g = toY ≫ inY) :
    Flat g ↔ Flat toY ∧ Flat toX' := by
  exact triple_induced hi hpo hpoT hpbi hpbf hl hr ▸
    (triple hi hpo hpoT hpbi hpbf).flat_induced_iff

/-- **[Stacks Project, Tag 07RX], clause (3), on arbitrary cocartesian squares.**  The morphism
`V' ⟶ Y'` glued from a triple is flat and locally of finite presentation if and only if both
`V ⟶ Y` and `U' ⟶ X'` are. -/
theorem flat_and_locallyOfFinitePresentation_induced_iff_of_isPushout (hi : IsThickening i)
    [IsAffineHom f] (hpo : IsPushout i f inX' inY) (hpoT : IsPushout iT fT inU' inV)
    (hpbi : IsPullback iT toX toX' i) (hpbf : IsPullback fT toX toY f)
    (hl : inU' ≫ g = toX' ≫ inX') (hr : inV ≫ g = toY ≫ inY) :
    (Flat g ∧ LocallyOfFinitePresentation g) ↔
      ((Flat toY ∧ LocallyOfFinitePresentation toY) ∧
        (Flat toX' ∧ LocallyOfFinitePresentation toX')) := by
  exact triple_induced hi hpo hpoT hpbi hpbf hl hr ▸
    (triple hi hpo hpoT hpbi hpbf).flat_and_locallyOfFinitePresentation_induced_iff

/-- **[Stacks Project, Tag 07RX], clause (4), on arbitrary cocartesian squares.**  The morphism
`V' ⟶ Y'` glued from a triple is smooth if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem smooth_induced_iff_of_isPushout (hi : IsThickening i) [IsAffineHom f]
    (hpo : IsPushout i f inX' inY) (hpoT : IsPushout iT fT inU' inV)
    (hpbi : IsPullback iT toX toX' i) (hpbf : IsPullback fT toX toY f)
    (hl : inU' ≫ g = toX' ≫ inX') (hr : inV ≫ g = toY ≫ inY) :
    Smooth g ↔ Smooth toY ∧ Smooth toX' := by
  exact triple_induced hi hpo hpoT hpbi hpbf hl hr ▸
    (triple hi hpo hpoT hpbi hpbf).smooth_induced_iff

/-- **[Stacks Project, Tag 07RX], clause (5), on arbitrary cocartesian squares.**  The morphism
`V' ⟶ Y'` glued from a triple is étale if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem etale_induced_iff_of_isPushout (hi : IsThickening i) [IsAffineHom f]
    (hpo : IsPushout i f inX' inY) (hpoT : IsPushout iT fT inU' inV)
    (hpbi : IsPullback iT toX toX' i) (hpbf : IsPullback fT toX toY f)
    (hl : inU' ≫ g = toX' ≫ inX') (hr : inV ≫ g = toY ≫ inY) :
    Etale g ↔ Etale toY ∧ Etale toX' := by
  exact triple_induced hi hpo hpoT hpbi hpbf hl hr ▸
    (triple hi hpo hpoT hpbi hpbf).etale_induced_iff

end ThickeningAffineGluing

end AlgebraicGeometry

end
