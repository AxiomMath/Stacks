module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# Finite flat morphisms of algebraic spaces

A representable morphism of algebraic spaces over a scheme `S` is finite locally free if and
only if it is finite, flat and locally of finite presentation; over a locally Noetherian target
the finite presentation condition is automatic, so there finite local freeness is finiteness
together with flatness.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFlat_iff_presheaf`,
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_presheaf` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_iff_presheaf` read the chart conditions of
  Stacks 03ML, 03XP and 03XF for a representable morphism as conditions on its represented base
  changes.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isFinite`: a finite morphism of algebraic
  spaces is locally of finite type.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff`: **Stacks 0416**, the equivalence
  of conditions (1) and (2).
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_of_isLocallyNoetherian`:
  **Stacks 0416**, condition (3), over a locally Noetherian target.

## Implementation notes

Finite local freeness of the morphism of algebraic spaces is read as
`CategoryTheory.MorphismProperty.presheaf` of the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of finite local freeness of morphisms of schemes, which
is condition (1) of Stacks 03ZW: the morphism is representable and every represented base change
of it is a finite locally free morphism of schemes. Condition (2) of Stacks 03ZW, the
direct-image definition `AlgebraicGeometry.Space.IsFiniteLocallyFree` of Stacks 03ZV, is not used
here; comparing it with the representable reading is Stacks 03ZU, which is proved, as
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`, but which this file
neither imports nor needs: Stacks 0416 is stated and proved at condition (1) throughout, so no
statement below mentions the direct image of the structure sheaf.

The equivalence of conditions (1) and (2) of Stacks 0416 is then the scheme-level equivalence
Stacks 02KB, `Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`,
applied to one represented base change at a time: the relative morphism property is a condition
on each represented base change separately, so an equivalence of properties of morphisms of
schemes transfers to it termwise. What this needs is that the three conditions on the right —
finiteness of Stacks 03ZP, flatness of Stacks 03ML and local finite presentation of Stacks 03XP —
also be conditions on the represented base changes. For finiteness that is Stacks 03ZQ,
`AlgebraicGeometry.Space.isFinite_iff_representable`; for the other two it is Stacks 03MJ for a
representable morphism, `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative`, whose fppf
locality hypothesis comes from fpqc locality because the fppf precoverage is contained in the
fpqc one.

Condition (3) is not obtained pointwise: a test scheme mapping to a locally Noetherian algebraic
space need not be Noetherian, so the scheme-level statement over a locally Noetherian base does
not apply to the represented base changes. Instead local finite presentation is produced from
local finite type by Stacks 06G4, part (1), the morphism being locally of finite type because a
finite morphism of schemes is.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Representable readings of the chart conditions -/

/-- A relative morphism property of presheaves on the big fppf site of `S` is monotone in the
underlying property of morphisms of schemes: it is a condition on each represented base change
separately. -/
theorem presheaf_inverseImage_mono {Q R : MorphismProperty Scheme.{u}}
    (hQR : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Q p → R p) {f : X ⟶ Y}
    (hf : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage R (BigFppfOver.toScheme B S hS)).presheaf f :=
  ⟨hf.1, fun _ _ g fst snd hpb => hQR _ (hf.2 g fst snd hpb)⟩

/-- Chart conditions for a property that is étale local on the source and target, stable under
base change and fpqc local on the target are conditions on the represented base changes. -/
private theorem holdsOnEveryEtaleChart_iff_presheaf {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (hP : IsEtaleLocalOnSourceAndTarget P) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) :
    HoldsOnEveryEtaleChart B S hS P f ↔
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f :=
  have : P.IsLocalAtTarget Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  holdsOnEveryEtaleChart_iff_relative B S hS _ hP hX hY f hf

/-- **Stacks 03ML**, part (1), for a representable morphism: a representable morphism of
algebraic spaces over `S` is flat exactly when all of its represented base changes are flat
morphisms of schemes.

Flatness of morphisms of schemes is étale local on the source and target, stable under base
change and local on the target for the fpqc, hence for the fppf, topology, so this is
Stacks 03MJ for a representable morphism at that property. This is the agreement, stated in the
introduction of the section on flat morphisms (Stacks 03MK), of flatness of a morphism of
algebraic spaces with the notion for representable morphisms of Section 03HA. -/
@[stacks 03MK "agreement of flatness with the notion for representable morphisms"]
theorem isFlat_iff_presheaf (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) :
    IsFlat B S hS f ↔
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  holdsOnEveryEtaleChart_iff_presheaf B S hS
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hX hY hf

/-- **Stacks 03XP**, part (1), for a representable morphism: a representable morphism of
algebraic spaces over `S` is locally of finite presentation exactly when all of its represented
base changes are morphisms of schemes locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_iff_presheaf (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) :
    IsLocallyOfFinitePresentation B S hS f ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  holdsOnEveryEtaleChart_iff_presheaf B S hS
    AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hX hY hf

/-- **Stacks 03XF**, part (1), for a representable morphism: a representable morphism of
algebraic spaces over `S` is locally of finite type exactly when all of its represented base
changes are morphisms of schemes locally of finite type. -/
theorem isLocallyOfFiniteType_iff_presheaf (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) :
    IsLocallyOfFiniteType B S hS f ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  holdsOnEveryEtaleChart_iff_presheaf B S hS
    AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hX hY hf

/-- A finite morphism of algebraic spaces over `S` is locally of finite type.

Finiteness is a condition on the represented base changes by Stacks 03ZQ, and a finite morphism
of schemes is locally of finite type. -/
theorem isLocallyOfFiniteType_of_isFinite (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsFinite B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  have hrep := (isFinite_iff_representable B S hS f hX hY).mp hf
  (isLocallyOfFiniteType_iff_presheaf B S hS hX hY hrep.1).mpr
    (presheaf_inverseImage_mono B S hS
      (fun p hp => by
        have : _root_.AlgebraicGeometry.IsFinite p := hp
        infer_instance) hrep.2)

/-! ### Stacks 0416 -/

/-- **Stacks 0416, conditions (1) and (2).** A morphism of algebraic spaces over `S` is
representable and finite locally free exactly when it is finite, flat and locally of finite
presentation.

Both sides are conditions on the represented base changes of the morphism, so this is the
scheme-level equivalence Stacks 02KB applied to one represented base change at a time. -/
@[stacks 0416 "conditions (1) and (2), finite local freeness in the representable sense"]
theorem isFiniteLocallyFree_presheaf_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      IsFinite B S hS f ∧ IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f := by
  have key : ∀ {Z W : Scheme.{u}} (p : W ⟶ Z), Stacks.Morphisms.IsFiniteLocallyFree p ↔
      _root_.AlgebraicGeometry.IsFinite p ∧ AlgebraicGeometry.Flat p ∧
        AlgebraicGeometry.LocallyOfFinitePresentation p := fun p =>
    Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p
  constructor
  · intro hf
    refine ⟨(isFinite_iff_representable B S hS f hX hY).mpr ⟨hf.1, ?_⟩,
      (isFlat_iff_presheaf B S hS hX hY hf.1).mpr ?_,
      (isLocallyOfFinitePresentation_iff_presheaf B S hS hX hY hf.1).mpr ?_⟩
    · exact presheaf_inverseImage_mono B S hS (fun p hp => ((key p).mp hp).1) hf
    · exact presheaf_inverseImage_mono B S hS (fun p hp => ((key p).mp hp).2.1) hf
    · exact presheaf_inverseImage_mono B S hS (fun p hp => ((key p).mp hp).2.2) hf
  · rintro ⟨hfin, hflat, hlfp⟩
    obtain ⟨hrep, hpfin⟩ := (isFinite_iff_representable B S hS f hX hY).mp hfin
    have hpflat := (isFlat_iff_presheaf B S hS hX hY hrep).mp hflat
    have hplfp := (isLocallyOfFinitePresentation_iff_presheaf B S hS hX hY hrep).mp hlfp
    exact ⟨hrep, fun _ _ g fst snd hpb => (key _).mpr
      ⟨hpfin.2 g fst snd hpb, hpflat.2 g fst snd hpb, hplfp.2 g fst snd hpb⟩⟩

/-- **Stacks 0416, condition (3).** A morphism of algebraic spaces over `S` with locally
Noetherian target is representable and finite locally free exactly when it is finite and flat.

A finite morphism is locally of finite type, hence locally of finite presentation over a locally
Noetherian target by Stacks 06G4, part (1), so the finite presentation condition of conditions
(1) and (2) is automatic. -/
@[stacks 0416 "condition (3) over a locally Noetherian target"]
theorem isFiniteLocallyFree_presheaf_iff_of_isLocallyNoetherian
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      IsFinite B S hS f ∧ IsFlat B S hS f := by
  rw [isFiniteLocallyFree_presheaf_iff B S hS hX hY f]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2,
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hX hY f hN
      (isLocallyOfFiniteType_of_isFinite B S hS hX hY h.1)⟩⟩

end AlgebraicGeometry.Space

end
