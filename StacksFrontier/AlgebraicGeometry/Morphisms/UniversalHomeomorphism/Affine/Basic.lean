module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Elementary consequences of being a universal homeomorphism

A universal homeomorphism is in particular a homeomorphism, is universally closed and
universally injective, and induces purely inseparable extensions of residue fields. For a
morphism of affine schemes it also forces the ring map to be integral. This file collects
those consequences, which the study of universal homeomorphisms of affine schemes uses
throughout, together with the stability of the class under composition and under isomorphism.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_of_isIso`: an isomorphism is a universal
  homeomorphism.
* `AlgebraicGeometry.universalHomeomorphism_isHomeomorph`,
  `AlgebraicGeometry.universalHomeomorphism_universallyClosed` and
  `AlgebraicGeometry.universalHomeomorphism_universallyInjective`: the three weaker
  topological properties.
* `AlgebraicGeometry.universalHomeomorphism_residueFieldMap_isPurelyInseparable`: the induced
  extension of residue fields at a point is purely inseparable.
* `AlgebraicGeometry.universalHomeomorphism_algebra_isIntegral`: for a map of affine schemes
  coming from an algebra, the algebra is integral.

## Implementation notes

The topological consequences are obtained from the defining `MorphismProperty.universally`
condition by specialising it to the trivial pullback square, and the integrality from the
characterization of universal homeomorphisms as the integral, universally injective,
surjective morphisms.

## References

* [Stacks Project, Tag 0CNC](https://stacks.math.columbia.edu/tag/0CNC)
* [Stacks Project, Tag 0CNE](https://stacks.math.columbia.edu/tag/0CNE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Being a homeomorphism on the underlying spaces is stable under isomorphism and
composition, which is what the `universally` construction needs. -/
public instance topologically_isHomeomorph_respectsIso :
    (topologically @IsHomeomorph).RespectsIso :=
  topologically_respectsIso (P := @IsHomeomorph) (fun e => e.isHomeomorph) (by
    intro α β γ _ _ _ f g hf hg
    exact hg.comp hf)

/-- Being a homeomorphism on underlying spaces is Zariski-local at the target. -/
public instance topologicallyIsHomeomorph_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically @IsHomeomorph) :=
  topologically_isZariskiLocalAtTarget' (P := @IsHomeomorph)
    (fun {α β} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) {ι : Type _}
      (U : ι → Opens β) (hU : IsOpenCover U) (hf : Continuous f) ↦
      hU.isHomeomorph_iff_restrictPreimage hf)

/-- Being a universal homeomorphism is Zariski-local at the target. -/
@[sga "4 IV 8.5.5" "special case"]
public instance universallyTopologicallyIsHomeomorph_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically @IsHomeomorph).universally :=
  universally_isZariskiLocalAtTarget (topologically @IsHomeomorph)
    (fun {X Y} (f : X ⟶ Y) {ι : Type _} (U : ι → Y.Opens) (hU : IsOpenCover U)
      (H : ∀ i, topologically @IsHomeomorph (f ∣_ U i)) ↦ by
    apply (hU.isHomeomorph_iff_restrictPreimage f.continuous).mpr
    intro i
    convert (by simpa only [topologically, morphismRestrict_base] using H i) using 1
    rfl)

/-- An isomorphism of schemes is a universal homeomorphism. -/
lemma universalHomeomorphism_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    UniversalHomeomorphism f := by
  rw [universalHomeomorphism_iff]
  have := topologically_isHomeomorph_respectsIso
  apply MorphismProperty.universally_mk' (P := topologically @IsHomeomorph) f
  intro T i hp
  have : HasPullback i f := hp
  exact topologically_iso_le (P := @IsHomeomorph) (fun e => e.isHomeomorph)
    (pullback.fst i f) inferInstance

/-- A universal homeomorphism is a homeomorphism: take the base change along the identity. -/
lemma universalHomeomorphism_isHomeomorph {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : IsHomeomorph f :=
  (inferInstance : UniversalHomeomorphism f).universally_isHomeomorph
    _ _ _ IsPullback.of_id_snd

/-- A universal homeomorphism satisfies `universally (topologically P)` for any property `P`
implied by being a homeomorphism. -/
private theorem universalHomeomorphism_universally_topologically
    {P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop}
    (hP : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] {g : α → β},
      IsHomeomorph g → P g)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    (topologically @P).universally f :=
  universally_mono (fun _ _ _ hg ↦ hP hg) f
    (inferInstance : UniversalHomeomorphism f).universally_isHomeomorph

/-- A universal homeomorphism is universally closed. -/
lemma universalHomeomorphism_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  exact universalHomeomorphism_universally_topologically (P := @IsClosedMap)
    (fun hg ↦ hg.isClosedMap) f

/-- A universal homeomorphism is universally injective. -/
lemma universalHomeomorphism_universallyInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : UniversallyInjective f := by
  rw [universallyInjective_iff]
  exact universalHomeomorphism_universally_topologically
    (P := fun g ↦ Function.Injective g) (fun hg ↦ hg.injective) f

/-- A universal homeomorphism induces a purely inseparable extension of the residue field at
every point. -/
lemma universalHomeomorphism_residueFieldMap_isPurelyInseparable {X Y : Scheme.{u}}
    (f : X ⟶ Y) [UniversalHomeomorphism f] (x : X) :
    RingHom.IsPurelyInseparable (CommRingCat.Hom.hom (f.residueFieldMap x)) := by
  have h := (tfae_universallyInjective f).out 1 3
  exact (h.mp (universalHomeomorphism_universallyInjective f)).2 x

/-- If the map on spectra attached to an algebra is a universal homeomorphism, the algebra is
integral. -/
lemma universalHomeomorphism_algebra_isIntegral
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)] :
    Algebra.IsIntegral A B := by
  have hf : IsIntegralHom (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
    rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom]
    exact ⟨universalHomeomorphism_universallyClosed _, inferInstance⟩
  exact algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hf)

end AlgebraicGeometry

end
