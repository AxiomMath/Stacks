module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The canonical morphism from the spectrum of a residue field is an isomorphism on residue fields

For a scheme `X` and a point `x`, the morphism `Spec κ(x) ⟶ X` induces an isomorphism on the
residue field at the unique point of `Spec κ(x)`.

For a local ring `B`, `AlgebraicGeometry.residueFieldAtClosedPointEquiv` identifies the residue
field of the scheme `Spec B` at its closed point with the residue field of `B`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes whose stalk map at `x` is surjective induces an isomorphism on
residue fields at `x`. -/
private theorem isIso_residueFieldMap_of_surjective_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (hf : Function.Surjective (f.stalkMap x)) : IsIso (f.residueFieldMap x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro y
    obtain ⟨z, hz⟩ := X.residue_surjective x y
    obtain ⟨w, hw⟩ := hf z
    refine ⟨Y.residue (f x) w, ?_⟩
    have heq := congrArg (fun φ => φ w)
      (congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x))
    change (f.residueFieldMap x).hom (Y.residue (f x) w) = X.residue x (f.stalkMap x w) at heq
    rw [hw, hz] at heq
    exact heq
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, hs⟩

/-- The canonical morphism from the spectrum of a residue field induces isomorphisms on
residue fields. -/
lemma isIso_residueFieldMap_fromSpecResidueField
    (X : Scheme.{u}) (x : X) (p : Spec (X.residueField x)) :
    IsIso ((X.fromSpecResidueField x).residueFieldMap p) := by
  let q : Spec (X.residueField x) := by
    rw [Spec_carrier]
    exact IsLocalRing.closedPoint (X.residueField x)
  have hp : p = q := Subsingleton.elim _ _
  subst p
  have : IsPreimmersion (X.fromSpecResidueField x) := by
    dsimp only [Scheme.fromSpecResidueField]
    rw [IsPreimmersion.comp_iff]
    infer_instance
  exact isIso_residueFieldMap_of_surjective_stalkMap _ _
    ((X.fromSpecResidueField x).stalkMap_surjective q)

/-- **A morphism admitting a section induces an isomorphism on residue fields at every point of
the image of that section.** The residue field map of `f` at `s y` is split by the residue field
map of `s` at `y`, because `s ≫ f` is the identity; a split map of residue fields whose composite
with its splitting is bijective is itself bijective, the splitting being injective as a map of
fields. -/
theorem isIso_residueFieldMap_of_mem_range_section {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    IsIso (f.residueFieldMap (s y)) := by
  have key : ∀ g : Y ⟶ Y, g = 𝟙 Y → IsIso (g.residueFieldMap y) := by
    intro g hg
    subst hg
    rw [Scheme.residueFieldMap_id]
    exact IsIso.id _
  have hcomp : IsIso (f.residueFieldMap (s y) ≫ s.residueFieldMap y) :=
    Scheme.residueFieldMap_comp s f y ▸ key _ hs
  have hbij := ConcreteCategory.bijective_of_isIso
    (f.residueFieldMap (s y) ≫ s.residueFieldMap y)
  apply (ConcreteCategory.isIso_iff_bijective (f.residueFieldMap (s y))).mpr
  refine ⟨fun a b hab => hbij.injective ?_, fun b => ?_⟩
  · simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (s.residueFieldMap y).hom hab
  · obtain ⟨a, ha⟩ := hbij.surjective ((s.residueFieldMap y).hom b)
    exact ⟨a, (s.residueFieldMap y).hom.injective (by
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using ha)⟩

/-- A morphism from the spectrum of a local ring induces an isomorphism on residue fields at
the closed point as soon as it is surjective on stalks there. -/
lemma isIso_residueFieldMap_of_surjective_stalkClosedPointTo
    {X : Scheme.{u}} {B : CommRingCat.{u}} [IsLocalRing B]
    (α : Spec B ⟶ X)
    (hsurj : Function.Surjective (Scheme.stalkClosedPointTo α).hom) :
    IsIso (α.residueFieldMap (IsLocalRing.closedPoint B)) := by
  let cp : Spec B := by
    rw [Spec_carrier]
    exact IsLocalRing.closedPoint B
  have : IsLocalRing ((Spec B).presheaf.stalk cp) := (Spec B).toLocallyRingedSpace.isLocalRing cp
  have hrel : Scheme.stalkClosedPointTo α =
      Scheme.Hom.stalkMap α cp ≫ (stalkClosedPointIso B).hom := CommRingCat.hom_ext rfl
  have hstalkMapSurj : Function.Surjective (Scheme.Hom.stalkMap α cp).hom := by
    have hiso : Function.Bijective (stalkClosedPointIso B).hom.hom :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have hcomp : (Scheme.stalkClosedPointTo α).hom =
        (stalkClosedPointIso B).hom.hom.comp (Scheme.Hom.stalkMap α cp).hom := by
      rw [hrel]
      rfl
    intro y
    obtain ⟨z, hz⟩ := hsurj ((stalkClosedPointIso B).hom.hom y)
    rw [hcomp] at hz
    exact ⟨z, hiso.injective hz⟩
  exact isIso_residueFieldMap_of_surjective_stalkMap α cp hstalkMapSurj

/-- A morphism of schemes whose stalk map at `x` is surjective induces an isomorphism on
residue fields at `x`. -/
public theorem isIso_residueFieldMap_of_stalkMap_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : Function.Surjective (f.stalkMap x)) : IsIso (f.residueFieldMap x) :=
    isIso_residueFieldMap_of_surjective_stalkMap f x hf

end AlgebraicGeometry
