module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of a scheme as field-valued points

A *field-valued point* of a scheme `X` is a morphism `Spec K ⟶ X` from the spectrum of a field.
Two of them are regarded as equal when they admit a common field-valued refinement, and the
points of `X` are exactly the resulting equivalence classes. Each class has a canonical smallest
representative, the morphism `Spec κ(x) ⟶ X` out of the residue field at `x`, through which every
other representative factors uniquely.

## Main definitions

* `AlgebraicGeometry.FieldValuedPoint`: a field together with a morphism from its spectrum.
* `AlgebraicGeometry.FieldValuedPoint.Dominates`: one field-valued point factors through another.
* `AlgebraicGeometry.FieldValuedPoint.HasCommonExtension`: the relation of admitting a common
  field-valued refinement.
* `AlgebraicGeometry.FieldValuedPoint.IsSmallest`: the universal property of a smallest
  representative.

## Main results

* `AlgebraicGeometry.pointsEquivFieldValuedPointClasses`: the points of a scheme correspond
  bijectively to the equivalence classes of its field-valued points.
* `AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq`: the common-extension
  relation is equality of the underlying points.
* `AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest`: `Spec κ(x) ⟶ X` is the smallest
  representative of the class of `x`.
* `AlgebraicGeometry.FieldValuedPoint.uniqueIso_of_isSmallest`: smallest representatives are
  unique up to unique isomorphism.

## References

* [Stacks Project, Tag 01J9](https://stacks.math.columbia.edu/tag/01J9)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

add_to_stacks 01J9 "morphisms from the spectrum of a fixed field"
  AlgebraicGeometry.Scheme.SpecToEquivOfField
add_to_ega "I 2.4.6" AlgebraicGeometry.Scheme.SpecToEquivOfField
add_to_ega "I 3.4.5" "partial, special case" AlgebraicGeometry.Scheme.SpecToEquivOfField
add_to_ega "II 1.7.10" "Opening clause" AlgebraicGeometry.Scheme.SpecToEquivOfField

/-- A field-valued point of `X` is a morphism `Spec(K) ⟶ X` for a field `K`. -/
structure FieldValuedPoint (X : Scheme.{u}) where
  /-- The field of definition of the point. -/
  carrier : Type u
  /-- The field structure on the field of definition. -/
  [field : Field carrier]
  /-- The morphism from the spectrum of the field. -/
  map : Spec (.of carrier) ⟶ X

attribute [instance] FieldValuedPoint.field

namespace FieldValuedPoint

/-- The image in `X` of the unique point of the spectrum of the field. -/
noncomputable def point {X : Scheme.{u}} (p : FieldValuedPoint X) : X :=
  p.map (IsLocalRing.closedPoint p.carrier)

/-- The canonical field-valued point `Spec(κ(x)) ⟶ X` attached to `x`. -/
noncomputable def canonical (X : Scheme.{u}) (x : X) : FieldValuedPoint X where
  carrier := X.residueField x
  map := X.fromSpecResidueField x

/-- A field-valued point dominates another if its map to `X` factors through it. -/
def Dominates {X : Scheme.{u}} (p q : FieldValuedPoint X) : Prop :=
  ∃ f : Spec (.of p.carrier) ⟶ Spec (.of q.carrier), f ≫ q.map = p.map

/-- Two field-valued points have a common field-valued extension. -/
def HasCommonExtension {X : Scheme.{u}} (p q : FieldValuedPoint X) : Prop :=
  ∃ r : FieldValuedPoint X, r.Dominates p ∧ r.Dominates q

/-- Two field-valued points represent the same point of `X`. -/
noncomputable def setoid (X : Scheme.{u}) : Setoid (FieldValuedPoint X) :=
  Setoid.ker point

/-- A representative is smallest in its equivalence class when every representative of the
same point factors through it in a unique way. -/
def IsSmallest {X : Scheme.{u}} (q : FieldValuedPoint X) : Prop :=
  ∀ p : FieldValuedPoint X, p.point = q.point →
    ∃! f : Spec (.of p.carrier) ⟶ Spec (.of q.carrier), f ≫ q.map = p.map

end FieldValuedPoint

/-- Points of a scheme correspond bijectively to equivalence classes of field-valued points. -/
@[stacks 01J9 "the bijection with equivalence classes"]
noncomputable def pointsEquivFieldValuedPointClasses (X : Scheme.{u}) :
    X ≃ Quotient (FieldValuedPoint.setoid X) :=
  (Setoid.quotientKerEquivOfRightInverse FieldValuedPoint.point
    (FieldValuedPoint.canonical X) (by
    intro x
    exact Scheme.fromSpecResidueField_apply x _)).symm

namespace FieldValuedPoint

/-- A field-valued point dominating another one has the same image point. -/
private theorem point_eq_of_dominates {X : Scheme.{u}} {p q : FieldValuedPoint X}
    (h : q.Dominates p) : q.point = p.point := by
  obtain ⟨f, hf⟩ := h
  rw [point, ← hf]
  exact congrArg p.map (Subsingleton.elim _ _)

/-- Two field-valued points have a common field-valued extension if and only if they have the same
image point. -/
@[stacks 01J9 "the common-extension relation", ega "I 3.4.5" "location map"]
theorem hasCommonExtension_iff_point_eq {X : Scheme.{u}} (p q : FieldValuedPoint X) :
    p.HasCommonExtension q ↔ p.point = q.point := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    exact (point_eq_of_dominates hrp).symm.trans (point_eq_of_dominates hrq)
  · intro h
    let ep := X.SpecToEquivOfField p.carrier p.map
    let eq := X.SpecToEquivOfField q.carrier q.map
    have hpq : ep.1 = eq.1 := by
      simpa [ep, eq, FieldValuedPoint.point] using h
    let K := X.residueField ep.1
    let eq' : Σ y, X.residueField y ⟶ .of q.carrier :=
      ⟨ep.1, (X.residueFieldCongr hpq).hom ≫ eq.2⟩
    let : Algebra K p.carrier := ep.2.hom.toAlgebra
    let : Algebra K q.carrier := eq'.2.hom.toAlgebra
    let : Nontrivial (p.carrier ⊗[K] q.carrier) :=
      Module.FaithfullyFlat.lTensor_nontrivial K p.carrier q.carrier
    obtain ⟨M, _, _, _, _, hEM, hFM⟩ :=
      exists_common_extension K p.carrier q.carrier
    let r : FieldValuedPoint X :=
      { carrier := M
        map := Spec.map (CommRingCat.ofHom (algebraMap p.carrier M)) ≫ p.map }
    refine ⟨r, ⟨Spec.map (CommRingCat.ofHom (algebraMap p.carrier M)), rfl⟩,
      Spec.map (CommRingCat.ofHom (algebraMap q.carrier M)), ?_⟩
    dsimp [r]
    rw [← (X.SpecToEquivOfField q.carrier).left_inv q.map,
      ← (X.SpecToEquivOfField p.carrier).left_inv p.map]
    change Spec.map (CommRingCat.ofHom (algebraMap q.carrier M)) ≫
        (Spec.map eq.2 ≫ X.fromSpecResidueField eq.1) =
      Spec.map (CommRingCat.ofHom (algebraMap p.carrier M)) ≫
        (Spec.map ep.2 ≫ X.fromSpecResidueField ep.1)
    rw [← Scheme.residueFieldCongr_fromSpecResidueField hpq, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_hom eq.2,
      ← CommRingCat.ofHom_hom ep.2, ← CommRingCat.ofHom_comp]
    have H : (algebraMap q.carrier M).comp eq'.2.hom =
        (algebraMap p.carrier M).comp ep.2.hom := by
      ext z
      change algebraMap q.carrier M (algebraMap K q.carrier z) =
        algebraMap p.carrier M (algebraMap K p.carrier z)
      rw [← IsScalarTower.algebraMap_apply K q.carrier M,
        ← IsScalarTower.algebraMap_apply K p.carrier M]
    rw [← CommRingCat.ofHom_hom (X.residueFieldCongr hpq).hom,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc]
    dsimp [eq'] at H
    rw [H, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The canonical morphism `Spec(κ(x)) ⟶ X` is the smallest representative of the equivalence
class corresponding to `x`. -/
@[stacks 01J9 "the smallest representative", ega "I 2.4.6" "factorization via κ(x)"]
theorem canonical_isSmallest {X : Scheme.{u}} (x : X) :
    (canonical X x).IsSmallest := by
  intro p hp
  let e := X.SpecToEquivOfField p.carrier p.map
  have he : e.1 = x := hp.trans (Scheme.fromSpecResidueField_apply x _)
  let φ : X.residueField x ⟶ .of p.carrier :=
    (X.residueFieldCongr he).inv ≫ e.2
  have hfac : Spec.map φ ≫ (canonical X x).map = p.map := by
    change Spec.map φ ≫ X.fromSpecResidueField x = p.map
    calc
      Spec.map φ ≫ X.fromSpecResidueField x =
          Spec.map e.2 ≫ (Spec.map (X.residueFieldCongr he).inv ≫
            X.fromSpecResidueField x) := by
        dsimp [φ]
        rw [Spec.map_comp, Category.assoc]
      _ = Spec.map e.2 ≫ X.fromSpecResidueField e.1 := by
        subst x
        simp
      _ = p.map := (X.SpecToEquivOfField p.carrier).left_inv p.map
  have : Mono (canonical X x).map := inferInstanceAs (Mono (X.fromSpecResidueField x))
  exact ⟨Spec.map φ, hfac, fun g hg ↦ (cancel_mono _).1 (hg.trans hfac.symm)⟩

/-- Any two smallest representatives of the same point are uniquely isomorphic over `X`. -/
@[stacks 01J9 "uniqueness up to unique isomorphism"]
theorem uniqueIso_of_isSmallest {X : Scheme.{u}} {p q : FieldValuedPoint X}
    (hp : p.IsSmallest) (hq : q.IsSmallest) (h : p.point = q.point) :
    ∃! e : Spec (.of p.carrier) ≅ Spec (.of q.carrier), e.hom ≫ q.map = p.map := by
  obtain ⟨f, hf, hfu⟩ := hq p h
  obtain ⟨g, hg, hgu⟩ := hp q h.symm
  have key : ∀ {p q : FieldValuedPoint X} (f : Spec (.of p.carrier) ⟶ Spec (.of q.carrier))
      (g : Spec (.of q.carrier) ⟶ Spec (.of p.carrier)), p.IsSmallest →
      f ≫ q.map = p.map → g ≫ p.map = q.map → f ≫ g = 𝟙 _ := fun f g hp hf hg ↦
    (hp _ rfl).unique (by simpa only [Category.assoc, hg] using hf) (by simp)
  have hfg := key f g hp hf hg
  have hgf := key g f hq hg hf
  exact ⟨{ hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }, hf,
    fun e he ↦ Iso.ext (hfu e.hom he)⟩

end FieldValuedPoint

end AlgebraicGeometry

end
