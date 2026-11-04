module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.AlgebraicGeometry.FieldToResidue
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of a base change along a field extension with a prescribed residue field

Let `K / k` be an extension of fields, let `X` be a scheme over `k` and let `x` be a point of `X`
whose residue field admits a `k`-algebra map `σ : κ(x) → K`. Then the base change
`X_K = X ×_{Spec k} Spec K` has a point `y` above `x` whose residue field is `K`: the morphism
`Spec K → X` determined by `σ` lifts to a section of `X_K → Spec K` through `y`, and a morphism
admitting a section induces an isomorphism on residue fields at a point of its image.

This is the construction of the point of `Spec (κ(x) ⊗_k K)` above `x` with residue field `K`
asked for by the reduction of Stacks Tag 0CBY to a split node — obtained without forming the
tensor product.

## Main results

* `AlgebraicGeometry.fieldToResidue_eq_specGammaResidue_comp_residueFieldMap` — the structural
  map from the ground field to a residue field factors through the residue field of the base.
* `AlgebraicGeometry.bijective_fieldToResidue_of_section` — if the structure morphism of a
  `K`-scheme admits a section, then at a point in the image of that section the structural map
  `K → κ(y)` is bijective.
* `AlgebraicGeometry.exists_baseChange_point_of_residueFieldHom` — the point of the base change
  above `x` with residue field `K`, together with the compatibility of `σ` with the residue-field
  map of the first projection.

## Implementation notes

The residue field of `Spec K` at its unique point is identified with `K` through
`AlgebraicGeometry.Scheme.Spec.residueFieldIso` and `Ideal.algEquivResidueFieldOfField`; this is
the only place where the structural map is computed, everything else being naturality.

The section is `CategoryTheory.Limits.pullback.lift` of the morphism `Spec K ⟶ X` determined by
`σ` and the identity of `Spec K`; the commutation it needs is the statement that `σ` is a
`k`-algebra map, read through
`AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv`.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

section Sections

variable {K : Type u} [Field K] {Z : Scheme.{u}}

/-- **The structural map from the ground field to a residue field factors through the residue
field of the base point.** For a scheme over `Spec K` the map `K → κ(y)` is the canonical map
from `K` to the residue field of `Spec K` at the image of `y`, followed by the residue-field map
of the structure morphism. This is naturality of evaluation. -/
theorem fieldToResidue_eq_specGammaResidue_comp_residueFieldMap (q : Z ⟶ Spec (.of K)) (y : Z) :
    fieldToResidue q y =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (Spec (CommRingCat.of K)).presheaf.germ ⊤ (q y) trivial ≫
          (Spec (CommRingCat.of K)).residue (q y)) ≫ q.residueFieldMap y := by
  have h : fieldToResidue q y =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (Spec (CommRingCat.of K)).Γevaluation (q y)) ≫ q.residueFieldMap y := by
    rw [Category.assoc, Scheme.Γevaluation_naturality, fieldToResidue, fieldToStalk]
    simp only [Category.assoc]
    rfl
  exact h

/-- **The canonical map from a field to the residue field of its spectrum at the unique point is
bijective.** -/
theorem bijective_germ_residue_spec_of_field (K : Type u) [Field K]
    (w : Spec (CommRingCat.of K)) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ w trivial ≫
        (Spec (CommRingCat.of K)).residue w).hom := by
  let : Field ↑(CommRingCat.of K) := inferInstanceAs (Field K)
  let : w.asIdeal.IsPrime := w.isPrime
  rw [← Scheme.Spec.algebraMap_residueFieldIso_inv]
  exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (CommRingCat.of K) w).inv).comp
    (Ideal.algEquivResidueFieldOfField w.asIdeal).bijective

/-- **At a point in the image of a section of the structure morphism the residue field is the
base field.** The residue-field map of the structure morphism is an isomorphism there
(`AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section`), and the structural map factors
through it. -/
theorem bijective_fieldToResidue_of_section (q : Z ⟶ Spec (.of K)) (j : Spec (.of K) ⟶ Z)
    (hj : j ≫ q = 𝟙 _) (z : Spec (.of K)) :
    Function.Bijective (fieldToResidue q (j z)).hom := by
  have hiso : IsIso (q.residueFieldMap (j z)) :=
    isIso_residueFieldMap_of_mem_range_section q j hj z
  rw [fieldToResidue_eq_specGammaResidue_comp_residueFieldMap q (j z)]
  exact (ConcreteCategory.bijective_of_isIso (q.residueFieldMap (j z))).comp
    (bijective_germ_residue_spec_of_field K (q (j z)))

/-- The residue-field map of `g` at `j c` followed by the map determined by `j` recovers `j ≫ g`
on spectra. -/
private theorem spec_map_residueFieldMap_comp_descResidueField_comp_fromSpecResidueField
    {Y : Scheme.{u}} (g : Z ⟶ Y) (j : Spec (.of K) ⟶ Z) :
    Spec.map (g.residueFieldMap (j (closedPoint (CommRingCat.of K))) ≫
        Scheme.descResidueField (Scheme.stalkClosedPointTo j)) ≫
      Y.fromSpecResidueField (g (j (closedPoint (CommRingCat.of K)))) = j ≫ g := by
  rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z j]

/-- **The residue field map of a section inverts the structural map of the base field.** The
composite `K → κ(y) → K`, the second map being the one that the section determines, is the
identity. -/
theorem fieldToResidue_comp_descResidueField_section (q : Z ⟶ Spec (.of K))
    (j : Spec (.of K) ⟶ Z) (hj : j ≫ q = 𝟙 _) :
    fieldToResidue q (j (closedPoint (CommRingCat.of K))) ≫
        Scheme.descResidueField (Scheme.stalkClosedPointTo j) = 𝟙 _ := by
  have h2 := spec_map_residueFieldMap_comp_descResidueField_comp_fromSpecResidueField q j
  rw [hj] at h2
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id] at h2
  rw [fieldToResidue_eq_specGammaResidue_comp_residueFieldMap q
    (j (closedPoint (CommRingCat.of K))), ← Scheme.Spec.algebraMap_residueFieldIso_inv]
  simpa only [Category.assoc] using Spec.map_injective h2

end Sections

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}

/-- **A point of the base change along a field extension with a prescribed residue field.** Let
`σ : κ(x) → K` be a `k`-algebra map. Then `X_K = X ×_{Spec k} Spec K` has a point `y` above `x`
whose structural map `K → κ(y)` is bijective, and the residue-field map of the first projection
at `y` is `σ` read into `κ(y)`.

The point is the image of the section of `X_K ⟶ Spec K` obtained by lifting the morphism
`Spec K ⟶ X` that `σ` determines; its residue field is computed by
`AlgebraicGeometry.bijective_fieldToResidue_of_section`. No tensor product is formed. -/
@[sga "3 V 4.1.2" "(iii), special case"]
theorem exists_baseChange_point_of_residueFieldHom (f : X ⟶ Spec (.of k)) (x : X)
    (σ : X.residueField x ⟶ CommRingCat.of K)
    (hσ : fieldToResidue f x ≫ σ = CommRingCat.ofHom (algebraMap k K)) :
    ∃ (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
      (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x),
      Function.Bijective (fieldToResidue
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y).hom ∧
        σ ≫ fieldToResidue
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y =
          (X.residueFieldCongr hy.symm).hom ≫
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap y := by
  let : Field ↑(CommRingCat.of k) := inferInstanceAs (Field k)
  let : Field ↑(CommRingCat.of K) := inferInstanceAs (Field K)
  let : (f x).asIdeal.IsPrime := (f x).isPrime
  have ha : (Spec.map σ ≫ X.fromSpecResidueField x) ≫ f =
      𝟙 (Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Category.id_comp, Category.assoc,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← Category.assoc, Scheme.Spec.algebraMap_residueFieldIso_inv, ← hσ,
      fieldToResidue_eq_specGammaResidue_comp_residueFieldMap f x]
    simp only [Category.assoc]
  have hjfst := pullback.lift_fst (Spec.map σ ≫ X.fromSpecResidueField x)
    (𝟙 (Spec (CommRingCat.of K))) ha
  have hjsnd := pullback.lift_snd (Spec.map σ ≫ X.fromSpecResidueField x)
    (𝟙 (Spec (CommRingCat.of K))) ha
  have hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base
      (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
        (𝟙 (Spec (CommRingCat.of K))) ha (closedPoint (CommRingCat.of K))) = x := by
    have h : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base
          (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
            (𝟙 (Spec (CommRingCat.of K))) ha (closedPoint (CommRingCat.of K))) =
        (X.fromSpecResidueField x) (Spec.map σ (closedPoint (CommRingCat.of K))) :=
      congrArg (fun m : Spec (CommRingCat.of K) ⟶ X =>
        m (closedPoint (CommRingCat.of K))) hjfst
    exact h.trans (Scheme.fromSpecResidueField_apply x _)
  refine ⟨_, hy, bijective_fieldToResidue_of_section _ _ hjsnd _, ?_⟩
  have hFτ := fieldToResidue_comp_descResidueField_section
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
      (𝟙 (Spec (CommRingCat.of K))) ha) hjsnd
  have hτF : Scheme.descResidueField (Scheme.stalkClosedPointTo
        (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
          (𝟙 (Spec (CommRingCat.of K))) ha)) ≫
      fieldToResidue (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) _ = 𝟙 _ := by
    refine CommRingCat.hom_ext (RingHom.ext fun w => ?_)
    refine (Scheme.descResidueField (Scheme.stalkClosedPointTo
      (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
        (𝟙 (Spec (CommRingCat.of K))) ha))).hom.injective ?_
    have hw := congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom
      ((Scheme.descResidueField (Scheme.stalkClosedPointTo
        (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
          (𝟙 (Spec (CommRingCat.of K))) ha))).hom w)) hFτ
    simpa using hw
  have h2 : Spec.map (((X.residueFieldCongr hy.symm).hom ≫
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap _) ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo
            (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
              (𝟙 (Spec (CommRingCat.of K))) ha))) ≫ X.fromSpecResidueField x =
      Spec.map σ ≫ X.fromSpecResidueField x := by
    rw [Category.assoc, Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField,
      spec_map_residueFieldMap_comp_descResidueField_comp_fromSpecResidueField, hjfst]
  calc σ ≫ fieldToResidue
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) _
      = (((X.residueFieldCongr hy.symm).hom ≫
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap _) ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo
            (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
              (𝟙 (Spec (CommRingCat.of K))) ha))) ≫
            fieldToResidue
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) _ := by
        rw [Spec.map_injective ((cancel_mono (X.fromSpecResidueField x)).mp h2)]
    _ = ((X.residueFieldCongr hy.symm).hom ≫
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap _) ≫
            (Scheme.descResidueField (Scheme.stalkClosedPointTo
              (pullback.lift (Spec.map σ ≫ X.fromSpecResidueField x)
                (𝟙 (Spec (CommRingCat.of K))) ha)) ≫
              fieldToResidue
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) _) :=
        Category.assoc _ _ _
    _ = _ := by rw [hτF, Category.comp_id]

end BaseChange

end AlgebraicGeometry

end
