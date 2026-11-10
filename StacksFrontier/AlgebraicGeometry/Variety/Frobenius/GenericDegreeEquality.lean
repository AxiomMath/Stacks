module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.GenericDegree

/-!
# The image of the residue-field map of the relative Frobenius

Let `X` be a scheme over a field `k` of characteristic `p > 0`. The image of the residue-field
map of the relative Frobenius `F_{X/k} : X ⟶ X^{(p)}` at a point `x` is exactly the compositum
`kκᵖ` of `k` with the `p`-th powers of the residue field `κ` of `X` at `x`.

## Main results

* `AlgebraicGeometry.fieldRange_residueFieldMap_relativeFrobenius` — the image of the
  residue-field map of the relative Frobenius is the compositum.
* `AlgebraicGeometry.range_residueFieldMap_eq_range_evaluation` — for a scheme over a field, the
  image of the residue-field map of the structure morphism is the image of the base field.

## References

* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- If the canonical morphism out of the residue field at a point factors through the spectrum
of a subfield `C`, then the residue-field map has image inside `C`. -/
private theorem fieldRange_le_of_spec_factorization {K : Type u} [Field K]
    {Y : Scheme.{u}} (y : Y) (φ : Y.residueField y ⟶ .of K) (C : Subfield K)
    (q : Spec (.of C) ⟶ Y)
    (hq : Spec.map (CommRingCat.ofHom C.subtype) ≫ q =
      Spec.map φ ≫ Y.fromSpecResidueField y) : φ.hom.fieldRange ≤ C := by
  have hpoint : Spec.map (CommRingCat.ofHom C.subtype) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint C := Subsingleton.elim _ _
  have hy : y = q (IsLocalRing.closedPoint C) := by
    have h : q (Spec.map (CommRingCat.ofHom C.subtype) (IsLocalRing.closedPoint K)) =
        Y.fromSpecResidueField y (Spec.map φ (IsLocalRing.closedPoint K)) :=
      congrArg (fun g : Spec (.of K) ⟶ Y => g (IsLocalRing.closedPoint K)) hq
    rw [hpoint, Scheme.fromSpecResidueField_apply] at h
    exact h.symm
  subst hy
  let ψ := Y.descResidueField (Scheme.stalkClosedPointTo q)
  have hψ : Spec.map ψ ≫ Y.fromSpecResidueField (q (IsLocalRing.closedPoint C)) = q :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField C Y q
  have heq : Spec.map (ψ ≫ CommRingCat.ofHom C.subtype) ≫
      Y.fromSpecResidueField (q (IsLocalRing.closedPoint C)) =
      Spec.map φ ≫ Y.fromSpecResidueField (q (IsLocalRing.closedPoint C)) := by
    rw [Spec.map_comp, Category.assoc]
    exact (congrArg (fun t => Spec.map (CommRingCat.ofHom C.subtype) ≫ t) hψ).trans hq
  have he : ψ ≫ CommRingCat.ofHom C.subtype = φ :=
    Spec.map_injective ((cancel_mono _).mp heq)
  rintro _ ⟨a, rfl⟩
  rw [← he]
  exact (ψ a).property

/-- Evaluation of the global sections of the spectrum of a field at a point is surjective onto
the residue field there. -/
theorem spec_field_evaluation_surjective {k : Type u} [Field k]
    (y : Spec (.of k)) : Function.Surjective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation y).hom) := by
  intro b
  obtain ⟨s, rfl⟩ := (Spec (.of k)).residue_surjective y b
  obtain ⟨U, hyU, s, rfl⟩ := (Spec (.of k)).presheaf.exists_germ_eq s
  have hU : U = ⊤ := top_unique fun z _ => by simpa [Subsingleton.elim z y] using hyU
  subst hU
  refine ⟨(Scheme.ΓSpecIso (.of k)).hom s, ?_⟩
  change (Spec (.of k)).Γevaluation y
    ((Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom s)) = _
  simp only [Iso.hom_inv_id_apply]
  rfl

/-- For a scheme over a field, the image of the residue-field map of the structure morphism at a
point is the image of the base field under evaluation of global sections there. -/
theorem range_residueFieldMap_eq_range_evaluation {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    (f.residueFieldMap x).hom.range =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom).range := by
  have he : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)) ≫
        f.residueFieldMap x := by
    rw [Category.assoc, Scheme.Γevaluation_naturality]
  rw [he]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := spec_field_evaluation_surjective (f x) b
    exact ⟨c, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f x)) b, rfl⟩

/-- **The image of the residue-field map of the relative Frobenius.** For a scheme `X` over a
field `k` of characteristic `p`, the image of the residue-field map of the relative Frobenius of
`X` at a point `x` is the compositum of `k` with the `p`-th powers of the residue field of `X`
at `x`. -/
theorem fieldRange_residueFieldMap_relativeFrobenius
    {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    (((relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left).residueFieldMap
        x).hom.fieldRange =
      compositumFrobenius k (X.residueField x) p := by
  let _ : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let S := Spec (.of k)
  let K := X.residueField x
  let C : Subfield K := compositumFrobenius k K p
  let r := (relativeFrobenius S p hS (Over.mk pX)).left
  let F := absoluteFrobenius X p (isInCharacteristic_of_hom pX p hS)
  refine le_antisymm ?_
    (compositumFrobenius_le_fieldRange_residueFieldMap_relativeFrobenius pX p hS x)
  let φ : K →+* C := (F.residueFieldMap x).hom.codRestrict C.toSubring fun a =>
    Subfield.subset_closure (Or.inr ⟨a, absoluteFrobenius_residueFieldMap_apply X p _ x a⟩)
  let ψ : S.residueField (pX x) →+* C :=
    (pX.residueFieldMap x).hom.codRestrict C.toSubring (by
      intro a
      have ha : (pX.residueFieldMap x).hom a ∈ (pX.residueFieldMap x).hom.range := ⟨a, rfl⟩
      rw [range_residueFieldMap_eq_range_evaluation] at ha
      exact Subfield.subset_closure (Or.inl ha))
  have hw : (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecResidueField x) ≫ pX =
      (Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecResidueField (pX x)) ≫
        absoluteFrobenius S p hS := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, Category.assoc,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext a
    change (F.residueFieldMap x) (pX.residueFieldMap x a) =
      pX.residueFieldMap x ((absoluteFrobenius S p hS).residueFieldMap (pX x) a)
    rw [absoluteFrobenius_residueFieldMap_apply, absoluteFrobenius_residueFieldMap_apply,
      map_pow]
  let q : Spec (.of C) ⟶ pullback pX (absoluteFrobenius S p hS) :=
    pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecResidueField x)
      (Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecResidueField (pX x)) hw
  have hfst : r ≫ pullback.fst pX (absoluteFrobenius S p hS) = F :=
    relativeFrobenius_fst S p hS (Over.mk pX)
  have hsnd : r ≫ pullback.snd pX (absoluteFrobenius S p hS) = pX :=
    relativeFrobenius_snd S p hS (Over.mk pX)
  have hliftfst : q ≫ pullback.fst pX (absoluteFrobenius S p hS) =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecResidueField x :=
    pullback.lift_fst _ _ _
  have hliftsnd : q ≫ pullback.snd pX (absoluteFrobenius S p hS) =
      Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecResidueField (pX x) :=
    pullback.lift_snd _ _ _
  have hq : Spec.map (CommRingCat.ofHom C.subtype) ≫ q =
      Spec.map (r.residueFieldMap x) ≫
        (pullback pX (absoluteFrobenius S p hS)).fromSpecResidueField (r x) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    refine pullback.hom_ext ?_ ?_ <;>
    · simp only [Category.assoc, hfst, hsnd, hliftfst, hliftsnd, ← Spec.map_comp_assoc]
      first
      | exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField F x
      | exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField pX x
  exact fieldRange_le_of_spec_factorization _ _ C q hq

end AlgebraicGeometry

end
