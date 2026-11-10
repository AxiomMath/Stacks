module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginSections
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlaneNotAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Two affine opens with a non-affine intersection

In affine space with the origin doubled, the two canonical affine charts intersect in the
complement of the origin. In dimension two that complement is the punctured affine plane, which
is not affine, and in every dimension greater than one it is not affine either, by base change
along a closed immersion from the two-dimensional case.

So two affine open subschemes of a scheme can have a non-affine intersection: the intersection
of affine opens is affine in an affine scheme, but not in general.

## Main results

* `AlgebraicGeometry.intersection_iso_puncturedAffinePlane`: in dimension two the overlap of the
  two charts is the punctured affine plane.
* `AlgebraicGeometry.not_isAffineOpen_chartIntersection`: in dimension greater than one the two
  charts have a non-affine intersection.
* `AlgebraicGeometry.exists_affineOpens_nonaffine_inf`: a scheme with two affine opens whose
  intersection is not affine.

## Implementation notes

The chart opens are the open ranges of the two canonical gluing maps. The final example is
stated over the field with two elements, lifted to the ambient universe.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

section Helpers

private lemma preimage_chart_opensRange (k : Type u) [Field k] (n : ℕ) :
    chartInclusion k n 0 ⁻¹ᵁ (chartInclusion k n 1).opensRange = puncturedAffineSpace k n := by
  have hij : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 := by decide
  ext x
  change chartInclusion k n 0 x ∈ (chartInclusion k n 1).opensRange ↔
    x ∈ puncturedAffineSpace k n
  rw [Scheme.Hom.mem_opensRange, ← opensRange_glueData_f k n hij]
  refine ⟨fun ⟨y, hy⟩ => ?_, fun ⟨z, hz⟩ => ⟨x, ?_⟩⟩
  · obtain ⟨z, hz, -⟩ :=
      ((doubledZeroGlueData k n).ι_eq_iff (ULift.up 0) (ULift.up 1) x y).mp hy.symm
    exact ⟨z, hz⟩
  · refine (((doubledZeroGlueData k n).ι_eq_iff (ULift.up 0) (ULift.up 1) x x).2
      ⟨z, hz, ?_⟩).symm
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glueData_t_comp_f k n hij]
    exact hz

private lemma chartOverlap_iso_puncturedAffineSpace (k : Type u) [Field k] (n : ℕ) :
    Nonempty (((chartInclusion k n 0).opensRange ⊓
      (chartInclusion k n 1).opensRange).toScheme ≅ (puncturedAffineSpace k n).toScheme) := by
  have himage : chartInclusion k n 0 ''ᵁ puncturedAffineSpace k n =
      (chartInclusion k n 0).opensRange ⊓ (chartInclusion k n 1).opensRange := by
    rw [← preimage_chart_opensRange k n,
      (chartInclusion k n 0).image_preimage_eq_opensRange_inf]
  exact ⟨(Scheme.isoOfEq _ himage).symm ≪≫
    ((chartInclusion k n 0).isoImage (puncturedAffineSpace k n)).symm⟩

private lemma mem_puncturedAffineSpace_iff (k : Type u) [Field k] (n : ℕ)
    (x : Spec (.of (MvPolynomial (Fin n) k))) :
    x ∈ puncturedAffineSpace k n ↔ ∃ i : Fin n, MvPolynomial.X i ∉ x.asIdeal := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, (PrimeSpectrum.mem_basicOpen _ _).mp hi⟩
  · rintro ⟨i, hi⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, (PrimeSpectrum.mem_basicOpen _ _).mpr hi⟩

private lemma puncturedAffineSpace_two_eq_sup (k : Type u) [Field k] :
    puncturedAffineSpace k 2 =
      ((PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k) ⊔
        PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k) :
          TopologicalSpace.Opens (PrimeSpectrum (affinePlaneRing k))) :
            (affinePlane k).Opens) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl)

private lemma coe_puncturedAffineSpace_two (k : Type u) [Field k] :
    ((puncturedAffineSpace k 2 : (affinePlane k).Opens) : Set (affinePlane k))
      = {affinePlaneOrigin k}ᶜ :=
  (congrArg (fun V : (affinePlane k).Opens => (V : Set (affinePlane k)))
    (puncturedAffineSpace_two_eq_sup k)).trans (coe_basicOpen_X_sup k)

private lemma puncturedAffineSpace_two_eq (S : PuncturedAffinePlane.{u}) :
    puncturedAffineSpace S.k 2 = S.U :=
  TopologicalSpace.Opens.ext ((coe_puncturedAffineSpace_two S.k).trans S.carrier_U.symm)

private lemma puncturedAffineSpace_not_isAffine (k : Type u) [Field k] (n : ℕ) (hn : 1 < n) :
    ¬ IsAffine (puncturedAffineSpace k n).toScheme := by
  classical
  let q0 : Fin n := ⟨0, by omega⟩
  let q1 : Fin n := ⟨1, by omega⟩
  let p : Fin n → Fin 2 := fun i => if i.val = 0 then 0 else 1
  have hp0 : p q0 = 0 := by simp [p, q0]
  have hp1 : p q1 = 1 := by simp [p, q1]
  have hp : Function.Surjective p := by
    intro i
    fin_cases i
    · exact ⟨q0, hp0⟩
    · exact ⟨q1, hp1⟩
  let φ : MvPolynomial (Fin n) k →+* MvPolynomial (Fin 2) k := (MvPolynomial.rename p).toRingHom
  let f : Spec (.of (MvPolynomial (Fin 2) k)) ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
    Spec.map (CommRingCat.ofHom φ)
  have hf : IsClosedImmersion f :=
    IsClosedImmersion.spec_of_surjective _ (MvPolynomial.rename_surjective p hp)
  have hpre : f ⁻¹ᵁ puncturedAffineSpace k n = puncturedAffineSpace k 2 := by
    ext x
    change f x ∈ puncturedAffineSpace k n ↔ x ∈ puncturedAffineSpace k 2
    rw [mem_puncturedAffineSpace_iff, mem_puncturedAffineSpace_iff]
    change (∃ i : Fin n, MvPolynomial.rename p (MvPolynomial.X i) ∉ x.asIdeal) ↔ _
    simp only [MvPolynomial.rename_X]
    refine ⟨fun ⟨i, hi⟩ => ⟨p i, hi⟩, fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨j, rfl⟩ := hp i
    exact ⟨j, hi⟩
  intro hWn
  have : IsAffine (puncturedAffineSpace k n).toScheme := hWn
  have : IsClosedImmersion (f ∣_ puncturedAffineSpace k n) := by infer_instance
  have hW2pre : IsAffine (f ⁻¹ᵁ puncturedAffineSpace k n).toScheme :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (f ∣_ puncturedAffineSpace k n)).1
  have hW2 : IsAffine (puncturedAffineSpace k 2).toScheme :=
    (IsAffine.iff_of_isIso (Scheme.isoOfEq _ hpre).hom).mp hW2pre
  exact not_isAffine_puncturedScheme
    { k := k, U := puncturedAffineSpace k 2, carrier_U := coe_puncturedAffineSpace_two k } hW2

end Helpers

/-- In dimension two, the overlap of the two affine charts of the doubled-origin scheme is the
punctured affine plane. -/
@[stacks 01JD "non_affine_intersection"]
theorem intersection_iso_puncturedAffinePlane (S : PuncturedAffinePlane.{u}) :
    Nonempty (((chartInclusion S.k 2 0).opensRange ⊓
      (chartInclusion S.k 2 1).opensRange).toScheme ≅ S.puncturedScheme) := by
  obtain ⟨e⟩ := chartOverlap_iso_puncturedAffineSpace S.k 2
  exact ⟨e ≪≫ Scheme.isoOfEq _ (puncturedAffineSpace_two_eq S)⟩

/-- For dimension greater than one, the two affine charts of affine space with doubled origin have
a non-affine intersection. -/
@[stacks 01JD "non_affine_intersection"]
theorem not_isAffineOpen_chartIntersection (k : Type u) [Field k] (n : ℕ)
    (hn : 1 < n) :
    ¬ IsAffineOpen ((chartInclusion k n 0).opensRange ⊓
      (chartInclusion k n 1).opensRange) := by
  intro h
  obtain ⟨e⟩ := chartOverlap_iso_puncturedAffineSpace k n
  have hP : IsAffine (puncturedAffineSpace k n).toScheme :=
    (IsAffine.iff_of_isIso e.hom).mp h
  exact puncturedAffineSpace_not_isAffine k n hn hP

/-- The intersection of two affine opens in a scheme need not be affine. -/
@[stacks 01JD "non_affine_intersection"]
theorem exists_affineOpens_nonaffine_inf :
    ∃ (X : Scheme.{u}) (U V : X.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ ¬ IsAffineOpen (U ⊓ V) := by
  let k : Type u := ULift.{u} (ZMod 2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Field k := ULift.field
  exact ⟨affineSpaceWithDoubledZero k 2,
    (chartInclusion k 2 0).opensRange, (chartInclusion k 2 1).opensRange,
    isAffineOpen_opensRange _, isAffineOpen_opensRange _,
    not_isAffineOpen_chartIntersection k 2 (by omega)⟩

end AlgebraicGeometry

end
