module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Chart
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpacePoincareLemma
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksCore.Tactic.StacksAttribute

/-!
# Local properties of a cyclic cover

Let `p : X ⟶ Z_S` be the cyclic cover `Spec_{Z_S}(Sym(L_S)/(φ - c))` of
`StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction`. Over the affine opens
`U_S` of `Z_S` with `U` an affine open of `Z` on which `L` is trivial, `p` is
`Spec (A ⊗_k S)[x]/(xⁿ - c f) ⟶ Spec (A ⊗_k S)`
(`Stacks.CyclicCover.coverMapArrowIso`). This file reads off properties of `p` local on the
target from that description.

## Main results

* `Stacks.CyclicCover.coverMap_of_forall`: a property of morphisms local at the target holds for
  `p` once it holds for every chart map `Spec (A ⊗_k S)[x]/(xⁿ - c f) ⟶ Spec (A ⊗_k S)`.
* `Stacks.CyclicCover.isFinite_coverMap`, `Stacks.CyclicCover.flat_coverMap`: **`p` is finite
  and flat** for `n ≥ 1`.
* `Stacks.CyclicCover.etale_coverMap`: **`p` is étale** if `n` and `c` are invertible.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace Stacks.CyclicCover

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (S : Type u) [CommRing S] [Algebra k S] (c : S)

/-- The affine opens of `Z` on which the sections of `L` are free of rank one. -/
abbrev TrivialOpen (L : Z.Modules) : Type u :=
  {U : Z.affineOpens // Nonempty (Module.Basis PUnit.{u + 1} Γ(Z, U.1) Γ(L, U.1))}

/-- The base changes `U_S` to `Z_S` of the affine opens `U` of `Z` on which `L` is trivial
cover `Z_S`. -/
theorem iSup_baseChangeOpen_trivialOpen :
    ⨆ U : TrivialOpen L, baseChangeOpen f S U.1.1 = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨U, ⟨hU, -, hb⟩, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 (situation f L).isBasis_chartOpens
    (show baseChangeFst f S z ∈ (⊤ : Z.Opens) from trivial)
  exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hb⟩, hxU⟩

/-- **A property of morphisms local at the target holds for `p` once it holds for the chart
maps** `Spec (A ⊗_k S)[x]/(xⁿ - c f) ⟶ Spec (A ⊗_k S)`. -/
theorem coverMap_of_forall (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ (U : Z.affineOpens) (b : Module.Basis PUnit.{u + 1} Γ(Z, U.1) Γ(L, U.1)),
      letI := (sectionsStructure f U.1).hom.toAlgebra
      P (Spec.map (CommRingCat.ofHom
        (algebraMap (Γ(Z, U.1) ⊗[k] S) (chartRing k n (chartCoeff f φ U b) c))))) :
    P (coverMap f φ S c) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top _
    (iSup_baseChangeOpen_trivialOpen f (L := L) S)).2 fun U => ?_
  obtain ⟨b⟩ := U.2
  exact (P.arrow_mk_iso_iff (coverMapArrowIso f φ U.1 b S c)).2 (h U.1 b)

/-- **`p : X ⟶ Z_S` is finite** for `n ≥ 1`. -/
theorem isFinite_coverMap (hn : n ≠ 0) : IsFinite (coverMap f φ S c) := by
  have := Stacks.Morphisms.isFinite_isZariskiLocalAtTarget.{u}
  refine coverMap_of_forall f φ S c @IsFinite fun U b => ?_
  let := (sectionsStructure f U.1).hom.toAlgebra
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  exact finite_adjoinRoot _ hn

/-- **`p : X ⟶ Z_S` is flat** for `n ≥ 1`: locally it is free of rank `n`. -/
theorem flat_coverMap (hn : n ≠ 0) : Flat (coverMap f φ S c) := by
  have : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)
  refine coverMap_of_forall f φ S c @Flat fun U b => ?_
  let := (sectionsStructure f U.1).hom.toAlgebra
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  have := free_adjoinRoot (Q := Γ(Z, U.1) ⊗[k] S) ((chartCoeff f φ U b) ⊗ₜ[k] c) hn
  infer_instance

/-- **`p : X ⟶ Z_S` is étale** when `n` is invertible in `k` and `c` is invertible in `S`. -/
theorem etale_coverMap (hn : (n : k) ≠ 0) (hc : IsUnit c) : Etale (coverMap f φ S c) := by
  have : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine coverMap_of_forall f φ S c @Etale fun U b => ?_
  let := (sectionsStructure f U.1).hom.toAlgebra
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
  refine etale_adjoinRoot _ hn0 ?_ ?_
  · simpa using (IsUnit.mk0 _ hn).map (algebraMap k (Γ(Z, U.1) ⊗[k] S))
  · have hf : IsUnit (chartCoeff f φ U b) :=
      IsUnit.of_mul_eq_one_right _ (rootCoeff_mul_chartCoeff f φ U b)
    have h : (chartCoeff f φ U b ⊗ₜ[k] c : Γ(Z, U.1) ⊗[k] S) =
        Algebra.TensorProduct.includeLeftRingHom (chartCoeff f φ U b) *
          Algebra.TensorProduct.includeRight (R := k) (A := Γ(Z, U.1)) c := by
      simp
    rw [h]
    exact (hf.map _).mul (hc.map _)

/-- **`p : X ⟶ Z_S` is surjective** for `n ≥ 1`: locally it is `Spec` of a free algebra of rank
`n`, which is faithfully flat. -/
theorem surjective_coverMap (hn : n ≠ 0) : Surjective (coverMap f φ S c) := by
  refine coverMap_of_forall f φ S c @Surjective fun U b => ?_
  let := (sectionsStructure f U.1).hom.toAlgebra
  set Q := Γ(Z, U.1) ⊗[k] S
  have := free_adjoinRoot (Q := Q) ((chartCoeff f φ U b) ⊗ₜ[k] c) hn
  refine ⟨fun x => ?_⟩
  by_cases hQ : Nontrivial Q
  · have : Nontrivial (chartRing k n (chartCoeff f φ U b) c) := by
      have := finrank_adjoinRoot (Q := Q) ((chartCoeff f φ U b) ⊗ₜ[k] c) hn
      exact Module.nontrivial_of_finrank_pos (R := Q) (by rw [this]; exact Nat.pos_of_ne_zero hn)
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (B := chartRing k n (chartCoeff f φ U b) c) x
  · rw [not_nontrivial_iff_subsingleton] at hQ
    exact ((x : PrimeSpectrum Q).isPrime.ne_top (Subsingleton.elim _ _)).elim

end Stacks.CyclicCover

end
