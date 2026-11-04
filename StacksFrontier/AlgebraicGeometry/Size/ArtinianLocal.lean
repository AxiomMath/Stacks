module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Spectra of Artinian local rings in a bounded site

An Artinian local ring has finite length over itself, every simple subquotient being its residue
field, so its cardinality is at most `(max ℵ₀ #κ)^ℵ₀` for `κ` its residue field. Consequently the
spectrum of an Artinian local ring whose residue field is no larger than some scheme of a big
fppf site `B` lies in `B`.

## Main results

* `AlgebraicGeometry.Scheme.mk_residueField_le_size`: the residue fields of a scheme are no
  larger than its size.
* `AlgebraicGeometry.BigFppfSite.contains_spec_of_isArtinianRing`: the containment.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry

/-- The residue fields of a scheme are no larger than its size. -/
theorem Scheme.mk_residueField_le_size (Z : Scheme.{u}) (z : Z) :
    Cardinal.mk (Z.residueField z) ≤ Z.size :=
  (Cardinal.mk_le_of_surjective (IsLocalRing.residue_surjective
    (R := Z.presheaf.stalk z))).trans (Z.mk_stalk_le_size z)

/-- **The spectrum of an Artinian local ring with a small residue field lies in the site.** If
the residue field of an Artinian local ring `D` is no larger than a scheme of a big fppf site
`B`, then `Spec D` lies in `B`. -/
theorem BigFppfSite.contains_spec_of_isArtinianRing (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (D : CommRingCat.{u}) [IsLocalRing D] [IsArtinianRing D]
    (h : Cardinal.mk (IsLocalRing.ResidueField D) ≤ X.size) : B.Contains (Spec D) := by
  apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hX
  have hquot : ∀ {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]
      (N : Submodule R M), Cardinal.mk M ≤ Cardinal.mk (M ⧸ N) * Cardinal.mk N := by
    intro R _ M _ _ N
    rw [← lift_id #(M ⧸ N), ← lift_id #N, ← mk_prod]
    exact (mk_congr (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := N.toAddSubgroup))).le
  have hlenb : ∀ {M : Type u} [AddCommGroup M] [Module D M], IsFiniteLength D M →
      Cardinal.mk M ≤ (max ℵ₀ (Cardinal.mk (IsLocalRing.ResidueField D))) ^ ℵ₀ := by
    intro M _ _ hM
    let κ := max ℵ₀ (Cardinal.mk (IsLocalRing.ResidueField D))
    have hκ0 : κ ≠ 0 := (Cardinal.aleph0_pos.trans_le (le_max_left _ _)).ne'
    induction hM with
    | @of_subsingleton M _ _ hsub =>
        exact (Cardinal.le_one_iff_subsingleton.mpr hsub).trans
          (Cardinal.one_le_iff_ne_zero.mpr (Cardinal.power_ne_zero ℵ₀ hκ0))
    | @of_simple_quotient M _ _ N _ _ ih =>
        obtain ⟨J, hJ, ⟨e⟩⟩ :=
          isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule D (M ⧸ N)›
        obtain rfl := IsLocalRing.eq_maximalIdeal hJ
        calc
          Cardinal.mk M ≤ Cardinal.mk (M ⧸ N) * Cardinal.mk N := hquot N
          _ ≤ κ * κ ^ ℵ₀ := mul_le_mul ((Cardinal.mk_congr e.toEquiv).trans_le (le_max_right _ _))
            ih (by positivity) (by positivity)
          _ = κ ^ 1 * κ ^ ℵ₀ := by simp
          _ = κ ^ (1 + ℵ₀) := (Cardinal.power_add κ 1 ℵ₀).symm
          _ = κ ^ ℵ₀ := congrArg (fun α : Cardinal => κ ^ α) (Cardinal.nat_add_aleph0 (1 : ℕ))
  exact (hlenb ((isArtinianRing_iff_isFiniteLength D).mp inferInstance)).trans
    (Cardinal.power_le_power_right (max_le X.aleph0_le_size h))

/-- The residue field of a local ring has the cardinality of the residue field of its spectrum
at the closed point. -/
theorem Scheme.mk_residueField_closedPoint (D : CommRingCat.{u}) [IsLocalRing D] :
    Cardinal.mk ((Spec D).residueField (IsLocalRing.closedPoint D)) =
      Cardinal.mk (IsLocalRing.ResidueField D) := by
  let e : D ≃+* Localization.AtPrime (IsLocalRing.maximalIdeal D) :=
    (IsLocalization.atUnits D (IsLocalRing.maximalIdeal D).primeCompl
      (S := Localization.AtPrime (IsLocalRing.maximalIdeal D))
      (fun x hx => by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using! hx)).toRingEquiv
  refine (Cardinal.mk_congr (Spec.residueFieldIso D
    (IsLocalRing.closedPoint D)).commRingCatIsoToRingEquiv.toEquiv).trans ?_
  exact (Cardinal.mk_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

/-- A version of `AlgebraicGeometry.BigFppfSite.contains_spec_of_isArtinianRing` bounding the
residue field of the spectrum at its closed point. -/
theorem BigFppfSite.contains_spec_of_isArtinianRing' (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (D : CommRingCat.{u}) [IsLocalRing D] [IsArtinianRing D]
    (h : Cardinal.mk ((Spec D).residueField (IsLocalRing.closedPoint D)) ≤ X.size) :
    B.Contains (Spec D) :=
  B.contains_spec_of_isArtinianRing hX D (Scheme.mk_residueField_closedPoint D ▸ h)

end AlgebraicGeometry
