module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DegreeZeroRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionDegreeOne

/-!
# Tag 0A58 for `Z/ℓ` on a smooth curve, `ℓ` invertible

Let `C` be a smooth curve over an algebraically closed field `k`, `ℓ` a prime invertible in `k`
and `k'/k` an extension of algebraically closed fields. Then
`H^q(C, Z/ℓ) ⟶ H^q(C_{k'}, Z/ℓ)` is bijective for every `q`. The source's argument (proof of
Tag 0A5B, Case I) is that the genus `g` and the number of punctures `r` do not change when
passing from `k` to `k'`. In detail:

* in degree zero the comparison is bijective for every sheaf (Tag 0A3I,
  `bijective_etaleCohomologyRestrictionMap_zero_of_isSepClosed`);
* the comparison is injective in every degree (Tag 03Q6 and the Nullstellensatz,
  `injective_scalarExtension_of_fg`);
* `C_{k'}` is a smooth curve over `k'` again, projective if `C` is, with the same genus
  (Tag 0BY9), and if `C` is affine with smooth projective compactification `C̄` (Tag 0H1F) then
  `C_{k'} ⊆ C̄_{k'}` is one with the same number of punctures;
* so Tag 03RQ, resp. Tag 03RR, gives the two groups the same finite order in degrees one and two,
  and both vanish above.

The computations of Tags 03RQ and 03RR enter as the hypotheses `hcardP`, `hcardA`, `hvanP` and
`hvanA`, quantified over all algebraically closed fields (they are applied over `k` and over
`k'`); Tag 03Q6 enters through `h03Q6`, its elementwise consequence for the finitely generated
subalgebras of `k'`; Tag 0A27 is `hAP`.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.bijective_scalarExtension_constantZModAb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The exponential characteristic is unchanged by a field extension. -/
theorem ringExpChar_eq_of_algebra (k' : Type u) [Field k'] [Algebra k k'] :
    ringExpChar k' = ringExpChar k := by
  have : ExpChar k' (ringExpChar k) :=
    expChar_of_injective_algebraMap (algebraMap k k').injective _
  exact ringExpChar.eq k' _

/-- **Tag 0A58 for `Z/ℓ` on a smooth curve, `ℓ` invertible in `k`.** See the module docstring
for the hypotheses. -/
theorem bijective_scalarExtension_constantZModAb {ℓ : ℕ}
    (hAP : ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD],
      IsAffine D ∨ IsProjectiveMorphism pD)
    (hvanA : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
      [IsCurve K pD] [Smooth pD] [IsAffine D], ℓ ≠ ringExpChar K → ∀ q : ℕ, 2 ≤ q →
        Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hvanP : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
      [IsCurve K pD] [Smooth pD] [IsProjectiveVariety K pD], ℓ ≠ ringExpChar K → ∀ q : ℕ,
        3 ≤ q →
        Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hcardP : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
      [IsCurve K pD] [Smooth pD] [IsProjectiveVariety K pD], ℓ ≠ ringExpChar K →
        Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) 1) =
          ℓ ^ (2 * genus pD) ∧
        Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) 2) = ℓ)
    (hcardA : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
      [IsCurve K pD] [Smooth pD] [IsAffine D] (Dbar : Scheme.{u}) (pbar : Dbar ⟶ Spec (.of K))
      [IsCurve K pbar] [Smooth pbar] [IsProjectiveVariety K pbar] (j : D ⟶ Dbar)
      [IsOpenImmersion j], j ≫ pbar = pD → ℓ ≠ ringExpChar K →
        Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) 1) =
          ℓ ^ (2 * genus pbar + Nat.card ↥(Set.range j.base)ᶜ - 1))
    (hℓ : ℓ.Prime) (hℓp : ℓ ≠ ringExpChar k)
    (C : Scheme.{u}) (pC : C ⟶ Spec (.of k)) [IsCurve k pC] [Smooth pC]
    (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' pC).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (h03Q6 : ∀ (q : ℕ) (x : Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb C ℓ) q),
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' pC)
        (StrongTorsionCurveAssertions.constantZModAb C ℓ) q x = 0 →
      ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (pullback.fst pC (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (StrongTorsionCurveAssertions.constantZModAb C ℓ) q x = 0)
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (scalarExtensionFst k k' pC) (StrongTorsionCurveAssertions.constantZModAb C ℓ) q) := by
  have hp' : ℓ ≠ ringExpChar k' := by rwa [ringExpChar_eq_of_algebra (k := k) k']
  set F := StrongTorsionCurveAssertions.constantZModAb C ℓ
  set C' := scalarExtension k k' pC
  -- the target of the comparison is the cohomology of `Z/ℓ` on `C_{k'}`
  let e : (etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' pC)).obj F ≅
      StrongTorsionCurveAssertions.constantZModAb C' ℓ :=
    (etaleAbelianInverseImageConstantIso.{u, u + 1} (scalarExtensionFst k k' pC)).app _
  have hcardT : ∀ q, Nat.card (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' pC)).obj F) q) =
      Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb C' ℓ) q) :=
    fun q => Nat.card_congr (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr e q).toEquiv
  have hvan : Subsingleton (Sheaf.H.{u + 1} F q) → Subsingleton (Sheaf.H.{u + 1}
      (StrongTorsionCurveAssertions.constantZModAb C' ℓ) q) → Function.Bijective
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' pC) F q) := fun h h' => by
    have := Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target e.symm q h'
    exact TorsionCurveAssertions.bijective_of_subsingleton _
  have hinj := injective_scalarExtension_of_fg pC k' F q (h03Q6 q)
  -- equal finite orders give bijectivity
  have hcard : ∀ (n : ℕ), Nat.card (Sheaf.H.{u + 1} F q) = n → n ≠ 0 →
      Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb C' ℓ) q) = n →
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' pC) F q) := fun n h1 hn h2 => by
    have h2' := (hcardT q).trans h2
    have : Finite (Sheaf.H.{u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' pC)).obj F) q) :=
      Nat.finite_of_card_ne_zero (h2'.symm ▸ hn)
    exact hinj.bijective_of_nat_card_le (h1.trans h2'.symm).ge
  have hℓ0 : ∀ m, ℓ ^ m ≠ 0 := fun m => pow_ne_zero _ hℓ.ne_zero
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact bijective_etaleCohomologyRestrictionMap_zero_of_isSepClosed k k' pC F
  rcases hAP C pC with hA | hP
  · -- the affine case
    obtain ⟨-, Y, qY, j, hj, hjq, hcY, hprojY, -, hsmY, -, hbdry⟩ :=
      exists_smooth_isProjectiveMorphism_compactification_of_perfectField k pC
        (isRegular_of_smooth_over_field pC)
    have := hj
    have := hcY
    have := hsmY
    have : IsProjectiveVariety k qY := ⟨hprojY⟩
    have : IsProper qY := isProper_of_isProjectiveMorphism qY hprojY
    subst hjq
    have : IsCurve k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') (j ≫ qY)) :=
      isCurve_scalarExtensionToSpec k' _
    have : IsCurve k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') qY) :=
      isCurve_scalarExtensionToSpec k' _
    have : IsProjectiveVariety k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') qY) :=
      isProjectiveVariety_scalarExtension k' qY
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · obtain rfl : q = 1 := by omega
      refine hcard _ (hcardA k C (j ≫ qY) Y qY j rfl hℓp) (hℓ0 _) ?_
      rw [hcardA k' C' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') (j ≫ qY)) _
        (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') qY)
        (scalarExtensionOpenImmersion k' qY j) (scalarExtensionOpenImmersion_snd k' qY j) hp',
        genus_scalarExtension, natCard_compl_range_scalarExtensionOpenImmersion k' qY j hbdry]
    · exact hvan (hvanA k C (j ≫ qY) hℓp q hq2)
        (hvanA k' C' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') (j ≫ qY)) hp' q hq2)
  · -- the projective case
    have : IsProjectiveVariety k pC := ⟨hP⟩
    have : IsProper pC := isProper_of_isProjectiveMorphism pC hP
    have : IsCurve k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') pC) :=
      isCurve_scalarExtensionToSpec k' _
    have : IsProjectiveVariety k' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') pC) :=
      isProjectiveVariety_scalarExtension k' pC
    have hC := hcardP k C pC hℓp
    have hC' := hcardP k' C' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') pC) hp'
    rw [genus_scalarExtension] at hC'
    rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · rcases (show q = 1 ∨ q = 2 by omega) with rfl | rfl
      · exact hcard _ hC.1 (hℓ0 _) hC'.1
      · exact hcard _ hC.2 hℓ.ne_zero hC'.2
    · exact hvan (hvanP k C pC hℓp q hq3)
        (hvanP k' C' (Stacks.ArtinSchreier.scalarExtensionStructure (k' := k') pC) hp' q hq3)

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
