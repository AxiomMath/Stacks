module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantSmoothCurve
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionConstant
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantSiteTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientsUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishingUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveGmVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.RootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityCurvesFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveStructureModuleBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionCurve
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionDegreeOne
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperScalarExtension
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# The computations of Tag 0A5B from the cohomology of curves

`Stacks.EtaleCohomology.TorsionCurveAssertions.constantZModAb_of_smoothCurve_computations` proves
the eight assertions for `Z/ℓ` on a smooth curve from seven computations. This file supplies them
from the cohomology of curves:

* the dichotomy affine / projective is Tag 0A27
  (`AlgebraicGeometry.isAffine_or_isProjectiveMorphism`);
* for `ℓ` the characteristic, vanishing in degrees `≥ 2` is Tag 0A3N and finiteness for a proper
  curve is Tag 0A3P (1);
* for `ℓ` invertible, the groups and their orders are Tag 03RQ for a projective curve
  (`AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`) and
  Tag 03RR for an affine one
  (`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`), over
  every algebraically closed field, which the comparison of orders of Tag 0A58 needs;
* a smooth affine curve has a smooth projective compactification (Tag 0H1F).

The remaining inputs are carried as the hypotheses of
`Stacks.EtaleCohomology.TorsionCurveAssertions.constantZModAb_of_smoothCurve_of_inputs`, each in
the shape of the statement it stands for: the elementwise form of Tag 03Q6 for a scalar extension
(`hQ6`). Tag 0A3P (2) is
`Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod`.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.constantZModAb_of_smoothCurve_of_inputs`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_inputs`: Tag 03SC from those inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.TorsionCurveAssertions

section Field

variable {K : Type u} [Field K]

/-- A prime equal to the exponential characteristic is the characteristic. -/
theorem charP_of_eq_ringExpChar {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ = ringExpChar K) : CharP K ℓ := by
  have : ExpChar K ℓ := h ▸ ringExpChar.expChar K
  cases this with
  | zero => exact absurd hℓ Nat.not_prime_one
  | prime _ => infer_instance

/-- A prime different from the exponential characteristic is invertible. -/
theorem isUnit_natCast_of_ne_ringExpChar {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ≠ ringExpChar K) :
    IsUnit (ℓ : K) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have : CharP K ℓ := (CharP.charP_iff_prime_eq_zero hℓ).mpr h0
  have : ExpChar K ℓ := ExpChar.prime hℓ
  exact h (ringExpChar.eq K ℓ).symm

/-- The `n`-th roots of unity of a ring isomorphic to a domain form a finite set. -/
theorem finite_rootsOfUnitySubtype {R : Type*} [CommRing R] {S : Type*} [CommRing S] [IsDomain S]
    (e : R ≃+* S) (n : ℕ) [NeZero n] : Finite {f : Rˣ // f ^ n = 1} :=
  Finite.of_injective (fun f => (⟨Units.map e.toRingHom.toMonoidHom f.1, (mem_rootsOfUnity n _).mpr
      (by rw [← map_pow, f.2, map_one])⟩ : rootsOfUnity n S))
    fun a b h => Subtype.ext (Units.ext (e.injective (congrArg (fun g => ((g.1 : Sˣ) : S)) h)))

end Field

section Curves

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **Tag 0A3N for `Z/ℓ` on a curve, `ℓ` the characteristic.** -/
@[sga "4 XIV 1.11" "special case"]
theorem subsingleton_constantZModAb_of_eq_ringExpChar {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hlp : ℓ = ringExpChar K) (D : Scheme.{u}) (pD : D ⟶ Spec (.of K)) [IsCurve K pD] (q : ℕ)
    (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q) := by
  have := charP_of_eq_ringExpChar hℓ hlp
  exact Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAlgClosed_unconditional
    hℓ.pos K pD 1
    (by rw [IsCurve.topologicalKrullDim_eq_one (k := K) (f := pD)]; rfl) q hq

/-- **Tag 0A3P (1) for `Z/ℓ` on a proper curve, `ℓ` the characteristic.** -/
@[sga "4 XIV 1.11" "special case"]
theorem finite_constantZModAb_of_eq_ringExpChar {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hlp : ℓ = ringExpChar K) (D : Scheme.{u}) (pD : D ⟶ Spec (.of K)) [IsProper pD] (q : ℕ) :
    Finite (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q) := by
  have := charP_of_eq_ringExpChar hℓ hlp
  exact Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper' hℓ.pos K pD q

/-- **Vanishing in degrees `≥ 3` on a smooth projective curve** (Tag 03RQ with Tag 03RM, or
Tag 0A3N when `ℓ` is the characteristic). -/
theorem subsingleton_constantZModAb_projective {ℓ : ℕ} (hℓ : ℓ.Prime) (D : Scheme.{u})
    (pD : D ⟶ Spec (.of K)) [IsCurve K pD] [Smooth pD] [IsProjectiveVariety K pD] (q : ℕ)
    (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q) := by
  by_cases hlp : ℓ = ringExpChar K
  · exact subsingleton_constantZModAb_of_eq_ringExpChar hℓ hlp D pD q (by omega)
  · let B := BigEtaleSite.containing D
    have hD : B.Contains D := BigEtaleSite.contains_containing D
    let : HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u}) :=
      HasExt.standard _
    exact ConstantTransport.subsingleton_sheafH_constantZModAb_of_boundedSite B D hD ℓ q
      (subsingleton_etaleH_constantZMod_of_three_le K D pD B hD ℓ
        (isUnit_natCast_of_ne_ringExpChar hℓ hlp)
        (fun q' hq' => subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve pD B hD ℓ q' hq') q hq)

/-- A smooth curve over an algebraically closed field has a smooth projective
compactification (Tag 0H1F). -/
theorem exists_smooth_projective_compactification (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
    [IsCurve K pD] [Smooth pD] :
    ∃ (Dbar : Scheme.{u}) (pbar : Dbar ⟶ Spec (.of K)) (j : D ⟶ Dbar),
      IsOpenImmersion j ∧ j ≫ pbar = pD ∧ IsCurve K pbar ∧ Smooth pbar ∧
        IsProjectiveVariety K pbar := by
  obtain ⟨-, Y, qY, j, hj, hjq, hcY, hpY, -, hsY, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField K pD
      (isRegular_of_smooth_over_field pD)
  have := hcY
  exact ⟨Y, qY, j, hj, hjq, hcY, hsY, (isProjectiveVariety_iff K qY).mpr ⟨inferInstance, hpY⟩⟩

end Curves

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Tag 0A5B on a smooth curve from the cohomology of curves.** The eight assertions for `Z/ℓ`
on a smooth curve over `k`, from the elementwise form of Tag 03Q6 for scalar extensions
(`hQ6`). -/
theorem constantZModAb_of_smoothCurve_of_inputs
    (hQ6 : ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
      (k' : Type u) [Field k'] [Algebra k k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} F q),
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' f) F q x = 0 →
      ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) F q x = 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (C : Scheme.{u}) (pC : C ⟶ Spec (.of k)) [IsCurve k pC] [Smooth pC] :
    TorsionCurveAssertions pC (StrongTorsionCurveAssertions.constantZModAb C ℓ) := by
  have hRQ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
    [IsCurve K pD] [IsProjectiveVariety K pD] [Smooth pD] (B : BigEtaleSite.{u})
    (hD : B.Contains D) [HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u})]
    (n : ℕ), IsUnit (n : K) →
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B D hD n) 1 ≃+
        (Fin (2 * genus pD) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf B D hD n) 2 ≃+ ZMod n) :=
    fun K _ _ D pD _ _ _ B hD _ n hn =>
    ⟨(etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus K D pD B hD n hn).2.2.2.2.2.1,
      (etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus K D pD B hD n hn).2.2.2.2.2.2.1⟩
  have hRR : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
    [IsCurve K pD] [Smooth pD] [IsAffine D] (B : BigEtaleSite.{u}) (hD : B.Contains D)
    [HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u})] (n : ℕ),
    IsUnit (n : K) → ∀ (Dbar : Scheme.{u}) (pbar : Dbar ⟶ Spec (.of K)) [IsCurve K pbar]
      [Smooth pbar] [IsProjectiveVariety K pbar] (j : D ⟶ Dbar) [IsOpenImmersion j],
      j ≫ pbar = pD →
      Nonempty (Sheaf.H (kummerSmallEtale B D hD n).X₁ 1 ≃+
        (Fin (2 * genus pbar + Nat.card ↥(Set.range j.base)ᶜ - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B D hD n).X₁ q) :=
    fun K _ _ D pD _ _ _ B hD _ n hn Dbar pbar _ _ _ j _ hj =>
    (etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification K D pD B hD n hn pbar j hj
      _ rfl).2
  -- the affine vanishing, over any algebraically closed field
  have hvanA' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u})
      (pD : D ⟶ Spec (.of K)) [IsCurve K pD] [Smooth pD] [IsAffine D] (q : ℕ), 2 ≤ q →
      Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q) := by
    intro K _ _ D pD _ _ _ q hq
    by_cases hlp : ℓ = ringExpChar K
    · exact subsingleton_constantZModAb_of_eq_ringExpChar hℓ hlp D pD q hq
    · let B := BigEtaleSite.containing D
      have hD : B.Contains D := BigEtaleSite.contains_containing D
      let : HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u}) :=
        HasExt.standard _
      have hu := isUnit_natCast_of_ne_ringExpChar hℓ hlp
      obtain ⟨Dbar, pbar, j, hj, hjp, hc, hs, hpv⟩ := exists_smooth_projective_compactification D pD
      have : Subsingleton (Sheaf.H (smallEtaleRootsOfUnitySheaf B D hD ℓ) q) :=
        (hRR K D pD B hD ℓ hu Dbar pbar j hjp).2 q hq
      exact Function.Injective.subsingleton
        (ConstantTransport.sheafHRootsOfUnityEquiv B D hD pD ℓ hℓ.pos hu q).symm.injective
  have hcardP : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
      [IsCurve K pD] [Smooth pD] [IsProjectiveVariety K pD], ℓ ≠ ringExpChar K →
        Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) 1) =
          ℓ ^ (2 * genus pD) ∧
        Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) 2) = ℓ := by
    intro K _ _ D pD _ _ _ hlp
    let B := BigEtaleSite.containing D
    have hD : B.Contains D := BigEtaleSite.contains_containing D
    let : HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u}) :=
      HasExt.standard _
    obtain ⟨h1, h2⟩ := hRQ K D pD B hD ℓ (isUnit_natCast_of_ne_ringExpChar hℓ hlp)
    refine ⟨?_, ?_⟩
    · rw [ConstantTransport.natCard_sheafH_constantZModAb_of_addEquiv B D hD ℓ 1 h1]
      simp [Nat.card_fun, Nat.card_zmod]
    · rw [ConstantTransport.natCard_sheafH_constantZModAb_of_addEquiv B D hD ℓ 2 h2]
      simp [Nat.card_zmod]
  have hcardA : ∀ (K : Type u) [Field K] [IsAlgClosed K] (D : Scheme.{u}) (pD : D ⟶ Spec (.of K))
      [IsCurve K pD] [Smooth pD] [IsAffine D] (Dbar : Scheme.{u}) (pbar : Dbar ⟶ Spec (.of K))
      [IsCurve K pbar] [Smooth pbar] [IsProjectiveVariety K pbar] (j : D ⟶ Dbar)
      [IsOpenImmersion j], j ≫ pbar = pD → ℓ ≠ ringExpChar K →
        Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) 1) =
          ℓ ^ (2 * genus pbar + Nat.card ↥(Set.range j.base)ᶜ - 1) := by
    intro K _ _ D pD _ _ _ Dbar pbar _ _ _ j _ hjp hlp
    let B := BigEtaleSite.containing D
    have hD : B.Contains D := BigEtaleSite.contains_containing D
    let : HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u}) :=
      HasExt.standard _
    have hu := isUnit_natCast_of_ne_ringExpChar hℓ hlp
    obtain ⟨e⟩ := (hRR K D pD B hD ℓ hu Dbar pbar j hjp).1
    have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rw [Nat.card_congr
      ((ConstantTransport.sheafHRootsOfUnityEquiv B D hD pD ℓ hℓ.pos hu 1).symm.trans e.toEquiv),
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  refine constantZModAb_of_smoothCurve_computations hℓ
    (fun D pD _ => isAffine_or_isProjectiveMorphism k pD)
    (fun D pD _ _ _ q hq => hvanA' k D pD q hq)
    (fun D pD _ _ _ q hq => subsingleton_constantZModAb_projective hℓ D pD q hq)
    (fun hlp D pD _ _ q hq => subsingleton_constantZModAb_of_eq_ringExpChar hℓ hlp D pD q hq)
    (fun D pD _ _ _ q => ?_) (fun hlp D pD _ _ _ q => ?_) (fun D pD _ _ h k' _ _ _ _ q => ?_) C pC
  · -- finiteness on a projective curve
    rcases Nat.lt_or_ge q 3 with hq | hq
    · by_cases hlp : ℓ = ringExpChar k
      · have : IsProper pD := inferInstance
        exact finite_constantZModAb_of_eq_ringExpChar hℓ hlp D pD q
      · let B := BigEtaleSite.containing D
        have hD : B.Contains D := BigEtaleSite.contains_containing D
        let : HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u}) :=
          HasExt.standard _
        have hu := isUnit_natCast_of_ne_ringExpChar hℓ hlp
        have : NeZero ℓ := ⟨hℓ.ne_zero⟩
        have hB : Finite (Sheaf.H (smallEtaleConstantZModSheaf B D hD ℓ) q) := by
          interval_cases q
          · obtain ⟨e⟩ :=
              (etaleCohomology_rootsOfUnity_smoothProjectiveCurve k D pD B hD ℓ hu).2.2.1
            exact Finite.of_equiv _ e.toEquiv.symm
          · obtain ⟨e⟩ := (hRQ k D pD B hD ℓ hu).1
            exact Finite.of_equiv _ e.toEquiv.symm
          · obtain ⟨e⟩ := (hRQ k D pD B hD ℓ hu).2
            exact Finite.of_equiv _ e.toEquiv.symm
        exact Finite.of_equiv _ (ConstantTransport.sheafHConstantZModEquiv B D hD ℓ q)
    · have := subsingleton_constantZModAb_projective hℓ D pD q hq
      exact Finite.of_subsingleton
  · -- finiteness on an affine curve, `ℓ` invertible
    rcases Nat.lt_or_ge q 2 with hq | hq
    · let B := BigEtaleSite.containing D
      have hD : B.Contains D := BigEtaleSite.contains_containing D
      let : HasExt.{u + 1} (Sheaf (SmallEtale.topology B D hD) AddCommGrpCat.{u}) :=
        HasExt.standard _
      have hu := isUnit_natCast_of_ne_ringExpChar hℓ hlp
      have : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hB : Finite (Sheaf.H (smallEtaleRootsOfUnitySheaf B D hD ℓ) q) := by
        interval_cases q
        · have : Finite ((rootsOfUnitySections ℓ).obj (Opposite.op (Spec (.of k)))) :=
            finite_rootsOfUnitySubtype
              (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv ℓ
          exact Finite.of_surjective _
            (baseRootsToEtaleH0_bijective_of_isIntegral B k D hD pD ℓ hℓ.pos).2
        · obtain ⟨Dbar, pbar, j, hj, hjp, hc, hs, hpv⟩ :=
            exists_smooth_projective_compactification D pD
          obtain ⟨e⟩ := (hRR k D pD B hD ℓ hu Dbar pbar j hjp).1
          exact Finite.of_equiv _ e.toEquiv.symm
      exact Finite.of_equiv _ (ConstantTransport.sheafHRootsOfUnityEquiv B D hD pD ℓ hℓ.pos hu q)
    · have := hvanA' k D pD q hq
      exact Finite.of_subsingleton
  · -- invariance under extension of the algebraically closed ground field
    by_cases hlp : ℓ = ringExpChar k
    · have hp : IsProper pD := h.resolve_left (not_not.mpr hlp)
      have := charP_of_eq_ringExpChar hℓ hlp
      exact
        Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod k k' pD hℓ.pos q
    · exact bijective_scalarExtension_constantZModAb
        (fun D pD _ => isAffine_or_isProjectiveMorphism _ pD)
        (fun K _ _ D pD _ _ _ _ q hq => hvanA' K D pD q hq)
        (fun K _ _ D pD _ _ _ _ q hq => subsingleton_constantZModAb_projective hℓ D pD q hq)
        hcardP hcardA hℓ hlp D pD k' (fun q x hx => hQ6 pD k' _ q x hx) q

/-- **Tag 03SC from the cohomology of curves.** The eight assertions of Situation 0A52 for every
torsion sheaf on a separated scheme of finite type and dimension at most one over `k`, from the
inputs of `constantZModAb_of_smoothCurve_of_inputs`. -/
theorem of_inputs
    (hQ6 : ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
      (k' : Type u) [Field k'] [Algebra k k']
      [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} F q),
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' f) F q x = 0 →
      ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) F q x = 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F :=
  of_constantZModAb (fun hℓ Yb pY _ _ _ _ h1 h2 =>
    constantZModAb_of_isNormal_of_computations
      (fun hℓ' C pC _ _ => constantZModAb_of_smoothCurve_of_inputs hQ6 hℓ' C pC)
      hℓ Yb pY h1 h2) f hdim F hF

end Stacks.EtaleCohomology.TorsionCurveAssertions

end
