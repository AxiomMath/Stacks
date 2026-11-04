module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantComponents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# The eight assertions for `Z/ℓ` on a smooth curve, clause by clause (Tag 0A5B)

Let `C` be a smooth curve over an algebraically closed field `k` of exponential characteristic
`p`, and `ℓ` a prime. The proof of Stacks Tag 0A5B computes the cohomology of `Z/ℓ` on `C`:

* for `ℓ ≠ p` by Tag 03RQ (projective case) and Tag 03RR (affine case), together with the
  invariance of the groups under extension of the algebraically closed ground field (Tag 0A58);
* for `ℓ = p` by Tag 0A3N (vanishing in degrees `≥ 2`) and Tag 0A3P (finiteness and invariance
  for proper curves);

and deduces assertion (8) from the vanishing of `H²` on every open `U ≠ C`, which is affine
(Varieties, Tags 0A24 and 0A27).

This file is the bookkeeping that turns those computations into the eight assertions of
Tag 03SC. The computations enter as the hypotheses of
`TorsionCurveAssertions.constantZModAb_of_smoothCurve_computations`, one for each statement the
source cites, quantified over all smooth curves over `k` (assertion (8) on `C` needs the affine
vanishing on the opens of `C`, which are smooth curves again):

* `hAP`: a curve is affine or H-projective (Tag 0A27);
* `hvanA`: `H^q(C, Z/ℓ) = 0` for `q ≥ 2` on an affine smooth curve (Tag 03RR (3) for `ℓ ≠ p`,
  Tag 0A3N for `ℓ = p`);
* `hvanP`: `H^q(C, Z/ℓ) = 0` for `q ≥ 3` on a projective smooth curve (Tag 03RQ);
* `hvanp`: `H^q(C, Z/p) = 0` for `q ≥ 2` when `ℓ = p` (Tag 0A3N);
* `hfinP`: finiteness on a projective smooth curve (Tag 03RQ, resp. Tag 0A3P (1));
* `hfinA`: finiteness on an affine smooth curve for `ℓ ≠ p` (Tag 03RR (1), (2));
* `hbc`: invariance under extension of algebraically closed fields, for `ℓ ≠ p` (Tag 0A58) and
  for proper curves (Tag 0A3P (2)).

The degenerate clauses are handled here: `Z/ℓ` which is `p'`-power torsion with `ℓ ≠ p'`, or
torsion prime to `p` with `ℓ = p`, is the zero sheaf.

## Main results

* `Stacks.EtaleCohomology.isCurve_ι_of_ne_top`: a nonempty open `U ≠ C` of a curve is a curve
  which is not proper over `k`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.constantZModAb_of_smoothCurve_computations`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- An isomorphism of schemes is a universal homeomorphism. -/
theorem universalHomeomorphism_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    UniversalHomeomorphism f :=
  ⟨fun _ _ _ _ f' h => by
    have : IsIso f' := h.isIso_fst_of_isIso
    exact (TopCat.homeoOfIso (asIso f'.base)).isHomeomorph⟩

variable {k : Type u} [Field k]

/-- **A nonempty open `U ≠ C` of a curve is a curve, and is not proper.** If `U` were proper
over `k`, its inclusion would be proper, so `U` would be clopen in the irreducible `C`. If `U`
had dimension zero it would be finite over `k`, hence proper. -/
theorem isCurve_ι_of_ne_top {C : Scheme.{u}} (pC : C ⟶ Spec (.of k)) [IsCurve k pC]
    (U : C.Opens) (hne : (U : Set C).Nonempty) (htop : U ≠ ⊤) :
    IsCurve k (U.ι ≫ pC) ∧ ¬ IsProper (U.ι ≫ pC) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
  have hnp : ¬ IsProper (U.ι ≫ pC) := by
    intro hp
    have := hp
    have : IsProper U.ι := IsProper.of_comp U.ι pC
    have hcl : IsClosed (U : Set C) := by
      have := U.ι.isClosedMap.isClosed_range
      rwa [U.range_ι] at this
    have : PreconnectedSpace C :=
      ⟨(IrreducibleSpace.isIrreducible_univ C).isPreirreducible.isPreconnected⟩
    rcases isClopen_iff.mp ⟨hcl, U.isOpen⟩ with h | h
    · exact (Set.nonempty_iff_ne_empty.mp hne) h
    · exact htop (SetLike.coe_injective (h.trans Opens.coe_top.symm))
  refine ⟨?_, hnp⟩
  have : Nonempty (U : Scheme.{u}) := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : IsIntegral (U : Scheme.{u}) := isIntegral_of_isOpenImmersion U.ι
  have hle : topologicalKrullDim (U : Scheme.{u}) ≤ 1 :=
    (Topology.IsInducing.topologicalKrullDim_le
      U.ι.isOpenEmbedding.isEmbedding.isInducing).trans
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := pC)).le
  have h0 : 0 ≤ topologicalKrullDim (U : Scheme.{u}) := by
    have : Nonempty (IrreducibleCloseds (U : Scheme.{u})) :=
      ⟨irreducibleClosedsOfPoint (Classical.arbitrary _)⟩
    exact Order.krullDim_nonneg
  have hz : topologicalKrullDim (U : Scheme.{u}) ≠ 0 := fun hz => by
    have : IsFinite (U.ι ≫ pC) := isFinite_of_finiteType_of_dimension_zero k _ hz
    exact hnp inferInstance
  exact { topologicalKrullDim_eq_one :=
    TorsionCurveAssertions.topologicalKrullDim_eq_one_of_ne_zero h0 hle hz }

/-- A curve which is affine and proper over a field does not exist: it would be finite over the
field, hence of dimension zero. -/
theorem not_isAffine_of_isProper {C : Scheme.{u}} (pC : C ⟶ Spec (.of k)) [IsCurve k pC]
    [IsProper pC] [IsAffine C] [IsAlgClosed k] : False := by
  have : IsFinite pC := (IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance,
    inferInstance⟩)
  have hd : DiscreteTopology C := discreteTopology_of_isFinite_over_field k pC
  have h0 : topologicalKrullDim C ≤ 0 :=
    topologicalKrullDim_nonpos_of_isClosed_singleton fun x => isClosed_discrete _
  have h1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := pC)
  rw [h1] at h0
  exact absurd h0 (by decide)

namespace TorsionCurveAssertions

variable [IsAlgClosed k]

/-- A bijection between two subsingleton groups. -/
theorem bijective_of_subsingleton {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Subsingleton A] [Subsingleton B] (φ : A →+ B) : Function.Bijective φ :=
  ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The eight assertions for `Z/ℓ` on a smooth curve, from the computations of its
cohomology** (the bookkeeping of the proof of Tag 0A5B). See the module docstring for the
hypotheses. -/
theorem constantZModAb_of_smoothCurve_computations {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hAP : ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD],
      IsAffine D ∨ IsProjectiveMorphism pD)
    (hvanA : ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD] [Smooth pD] [IsAffine D]
      (q : ℕ), 2 ≤ q →
        Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hvanP : ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD] [Smooth pD]
      [IsProjectiveVariety k pD] (q : ℕ), 3 ≤ q →
        Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hvanp : ℓ = ringExpChar k → ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD]
      [Smooth pD] (q : ℕ), 2 ≤ q →
        Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hfinP : ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD] [Smooth pD]
      [IsProjectiveVariety k pD] (q : ℕ),
        Finite (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hfinA : ℓ ≠ ringExpChar k → ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD]
      [Smooth pD] [IsAffine D] (q : ℕ),
        Finite (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (hbc : ∀ (D : Scheme.{u}) (pD : D ⟶ Spec (.of k)) [IsCurve k pD] [Smooth pD],
      (ℓ ≠ ringExpChar k ∨ IsProper pD) →
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{u + 1}
          (Sheaf (scalarExtension k k' pD).smallEtaleTopology AddCommGrpCat.{u + 1})]
        (q : ℕ), Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
          (scalarExtensionFst k k' pD) (StrongTorsionCurveAssertions.constantZModAb D ℓ) q))
    (C : Scheme.{u}) (pC : C ⟶ Spec (.of k)) [IsCurve k pC] [Smooth pC] :
    TorsionCurveAssertions pC (StrongTorsionCurveAssertions.constantZModAb C ℓ) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsNoetherian C := isNoetherian_of_finiteType pC
  set F := StrongTorsionCurveAssertions.constantZModAb C ℓ
  have hℓF : ℓ • 𝟙 F = 0 := nsmul_id_constantSheaf_zmod.{u + 1} ℓ C.smallEtaleTopology
  -- the degenerate cases: the zero sheaf
  have hzero : IsZero F → ∀ q, Subsingleton (Sheaf.H.{u + 1} F q) := fun hz q =>
    subsingleton_ext_of_isZero_right _ hz q
  have hzero_bij : IsZero F → ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
      [HasExt.{u + 1}
        (Sheaf (scalarExtension k k' pC).smallEtaleTopology AddCommGrpCat.{u + 1})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' pC) F q) := fun hz k' _ _ _ _ q => by
    have := hzero hz q
    have : Subsingleton (Sheaf.H.{u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' pC)).obj F) q) :=
      subsingleton_ext_of_isZero_right _
        ((etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' pC)).map_isZero hz) q
    exact bijective_of_subsingleton _
  have hprime_to : Stacks.Torsion.IsPrimeToCharacteristicTorsion C.smallEtaleTopology
      (ringExpChar k) F → ℓ = ringExpChar k → IsZero F := fun ht hlp => by
    rw [Stacks.Torsion.isPrimeToCharacteristicTorsion_iff_locallyKilledBy] at ht
    exact isZero_of_locallyKilledBy_of_nsmul_id_eq_zero C.smallEtaleTopology
      (fun n hn => hlp ▸ hn.2) ht hℓF
  -- the projective case
  have hAP' : IsAffine C ∨ IsProjectiveVariety k pC := (hAP C pC).imp_right fun h => ⟨h⟩
  have hproper : IsProper pC → IsProjectiveVariety k pC := fun hp =>
    hAP'.resolve_left fun _ => have := hp; (not_isAffine_of_isProper pC).elim
  refine
    { vanishing := fun q hq => ?_
      vanishing_of_isAffine := fun hA q hq => hvanA C pC q hq
      vanishing_of_isPrimePowerTorsion := fun p' hp' hp0 ht q hq => ?_
      finite_of_isPrimeToCharacteristicTorsion := fun _ ht q => ?_
      finite_of_isProper := fun hp _ q => by
        have := hproper hp; exact hfinP C pC q
      bijective_of_isPrimeToCharacteristicTorsion := fun ht k' _ _ _ _ q => ?_
      bijective_of_isProper := fun hp k' _ _ _ _ q => hbc C pC (Or.inr hp) k' q
      surjective_restriction := fun U _ => ?_ }
  · -- (1)
    rcases hAP' with hA | hP
    · exact hvanA C pC q (by omega)
    · exact hvanP C pC q (by omega)
  · -- (3)
    rcases CharP.char_is_prime_or_zero k p' with hpp | hpp
    · by_cases hlp : ℓ = p'
      · have : ExpChar k p' := ExpChar.prime hpp
        exact hvanp (hlp.trans (ringExpChar.eq k p').symm) C pC q (by omega)
      · refine hzero ?_ q
        rw [Stacks.Torsion.isPrimePowerTorsion_iff_locallyKilledBy] at ht
        refine isZero_of_locallyKilledBy_of_nsmul_id_eq_zero C.smallEtaleTopology
          (fun n hn => ?_) ht hℓF
        obtain ⟨r, -, rfl⟩ := hn
        exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hpp hℓ).mpr (Ne.symm hlp))
    · omega
  · -- (4)
    by_cases hlp : ℓ = ringExpChar k
    · have := hzero (hprime_to ht hlp) q; exact Finite.of_subsingleton
    · rcases hAP' with hA | hP
      · exact hfinA hlp C pC q
      · exact hfinP C pC q
  · -- (6)
    by_cases hlp : ℓ = ringExpChar k
    · exact hzero_bij (hprime_to ht hlp) k' q
    · exact hbc C pC (Or.inl hlp) k' q
  · -- (8)
    by_cases htop : U = ⊤
    · subst htop
      have : IsIso (⊤ : C.Opens).ι := (Scheme.topIso C).isIso_hom
      have := universalHomeomorphism_of_isIso (⊤ : C.Opens).ι
      exact (etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, u + 1, u + 1}
        (⊤ : C.Opens).ι F 2).2
    have hsub : Subsingleton (Sheaf.H.{u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} U.ι).obj F) 2) := by
      by_cases hne : (U : Set C).Nonempty
      · obtain ⟨hcurve, hnp⟩ := isCurve_ι_of_ne_top pC U hne htop
        have := hcurve
        have hA : IsAffine (U : Scheme.{u}) := by
          rcases hAP U (U.ι ≫ pC) with hA | hP
          · exact hA
          · exact (hnp (isProper_of_isProjectiveMorphism _ hP)).elim
        have h := hvanA U (U.ι ≫ pC) 2 le_rfl
        exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
          ((etaleRestrictionConstantSheafIso U.ι _).symm ≪≫
            ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} U.ι).app F).symm) 2 h
      · have : IsEmpty (U : Scheme.{u}) := ⟨fun x => hne ⟨x.1, x.2⟩⟩
        exact subsingleton_ext_of_isZero_right _ (isZero_of_isEmpty _) 2
    exact fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- **Tag 0A5B in the form Tag 03SC consumes it** (the hypothesis `h0A5B` of
`TorsionCurveAssertions.of_genericLocalConstancy_of_torsion`), from the computations of the
cohomology of `Z/ℓ` on smooth curves: the components of a normal curve
(`constantZModAb_of_smoothCurve`) and then `constantZModAb_of_smoothCurve_computations`. -/
theorem constantZModAb_of_isNormal_of_computations
    (hcomp : ∀ {ℓ : ℕ}, ℓ.Prime → ∀ (C : Scheme.{u}) (pC : C ⟶ Spec (.of k)) [IsCurve k pC]
      [Smooth pC], TorsionCurveAssertions pC (StrongTorsionCurveAssertions.constantZModAb C ℓ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Yb : Scheme.{u}) (pY : Yb ⟶ Spec (.of k)) [IsSeparated pY]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [HasExt.{u + 1} (Sheaf Yb.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim Yb ≤ 1) (hN : IsNormal Yb) :
    TorsionCurveAssertions pY (StrongTorsionCurveAssertions.constantZModAb Yb ℓ) :=
  constantZModAb_of_smoothCurve hℓ (fun C pC _ _ => hcomp hℓ C pC) pY hdim hN

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
