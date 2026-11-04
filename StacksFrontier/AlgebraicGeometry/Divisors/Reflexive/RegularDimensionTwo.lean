module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.RingTheory.CohenMacaulay.Bridges
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reflexive coherent modules on a regular scheme of dimension at most two

On a regular scheme of dimension at most two a coherent module is reflexive exactly when it is
finite locally free.  The content is local: over a regular local ring of Krull dimension at
most two a finite reflexive module is free, because in dimension at most one it is torsion free
over a discrete valuation ring and in dimension two it has depth two, hence is maximal
Cohen–Macaulay.

## Main results

* `Module.free_of_isReflexive_of_ringKrullDim_le_two`: a finite reflexive module over a regular
  local ring of Krull dimension at most two is free.
* `AlgebraicGeometry.isReflexive_iff_isFiniteLocallyFree_of_isRegular_of_dim_le_two`: the
  characterization of reflexive coherent modules.

## Implementation notes

Finite local freeness is stated over the class carrying the Tag 01C6 attribute,
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, and crossed to the class the Tag 05P2
equivalence is stated over by the bridge lemmas of `Stacks.StalkFreeBridge`.

## References

* [Stacks Project, Tag 0B3N](https://stacks.math.columbia.edu/tag/0B3N)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

/-- A finite reflexive module over a regular local ring of Krull dimension at most two is
free. -/
@[ega "III 7.6.11" "partial"]
theorem Module.free_of_isReflexive_of_ringKrullDim_le_two {R M : Type*} [CommRing R]
    [IsRegularLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsReflexive R M] (hdim : ringKrullDim R ≤ 2) : Module.Free R M := by
  classical
  by_cases hzero : Subsingleton M
  · let : Subsingleton M := hzero
    exact Module.Free.of_subsingleton R M
  have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hzero
  have hRdom : IsDomain R := IsRegularLocalRing.isDomain R
  let : IsDomain R := hRdom
  have htf := (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
    (R := R) (M := M)).1 (inferInstance : Module.IsReflexive R M)
  by_cases hdimOne : ringKrullDim R ≤ 1
  · by_cases hField : IsField R
    · let : Field R := hField.toField
      infer_instance
    · have hdimEq : ringKrullDim R = 1 := by
        have hchain : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
          show (1 : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R)
          rw [Order.one_le_krullDim_iff]
          refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨IsLocalRing.maximalIdeal R,
            (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩, ?_⟩
          show (⊥ : Ideal R) < IsLocalRing.maximalIdeal R
          exact bot_lt_iff_ne_bot.mpr fun h =>
            hField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
        exact le_antisymm hdimOne hchain
      have hRegDim : IsRegularLocalRing R ∧ ringKrullDim R = 1 := ⟨inferInstance, hdimEq⟩
      have hDVRExists : ∃ _ : IsDomain R, IsDiscreteValuationRing R :=
        ((isDiscreteValuationRing_tfae R).out 3 1).mp hRegDim
      obtain ⟨_, hDVR⟩ := hDVRExists
      let : IsDiscreteValuationRing R := hDVR
      let : IsPrincipalIdealRing R := IsDiscreteValuationRing.toIsPrincipalIdealRing
      exact Module.free_iff_isTorsionFree.mpr htf
  · have hlt : (1 : WithBot ℕ∞) < ringKrullDim R := lt_of_not_ge hdimOne
    have hnotBot : ringKrullDim R ≠ ⊥ := by
      intro h
      rw [h] at hlt
      simp at hlt
    lift ringKrullDim R to ℕ∞ using hnotBot with d hd
    have hltNat : (1 : ℕ∞) < d := WithBot.coe_lt_coe.mp (by simpa [hd] using hlt)
    have hleNat : d ≤ 2 := WithBot.coe_le_coe.mp (by simpa [hd] using hdim)
    have hnotTop : d ≠ ⊤ := by
      intro h
      rw [h] at hleNat
      norm_num at hleNat
    lift d to ℕ using hnotTop with n hn
    have hnEq : n = 2 := by
      have : 1 < n := by exact_mod_cast hltNat
      have : n ≤ 2 := by exact_mod_cast hleNat
      omega
    have hdimEq : ringKrullDim R = 2 := by
      rw [← hd, hnEq]
      norm_num
    have hdepthR : (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R := by
      have hmcm : Module.IsMaximalCohenMacaulay R R :=
        (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
          R).2
      change ((Module.depth R (IsLocalRing.maximalIdeal R) R : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim R at hmcm
      rw [hdimEq] at hmcm
      have hcast : (2 : WithBot ℕ∞) ≤
          ((Module.depth R (IsLocalRing.maximalIdeal R) R : ℕ∞) : WithBot ℕ∞) := by rw [hmcm]
      exact WithBot.coe_le_coe.mp hcast
    have hdepthDD : (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R)
        (Module.Dual R (Module.Dual R M)) :=
      (one_le_depth_and_two_le_depth_linearMap (R := R) (M := Module.Dual R M) (N := R)).2
        hdepthR
    have hdepthM : (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := by
      rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal R) (Module.evalEquiv R M)]
      exact hdepthDD
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
    have hdepthUpper : ((Module.depth R (IsLocalRing.maximalIdeal R) M : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim R :=
      (Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hp).trans
        (ringKrullDim_quotient_le p)
    have hdepthEq : Module.depth R (IsLocalRing.maximalIdeal R) M = 2 := by
      refine le_antisymm ?_ hdepthM
      have hupper : ((Module.depth R (IsLocalRing.maximalIdeal R) M : ℕ∞) : WithBot ℕ∞) ≤
          (2 : WithBot ℕ∞) := by simpa [hdimEq] using hdepthUpper
      exact WithBot.coe_le_coe.mp hupper
    have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
      intro htop
      have h := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top htop.ge
        (by simpa using (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge)
      exact top_ne_bot h
    have hdepthSup : Module.depthSup R (IsLocalRing.maximalIdeal R) M =
        Module.depth R (IsLocalRing.maximalIdeal R) M := by
      rw [Module.depth, Module.depthSup_eq_iSup]
      split_ifs with h
      · exact (hmax h).elim
      · rfl
    have hMCM : IsMaxCM R M := by
      apply (isMaxCM_iff_depth_eq_ringKrullDim (R := R) (M := M)).2
      rw [hdepthSup, hdepthEq, hdimEq]
      norm_num
    exact regular_mcm_free R M hMCM

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B3N.** A coherent module on a regular scheme of dimension at most
two is reflexive precisely when it is finite locally free. -/
@[stacks 0B3N]
theorem isReflexive_iff_isFiniteLocallyFree_of_isRegular_of_dim_le_two (X : Scheme.{u})
    (hX : IsRegular X) (hXdim : topologicalKrullDim X ≤ 2) (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    IsReflexive F ↔ SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F := by
  have hreg := ((isRegular_tfae X).out 1 2 rfl rfl).mp hX
  let : IsLocallyNoetherian X := hreg.1
  let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  let : F.IsFiniteType := _root_.IsCoherent.toIsFiniteType F
  let : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  let : _root_.SheafOfModules.IsCoherent (dualSheaf F) := isCoherent_dualSheaf F
  let : (dualSheaf F).IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent _
  have hstalkdim (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ 2 :=
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x).trans
      ((topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X).symm.le.trans hXdim)
  let stalkModule (x : X) : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let stalkFinite (x : X) : Module.Finite ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    Stacks.StalkFiniteType.finite_stalk F x
  refine ⟨fun hF => ?_, fun hF => ?_⟩
  · have hstalkFree : ∀ x : X, Module.Free (X.presheaf.stalk x) ↑(F.presheaf.stalk x) := by
      intro x
      let : IsRegularLocalRing ↑(X.presheaf.stalk x) := hreg.2 x
      let : Module.IsReflexive ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        isReflexive_stalk_of_isReflexive F hF x
      exact Module.free_of_isReflexive_of_ringKrullDim_le_two (hstalkdim x)
    apply ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae F).out 2 4).mp
    exact ⟨inferInstance, hstalkFree⟩
  · have hstalkFree :=
      ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae F).out 4 2).mp hF
    refine isReflexive_of_forall_isReflexive_stalk F fun x => ?_
    let : Module.Free ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) := hstalkFree.2 x
    exact Module.IsReflexive.of_finite_of_free _ _

end AlgebraicGeometry

end
