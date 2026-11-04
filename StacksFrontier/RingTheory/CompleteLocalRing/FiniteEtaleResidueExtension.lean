module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.LocalRing.NonLocalRing
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.OfHenselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale local extensions of a Noetherian complete local ring

A finite algebra over a Noetherian complete local ring is a finite product of Noetherian
complete local rings (**Stacks 0325**). If it is moreover local the product has a single
factor, so the algebra is itself a Noetherian complete local ring.

A complete local ring is Henselian (**Stacks 04GM**), and over a local ring every finite
separable extension of the residue field is the residue field extension of a finite étale
local algebra (**Stacks 04GK**). Together these produce, for a finite separable extension `K`
of the residue field of a Noetherian complete local ring `R`, a finite étale `R`-algebra which
is again a Noetherian complete local ring and has residue field `K`.

## Main results

* `IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing`: a local finite algebra over a
  Noetherian complete local ring is a Noetherian complete local ring.
* `exists_finite_etale_isNoetherianCompleteLocalRing_residueField`: the finite étale extension
  of Noetherian complete local rings realising a prescribed finite separable extension of the
  residue field.

## References

* [Stacks Project, Tag 0325](https://stacks.math.columbia.edu/tag/0325)
* [Stacks Project, Tag 04GK](https://stacks.math.columbia.edu/tag/04GK)
* [Stacks Project, Tag 04GM](https://stacks.math.columbia.edu/tag/04GM)
-/

@[expose] public section

universe u

/-- A local finite algebra over a Noetherian complete local ring is a Noetherian complete
local ring: the product decomposition of **Stacks 0325** has a single factor, because a
product of two or more nontrivial rings is not local. -/
theorem IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing
    {R S : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    [CommRing S] [Algebra R S] [Module.Finite R S] [IsLocalRing S] :
    IsNoetherianCompleteLocalRing S := by
  obtain ⟨m, T, hTComm, hTNCLR, ⟨e⟩⟩ :=
    finite_isProduct_isNoetherianCompleteLocalRing (S := S) hR
  let _ : ∀ i, CommRing (T i) := hTComm
  have _ : ∀ i, IsLocalRing (T i) := fun i => (hTNCLR i).isLocal
  have _ : ∀ i, IsNoetherianRing (T i) := fun i => (hTNCLR i).isNoetherian
  have hprodLocal : IsLocalRing (∀ i, T i) := by
    have : Nontrivial (∀ i, T i) := e.symm.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.toRingHom e.surjective
  have hm : m = 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      exact (not_subsingleton S e.toEquiv.subsingleton).elim
    · by_contra hne
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
      exact IsLocalRing.not_isLocalRing_of_nontrivial_pi T hprodLocal
  subst hm
  let e₀ : S ≃+* T 0 := e.trans (RingEquiv.piUnique T)
  refine ⟨isNoetherianRing_of_ringEquiv (T 0) e₀.symm, ‹IsLocalRing S›, ?_⟩
  have hmap : Ideal.map e₀.symm.toRingHom
      (@IsLocalRing.maximalIdeal (T 0) _ (hTNCLR 0).isLocal) =
      @IsLocalRing.maximalIdeal S _ ‹IsLocalRing S› :=
    IsLocalRing.map_maximalIdeal_of_surjective e₀.symm.toRingHom e₀.symm.surjective
  rw [← hmap]
  exact (IsAdicComplete.congr_ringEquiv
    (I := @IsLocalRing.maximalIdeal (T 0) _ (hTNCLR 0).isLocal) e₀.symm).mpr
      (hTNCLR 0).isComplete

/-- **The finite étale extension of Noetherian complete local rings realising a finite
separable residue field extension** (**Stacks 04GK** and **04GM**). For `R` a Noetherian
complete local ring and `K` a finite separable extension of its residue field there is a
finite étale local `R`-algebra `B`, again a Noetherian complete local ring, whose residue
field is `K` over that of `R`. -/
@[ega "0 10.3.1" "special case", sga "1 I 6.1" "partial"]
theorem exists_finite_etale_isNoetherianCompleteLocalRing_residueField
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsNoetherianCompleteLocalRing R)
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra R B)
      (_ : IsLocalHom (algebraMap R B)) (_ : Module.Finite R B) (_ : Algebra.Etale R B),
      IsNoetherianCompleteLocalRing B ∧
        Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField R] K) := by
  obtain ⟨B, hBring, hBlocal, hBalg, hBlochom, hBfin, hBetale, hres⟩ :=
    IsLocalRing.FiniteEtaleLocalResidueLift.exists_residueField_algEquiv.{u, u} R K
  exact ⟨B, hBring, hBlocal, hBalg, hBlochom, hBfin, hBetale,
    IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing hR, hres⟩

end
