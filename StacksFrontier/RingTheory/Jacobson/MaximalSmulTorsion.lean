module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Elements of `𝔪 N` for every maximal ideal `𝔪` of a Jacobson domain are torsion

Let `R` be a Noetherian Jacobson domain and `N` a finite `R`-module. If `x ∈ N` lies in `𝔪 N` for
every maximal ideal `𝔪` of `R`, then `x` is torsion: `r • x = 0` for some `r ≠ 0`.

Over the fraction field `N` becomes free, so `N_r` is free over `R_r` for some `r ≠ 0`
(generic freeness, `Module.FinitePresentation.exists_free_localizedModule_powers`). The maximal
ideals of `R_r` are the `𝔪 R_r` with `𝔪` maximal in `R` not containing `r` (`R` is Jacobson), so
every coordinate of `x / 1` in a basis of `N_r` lies in every maximal ideal of `R_r`, that is in
the Jacobson radical of the reduced Jacobson ring `R_r`, which is zero.

This is the algebra by which a statement about the closed fibres of a family over a ring of
finite type over `ℤ` is carried to its generic fibre.

## Main results

* `Stacks.JacobsonTorsion.exists_smul_eq_zero_of_forall_mem_smul_top`.
-/

@[expose] public section

universe u

namespace Stacks.JacobsonTorsion

variable {R : Type u} [CommRing R]

/-- In a free module, an element of `I • ⊤` has all its coordinates in `I`. -/
theorem repr_mem_of_mem_smul_top {S : Type u} [CommRing S] {M : Type u} [AddCommGroup M]
    [Module S M] {ι : Type u} (b : Module.Basis ι S M) (I : Ideal S) {y : M}
    (hy : y ∈ I • (⊤ : Submodule S M)) (i : ι) : b.repr y i ∈ I :=
  Submodule.smul_induction_on hy
    (fun a ha m _ => by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ ha)
    (fun y z hy hz => by rw [map_add, Finsupp.add_apply]; exact I.add_mem hy hz)

/-- **An element of `𝔪 N` for every maximal ideal `𝔪` of a Noetherian Jacobson domain is
torsion.** -/
theorem exists_smul_eq_zero_of_forall_mem_smul_top [IsDomain R] [IsNoetherianRing R]
    [IsJacobsonRing R] {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] (x : N)
    (hx : ∀ m : Ideal R, m.IsMaximal → x ∈ m • (⊤ : Submodule R N)) :
    ∃ r : R, r ≠ 0 ∧ r • x = 0 := by
  have : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) N) (FractionRing R)
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  let Rr := Localization.Away r
  have : IsDomain Rr :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
  have : IsJacobsonRing Rr := isJacobsonRing_localization (S := Rr) r
  let b := Module.Free.chooseBasis Rr (LocalizedModule.Away r N)
  let y : LocalizedModule.Away r N := LocalizedModule.mkLinearMap (Submonoid.powers r) N x
  have hcoord : ∀ i, b.repr y i = 0 := by
    intro i
    have hrad : (⊥ : Ideal Rr).jacobson = ⊥ :=
      IsJacobsonRing.out ‹_› Ideal.isRadical_bot
    rw [← Ideal.mem_bot, ← hrad, Ideal.jacobson, Ideal.mem_sInf]
    rintro m' ⟨-, hm'⟩
    have hm := ((IsLocalization.isMaximal_iff_isMaximal_disjoint Rr r m').1 hm').1
    refine repr_mem_of_mem_smul_top b m' ?_ i
    have key : ∀ z ∈ (m'.comap (algebraMap R Rr)) • (⊤ : Submodule R N),
        LocalizedModule.mkLinearMap (Submonoid.powers r) N z ∈
          m' • (⊤ : Submodule Rr (LocalizedModule.Away r N)) := fun z hz =>
      Submodule.smul_induction_on hz
        (fun a ha n _ => by
          rw [map_smul, ← algebraMap_smul Rr a]
          exact Submodule.smul_mem_smul ha Submodule.mem_top)
        (fun z w hz hw => by rw [map_add]; exact Submodule.add_mem _ hz hw)
    exact key x (hx _ hm)
  have hy : y = 0 := b.repr.injective (Finsupp.ext fun i => by rw [hcoord i, map_zero]; rfl)
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) N)).1 hy
  obtain ⟨n, rfl⟩ := hs
  exact ⟨r ^ n, pow_ne_zero n hr0, hsx⟩

end Stacks.JacobsonTorsion
