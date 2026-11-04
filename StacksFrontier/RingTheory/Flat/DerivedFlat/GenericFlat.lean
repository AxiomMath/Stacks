module

public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Generic flatness of a base change

Generic freeness (Stacks 051T) produces, for an algebra `S` of finite type over a domain `R`, a
nonzero `f ∈ R` such that `S_f` is free over `R_f`. This file restates the flatness half of that
conclusion with `S_f` presented as the base change `R_f ⊗[R] S`, and records the resulting
statement for an algebra of finite type over a ring `A₀`, reduced modulo a prime ideal.

## Main results

* `StacksDraft.DerivedFlat.flat_tensor_of_isFinitePresentationFreeAway`: if `f` satisfies the
  condition of Stacks 051U for `R → S` and the module `S`, then `R_f ⊗[R] S` is flat over `R_f`.
* `StacksDraft.DerivedFlat.exists_flat_tensor_quotient`: for an algebra `D` of finite type over
  `A₀` and a prime `p` of `A₀`, some element of `A₀ ⧸ p` that is nonzero makes
  `(A₀ ⧸ p)_f ⊗[A₀] D` flat over `(A₀ ⧸ p)_f`, and so does every multiple of it.

## References

* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
-/

@[expose] public noncomputable section

open TensorProduct

universe u

namespace StacksDraft.DerivedFlat

/-- If `f` satisfies the condition of Stacks 051U for `R → S` and the module `S`, then the base
change `R_f ⊗[R] S` is flat over `R_f`. -/
lemma flat_tensor_of_isFinitePresentationFreeAway {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {f : R} (h : Algebra.IsFinitePresentationFreeAway R S S f) :
    Module.Flat (Localization.Away f) (Localization.Away f ⊗[R] S) := by
  let Rf := Localization.Away f
  let Sf := Rf ⊗[R] S
  let : Algebra S Sf := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R S Sf := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R Sf r = (1 : Rf) ⊗ₜ algebraMap R S r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) Sf :=
    IsLocalization.tensorRight (R := R) (S := S) Rf (Submonoid.powers f)
  have : IsLocalization.Away (algebraMap R S f) Sf := by
    rwa [show Algebra.algebraMapSubmonoid S (Submonoid.powers f) =
      Submonoid.powers (algebraMap R S f) from Submonoid.map_powers _ _] at hloc
  have : IsLocalizedModule (Submonoid.powers (algebraMap R S f)) (Algebra.linearMap S Sf) :=
    (isLocalizedModule_iff_isLocalization' _ _).2 inferInstance
  have hfree := ((Algebra.isFinitePresentationFreeAway_iff f Rf Sf Sf
    (Algebra.linearMap S Sf)).1 h).2.2.1
  exact Module.Flat.of_free

/-- **Generic flatness modulo a prime.** Let `D` be an algebra of finite type over a ring `A₀`
and `p` a prime of `A₀`. There is a nonzero `h ∈ A₀ ⧸ p` such that for every multiple `f` of
`h`, the base change `(A₀ ⧸ p)_f ⊗[A₀] D` is flat over `(A₀ ⧸ p)_f`. -/
lemma exists_flat_tensor_quotient {A₀ D : Type u} [CommRing A₀] [CommRing D] [Algebra A₀ D]
    [Algebra.FiniteType A₀ D] (p : Ideal A₀) [p.IsPrime] :
    ∃ h : A₀ ⧸ p, h ≠ 0 ∧ ∀ f : A₀ ⧸ p, h ∣ f →
      Module.Flat (Localization.Away f) (Localization.Away f ⊗[A₀] D) := by
  let R := A₀ ⧸ p
  let S := R ⊗[A₀] D
  obtain ⟨h, hne, hh⟩ := Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := R) (S := S)
    (M := S)
  refine ⟨h, hne, fun f hf => ?_⟩
  have := flat_tensor_of_isFinitePresentationFreeAway (hh.of_dvd hf)
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.cancelBaseChange A₀ R (Localization.Away f) (Localization.Away f)
      D).symm.toLinearEquiv

end StacksDraft.DerivedFlat

end
