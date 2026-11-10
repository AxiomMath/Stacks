module

public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness
public import StacksFrontier.RingTheory.Flat.ShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsion and base change for a module over an algebra

Let `A` be a commutative ring, let `B` be an `A`-algebra and let `N` be a `B`-module, regarded
as an `A`-module by restriction of scalars. This file collects results comparing `N` with its
base changes along the two kinds of map out of `A` that occur in generic flatness arguments: the
residue field `A → κ(p)` at a prime, and the localization `A → A_h` away from an element.

Two themes run through the file. The first is that base change to a residue field is a
localization followed by a quotient, so denominators can be cleared: every element of
`M ⊗_A κ(p)` becomes of the form `m ⊗ 1` after multiplication by an element of `A ∖ p`, and for
a domain `A` the module `M ⊗_A κ(⊥)` is exactly the localization of `M` at the nonzerodivisors.
The second is that generic flatness (Stacks Tag 051T, `Algebra.IsFinitePresentationFreeAway`)
turns qualitative statements about `A`-torsion in a finite `B`-module into uniform ones: a single
nonzero `h ∈ A` whose powers annihilate all of the torsion, and injectivity of `P ⊗_A X → P ⊗_A Y`
for *every* `A_h`-module `P`.

## Main results

* `Stacks.TorsionBaseChange.exists_notMem_smul_eq_tmul_one`: clearing denominators in
  `M ⊗_A κ(p)`, for an arbitrary `A`-module `M`. (Mathlib's
  `Ideal.ResidueField.exists_smul_eq_tmul_one` is the case of an `A`-algebra.)
* `Stacks.TorsionBaseChange.colon_bot_singleton_comap_algebraMap`: the annihilator of an element
  of a `C`-module taken over a subring `B` is the contraction of its annihilator over `C`.
* `Stacks.TorsionBaseChange.isLocalizedModule_tmul_one_residueField_bot`: for a domain `A`, the
  module `M ⊗_A κ(⊥)` is the localization of `M` at `nonZeroDivisors A`, via `m ↦ m ⊗ 1`.
* `Stacks.TorsionBaseChange.exists_ne_zero_forall_torsion_pow_smul_eq_zero`: for `N` a finite
  module over a finite type algebra `B` over a domain `A`, some nonzero `h ∈ A` is such that
  every `A`-torsion element of `N` is annihilated by a power of `h`.
* `Stacks.TorsionBaseChange.injective_of_isLocalizedModule_id`: a localization map is injective
  once the localizing submonoid already acts invertibly on the source.
* `Stacks.TorsionBaseChange.injective_lTensor_of_isFinitePresentationFreeAway`: universal
  injectivity. If `0 → X → Y → Z → 0` is short exact over `B` and `Z` becomes free over `A_h`
  after inverting `h`, then `P ⊗_A X → P ⊗_A Y` is injective for every `A_h`-module `P`.
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.TorsionBaseChange

/-- Clearing denominators in `M ⊗_A κ(p)`: every element becomes of the form `m ⊗ 1` after
multiplication by an element of `A` outside `p`. This is the module version of Mathlib's
`Ideal.ResidueField.exists_smul_eq_tmul_one`, which assumes `M` is an `A`-algebra. -/
public theorem exists_notMem_smul_eq_tmul_one {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (p : Ideal A) [p.IsPrime] (z : M ⊗[A] p.ResidueField) :
    ∃ a ∉ p, ∃ m : M, a • z = m ⊗ₜ[A] 1 := by
  induction z using TensorProduct.inductionOn with
  | tmul m k =>
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective (R := Localization.AtPrime p) k
      obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
      refine ⟨t, t.2, x • m, ?_⟩
      have hk : (t : A) • IsLocalRing.residue (Localization.AtPrime p)
          (IsLocalization.mk' (Localization.AtPrime p) x t) = algebraMap A p.ResidueField x := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A (Localization.AtPrime p)
          p.ResidueField, IsScalarTower.algebraMap_apply A (Localization.AtPrime p)
          p.ResidueField x]
        rw [show (algebraMap (Localization.AtPrime p) p.ResidueField) =
          IsLocalRing.residue (Localization.AtPrime p) from rfl]
        rw [← map_mul, IsLocalization.mk'_spec']
      calc (t : A) • (m ⊗ₜ[A] IsLocalRing.residue (Localization.AtPrime p)
              (IsLocalization.mk' (Localization.AtPrime p) x t))
          = m ⊗ₜ[A] ((t : A) • IsLocalRing.residue (Localization.AtPrime p)
              (IsLocalization.mk' (Localization.AtPrime p) x t)) :=
            (TensorProduct.tmul_smul _ _ _).symm
        _ = m ⊗ₜ[A] (algebraMap A p.ResidueField x) := by rw [hk]
        _ = (x • m) ⊗ₜ[A] (1 : p.ResidueField) := by
            rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul']
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨a₁, ha₁, m₁, hm₁⟩ := h₁
      obtain ⟨a₂, ha₂, m₂, hm₂⟩ := h₂
      refine ⟨a₁ * a₂, fun h => ((Ideal.IsPrime.mem_or_mem ‹p.IsPrime›) h).elim ha₁ ha₂,
        a₂ • m₁ + a₁ • m₂, ?_⟩
      calc (a₁ * a₂) • (z₁ + z₂)
          = a₂ • (a₁ • z₁) + a₁ • (a₂ • z₂) := by
            rw [smul_add, smul_smul, smul_smul, mul_comm a₂ a₁]
        _ = a₂ • (m₁ ⊗ₜ[A] (1 : p.ResidueField)) + a₁ • (m₂ ⊗ₜ[A] (1 : p.ResidueField)) := by
            rw [hm₁, hm₂]
        _ = (a₂ • m₁ + a₁ • m₂) ⊗ₜ[A] 1 := by
            rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.add_tmul]

/-- The annihilator over the base ring of an element of a module over an algebra is the
contraction of its annihilator over the algebra: `ann_B(z) = (ann_C z).comap (algebraMap B C)`. -/
public theorem colon_bot_singleton_comap_algebraMap {B C N : Type*} [CommRing B] [CommRing C]
    [Algebra B C] [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N] (z : N) :
    (⊥ : Submodule B N).colon {z} = ((⊥ : Submodule C N).colon {z}).comap (algebraMap B C) := by
  ext b
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Ideal.mem_comap,
    algebraMap_smul]

/-- For a domain `A`, the module `M ⊗_A κ(⊥)` is the localisation of `M` at the nonzero
divisors of `A`, the structural map being `m ↦ m ⊗ 1`. -/
public theorem isLocalizedModule_tmul_one_residueField_bot (A M : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] :
    IsLocalizedModule (nonZeroDivisors A)
      ((TensorProduct.comm A ((⊥ : Ideal A).ResidueField) M).toLinearMap.comp
          (TensorProduct.mk A ((⊥ : Ideal A).ResidueField) M 1)) :=
  IsLocalizedModule.of_linearEquiv _ _ _

/-- **Generic freeness kills torsion uniformly.** For a finite module `N` over a finite type
algebra `B` on a domain `A`, some nonzero `h ∈ A` is such that every `A`-torsion element of `N`
is annihilated by a power of `h`. -/
public theorem exists_ne_zero_forall_torsion_pow_smul_eq_zero
    (A B N : Type u) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.Finite B N] :
    ∃ h : A, h ≠ 0 ∧ ∀ n : N, (∃ a : A, a ≠ 0 ∧ a • n = 0) →
      ∃ k : ℕ, (h ^ k) • n = 0 := by
  obtain ⟨h, hh, -, -, -, hfree⟩ :=
    Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := A) (S := B) (M := N)
  refine ⟨h, hh, ?_⟩
  rintro n ⟨a, ha, han⟩
  have hT : IsDomain (Localization.Away h) := Localization.Away.isDomain hh
  have htf : Module.IsTorsionFree (Localization.Away h)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers h)) ⊗[B] N) := inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.Away h)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  have ha' : algebraMap A (Localization.Away h) a ≠ 0 := fun hc =>
    ha (hinj (by simpa using hc))
  set Bh := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers h)) with hBh
  set ι : N →ₗ[B] Bh ⊗[B] N := TensorProduct.mk B Bh N 1 with hιdef
  have hBsm : (algebraMap A B a) • ι n = 0 := by
    rw [← ι.map_smul, algebraMap_smul, han, map_zero]
  have hsm : (algebraMap A (Localization.Away h) a) • ι n = 0 := by
    rw [algebraMap_smul, ← algebraMap_smul B a (ι n)]
    exact hBsm
  have h0 : ι n = 0 := by
    rcases smul_eq_zero.mp hsm with hc | hc
    · exact absurd hc ha'
    · exact hc
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff
    (Algebra.algebraMapSubmonoid B (Submonoid.powers h)) ι).mp h0
  obtain ⟨y, ⟨k, hk⟩, hys⟩ := s.2
  refine ⟨k, ?_⟩
  have hk' : h ^ k = y := hk
  have h1 : (algebraMap A B (h ^ k)) • n = 0 := by rw [hk', hys]; exact hs
  rwa [algebraMap_smul] at h1

/-- A localisation map is injective as soon as the localising submonoid already acts
invertibly on the source, i.e. as soon as the identity of the source is itself a localisation
map for that submonoid. -/
@[ega "0 6.3.1" "partial"]
public theorem injective_of_isLocalizedModule_id {R N N' : Type*} [CommRing R]
    [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] (S : Submonoid R)
    (f : N →ₗ[R] N') [IsLocalizedModule S f]
    [IsLocalizedModule S (LinearMap.id : N →ₗ[R] N)] :
    Function.Injective f := by
  intro a b hab
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) hab
  exact IsLocalizedModule.smul_injective (LinearMap.id : N →ₗ[R] N) c hc

/-- **Universal injectivity from generic flatness.** Let `0 → X → Y → Z → 0` be a short exact
sequence of `B`-modules over an `A`-algebra `B` and let `h ∈ A` be such that `Z` becomes free
over `A_h` after inverting `h`. Then for every `A`-module `P` which is a module over `A_h` the
map `P ⊗_A X → P ⊗_A Y` is injective. -/
public theorem injective_lTensor_of_isFinitePresentationFreeAway
    {A B X Y Z P : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup P]
    [Module B X] [Module B Y] [Module B Z] [Module A X] [Module A Y] [Module A Z] [Module A P]
    [IsScalarTower A B X] [IsScalarTower A B Y] [IsScalarTower A B Z]
    (u : X →ₗ[B] Y) (v : Y →ₗ[B] Z) (hu : Function.Injective u)
    (huv : Function.Exact u v) (hv : Function.Surjective v)
    {h : A} (hZ : Algebra.IsFinitePresentationFreeAway A B Z h)
    [Module (Localization.Away h) P] [IsScalarTower A (Localization.Away h) P] :
    Function.Injective (LinearMap.lTensor P (u.restrictScalars A)) := by
  have hfree := hZ.2.2.2
  set Bh := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers h)) with hBh
  have hflatA : Module.Flat A (Bh ⊗[B] Z) :=
    Module.Flat.trans A (Localization.Away h) _
  have hinjB := (flat_tor_zero (R := A) (N := P)
    ((LinearMap.lTensor Bh u).restrictScalars A) ((LinearMap.lTensor Bh v).restrictScalars A)
    (Module.Flat.lTensor_preserves_injective_linearMap u hu) (Module.Flat.lTensor_exact Bh huv)
    (LinearMap.lTensor_surjective Bh hv)).1
  have hidP : IsLocalizedModule (Submonoid.powers h) (LinearMap.id : P →ₗ[A] P) :=
    isLocalizedModule_id (Submonoid.powers h) P (Localization.Away h)
  have hidPX : IsLocalizedModule (Submonoid.powers h)
      (LinearMap.id : P ⊗[A] X →ₗ[A] P ⊗[A] X) :=
    isLocalizedModule_id (Submonoid.powers h) (P ⊗[A] X) (Localization.Away h)
  have hiX : IsLocalizedModule (Submonoid.powers h)
      ((TensorProduct.mk B Bh X 1).restrictScalars A) := IsLocalizedModule.restrictScalars _ _
  have hψX : Function.Injective (TensorProduct.map (LinearMap.id : P →ₗ[A] P)
      ((TensorProduct.mk B Bh X 1).restrictScalars A)) :=
    injective_of_isLocalizedModule_id (Submonoid.powers h) _
  have hsq : ∀ w : P ⊗[A] X,
      TensorProduct.map (LinearMap.id : P →ₗ[A] P) ((TensorProduct.mk B Bh Y 1).restrictScalars A)
          (LinearMap.lTensor P (u.restrictScalars A) w) =
        LinearMap.lTensor P ((LinearMap.lTensor Bh u).restrictScalars A)
          (TensorProduct.map (LinearMap.id : P →ₗ[A] P)
            ((TensorProduct.mk B Bh X 1).restrictScalars A) w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p x => simp [LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  intro w₁ w₂ hw
  refine hψX (hinjB ?_)
  rw [← hsq w₁, ← hsq w₂, hw]

end Stacks.TorsionBaseChange

end
