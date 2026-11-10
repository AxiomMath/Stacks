module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Injectivity on a fibre spreads to a principal neighbourhood

Let `R` be a ring, `p` a prime of `R` and `b : M →ₗ[R] N` a linear map from a finite module to a
finite projective module. If `b ⊗ κ(p)` is injective, then there is `g ∉ p` such that `b ⊗ B` is
injective for every `R`-algebra `B` in which `g` becomes a unit.

Over the local ring `R_p` the map is split injective by Nakayama's lemma
(`IsLocalRing.split_injective_iff_lTensor_residueField_injective`); a left inverse over `R_p`
lifts, after clearing a denominator, to a map `h : N → M` with `h ∘ b = s · id` up to a further
element of the complement of `p`, and that identity survives every base change in which the two
elements are invertible.

## Main results

* `exists_notMem_injective_baseChange_of_injective_residueField`.
-/

@[expose] public section

open TensorProduct

universe u

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If `b ⊗ S` is injective, so is `(b ⊗ A) ⊗ S` for any tower `R → A → S`. -/
private theorem injective_lTensor_baseChange_of_injective
    {A S : Type*} [CommRing A] [Algebra R A] [CommRing S] [Algebra R S] [Algebra A S]
    [IsScalarTower R A S] (b : M →ₗ[R] N) (hb : Function.Injective (b.baseChange S)) :
    Function.Injective ((b.baseChange A).lTensor S) := by
  let eM : S ⊗[A] (A ⊗[R] M) ≃ₗ[S] S ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S M
  let eN : S ⊗[A] (A ⊗[R] N) ≃ₗ[S] S ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S N
  have hcomm : ∀ x, eN ((b.baseChange A).lTensor S x) = b.baseChange S (eM x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c y =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
      | tmul a m =>
        simp [eM, eN, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  intro x y hxy
  have h1 := congrArg eN hxy
  rw [hcomm, hcomm] at h1
  exact eM.injective (hb h1)

/-- **Injectivity at a point spreads to a principal neighbourhood.** For `b : M →ₗ[R] N` with `M`
finite and `N` finite projective, if `b ⊗ κ(p)` is injective then there is `g ∉ p` such that
`b ⊗ B` is injective for every `R`-algebra `B` in which `g` is a unit. -/
theorem exists_notMem_injective_baseChange_of_injective_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    (b : M →ₗ[R] N) (hb : Function.Injective (b.baseChange p.ResidueField)) :
    ∃ g : R, g ∉ p ∧ ∀ (B : Type u) [CommRing B] [Algebra R B], IsUnit (algebraMap R B g) →
      Function.Injective (b.baseChange B) := by
  classical
  let Rp := Localization.AtPrime p
  let k := p.ResidueField
  let mkM : M →ₗ[R] Rp ⊗[R] M := TensorProduct.mk R Rp M 1
  let mkN : N →ₗ[R] Rp ⊗[R] N := TensorProduct.mk R Rp N 1
  have hmkM : IsLocalizedModule p.primeCompl mkM :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl Rp mkM).mpr (TensorProduct.isBaseChange R M Rp)
  let bp : Rp ⊗[R] M →ₗ[Rp] Rp ⊗[R] N := b.baseChange Rp
  -- the fibre of `bp` is the fibre of `b`
  have hinj : Function.Injective (bp.lTensor (IsLocalRing.ResidueField Rp)) :=
    injective_lTensor_baseChange_of_injective b hb
  have : Module.Free Rp (Rp ⊗[R] N) := Module.free_of_flat_of_isLocalRing
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective bp).mpr hinj
  have : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule p.primeCompl
    mkM ((l'.restrictScalars R) ∘ₗ mkN)
  have hcomp : mkM ∘ₗ (h ∘ₗ b) = mkM ∘ₗ ((s : R) • LinearMap.id) := by
    ext m
    have e1 := congrArg (fun φ => φ (b m)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply] at e1
    have e2 : l' (mkN (b m)) = mkM m := by
      have := congrArg (fun φ => φ (mkM m)) hl'
      simpa [bp, mkM, mkN] using this
    simp only [LinearMap.coe_comp, Function.comp_apply, e1, LinearMap.restrictScalars_apply,
      e2, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    rfl
  obtain ⟨t, ht⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule p.primeCompl mkM
    (h ∘ₗ b) ((s : R) • LinearMap.id) hcomp
  refine ⟨(t : R) * s, fun hmem => ?_, fun B _ _ hunit => ?_⟩
  · rcases (Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hmem) with h' | h'
    · exact t.2 h'
    · exact s.2 h'
  · intro x y hxy
    have key : ∀ z : B ⊗[R] M, (((t : R) * s : R) • z) =
        (t : R) • ((h.baseChange B) ((b.baseChange B) z)) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [smul_add, map_add, hz, hw]
      | tmul c m =>
        have := congrArg (fun φ => φ m) ht
        simp only [LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.id_apply] at this
        rw [Submonoid.smul_def, Submonoid.smul_def] at this
        simp only [LinearMap.baseChange_tmul]
        rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul, this, mul_smul]
    have hx := key x
    have hy := key y
    rw [hxy, ← hy] at hx
    have hu : IsUnit (algebraMap R B ((t : R) * s)) := hunit
    have hx' : (algebraMap R B ((t : R) * s)) • x = (algebraMap R B ((t : R) * s)) • y := by
      rw [algebraMap_smul, algebraMap_smul]
      exact hx
    exact (hu.smul_left_cancel).mp hx'

/-- **Injectivity at a field-valued point spreads to a principal neighbourhood.** The same as
`exists_notMem_injective_baseChange_of_injective_residueField`, with the residue field replaced
by an arbitrary field `K` receiving `R`: the base change to `K` of `b ⊗ κ(p)`, for `p` the kernel
of `R → K`, is `b ⊗ K`, and `K` is faithfully flat over `κ(p)`. -/
theorem exists_ne_zero_injective_baseChange_of_injective_field
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    {K : Type u} [Field K] (χ : R →+* K) (b : M →ₗ[R] N)
    (hb : letI := χ.toAlgebra; Function.Injective (b.baseChange K)) :
    ∃ g : R, χ g ≠ 0 ∧ ∀ (B : Type u) [CommRing B] [Algebra R B], IsUnit (algebraMap R B g) →
      Function.Injective (b.baseChange B) := by
  classical
  let q := RingHom.ker χ
  have : q.IsPrime := RingHom.ker_isPrime χ
  let : Algebra R K := χ.toAlgebra
  let κ := q.ResidueField
  let ι : κ →+* K := Ideal.ResidueField.lift q χ le_rfl (fun x hx => by
    have hx' : χ x ≠ 0 := fun h => hx (by simpa [q, RingHom.mem_ker] using h)
    exact (isUnit_iff_ne_zero.mpr hx' : IsUnit (χ x)))
  let : Algebra κ K := ι.toAlgebra
  have : IsScalarTower R κ K := IsScalarTower.of_algebraMap_eq fun r => by
    change χ r = ι (algebraMap R κ r)
    exact (Ideal.ResidueField.lift_algebraMap q χ le_rfl _ r).symm
  have : Module.FaithfullyFlat κ K := inferInstance
  have hinjK : Function.Injective ((b.baseChange κ).lTensor K) :=
    injective_lTensor_baseChange_of_injective b hb
  have hinjκ : Function.Injective (b.baseChange κ) :=
    (Module.FaithfullyFlat.lTensor_injective_iff_injective κ K _).1 hinjK
  obtain ⟨g, hg, hB⟩ := exists_notMem_injective_baseChange_of_injective_residueField q b hinjκ
  exact ⟨g, fun h => hg h, hB⟩
