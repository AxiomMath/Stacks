module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

/-!
# Properties of standard smooth algebras

Let `S = R[x_1, …, x_n]/(f_1, …, f_c)` be a standard smooth algebra, given by a submersive
presentation `P`. Then `R → S` is smooth, `Ω_{S/R}` is free on the `dx_i` for the variables not
paired with a relation, `I/I²` is free on the classes of the `f_j`, standard smoothness is
preserved by principal localization of `S`, by base change and by passing to `R_f → S` when `f`
becomes invertible in `S`, and `S` is a relative global complete intersection over `R`.

## References

* [Stacks Project, Tag 00T7](https://stacks.math.columbia.edu/tag/00T7)
-/

@[expose] public section

open TensorProduct

namespace Algebra.SubmersivePresentation

/-- A nonzero algebra over a field with a submersive presentation by `n` variables and `c`
relations has Krull dimension `n - c`, written additively. -/
theorem ringKrullDim_add_natCard_eq {K T : Type*} [Field K] [CommRing T] [Algebra K T]
    [Nontrivial T] {ι σ : Type*} [Finite ι] [Finite σ] (Q : SubmersivePresentation K T ι σ) :
    ringKrullDim T + ((Nat.card σ : ℕ) : WithBot ℕ∞) = ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
  have : IsStandardSmooth K T := Q.isStandardSmooth
  have hcn : Nat.card σ ≤ Nat.card ι := Nat.card_le_card_of_injective Q.map Q.map_inj
  have hrank : Module.finrank T Ω[T⁄K] = Nat.card ι - Nat.card σ := by
    classical
    rw [Module.finrank_eq_nat_card_basis Q.basisKaehler]
    have h := Nat.card_congr (Equiv.Set.sumCompl (Set.range Q.map))
    rw [Nat.card_sum, Nat.card_range_of_injective Q.map_inj] at h
    omega
  have hloc (x : PrimeSpectrum T) : TopologicalSpace.localKrullDim (PrimeSpectrum T) x =
      ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞) := by
    have hsm : IsSmoothAt K x.asIdeal := inferInstance
    have h3 := (isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := K) x
      (Localization.AtPrime x.asIdeal)).1
    have h4 := (h3.out 1 3).mp hsm
    rw [← h4, Module.finrank_baseChange, hrank]
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim, iSup_congr hloc, iSup_const]
  norm_cast
  omega

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι]
  [Finite σ] (P : SubmersivePresentation R S ι σ)

/-- A submersive presentation is a relative global complete intersection: every nonempty fibre
has dimension `n - c`. -/
theorem isRelativeGlobalCompleteIntersection :
    P.toPresentation.IsRelativeGlobalCompleteIntersection :=
  ⟨fun p _ _ ↦ (P.baseChange p.ResidueField).ringKrullDim_add_natCard_eq⟩

/-- A standard smooth algebra is a relative global complete intersection. -/
theorem _root_.Algebra.IsStandardSmooth.isRelativeGlobalCompleteIntersection
    [IsStandardSmooth R S] : IsRelativeGlobalCompleteIntersection R S := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  let P' := P.reindex (Finite.equivFin ι).symm (Finite.equivFin σ).symm
  exact ⟨⟨_, _, _, P'.isRelativeGlobalCompleteIntersection⟩⟩

/-- If `f ∈ R` maps to a unit of a standard smooth `R`-algebra `S`, then `S` is standard smooth
over `R_f`. -/
theorem _root_.Algebra.IsStandardSmooth.localizationAway_of_isUnit [IsStandardSmooth R S] (f : R)
    (hf : IsUnit (algebraMap R S f)) :
    letI := (IsLocalization.Away.lift (S := Localization.Away f) f hf).toAlgebra
    IsStandardSmooth (Localization.Away f) S := by
  let := (IsLocalization.Away.lift (S := Localization.Away f) f hf).toAlgebra
  have hM (y : Algebra.algebraMapSubmonoid S (Submonoid.powers f)) : IsUnit (y : S) := by
    obtain ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩⟩ := y
    simpa using hf.pow n
  let e₀ : S ≃ₐ[S] S ⊗[R] Localization.Away f := IsLocalization.atUnits S _
    fun y hy ↦ (IsUnit.mem_submonoid_iff y).mpr (hM ⟨y, hy⟩)
  let e : Localization.Away f ⊗[R] S ≃ₐ[Localization.Away f] S :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R _ S).toRingEquiv.trans e₀.symm.toRingEquiv) fun a ↦ by
      show ((e₀.symm.toRingHom.comp (Algebra.TensorProduct.comm R _ S).toRingHom).comp
        (algebraMap _ _)) a = algebraMap (Localization.Away f) S a
      congr 1
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r ↦ ?_)
      have h1 : (1 : S) ⊗ₜ[R] algebraMap R (Localization.Away f) r =
          algebraMap S (S ⊗[R] Localization.Away f) (algebraMap R S r) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_one_eq_one_tmul]
      simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, RingHom.algebraMap_toAlgebra,
        IsLocalization.Away.lift_eq]
      show e₀.symm (Algebra.TensorProduct.comm R _ S _) = _
      rw [Algebra.TensorProduct.comm_tmul, h1, AlgEquiv.commutes]
      rfl
  exact .of_algEquiv e

/-- Let `S = R[x_1, …, x_n]/(f_1, …, f_c)` be standard smooth, via a submersive presentation `P`.
Then (1) `R → S` is smooth; (2) `Ω_{S/R}` is free on the `dx_i` for the variables `x_i` not paired
with a relation; (3) `I/I²` is free on the classes of the `f_j`; (4) `S_g` is standard smooth over
`R` for every `g ∈ S`; (5) `R' ⊗_R S` is standard smooth over `R'` for every `R`-algebra `R'`; (6)
if `f ∈ R` maps to a unit of `S`, then `S` is standard smooth over `R_f`; (7) `S` is a relative
global complete intersection over `R`. -/
@[stacks 00T7 "The standard smooth algebra is a submersive presentation `P` (Definition 00T6 is
Mathlib's `Algebra.IsStandardSmooth`). The source's `x_1, …, x_c` are the variables `P.map j`
paired with the relations, so its `dx_{c+1}, …, dx_n` are the `dx_i` for `i ∉ range P.map`.
`I/I²` is `P.toExtension.Cotangent`. In (6) the `R_f`-algebra structure on `S` is the one
factoring `R → S`. (7) is stated for the presentation `P` itself."]
theorem smooth_and_free_and_isStandardSmooth_and_isRelativeGlobalCompleteIntersection :
    Algebra.Smooth R S ∧
    (∃ b : Module.Basis ((Set.range P.map)ᶜ : Set ι) S Ω[S⁄R],
      ∀ i, b i = KaehlerDifferential.D R S (P.val i)) ∧
    (∃ b : Module.Basis σ S P.toExtension.Cotangent,
      ∀ j, b j = Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩) ∧
    (∀ g : S, IsStandardSmooth R (Localization.Away g)) ∧
    (∀ (R' : Type*) [CommRing R'] [Algebra R R'], IsStandardSmooth R' (R' ⊗[R] S)) ∧
    (∀ (f : R) (hf : IsUnit (algebraMap R S f)),
      letI := (IsLocalization.Away.lift (S := Localization.Away f) f hf).toAlgebra
      IsStandardSmooth (Localization.Away f) S) ∧
    P.toPresentation.IsRelativeGlobalCompleteIntersection := by
  have : IsStandardSmooth R S := P.isStandardSmooth
  refine ⟨inferInstance, ⟨P.basisKaehler, P.basisKaehler_apply⟩,
    ⟨P.basisCotangent, P.basisCotangent_apply⟩, fun g ↦ ?_, fun _ _ _ ↦ inferInstance,
    IsStandardSmooth.localizationAway_of_isUnit, P.isRelativeGlobalCompleteIntersection⟩
  have : IsStandardSmooth S (Localization.Away g) := .localization_away g
  exact .trans R S (Localization.Away g)

end Algebra.SubmersivePresentation
