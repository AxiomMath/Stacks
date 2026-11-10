module

public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Field.ULift

/-!
# A connected cover with points over extensions of coprime degrees is geometrically irreducible

Let `X` be a smooth proper curve over a finite field `k` and `Z` a connected finite étale cover of
`X`. Then `Z` is a smooth proper geometrically irreducible curve over its field of constants `κ`,
a finite extension of `k` (`AlgebraicGeometry.exists_constantField_of_finiteEtale`). A point of `Z`
with values in an extension `K` of `k` gives a `k`-embedding `κ → K`, so `[κ : k]` divides
`[K : k]`. If `Z` has points over two extensions of coprime degrees, then `κ = k`, and `Z` is a
smooth proper geometrically irreducible curve over `k` itself.

This is the step "This exactly means ... `Y_k̄` irreducible" of the proof of Tag 03W5, where the
two degrees are `N` and `N - 1`.

## Main results

* `AlgebraicGeometry.FrobeniusSplitting.exists_finrank_eq`: finite extensions of a finite field
  of every positive degree, in every universe.
* `AlgebraicGeometry.FrobeniusSplitting.isCurve_comp_of_coprime`: the conclusion above.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FrobeniusSplitting

open Stacks.EtaleCohomology

/-- **Finite extensions of every degree.** A finite field `k` has an extension of degree `n` for
every `n ≠ 0`, in the universe of `k`. -/
theorem exists_finrank_eq (k : Type u) [Field k] [Finite k] {n : ℕ} (hn : n ≠ 0) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra k K), Module.finrank k K = n := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let := ZMod.algebra k p
  set e := Module.finrank (ZMod p) k
  have he : e ≠ 0 := Module.finrank_pos.ne'
  set K₀ := GaloisField p (e * n)
  have : Finite K₀ := inferInstance
  have hfr : Module.finrank (ZMod p) K₀ = e * n := GaloisField.finrank p (Nat.mul_ne_zero he hn)
  obtain ⟨φ⟩ : Nonempty (k →ₐ[ZMod p] K₀) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (Dvd.intro n hfr.symm)
  let : Fintype K₀ := Fintype.ofFinite K₀
  let alg : Algebra k (ULift.{u} K₀) :=
    ((ULift.ringEquiv.symm : K₀ ≃+* ULift.{u} K₀).toRingHom.comp φ.toRingHom).toAlgebra
  refine ⟨ULift.{u} K₀, inferInstance, inferInstance, alg, ?_⟩
  have hcardk : Fintype.card k = p ^ e := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_zmod p]
    exact Module.natCard_eq_pow_finrank
  have hcardK₀ : Fintype.card (ULift.{u} K₀) = Fintype.card k ^ n := by
    rw [Fintype.card_ulift, ← Nat.card_eq_fintype_card, GaloisField.card p _
      (Nat.mul_ne_zero he hn), hcardk, pow_mul]
  exact Nat.pow_right_injective (Fintype.one_lt_card (α := k))
    ((Module.card_eq_pow_finrank (K := k) (V := ULift.{u} K₀)).symm.trans hcardK₀)

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

omit [Finite k] in
/-- A `K`-valued point of a scheme `Z` over a field `κ` over `k`, lying over `Spec k`, gives a
`k`-embedding `κ → K`. -/
theorem nonempty_algHom_of_fieldValuedPoints {Z : Scheme.{u}} {κ : Type u} [Field κ]
    [Algebra k κ] (r : Z ⟶ Spec (.of κ)) (K : Type u) [Field K] [Algebra k K]
    (t : fieldValuedPoints (r ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ))) K) :
    Nonempty (κ →ₐ[k] K) := by
  set ψ := Spec.preimage (t.1 ≫ r)
  have hψ : Spec.map ψ = t.1 ≫ r := Spec.map_preimage _
  have h := t.2
  rw [← Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at h
  exact ⟨{ toRingHom := ψ.hom, commutes' := fun c => congrArg (fun φ => φ.hom c) h }⟩

/-- **A connected cover with points over extensions of coprime degrees is a smooth proper
geometrically irreducible curve over `k`.** -/
theorem isCurve_comp_of_coprime [IsProper f] [Smooth f] [IsCurve k f] [ConnectedSpace X]
    (Z : FiniteEtaleOver X) [ConnectedSpace Z.left] (K₁ K₂ : Type u) [Field K₁] [Finite K₁]
    [Algebra k K₁] [Field K₂] [Finite K₂] [Algebra k K₂]
    (hcop : Nat.Coprime (Module.finrank k K₁) (Module.finrank k K₂))
    (t₁ : fieldValuedPoints (Z.hom ≫ f) K₁) (t₂ : fieldValuedPoints (Z.hom ≫ f) K₂) :
    IsProper (Z.hom ≫ f) ∧ Smooth (Z.hom ≫ f) ∧ GeometricallyIrreducible (Z.hom ≫ f) ∧
      IsCurve k (Z.hom ≫ f) := by
  obtain ⟨κ, _, _, _, r, hr, hP, hS, hG, hC⟩ := exists_constantField_of_finiteEtale k f Z
  let : Fintype k := Fintype.ofFinite k
  have : Finite κ := Module.finite_of_finite k
  let : Fintype κ := Fintype.ofFinite κ
  have hpt : ∀ (K : Type u) [Field K] [Finite K] [Algebra k K],
      fieldValuedPoints (Z.hom ≫ f) K → Module.finrank k κ ∣ Module.finrank k K := by
    intro K _ _ _ t
    exact FiniteField.nonempty_algHom_iff_finrank_dvd.1
      (nonempty_algHom_of_fieldValuedPoints r K ⟨t.1, by rw [hr]; exact t.2⟩)
  have h1 : Module.finrank k κ = 1 :=
    (Nat.coprime_self _).1 ((hcop.coprime_dvd_left (hpt K₁ t₁)).coprime_dvd_right (hpt K₂ t₂))
  have hbij : Function.Bijective (algebraMap k κ) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨(algebraMap k κ).injective, ?_⟩
    rw [Module.card_eq_pow_finrank (K := k) (V := κ), h1, pow_one]
  set e := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  have : IsIso (CommRingCat.ofHom (algebraMap k κ)) :=
    (RingEquiv.ofBijective (algebraMap k κ) hbij).toCommRingCatIso.isIso_hom
  have : IsIso e := inferInstance
  have hsq : IsPullback (𝟙 Z.left) (r ≫ e) r (inv e) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [← hr]
  exact ⟨MorphismProperty.of_isPullback hsq hP, MorphismProperty.of_isPullback hsq hS,
    MorphismProperty.of_isPullback hsq hG,
    { toIsIntegral := hC.toIsIntegral
      topologicalKrullDim_eq_one := hC.topologicalKrullDim_eq_one }⟩

end AlgebraicGeometry.FrobeniusSplitting

end
