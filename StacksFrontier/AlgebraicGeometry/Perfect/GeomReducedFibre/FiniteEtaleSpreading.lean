module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.StructureSheafDecomposition
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite

/-!
# Finite etaleness spread out from a fibre, after a first localization

Let `A` be an `R`-algebra and `p` a prime of `R`. Assume that after inverting some `g ∉ p` the
algebra `A_g = R_g ⊗_R A` is finite free over `R_g`, and that the fibre `κ(p) ⊗_R A` is formally
unramified over `κ(p)`. Then there is `h ∉ p` such that for every localization `B` of `R` away
from `h`, the `B`-algebra `B ⊗_R A` is finite and etale.

This is the step of the proof of [Stacks, Tag 0G7Y] that applies [Stacks, Tag 0476] to the finite
locally free `Spec_S(H⁰(E)) → S`, after the shrinking that makes `H⁰(E)` free. It reduces to
`Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.exists_away_finiteEtale_of_unramified_fibre`
over `R_g`, the fibre of `A_g` at the prime above `p` being the base change of `κ(p) ⊗_R A`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- The fibre of `R' ⊗[R] A` at a prime `p'` over `p` is formally unramified if that of `A` is. -/
private theorem formallyUnramified_fiber_baseChange {R R' A : Type*} [CommRing R] [CommRing R']
    [CommRing A] [Algebra R R'] [Algebra R A] (p : Ideal R) [p.IsPrime] (p' : Ideal R')
    [p'.IsPrime] (hcomap : p'.comap (algebraMap R R') = p)
    (hfib : Algebra.FormallyUnramified p.ResidueField (p.Fiber A)) :
    Algebra.FormallyUnramified p'.ResidueField (p'.Fiber (R' ⊗[R] A)) := by
  let : Algebra p.ResidueField p'.ResidueField :=
    (Ideal.ResidueField.map p p' (algebraMap R R') hcomap.symm).toAlgebra
  have : IsScalarTower R p.ResidueField p'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p p' (algebraMap R R') hcomap.symm r).symm
  let e₁ : p'.Fiber (R' ⊗[R] A) ≃ₐ[p'.ResidueField] p'.ResidueField ⊗[R] A :=
    Algebra.TensorProduct.cancelBaseChange R R' p'.ResidueField p'.ResidueField A
  let e₂ : p'.ResidueField ⊗[p.ResidueField] (p.Fiber A) ≃ₐ[p'.ResidueField]
      p'.ResidueField ⊗[R] A :=
    Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField p'.ResidueField A
  exact Algebra.FormallyUnramified.of_equiv (e₂.trans e₁.symm)

/-- Finiteness and etaleness of `B₀ ⊗[R] A` over `B₀` transfer along `B₀ ≃ₐ[R] B`. -/
private theorem finite_etale_tensor_of_algEquiv {R A B₀ B : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [CommRing B₀] [Algebra R B₀] [CommRing B] [Algebra R B] (eB : B₀ ≃ₐ[R] B)
    [Module.Finite B₀ (B₀ ⊗[R] A)] [Algebra.Etale B₀ (B₀ ⊗[R] A)] :
    Module.Finite B (B ⊗[R] A) ∧ Algebra.Etale B (B ⊗[R] A) := by
  let ψ : B₀ ⊗[R] A ≃ₐ[R] B ⊗[R] A := Algebra.TensorProduct.congr eB AlgEquiv.refl
  have hcomp : algebraMap B (B ⊗[R] A) =
      (ψ.toRingEquiv.toRingHom.comp (algebraMap B₀ (B₀ ⊗[R] A))).comp
        eB.symm.toRingEquiv.toRingHom := by
    ext b
    simp [ψ, Algebra.TensorProduct.algebraMap_apply]
  constructor
  · rw [← RingHom.finite_algebraMap, hcomp]
    refine RingHom.finite_respectsIso.2 _ _ ?_
    refine RingHom.finite_respectsIso.1 _ _ ?_
    exact RingHom.finite_algebraMap.2 ‹_›
  · rw [← RingHom.etale_algebraMap, hcomp]
    refine RingHom.Etale.respectsIso.2 _ _ ?_
    refine RingHom.Etale.respectsIso.1 _ _ ?_
    exact RingHom.etale_algebraMap.2 ‹_›

/-- **Finite etaleness spread out from a formally unramified fibre.** -/
theorem exists_away_finite_etale_of_formallyUnramified {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (p : Ideal R) [p.IsPrime] (g : R) (hg : g ∉ p)
    [Module.Finite (Localization.Away g) (Localization.Away g ⊗[R] A)]
    [Module.Free (Localization.Away g) (Localization.Away g ⊗[R] A)]
    (hfib : Algebra.FormallyUnramified p.ResidueField (p.Fiber A)) :
    ∃ h : R, h ∉ p ∧ g ∣ h ∧ ∀ (B : Type u) [CommRing B] [Algebra R B] [IsLocalization.Away h B],
      Module.Finite B (B ⊗[R] A) ∧ Algebra.Etale B (B ⊗[R] A) := by
  let R' := Localization.Away g
  let A' := R' ⊗[R] A
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R) : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hg (‹p.IsPrime›.mem_of_pow_mem n hx)
  let p' : Ideal R' := p.map (algebraMap R R')
  have : p'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) R' p ‹_› hdisj
  have hcomap : p'.comap (algebraMap R R') = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) R' ‹_› hdisj
  obtain ⟨h', hh', hall⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.exists_away_finiteEtale_of_unramified_fibre
      p' A' (formallyUnramified_fiber_baseChange p p' hcomap hfib)
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) h'
  simp only at hr
  have hrp : r ∉ p := fun hrp => hh' <|
    (p'.mul_unit_mem_iff_mem (IsLocalization.map_units R' (⟨g ^ n, n, rfl⟩ : Submonoid.powers g))).1
      (hr ▸ Ideal.mem_map_of_mem _ hrp)
  refine ⟨g * r, fun hgr => (‹p.IsPrime›.mem_or_mem hgr).elim hg hrp, dvd_mul_right g r,
    fun B _ _ _ => ?_⟩
  let h'' := algebraMap R R' r
  have hdvd : h' ∣ h'' := ⟨algebraMap R R' (g ^ n), hr.symm⟩
  obtain ⟨hfin₀, -, hét₀⟩ := hall h'' hdvd
  let B₀ := Localization.Away h''
  let c : B₀ ⊗[R'] A' ≃ₐ[B₀] B₀ ⊗[R] A :=
    Algebra.TensorProduct.cancelBaseChange R R' B₀ B₀ A
  have : Module.Finite B₀ (B₀ ⊗[R] A) := Module.Finite.equiv c.toLinearEquiv
  have : Algebra.Etale B₀ (B₀ ⊗[R] A) := Algebra.Etale.of_equiv c
  exact finite_etale_tensor_of_algEquiv
    (IsLocalization.algEquiv (Submonoid.powers (g * r)) B₀ B)

end StacksDraft.Perfect.GeomReducedFibre

end
