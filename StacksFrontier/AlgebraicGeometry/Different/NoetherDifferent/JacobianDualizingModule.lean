module

public import Mathlib.RingTheory.PicardGroup
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.TraceElement
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleQuasiFiniteSyntomic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartFactorization
public import StacksFrontier.RingTheory.Different.Formula.NoetherDifferentFormula

/-!
# The dualizing module of a localized complete intersection is free on the Jacobian

Let `A` be a Noetherian ring, let `h, f_1, …, f_n` be polynomials in `n` variables over `A` and
set `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`, assumed quasi-finite over `A`. Then `ω_{B/A}` is
free of rank one over `B` on a generator carrying the Jacobian determinant `det(∂f_i/∂x_j)` to
the trace element `τ_{B/A}`.

## Main results

* `Stacks.Discriminant.bijective_noetherPairingEquiv_of_invertible`: if `ω_{B/A}` is invertible
  and the diagonal annihilator is free of rank one on `ξ`, then pairing against `ξ` is an
  isomorphism `ω_{B/A} → B`.
* `Stacks.Discriminant.exists_linearEquiv_dualizingModule_map_lmul'_eq_traceElement`: under those
  hypotheses there is an isomorphism `B → ω_{B/A}` carrying the image of `ξ` under multiplication
  to `τ_{B/A}`.
* `Stacks.Discriminant.exists_linearEquiv_dualizingModule_map_det_eq_traceElement`: the same for
  `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` over a Noetherian ring, where the generator of the
  diagonal annihilator has the Jacobian determinant as its image. This is the Noetherian part of
  Tag 0BWH, whose full statement is
  `Stacks.Discriminant.exists_linearEquiv_dualizingModule_jacobianDet`.

## Implementation notes

This is the source's argument. Pairing against a generator `ξ` of the diagonal annihilator is a
functional `φ` on `ω_{B/A}` which generates `Hom_B(ω_{B/A}, B)`, because the Noether pairing
identifies the diagonal annihilator with that dual (Tag 0BVT); invertibility of `ω_{B/A}` then
makes `φ` itself an isomorphism, since `1` is a sum of values of functionals on `ω_{B/A}` and
every functional is a multiple of `φ`, so `φ` is surjective, and a surjection onto an invertible
module is bijective. Invertibility is where the source's warning applies: a finite module `M`
with `Hom_B(M, B) ≅ B` need not be free. The value `φ(τ_{B/A})` is the image of `ξ` under
multiplication, again by Tag 0BVT, which for the localized complete intersection is the Jacobian
determinant (Tag 0BWD).

Flatness of `B` over `A` and invertibility of `ω_{B/A}` are derived from quasi-finiteness, by
`Stacks.Discriminant.flat_localizedCompleteIntersection` and
`Stacks.Discriminant.dualizingModule_invertible_of_isRelativeGlobalCompleteIntersection`; the
`letI` in the statement of the last result is that derivation, not a hypothesis. The source
states the lemma for an arbitrary ring `A`, but the trace element `τ_{B/A}` is defined only for a
flat quasi-finite map of Noetherian rings (Definition 0BT6), so `A` is Noetherian here; `B` is
then Noetherian too, being of finite type over `A`. The statement is for every finite-open
factorization of `A → B`, of which there is one by
`Stacks.Discriminant.nonempty_finiteOpenFactorization_localizedCompleteIntersection`.

The source assumes `n ≥ 1`; the argument and the conclusion also hold for `n = 0`, when `B` is
the localization `A[1/h]` and the Jacobian matrix is the empty matrix with determinant `1`, so no
positivity hypothesis is imposed.

## References

* [Stacks Project, Tag 0BWH](https://stacks.math.columbia.edu/tag/0BWH)
* [Stacks Project, Tag 0BVT](https://stacks.math.columbia.edu/tag/0BVT)
* [Stacks Project, Tag 0BWD](https://stacks.math.columbia.edu/tag/0BWD)
* [Stacks Project, Tag 0BWF](https://stacks.math.columbia.edu/tag/0BWF)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

section General

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]

/-- Let `A → B` be a flat quasi-finite homomorphism of Noetherian rings whose relative dualizing
module is invertible, and suppose multiplication by `ξ` identifies `B` with the annihilator `J`
of `Ker(B ⊗_A B → B)`. Then pairing against `ξ` is an isomorphism `ω_{B/A} → B`.

The Noether pairing identifies `J` with `Hom_B(ω_{B/A}, B)` (Tag 0BVT), so every functional on
`ω_{B/A}` is a multiple of the functional `φ` paired from `ξ`; as `1` is a sum of values of
functionals on `ω_{B/A}` by invertibility, `φ` is surjective, hence bijective. -/
theorem bijective_noetherPairingEquiv_of_invertible
    (F : FiniteOpenFactorization.{u, v, w} A B) [Module.Invertible B (dualizingModule F)]
    (e : B ≃ₗ[B] diagonalAnnihilator A B) :
    Function.Bijective (noetherPairingEquiv F (e 1)) := by
  have hgen : ∀ ψ : dualizingModule F →ₗ[B] B, ∃ c : B,
      ∀ x, ψ x = noetherPairingEquiv F (e 1) (c • x) := by
    intro ψ
    obtain ⟨j, rfl⟩ := (noetherPairingEquiv F).surjective ψ
    obtain ⟨c, rfl⟩ := e.surjective j
    refine ⟨c, fun x ↦ ?_⟩
    have h1 : e c = c • e 1 := by rw [← e.map_smul]; simp
    rw [h1, (noetherPairingEquiv F).map_smul, LinearMap.smul_apply, LinearMap.map_smul]
  have hcontract : Function.Surjective (_root_.contractLeft B (dualizingModule F)) :=
    Module.Invertible.bijective.2
  have key : ∀ z, _root_.contractLeft B (dualizingModule F) z ∈
      LinearMap.range (noetherPairingEquiv F (e 1)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul ψ x =>
        obtain ⟨c, hc⟩ := hgen ψ
        rw [contractLeft_apply]
        exact LinearMap.mem_range.mpr ⟨c • x, (hc x).symm⟩
    | add z t hz ht => rw [map_add]; exact Submodule.add_mem _ hz ht
  refine Module.Invertible.bijective_of_surjective ?_
  rw [← LinearMap.range_eq_top, Ideal.eq_top_iff_one]
  obtain ⟨z, hz⟩ := hcontract 1
  exact hz ▸ key z

/-- Let `A → B` be a flat quasi-finite homomorphism of Noetherian rings whose relative dualizing
module is invertible, and suppose multiplication by `ξ` identifies `B` with the annihilator of
`Ker(B ⊗_A B → B)`. Then there is an isomorphism `B → ω_{B/A}` carrying the image of `ξ` under
the multiplication map `B ⊗_A B → B` to the trace element `τ_{B/A}`. -/
theorem exists_linearEquiv_dualizingModule_map_lmul'_eq_traceElement
    (F : FiniteOpenFactorization.{u, v, w} A B) [Module.Invertible B (dualizingModule F)]
    (e : B ≃ₗ[B] diagonalAnnihilator A B) :
    ∃ ε : B ≃ₗ[B] dualizingModule F,
      ε (Algebra.TensorProduct.lmul' A (e 1 : B ⊗[A] B)) = dualizingModule.traceElement F := by
  refine ⟨(LinearEquiv.ofBijective _ (bijective_noetherPairingEquiv_of_invertible F e)).symm, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  exact (noetherPairingEquiv_apply_traceElement F (e 1)).symm

end General

section LocalizedCompleteIntersection

variable (A : Type u) [CommRing A] (n : ℕ) (h : MvPolynomial (Fin n) A)
  (f : Fin n → MvPolynomial (Fin n) A)
  [Algebra.QuasiFinite A (localizedCompleteIntersection A n h f)]

omit [Algebra.QuasiFinite A (localizedCompleteIntersection A n h f)] in
/-- `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is a finitely presented `A`-algebra: it is a quotient
of the localization `A[x_1, …, x_n, 1/h]` by finitely many equations. -/
theorem finitePresentation_localizedCompleteIntersection :
    Algebra.FinitePresentation A (localizedCompleteIntersection A n h f) := by
  classical
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) A) (Localization.Away h) :=
    IsLocalization.Away.finitePresentation h
  have : Algebra.FinitePresentation A (Localization.Away h) :=
    Algebra.FinitePresentation.trans A (MvPolynomial (Fin n) A) (Localization.Away h)
  exact Algebra.FinitePresentation.quotient ⟨Finset.univ.image (localizedRelations A n h f),
    by simp⟩

/-- A quasi-finite `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` admits a finite-open factorization of
`A → B`, so the relative dualizing module `ω_{B/A}` of Tag 0BSZ is defined for it. -/
theorem nonempty_finiteOpenFactorization_localizedCompleteIntersection :
    Nonempty (FiniteOpenFactorization.{u, u, u} A (localizedCompleteIntersection A n h f)) :=
  let : Algebra.FinitePresentation A (localizedCompleteIntersection A n h f) :=
    finitePresentation_localizedCompleteIntersection A n h f
  nonempty_finiteOpenFactorization

variable [IsNoetherianRing A]

/-- **Stacks Project, Tag 0BWH.** Let `A` be a Noetherian ring, let `h, f_1, …, f_n` be
polynomials in `n` variables over `A` and set `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`, assumed
quasi-finite over `A`. There is an isomorphism `B → ω_{B/A}` mapping the Jacobian determinant
`det(∂f_i/∂x_j)` to the trace element `τ_{B/A}`.

Flatness of `B` over `A` is derived from quasi-finiteness
(`Stacks.Discriminant.flat_localizedCompleteIntersection`); the `letI` below is that derivation,
not a hypothesis. The statement is for every finite-open factorization `F` of `A → B`, of which
there is one by
`Stacks.Discriminant.nonempty_finiteOpenFactorization_localizedCompleteIntersection`, and the
dualizing module is independent of the choice by `Stacks.Discriminant.dualizingModuleEquiv`.
The full statement of Tag 0BWH, including arbitrary rings `A`, is
`Stacks.Discriminant.exists_linearEquiv_dualizingModule_jacobianDet`. -/
theorem exists_linearEquiv_dualizingModule_map_det_eq_traceElement :
    letI : Module.Flat A (localizedCompleteIntersection A n h f) :=
      flat_localizedCompleteIntersection A n h f
    ∀ F : FiniteOpenFactorization.{u, u, w} A (localizedCompleteIntersection A n h f),
      ∃ ε : localizedCompleteIntersection A n h f ≃ₗ[localizedCompleteIntersection A n h f]
          dualizingModule F,
        ε (Matrix.det fun i j : Fin n ↦ algebraMap (MvPolynomial (Fin n) A)
            (localizedCompleteIntersection A n h f) (MvPolynomial.pderiv j (f i))) =
          dualizingModule.traceElement F := by
  let : Module.Flat A (localizedCompleteIntersection A n h f) :=
    flat_localizedCompleteIntersection A n h f
  intro F
  let : Module.Invertible (localizedCompleteIntersection A n h f) (dualizingModule F) :=
    dualizingModule_invertible_of_isRelativeGlobalCompleteIntersection F
  obtain ⟨e, he⟩ := exists_linearEquiv_diagonalAnnihilator_lmul'_eq_det A n h f
  obtain ⟨ε, hε⟩ := exists_linearEquiv_dualizingModule_map_lmul'_eq_traceElement F e
  exact ⟨ε, by rw [← he]; exact hε⟩

end LocalizedCompleteIntersection

end Stacks.Discriminant

end
