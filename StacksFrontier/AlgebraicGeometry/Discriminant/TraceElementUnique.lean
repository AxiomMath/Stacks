module

public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceCondition
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Uniqueness of the trace element

For a flat quasi-finite map of Noetherian rings there is at most one trace element in the
relative dualizing module.

The argument is the one in the Stacks Project. Suppose `τ₁ ≠ τ₂` and put `x = τ₁ - τ₂`. Pick a
prime `q` of `B` in the support of `B · x`, lying over `p ⊆ A`. By the étale local structure of
quasi-finite algebras there is an étale `A`-algebra `A₁` and an idempotent `e` of
`S = A₁ ⊗_A B` such that the factor `C = S/(1-e)` is finite over `A₁` and contains a prime over
`q`. Both `τ₁` and `τ₂` restrict to `Trace_{C/A₁}` on that factor, so `x` restricts to zero; the
local step `exists_smul_eq_zero_of_restriction_eq_zero` then produces a scalar restricting to
`1` on `C` that annihilates the image of `x`, and flat base change (Tag 0BT3) turns that into a
vanishing tensor, which `mem_prime_of_tmul_eq_zero` contradicts.

## Main results

* `Stacks.Discriminant.isTraceElement_unique` is Tag 0BT7.

## Implementation notes

The base-change and factor universes in the trace condition are instantiated at those of the
base ring and of `A₁ ⊗_A B`, so the condition is applied exactly to the decomposition produced
by `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`.

This theorem is what makes `IsTraceElement` an honest definition: together with existence it
pins the trace element down to a single element of the relative dualizing module, so a
statement about "the" trace element is a statement about a determined object.

## References

* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

/-- **Stacks Project, Tag 0BT7.** A flat quasi-finite algebra of Noetherian rings has at most
one trace element. -/
@[stacks 0BT7]
theorem isTraceElement_unique
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    {τ₁ τ₂ : dualizingModule F}
    (h₁ : IsTraceElement.{u, v, w, u, max u v, max u v} F τ₁)
    (h₂ : IsTraceElement.{u, v, w, u, max u v, max u v} F τ₂) :
    τ₁ = τ₂ := by
  classical
  by_contra hne
  let x : dualizingModule F := τ₁ - τ₂
  have hx : x ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨q, hxann⟩ : ∃ q : PrimeSpectrum B, ∀ r : B, r • x = 0 → r ∈ q.asIdeal := by
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Submodule.span B {x}).annihilator (by
      rw [Ne, Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul]
      exact hx)
    exact ⟨⟨m, hm.isPrime⟩, fun r hr ↦ hle ((Submodule.mem_annihilator_span_singleton x r).mpr hr)⟩
  let p : Ideal A := q.asIdeal.comap (algebraMap A B)
  have : p.IsPrime := q.2.comap (algebraMap A B)
  have : q.asIdeal.LiesOver p := ⟨rfl⟩
  let : Algebra.FiniteType A B := finiteType_of_finiteOpenFactorization F
  let : Algebra.QuasiFinite A (Localization.AtPrime q.asIdeal) :=
    Algebra.QuasiFinite.of_isLocalization q.asIdeal.primeCompl
  have hqf : Algebra.QuasiFiniteAt A q.asIdeal := inferInstance
  obtain ⟨A₁, hA₁ring, hA₁alg, hA₁etale, p₁, hp₁, hp₁over, e, he,
      P, hP, hPover, hrest⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q.asIdeal
  rcases hrest with ⟨hPq, heP, hres, hfinite, hunique⟩
  let : CommRing A₁ := hA₁ring
  let : Algebra A A₁ := hA₁alg
  let : Algebra.Etale A A₁ := hA₁etale
  let : Algebra.FiniteType A A₁ := inferInstance
  let : IsNoetherianRing A₁ := Algebra.FiniteType.isNoetherianRing A A₁
  let S := A₁ ⊗[A] B
  let C := S ⧸ Ideal.span {1 - e}
  let D := S ⧸ Ideal.span {e}
  let : Algebra S C := Ideal.Quotient.algebra _
  let : Algebra S D := Ideal.Quotient.algebra _
  have heAway : IsLocalization.Away e C :=
    idempotent_quotient_isLocalization_away e he
  let qToAway : C ≃ₐ[S] Localization.Away e :=
    IsLocalization.algEquiv (Submonoid.powers e) C (Localization.Away e)
  let eProd : S ≃ₐ[A₁] C × D :=
    AlgEquiv.prodQuotientOfIsIdempotentElem (R := A₁) he.one_sub he (by ring) (by simp [he])
  have hfiniteC : Module.Finite A₁ C := by
    let : IsLocalization (Submonoid.powers e) C := heAway
    let : Module.Finite A₁ (Localization.Away e) := hfinite
    exact Module.Finite.equiv (qToAway.restrictScalars A₁).symm.toLinearEquiv
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  obtain ⟨hproj₁, hmfinite₁, hmprojective₁, hvalue₁⟩ := h₁ A₁ C D eProd hfiniteC
  obtain ⟨_, _, _, hvalue₂⟩ := h₂ A₁ C D eProd hfiniteC
  let restriction₁ := finiteFactorRestriction F A₁ C D eProd (by intro; rfl)
    hfiniteC hproj₁ hmfinite₁ hmprojective₁
  have hzeroRestriction : restriction₁.1
      (dualizingModule.baseChange F A₁ x) = 0 := by
    dsimp [x]
    rw [map_sub, map_sub, hvalue₁, hvalue₂, sub_self]
  let : Module.Finite F₁.middle C := hmfinite₁
  let : Module.Projective F₁.middle C := hmprojective₁
  have hmk : ∀ y : F₁.middle,
      algebraMap F₁.middle C y = algebraMap S C (algebraMap F₁.middle S y) := fun _ => rfl
  have htowerS : IsScalarTower F₁.middle S C := IsScalarTower.of_algebraMap_eq hmk
  have htowerA : IsScalarTower A₁ F₁.middle C := IsScalarTower.of_algebraMap_eq (fun a₁ => by
    rw [hmk, ← IsScalarTower.algebraMap_apply A₁ F₁.middle S a₁,
      ← IsScalarTower.algebraMap_apply A₁ S C a₁])
  obtain ⟨a, ha, hazero⟩ :=
    @exists_smul_eq_zero_of_restriction_eq_zero A₁ S C _ _ _ _ F₁ _ _ _ htowerA htowerS _ _
      Ideal.Quotient.mk_surjective restriction₁.1 (fun f b c => restriction₁.2 f b c)
      (dualizingModule.baseChange F A₁ x) hzeroRestriction
  have hIP : Ideal.span {1 - e} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine (hP.mem_or_mem ?_).resolve_left heP
    rw [he.mul_one_sub_self]
    exact P.zero_mem
  have haP : algebraMap F₁.middle S a ∉ P := fun hmem =>
    hP.ne_top ((Ideal.eq_top_iff_one P).mpr <| by
      simpa using P.sub_mem hmem (hIP (Ideal.Quotient.eq.mp ha)))
  let : Algebra B S := Algebra.TensorProduct.rightAlgebra
  let : P.IsPrime := hP
  let : P.LiesOver q.asIdeal := ⟨hPq.symm⟩
  let : Module.Flat B S := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight A B A₁).symm.toLinearEquiv
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B S)
  let : IsScalarTower B S (dualizingModule F₁) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hbc := dualizingModule_isBaseChange_of_flat F A₁
  have htensor : algebraMap F₁.middle S a ⊗ₜ[B] x = 0 := by
    apply hbc.equiv.injective
    simpa only [IsBaseChange.equiv_tmul, map_zero] using hazero
  exact haP (mem_prime_of_tmul_eq_zero q.asIdeal P x hxann _ htensor)

end Stacks.Discriminant

end
