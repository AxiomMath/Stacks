module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.NNRat.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.TorTwoQuotientSelf

/-!
# A formally étale ring map with nontrivial cotangent complex

There is a surjective formally étale map of commutative rings `A → B` with nonzero cotangent
complex `L_{B/A}` (Stacks Tag 06E6). The kernel `J = Ker(A → B)` satisfies `J² = J`, so that
`A → B` is formally étale, and yet `Ker(J ⊗_A J → J²) ≠ 0`, so `J` is not weakly regular and
`Tor₂^A(B, B) ≠ 0`; the five-term exact sequence of Quillen's fundamental spectral sequence then
gives `H^{-2}(L_{B/A}) ≠ 0`.

## Main results

* `Stacks.Examples.exists_formallyEtale_surjective_mulKernel_ne_bot`: a formally étale surjection
  with `Ker(J ⊗_A J → J²) ≠ 0`.
* `Stacks.Examples.exists_formallyEtale_surjective_not_isZero_torTwo`: the same example, with the
  nonvanishing read on `Tor₂^A(B, B)` through Tag 09D6.

## Implementation notes

The example. Take the group algebra `k[ℚ≥0]` of the monoid of nonnegative rationals over a
nontrivial commutative ring `k`, let `I` be the ideal of elements with vanishing constant
coefficient, and put `A = k[ℚ≥0]/(t)` for `t = t^1` the monomial of exponent one, `J = I·A`.
Divisibility of `ℚ≥0` makes `I` — hence `J` — idempotent, so `A → A/J` is formally étale by
`Algebra.FormallyEtale.iff_of_surjective`. The class of `t^{1/2} ⊗ t^{1/2}` in `J ⊗_A J` is
killed by multiplication, because `t^{1/2} · t^{1/2} = t = 0` in `A`, and is nonzero, because the
`k`-bilinear form `(a, b) ↦ ab mod I·(t)` on `I × I` sends it to the class of `t`, which does not
lie in `I·(t)`. This is the one-variable form of the source's two-variable example `k[{x_n},
{y_n}]/(x_1y_1, x_{nm}^m - x_n, y_{nm}^m - y_n)`, with `t^{1/2} ⊗ t^{1/2}` in place of
`x_1 ⊗ y_1`; the role of the relation `x_1y_1 = 0` is played by dividing out `(t)`. The
localization the source performs is not needed: idempotency of `J` and nonvanishing of the
tensor kernel are already visible before it.

The cotangent complex. The source deduces `H_2(L_{B/A}) ≠ 0` from the nonvanishing of
`Tor₂^A(B, B)` by the five-term exact sequence of Remark 08RG. That deduction, and with it the
lemma of Tag 06E6 itself, is
`Stacks.Examples.exists_formallyEtale_surjective_cotangentComplex_ne_zero` in
`StacksFrontier.Examples.Algebra.FormallyEtaleCotangentComplexNonzero`.

Universes. `CategoryTheory.Tor'` requires the modules and the scalars to live in one universe, so
`A` and `B` are both in `Type u`; the coefficient ring is `ULift.{u} ℚ`.

## References

* [Stacks Project, Tag 06E6](https://stacks.math.columbia.edu/tag/06E6)
* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace Stacks.Examples

noncomputable section

/-- The constant-coefficient homomorphism of the group algebra of the nonnegative rationals. -/
private def constantCoeffHom (k : Type u) [CommRing k] :
    AddMonoidAlgebra k ℚ≥0 →+* k where
  toFun f := f.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' _ _ := by simp
  map_mul' f g := by
    have h : UniqueAdd f.coeff.support g.coeff.support 0 0 := by
      intro a b ha hb hab
      exact (add_eq_zero_iff_of_nonneg zero_le zero_le).mp (by simpa using hab)
    simpa using AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd h

/-- Every monomial of nonzero exponent has vanishing constant coefficient. -/
private theorem single_mem_constantCoeffKer (k : Type u) [CommRing k]
    (q : ℚ≥0) (hq : q ≠ 0) (c : k) :
    AddMonoidAlgebra.single q c ∈ RingHom.ker (constantCoeffHom k) := by
  change (AddMonoidAlgebra.single q c).coeff 0 = 0
  simp [AddMonoidAlgebra.coeff_single, hq]

/-- The ideal of elements with vanishing constant coefficient is idempotent: every monomial
`t^q` with `q ≠ 0` is `t^{q/2} · t^{q/2}`. -/
private theorem constantCoeffKer_idempotent (k : Type u) [CommRing k] :
    RingHom.ker (constantCoeffHom k) * RingHom.ker (constantCoeffHom k) =
      RingHom.ker (constantCoeffHom k) := by
  apply le_antisymm Ideal.mul_le_left
  intro f hf
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single f]
  apply Submodule.sum_mem
  intro q hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hq) hf
  have hhalf : q / 2 ≠ 0 := div_ne_zero hq0 (by norm_num)
  convert Ideal.mul_mem_mul (single_mem_constantCoeffKer k (q / 2) hhalf 1)
    (single_mem_constantCoeffKer k (q / 2) hhalf (f.coeff q)) using 1
  simp [AddMonoidAlgebra.single_mul_single, show q / 2 + q / 2 = q by ring]

/-- The reduction map from `I` onto its image in `R ⧸ K`, as an `R`-linear map. -/
private def idealMapQuotient {R : Type u} [CommRing R] (I K : Ideal R) :
    I →ₗ[R] I.map (Ideal.Quotient.mk K) where
  toFun a := ⟨Ideal.Quotient.mk K a.val, Ideal.mem_map_of_mem _ a.property⟩
  map_add' a b := by ext; simp
  map_smul' r a := by ext; simp [Algebra.smul_def]

private theorem idealMapQuotient_surjective {R : Type u} [CommRing R] (I K : Ideal R) :
    Function.Surjective (idealMapQuotient I K) := by
  intro a
  obtain ⟨b, hb, he⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective).mp a.property
  exact ⟨⟨b, hb⟩, Subtype.ext he⟩

/-- The class of `x ⊗ y` over `R` is nonzero when `x · y ∉ I · K`: the `R`-bilinear form
`(a, b) ↦ ab mod I·K` detects it. -/
private theorem idealMapQuotient_tmul_ne_zero {R : Type u} [CommRing R] (I K : Ideal R)
    (x y : I) (hne : x.val * y.val ∉ I * K) :
    idealMapQuotient I K x ⊗ₜ[R] idealMapQuotient I K y ≠ 0 := by
  let f := idealMapQuotient I K
  let b : I →ₗ[R] I →ₗ[R] R ⧸ (I * K) :=
    ((LinearMap.mul R R).compl₁₂ I.subtype I.subtype).compr₂ (I * K).mkQ
  have hK (a : I) (ha : a ∈ LinearMap.ker f) : a.val ∈ K :=
    Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val (LinearMap.mem_ker.mp ha))
  have hb₁ : LinearMap.ker f ≤ LinearMap.ker b := by
    intro a ha
    refine LinearMap.ext fun c => ?_
    change Ideal.Quotient.mk (I * K) (a.val * c.val) = 0
    rw [mul_comm a.val c.val]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_mul c.property (hK a ha))
  have hb₂ : LinearMap.ker f ≤ LinearMap.ker b.flip := by
    intro a ha
    refine LinearMap.ext fun c => ?_
    change Ideal.Quotient.mk (I * K) (c.val * a.val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_mul c.property (hK a ha))
  let e := f.quotKerEquivOfSurjective (idealMapQuotient_surjective I K)
  let b' := (b.liftQ₂ (LinearMap.ker f) (LinearMap.ker f) hb₁ hb₂).compl₁₂
    e.symm.toLinearMap e.symm.toLinearMap
  intro h
  have hh := congrArg (TensorProduct.lift b') h
  have he (a : I) : e.symm (f a) = Submodule.Quotient.mk a := by
    apply e.injective
    simp [e]
  change (b.liftQ₂ _ _ hb₁ hb₂) (e.symm (f x)) (e.symm (f y)) = 0 at hh
  rw [he, he] at hh
  exact hne (Ideal.Quotient.eq_zero_iff_mem.mp hh)

/-- A nonzero element of the kernel of multiplication on the image of `I` in `R ⧸ K`, from a
product `x · y` of elements of `I` which lies in `K` but not in `I · K`. The witness is the class
of `x ⊗ y`. -/
private theorem tensorKernel_quotient
    {R : Type u} [CommRing R] (I K : Ideal R)
    (x y : I) (hxy : x.val * y.val ∈ K) (hne : x.val * y.val ∉ I * K) :
    ∃ z : LinearMap.ker (Submodule.mulMap
      (I.map (Ideal.Quotient.mk K)) (I.map (Ideal.Quotient.mk K))), z ≠ 0 := by
  let J : Ideal (R ⧸ K) := I.map (Ideal.Quotient.mk K)
  let f := idealMapQuotient I K
  have : TensorProduct.CompatibleSMul R (R ⧸ K) J J := ⟨fun a j k => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := K) a
    change (r • j) ⊗ₜ[R] k = j ⊗ₜ[R] (r • k)
    exact TensorProduct.smul_tmul r j k⟩
  have hn : f x ⊗ₜ[R ⧸ K] f y ≠ 0 := fun h =>
    idealMapQuotient_tmul_ne_zero I K x y hne
      (by simpa using congrArg (TensorProduct.mapOfCompatibleSMul R (R ⧸ K) R J J) h)
  refine ⟨⟨f x ⊗ₜ[R ⧸ K] f y, ?_⟩, fun h => hn (congrArg Subtype.val h)⟩
  rw [LinearMap.mem_ker, Submodule.mulMap_tmul]
  change Ideal.Quotient.mk K x.val * Ideal.Quotient.mk K y.val = 0
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hxy

/-- An idempotent ideal with nonzero multiplication kernel: `A = k[ℚ≥0]/(t)` with `J` the image
of the ideal of elements with vanishing constant coefficient, and `t^{1/2} ⊗ t^{1/2}` the
witness. -/
private theorem exists_idempotentIdeal_nonzero_tensorKernel (k : Type u)
    [CommRing k] [Nontrivial k] :
    ∃ (A : Type u) (_ : CommRing A) (J : Ideal A),
      J * J = J ∧ ∃ z : LinearMap.ker (Submodule.mulMap J J), z ≠ 0 := by
  let R := AddMonoidAlgebra k ℚ≥0
  let I : Ideal R := RingHom.ker (constantCoeffHom k)
  let c : R := AddMonoidAlgebra.single 1 1
  let K : Ideal R := Ideal.span {c}
  let x : I := ⟨AddMonoidAlgebra.single (1 / 2) 1,
    single_mem_constantCoeffKer k _ (by norm_num) _⟩
  have hxx : x.val * x.val = c := by
    change AddMonoidAlgebra.single (1 / 2 : ℚ≥0) (1 : k) *
      AddMonoidAlgebra.single (1 / 2 : ℚ≥0) (1 : k) = AddMonoidAlgebra.single 1 1
    rw [AddMonoidAlgebra.single_mul_single]
    norm_num
  have hmem : x.val * x.val ∈ K := hxx ▸ Ideal.mem_span_singleton_self c
  have hnmem : x.val * x.val ∉ I * K := by
    rw [hxx]
    intro h
    obtain ⟨r, hr, he⟩ := Ideal.mem_mul_span_singleton.mp h
    have hc := congrArg (fun f : R => f.coeff 1) he
    have hh : (r * c).coeff 1 = r.coeff 0 := by
      simpa [c] using AddMonoidAlgebra.coeff_mul_single_add r (1 : k) 1 0
    rw [hh, show r.coeff 0 = 0 from hr] at hc
    simp [c] at hc
  exact ⟨R ⧸ K, inferInstance, I.map (Ideal.Quotient.mk K),
    by rw [← Ideal.map_mul, constantCoeffKer_idempotent], tensorKernel_quotient I K x x hmem hnmem⟩

/-- A surjection with idempotent kernel is formally étale. -/
private theorem formallyEtale_idealQuotient {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I * I = I) :
    Algebra.FormallyEtale R (R ⧸ I) := by
  refine (Algebra.FormallyEtale.iff_of_surjective Ideal.Quotient.mk_surjective).2 ?_
  change IsIdempotentElem (RingHom.ker (Ideal.Quotient.mk I))
  rwa [Ideal.mk_ker]

/-- A formally étale surjection whose kernel `J` has nonzero `Ker(J ⊗_A J → J²)`. -/
private theorem exists_formallyEtale_surjective_nonzero_mulKernel :
    ∃ (A : Type u) (_ : CommRing A) (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.FormallyEtale A B ∧ Function.Surjective (algebraMap A B) ∧
        ∃ z : LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap A B))
          (RingHom.ker (algebraMap A B))), z ≠ 0 := by
  obtain ⟨A, hA, J, hJ, z, hz⟩ :=
    exists_idempotentIdeal_nonzero_tensorKernel (ULift.{u} ℚ)
  have hker : RingHom.ker (algebraMap A (A ⧸ J)) = J := Ideal.mk_ker
  refine ⟨A, hA, A ⧸ J, inferInstance, inferInstance, formallyEtale_idealQuotient J hJ,
    Ideal.Quotient.mk_surjective, ?_⟩
  rw [hker, Stacks.Cotangent.ker_mulMap'_eq]
  exact ⟨z, hz⟩

end

/-- The example of Stacks 06E6. There is a formally étale surjective map of commutative rings
`A → B` whose kernel `J` has `Ker(J ⊗_A J → J²) ≠ 0`; equivalently, `J` is idempotent but not
weakly regular. This is an intermediate step of the source's argument; the lemma itself,
`L_{B/A} ≠ 0`, is `exists_formallyEtale_surjective_cotangentComplex_ne_zero`. -/
theorem exists_formallyEtale_surjective_mulKernel_ne_bot :
    ∃ (A : Type u) (_ : CommRing A) (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.FormallyEtale A B ∧ Function.Surjective (algebraMap A B) ∧
        LinearMap.ker (Submodule.mulMap' (RingHom.ker (algebraMap A B))
          (RingHom.ker (algebraMap A B))) ≠ ⊥ := by
  obtain ⟨A, hA, B, hB, hAlg, hAB, hsurj, z, hz⟩ :=
    exists_formallyEtale_surjective_nonzero_mulKernel
  exact ⟨A, hA, B, hB, hAlg, hAB, hsurj, fun hbot => hz (Subtype.ext
    ((Submodule.eq_bot_iff _).mp hbot z.val z.property))⟩

/-- The example of Stacks 06E6, with the nonvanishing read on `Tor₂`. There is a formally étale
surjective map of commutative rings `A → B` with `Tor₂^A(B, B) ≠ 0`. By Tag 09D6 this is the same
statement as `exists_formallyEtale_surjective_mulKernel_ne_bot`; it is the input from which the
source deduces, via the five-term exact sequence of Quillen's spectral sequence, that
`L_{B/A} ≠ 0`, which is `exists_formallyEtale_surjective_cotangentComplex_ne_zero` in
`StacksFrontier.Examples.Algebra.FormallyEtaleCotangentComplexNonzero`. -/
theorem exists_formallyEtale_surjective_not_isZero_torTwo :
    ∃ (A : Type u) (_ : CommRing A) (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.FormallyEtale A B ∧ Function.Surjective (algebraMap A B) ∧
        ¬ IsZero (((Tor' (ModuleCat.{u} A) 2).obj (ModuleCat.of A B)).obj
          (ModuleCat.of A B)) := by
  obtain ⟨A, hA, B, hB, hAlg, hAB, hsurj, z, hz⟩ :=
    exists_formallyEtale_surjective_nonzero_mulKernel
  refine ⟨A, hA, B, hB, hAlg, hAB, hsurj, fun hzero => hz ?_⟩
  have := ModuleCat.isZero_iff_subsingleton.mp
    (hzero.of_iso (Stacks.Cotangent.torTwoSelfIsoMulKernel hsurj).symm)
  exact Subsingleton.elim _ _

end Stacks.Examples

end
