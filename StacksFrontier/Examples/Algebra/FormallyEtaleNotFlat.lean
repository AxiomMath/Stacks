module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Data.NNRat.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# A formally étale ring map which is not flat

There exists a formally étale map of commutative rings which is not flat; equivalently, a formally
étale ring map need not be of finite presentation.

The witness is the residue map of a local ring with idempotent maximal ideal. Take the group
algebra `ℚ[ℚ≥0]` of the monoid of nonnegative rationals, localize at the augmentation prime `p`,
and divide by the resulting maximal ideal `m`. Divisibility of `ℚ≥0` makes `p` — hence `m` —
idempotent, and a surjection with idempotent kernel is formally étale. The map is not flat: a flat
local homomorphism of local rings is faithfully flat, hence injective, while `m ≠ 0`.

## Main results

* `Stacks.Examples.exists_formallyEtale_not_flat`: there is a formally étale, non-flat ring map.

## Implementation notes

The map is stated as a bare ring homomorphism. Mathlib's predicates `RingHom.FormallyEtale` and
`RingHom.Flat` install the algebra structure induced by that homomorphism, so both properties refer
to the same ring map. The statement is universe polymorphic, so the construction is transported
along `ULift`.

## References

* [Stacks Project, Tag 060I](https://stacks.math.columbia.edu/tag/060I)
-/

@[expose] public section

namespace Stacks.Examples

noncomputable section

open AddMonoidAlgebra

private abbrev nnratMonoid := ℚ≥0

private abbrev nnratGroupAlgebra := AddMonoidAlgebra ℚ nnratMonoid

private def castNNRat : nnratMonoid →ₙ+ ℚ where
  toFun := NNRat.cast
  map_add' := by intros; simp

private theorem uniqueSums_nnratMonoid : UniqueSums nnratMonoid :=
  UniqueSums.of_injective_addHom castNNRat (by exact NNRat.coe_injective)
    (inferInstance : UniqueSums ℚ)

private theorem isDomain_nnratGroupAlgebra : IsDomain nnratGroupAlgebra := by
  let : UniqueSums nnratMonoid := uniqueSums_nnratMonoid
  infer_instance

private theorem eq_zero_of_add_eq_zero {a b : nnratMonoid} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  have h' : (a : ℚ) + (b : ℚ) = 0 := congrArg NNRat.cast h
  have hz := (add_eq_zero_iff_of_nonneg a.2 b.2).mp h'
  exact ⟨Subtype.ext hz.1, Subtype.ext hz.2⟩

private def augmentation : nnratGroupAlgebra →+* ℚ where
  toFun x := x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp
  map_mul' x y := by
    have hu : UniqueAdd x.coeff.support y.coeff.support 0 0 := by
      intro a b ha hb hab
      have hz := eq_zero_of_add_eq_zero (by simpa using hab)
      exact ⟨hz.1, hz.2⟩
    simpa using (AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu)

private theorem single_mem_augmentation_ker (q : nnratMonoid) (hq : q ≠ 0) (c : ℚ) :
    AddMonoidAlgebra.single q c ∈ RingHom.ker augmentation := by
  change (AddMonoidAlgebra.single q c).coeff 0 = 0
  simp [AddMonoidAlgebra.coeff_single, hq]

private theorem augmentation_ker_idempotent :
    RingHom.ker augmentation * RingHom.ker augmentation = RingHom.ker augmentation := by
  refine le_antisymm Ideal.mul_le_left fun x hx => ?_
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x]
  refine Submodule.sum_mem _ fun q hq => ?_
  have hx0 : x.coeff 0 = 0 := hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact Finsupp.mem_support_iff.mp hq (by simpa using hx0)
  have hq' : q / 2 ≠ 0 := div_ne_zero hq0 (by norm_num)
  rw [show AddMonoidAlgebra.single q (x.coeff q) =
      AddMonoidAlgebra.single (q / 2) 1 * AddMonoidAlgebra.single (q / 2) (x.coeff q) by
    rw [AddMonoidAlgebra.single_mul_single, one_mul, add_halves]]
  exact Ideal.mul_mem_mul (single_mem_augmentation_ker _ hq' 1)
    (single_mem_augmentation_ker _ hq' _)

private theorem exists_base_formallyEtale_residue :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
      (S : Type) (_ : CommRing S) (_ : IsLocalRing S)
      (f : R →+* S) (_ : IsLocalHom f) (_ : Function.Surjective f) (x : R),
      f.FormallyEtale ∧ x ≠ 0 ∧ f x = 0 := by
  have : IsDomain nnratGroupAlgebra := isDomain_nnratGroupAlgebra
  let p : Ideal nnratGroupAlgebra := RingHom.ker augmentation
  have : p.IsPrime := RingHom.ker_isPrime augmentation
  let R := Localization.AtPrime p
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let S := R ⧸ m
  have : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let : Field S := Ideal.Quotient.field m
  let f : R →+* S := Ideal.Quotient.mk m
  let : Algebra R S := f.toAlgebra
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have : IsLocalHom f := IsLocalHom.of_surjective f hsurj
  have hmap : p.map (algebraMap nnratGroupAlgebra R) = m :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p R
  have hm : m * m = m := by
    rw [← hmap, ← Ideal.map_mul, augmentation_ker_idempotent]
  have hFE : Algebra.FormallyEtale R S := by
    rwa [Algebra.FormallyEtale.iff_of_surjective
      (show Function.Surjective (algebraMap R S) from hsurj), RingHom.algebraMap_toAlgebra,
      Ideal.mk_ker]
  let z : nnratGroupAlgebra := AddMonoidAlgebra.single (1 : nnratMonoid) (1 : ℚ)
  have hzbase : z ≠ 0 := by simp [z]
  have hzloc : algebraMap nnratGroupAlgebra R z ∈ m := by
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ (single_mem_augmentation_ker 1 (by norm_num) 1)
  have hzlocne : algebraMap nnratGroupAlgebra R z ≠ 0 := fun h =>
    hzbase (IsLocalization.injective R p.primeCompl_le_nonZeroDivisors (by simpa using h))
  exact ⟨R, inferInstance, inferInstance, S, inferInstance, inferInstance,
    f, inferInstance, hsurj, algebraMap nnratGroupAlgebra R z, hFE, hzlocne,
    Ideal.Quotient.eq_zero_iff_mem.mpr hzloc⟩

private theorem formallyEtale_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) : f.FormallyEtale := by
  let : Algebra R S := f.toAlgebra
  change Algebra.FormallyEtale R S
  rw [Algebra.FormallyEtale.iff_of_surjective hf.2, RingHom.algebraMap_toAlgebra,
    (RingHom.injective_iff_ker_eq_bot f).mp hf.1]
  simp [IsIdempotentElem]

private theorem not_flat_of_flat_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] {x : R}
    (hx : x ≠ 0) (hfx : f x = 0) : ¬ f.Flat := by
  intro hflat
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hflat
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  exact hx (FaithfulSMul.algebraMap_injective R S (by rwa [map_zero]))

private theorem exists_formallyEtale_notFlat.{u, v} :
    ∃ (R : Type u) (S : Type v) (_ : CommRing R) (_ : CommRing S)
      (f : R →+* S), f.FormallyEtale ∧ ¬ f.Flat := by
  obtain ⟨R₀, hRring, hRlocal, S₀, hSring, hSlocal, f₀, hflocal, hfsurj,
      x₀, hf₀, hx₀, hfx₀⟩ := exists_base_formallyEtale_residue
  let R := ULift.{u, 0} R₀
  let S := ULift.{v, 0} S₀
  let eR : R ≃+* R₀ := ULift.ringEquiv (R := R₀)
  let eS : S ≃+* S₀ := ULift.ringEquiv (R := S₀)
  have : IsLocalRing R := eR.symm.isLocalRing
  have : IsLocalRing S := eS.symm.isLocalRing
  let f : R →+* S := eS.symm.toRingHom.comp (f₀.comp eR.toRingHom)
  have hsurj : Function.Surjective f := eS.symm.surjective.comp (hfsurj.comp eR.surjective)
  have : IsLocalHom f := IsLocalHom.of_surjective f hsurj
  have hform : f.FormallyEtale := ((formallyEtale_of_bijective _ eR.bijective).comp hf₀).comp
    (formallyEtale_of_bijective _ eS.symm.bijective)
  have hxf : f (eR.symm x₀) = 0 := by simp [f, hfx₀]
  exact ⟨R, S, inferInstance, inferInstance, f, hform,
    not_flat_of_flat_isLocalHom f (eR.symm.map_ne_zero_iff.mpr hx₀) hxf⟩

end

/-- There exists a formally étale map of commutative rings which is not flat. -/
@[stacks 060I]
public theorem exists_formallyEtale_not_flat :
    ∃ (R S : Type*) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
      f.FormallyEtale ∧ ¬ f.Flat := exists_formallyEtale_notFlat

end Stacks.Examples

end
