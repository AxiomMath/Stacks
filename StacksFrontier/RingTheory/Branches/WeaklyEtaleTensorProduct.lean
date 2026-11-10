module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingChartHenselization
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.Branches.Miscellaneous
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.StrictlyHenselian

/-!
# Minimal primes of a strictly henselian weakly étale algebra over a tensor product

Let `k` be an algebraically closed field and let `A`, `B` be strictly henselian local
`k`-algebras with residue field `k`. This file recognises a strict henselization of the
localization of `A ⊗[k] B` at the maximal ideal `𝔪_A ⊗ B + A ⊗ 𝔪_B` without constructing one:
any strictly henselian local ring `C` together with a weakly étale homomorphism
`A ⊗[k] B → C` that is local on both factors is such a strict henselization, so the
classification of minimal primes of [Stacks Project, Tag 06DU] applies to `C`.

## Main results

* `IsLocalRing.IsHenselization.of_weaklyEtale`: a strictly henselian local ring which is a local
  weakly étale algebra over a local ring `R` is a strict henselization of `R`.
* `minimalPrimes_bijOn_of_weaklyEtale_tensorProduct`: [Stacks Project, Tag 06DU] for a strictly
  henselian local ring `C` with a weakly étale homomorphism `φ : A ⊗[k] B → C` local on both
  factors: contracting along `φ` restricted to the two factors is a bijection from the minimal
  primes of `C` onto the pairs of minimal primes of `A` and `B`, and every minimal prime of `C` is
  the smallest prime containing the images of its two contractions.

## References

* [Stacks Project, Tag 06DU](https://stacks.math.columbia.edu/tag/06DU)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 092L](https://stacks.math.columbia.edu/tag/092L)
* [Stacks Project, Tag 092Z](https://stacks.math.columbia.edu/tag/092Z)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace IsLocalRing.IsHenselization

/-- **A strictly henselian weakly étale local algebra is a strict henselization.** Let `R` be a
local ring and let `C` be a strictly henselian local ring which is a weakly étale `R`-algebra
through a local homomorphism. Then `C` is a strict henselization of `R`. -/
theorem of_weaklyEtale {R : Type u} {C : Type v} [CommRing R] [IsLocalRing R] [CommRing C]
    [HenselianLocalRing C] [IsSepClosed (ResidueField C)] [Algebra R C]
    [IsLocalHom (algebraMap R C)] [Algebra.WeaklyEtale R C] :
    IsHenselization R (SeparableClosure (ResidueField R)) C := by
  let T := IsLocalRing.henselizationTower R (SeparableClosure (ResidueField R))
  have : IsHenselization C (ResidueField C) C := isHenselization_self C
  obtain ⟨ψ, hψloc, hψ⟩ := exists_isLocalHom_comp_of_isSepClosure (algebraMap R C)
    (κA := SeparableClosure (ResidueField R)) (κA' := ResidueField C)
    (Ash := T.strictHenselization) (A'sh := C)
  let : Algebra T.strictHenselization C := ψ.toAlgebra
  have : IsScalarTower R T.strictHenselization C :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (RingHom.congr_fun hψ r).symm
  have hRT : Algebra.WeaklyEtale R T.strictHenselization :=
    Algebra.weaklyEtale_of_ind_etale
      (StacksDraft.indEtale_of_isHenselization (SeparableClosure (ResidueField R)))
  have hTC : Algebra.WeaklyEtale T.strictHenselization C :=
    weaklyEtale_of_comp R T.strictHenselization C hRT inferInstance
  have : IsLocalHom (algebraMap T.strictHenselization C) := hψloc
  have hbij := bijective_algebraMap_of_weaklyEtale_of_isLocalHom T.strictHenselization C hTC
  exact of_ringEquiv (RingEquiv.ofBijective ψ hbij) fun r ↦ RingHom.congr_fun hψ r

end IsLocalRing.IsHenselization

/-- A `k`-algebra map `res : A → k` with kernel the maximal ideal, composed with a local
homomorphism `f` out of `A` over `g : k → C`, is computed on residue classes by `g ∘ res`. -/
private theorem residue_apply_eq_of_ker_eq_maximalIdeal {k A C : Type*} [Field k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [CommRing C] [IsLocalRing C] (res : A →ₐ[k] k)
    (hres : RingHom.ker res.toRingHom = maximalIdeal A) (f : A →+* C) [IsLocalHom f]
    (g : k →+* C) (hfg : ∀ c, f (algebraMap k A c) = g c) (a : A) :
    residue C (f a) = residue C (g (res a)) := by
  have hmem : a - algebraMap k A (res a) ∈ maximalIdeal A := by
    rw [← hres, RingHom.mem_ker]
    change res (a - algebraMap k A (res a)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have h0 := (residue_eq_zero_iff _).mpr (map_nonunit f _ hmem)
  rw [map_sub, map_sub, hfg, sub_eq_zero] at h0
  exact h0

/-- **Stacks 06DU at a weakly étale strictly henselian algebra.** Let `k` be an algebraically
closed field, let `A` and `B` be strictly henselian local `k`-algebras whose residue fields are
identified with `k` by the `k`-algebra maps `resA` and `resB`, and let `C` be a strictly henselian
local ring with a weakly étale homomorphism `φ : A ⊗[k] B → C` which is local on both factors.
Then contracting along the two restrictions of `φ` is a bijection from the minimal primes of `C`
onto the pairs of a minimal prime of `A` and a minimal prime of `B`, and every minimal prime of
`C` is the smallest prime containing the images of its two contractions. -/
theorem minimalPrimes_bijOn_of_weaklyEtale_tensorProduct
    (k A B : Type u) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    [CommRing B] [Algebra k B] [HenselianLocalRing B] [IsSepClosed (ResidueField B)]
    (resA : A →ₐ[k] k) (resB : B →ₐ[k] k)
    (hresA : RingHom.ker resA.toRingHom = maximalIdeal A)
    (hresB : RingHom.ker resB.toRingHom = maximalIdeal B)
    (C : Type u) [CommRing C] [HenselianLocalRing C] [IsSepClosed (ResidueField C)]
    (φ : A ⊗[k] B →+* C) (hφ : @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra)
    (hA : IsLocalHom (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom))
    (hB : IsLocalHom
      (φ.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom)) :
    Set.BijOn
        (fun q : Ideal C ↦
          (q.comap (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom),
           q.comap (φ.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom)))
        (minimalPrimes C) ((minimalPrimes A) ×ˢ (minimalPrimes B)) ∧
      ∀ q ∈ minimalPrimes C, ∀ P : Ideal C, P.IsPrime →
        (q.comap (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom)).map
            (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom) ≤ P →
        (q.comap (φ.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom)).map
            (φ.comp (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom) ≤ P →
        q ≤ P := by
  classical
  let D := A ⊗[k] B
  let iA := (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
  let iB := (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
  let L := Algebra.TensorProduct.lift resA resB (fun _ _ ↦ Commute.all _ _)
  let M := Submonoid.comap L.toRingHom (nonZeroDivisors k)
  let χ : k →+* ResidueField C := (residue C).comp (φ.comp (algebraMap k D))
  have hleft : ∀ a : A, residue C (φ (iA a)) = χ (resA a) := fun a ↦
    residue_apply_eq_of_ker_eq_maximalIdeal resA hresA (φ.comp iA) (φ.comp (algebraMap k D))
      (fun c ↦ congrArg φ (Algebra.TensorProduct.includeLeft.commutes c)) a
  have hright : ∀ b : B, residue C (φ (iB b)) = χ (resB b) := fun b ↦
    residue_apply_eq_of_ker_eq_maximalIdeal resB hresB (φ.comp iB) (φ.comp (algebraMap k D))
      (fun c ↦ congrArg φ (Algebra.TensorProduct.includeRight.commutes c)) b
  have hres : ∀ d : D, residue C (φ d) = χ (L d) := by
    intro d
    induction d using TensorProduct.inductionOn with
    | tmul a b =>
      have hab : (a ⊗ₜ[k] b : D) = iA a * iB b := by
        change a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hab, map_mul, map_mul, hleft, hright, map_mul, ← map_mul]
      congr 1
      change resA a * resB b = L (a ⊗ₜ[k] 1) * L (1 ⊗ₜ[k] b)
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one,
        mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hunit : ∀ d : D, L d ≠ 0 → IsUnit (φ d) := by
    intro d hd
    rwa [← residue_ne_zero_iff_isUnit, hres, map_ne_zero χ]
  have hzero : ∀ d : D, L d = 0 → φ d ∈ maximalIdeal C := by
    intro d hd
    rw [← residue_eq_zero_iff, hres, hd, map_zero]
  let P : Ideal D := RingHom.ker L.toRingHom
  have : P.IsPrime := RingHom.ker_isPrime _
  have hMP : M = P.primeCompl := by
    ext d
    change L d ∈ nonZeroDivisors k ↔ d ∉ RingHom.ker L.toRingHom
    rw [mem_nonZeroDivisors_iff_ne_zero, RingHom.mem_ker]
    rfl
  let R := Localization M
  have : IsLocalization.AtPrime R P := by
    change IsLocalization P.primeCompl R
    rw [← hMP]
    infer_instance
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R P
  have hMunit : ∀ m : M, IsUnit (φ m) := fun m ↦ hunit m (mem_nonZeroDivisors_iff_ne_zero.mp m.2)
  let ψ : R →+* C := IsLocalization.lift hMunit
  let : Algebra R C := ψ.toAlgebra
  let : Algebra D C := φ.toAlgebra
  have hψφ : ψ.comp (algebraMap D R) = φ := IsLocalization.lift_comp hMunit
  have : IsScalarTower D R C :=
    IsScalarTower.of_algebraMap_eq fun d ↦ (RingHom.congr_fun hψφ d).symm
  have : IsLocalHom (algebraMap R C) := by
    refine ⟨fun x hx ↦ ?_⟩
    obtain ⟨⟨d, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    have hx' : IsUnit (ψ (IsLocalization.mk' R d m)) := hx
    rw [IsLocalization.lift_mk'] at hx'
    have hd : IsUnit (φ d) := (IsUnit.mul_iff.mp hx').1
    exact IsUnit.of_mul_eq_one _ (IsLocalization.mk'_mul_mk'_eq_one' (S := R) d m
      (mem_nonZeroDivisors_iff_ne_zero.mpr fun h ↦ (mem_maximalIdeal _).mp (hzero d h) hd))
  have hDR : Algebra.WeaklyEtale D R :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, u, u} D).1 R M
  have : Algebra.WeaklyEtale R C := weaklyEtale_of_comp D R C hDR hφ
  have : IsHenselization R (SeparableClosure (ResidueField R)) C :=
    IsHenselization.of_weaklyEtale
  have hcomp : ∀ {X : Type u} [CommRing X] (f : X →+* D),
      (algebraMap R C).comp ((algebraMap D R).comp f) = φ.comp f :=
    fun f ↦ by rw [← RingHom.comp_assoc]; exact congrArg (fun g ↦ g.comp f) hψφ
  have hbij := minimalPrimes_strictHenselization_tensorProduct_bijOn k A B resA resB hresA hresB
    R C (SeparableClosure (ResidueField R))
  rw [hcomp, hcomp] at hbij
  refine ⟨hbij, fun q hq Q _ hQA hQB ↦ ?_⟩
  have hsup := minimalPrimes_localized_tensorProduct_eq_sup k A B resA resB hresA hresB R C
    (SeparableClosure (ResidueField R)) q hq
  rw [hcomp, hcomp] at hsup
  exact hsup.le.trans (sup_le hQA hQB)

end
