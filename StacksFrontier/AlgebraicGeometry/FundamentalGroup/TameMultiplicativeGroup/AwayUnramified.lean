module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.RingHom.Unramified
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.BoundaryAlgebra
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.UnramifiedLocalization
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
import all StacksFrontier.RingTheory.DiscreteValuationRing.Unramified

/-!
# Unramifiedness of a cover of `𝐆_m` away from the boundary

Let `C` be a finite formally unramified `A`-algebra, `R_f = M⁻¹D` a Dedekind localization of a
domain `D` with fraction field `K''`, and `ψ : C → N` an `A`-algebra map into a field over `K''`
(with `A → R_f → N`) whose image generates `N` over `K''`. The image `S` of `R_f ⊗_A C` in `N` is a
finite formally unramified `R_f`-algebra generating `N`, so the integral closure of `R_f` in `N`
is formally unramified (it is `S`), and the integral closure of `D` in `N` is unramified at every
prime not meeting `M`.

For `D = F[s]`, `s` transcendental, and `M` the powers of `s`, this is unramifiedness at the
primes of the integral closure of `F[s]` not containing `s`, for a point of a finite étale cover of
`𝐆_m = Spec k[x]_x` over `x ↦ s^e` (or `x ↦ s^{-e}`).

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.localAway`: `F[s]_s` inside a fraction field of
  `F[s]`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.formallyUnramified_integralClosure_of_point`.
* `AlgebraicGeometry.TameMultiplicativeGroup.isUnramifiedAt_of_disjoint_of_point`.
* `AlgebraicGeometry.TameMultiplicativeGroup.isUnramifiedAt_of_cover_of_not_mem`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.TameMultiplicativeGroup

section Generic

variable {A Rf K'' N C : Type*} [CommRing A] [CommRing Rf] [Field K''] [Algebra Rf K'']
  [IsFractionRing Rf K''] [Field N] [Algebra K'' N] [Algebra Rf N] [IsScalarTower Rf K'' N]
  [CommRing C] [Algebra A C] [Algebra A Rf] [Algebra A N] [IsScalarTower A Rf N]

/-- The `R_f`-algebra map `R_f ⊗_A C → N` of an `A`-algebra map `C → N`. -/
def pointTensorLift (ψ : C →ₐ[A] N) : Rf ⊗[A] C →ₐ[Rf] N :=
  Algebra.TensorProduct.lift (Algebra.ofId Rf N) ψ fun _ _ ↦ Commute.all _ _

/-- `pointTensorLift ψ` sends `1 ⊗ₜ c` to `ψ c`. -/
theorem pointTensorLift_one_tmul (ψ : C →ₐ[A] N) (c : C) :
    pointTensorLift (Rf := Rf) ψ (1 ⊗ₜ c) = ψ c := by
  rw [pointTensorLift, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

variable [IsDedekindDomain Rf] [Module.Finite A C] [Algebra.FormallyUnramified A C]

/-- **The integral closure of `R_f` in `N` is formally unramified** when `N` is generated over
`K'' = Frac R_f` by a point of a finite formally unramified `A`-algebra. -/
theorem formallyUnramified_integralClosure_of_point (ψ : C →ₐ[A] N)
    (hψ : IntermediateField.adjoin K'' (Set.range ψ) = ⊤) :
    Algebra.FormallyUnramified Rf (integralClosure Rf N) := by
  let t := pointTensorLift (Rf := Rf) ψ
  have : Module.Finite Rf t.range :=
    Module.Finite.of_surjective t.rangeRestrict.toLinearMap t.rangeRestrict_surjective
  have : Algebra.FormallyUnramified Rf t.range :=
    Algebra.FormallyUnramified.of_surjective t.rangeRestrict t.rangeRestrict_surjective
  refine IsDiscreteValuationRing.formallyUnramified_integralClosure_of_adjoin_eq_top Rf K'' N
    t.range ?_
  rw [eq_top_iff, ← hψ]
  refine IntermediateField.adjoin.mono K'' _ _ ?_
  rintro _ ⟨c, rfl⟩
  exact ⟨1 ⊗ₜ c, pointTensorLift_one_tmul ψ c⟩

/-- **Unramified primes away from a localization.** With `R_f = M⁻¹D` as above, the integral
closure of `D` in `N` is unramified over `D` at every prime whose contraction misses `M`. -/
theorem isUnramifiedAt_of_disjoint_of_point {D : Type*} [CommRing D] [Algebra D Rf]
    [Algebra D N] [IsScalarTower D Rf N] (M : Submonoid D) (hM : ∀ m ∈ M, algebraMap D N m ≠ 0)
    [IsLocalization M Rf] (ψ : C →ₐ[A] N) (hψ : IntermediateField.adjoin K'' (Set.range ψ) = ⊤)
    (P : Ideal (integralClosure D N)) [P.IsPrime]
    (hP : Disjoint (M : Set D) (P.comap (algebraMap D (integralClosure D N)))) :
    Algebra.IsUnramifiedAt D P := by
  have := formallyUnramified_integralClosure_of_point (K'' := K'') (Rf := Rf) ψ hψ
  exact isUnramifiedAt_of_isLocalization_integralClosure (Rf := Rf) M hM P hP

end Generic

section Away

variable {F K'' : Type*} [Field F] [Field K''] [Algebra F K''] {s : K''}

/-- The generator `s` of `F[s]` is nonzero when `s` is transcendental over `F`. -/
theorem adjoinGen_ne_zero (hs : Transcendental F s) : adjoinGen F s ≠ 0 :=
  (irreducible_adjoinGen hs).ne_zero

/-- **`F[s, s⁻¹]`** as the localization of `F[s]` at the powers of `s`, inside a fraction field
`K''` of `F[s]`. -/
def localAway (hs : Transcendental F s) [IsFractionRing (Algebra.adjoin F {s}) K''] :
    Subalgebra (Algebra.adjoin F {s}) K'' :=
  Localization.subalgebra K'' (Submonoid.powers (adjoinGen F s))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (adjoinGen_ne_zero hs))

variable (hs : Transcendental F s) [IsFractionRing (Algebra.adjoin F {s}) K'']

/-- The `F[s]`-algebra structure of `F[s]_s`. -/
abbrev localAwayAlgebra : Algebra (Algebra.adjoin F {s}) (localAway hs) :=
  Subalgebra.algebra _

attribute [local instance high] localAwayAlgebra

/-- The algebra structure of a ring over `K''` over `F[s]_s`. -/
abbrev localAwayToAlgebra {B : Type*} [CommRing B] [Algebra K'' B] : Algebra (localAway hs) B :=
  Subalgebra.toAlgebra _

attribute [local instance high] localAwayToAlgebra

/-- `F[s]_s` is the localization of `F[s]` at the powers of `s`. -/
theorem isLocalization_localAway :
    IsLocalization (Submonoid.powers (adjoinGen F s)) (localAway hs) :=
  Localization.subalgebra.isLocalization_subalgebra (K := K'') _ _

/-- `K''` is a fraction field of `F[s]_s`. -/
theorem isFractionRing_localAway : IsFractionRing (localAway hs) K'' :=
  Localization.subalgebra.isFractionRing (K := K'') _ _

/-- `F[s]_s` is a Dedekind domain. -/
theorem isDedekindDomain_localAway : IsDedekindDomain (localAway hs) := by
  have := Polynomial.isPrincipalIdealRing_adjoin F hs
  have := isLocalization_localAway hs
  exact IsLocalization.isDedekindDomain (Algebra.adjoin F {s})
    (powers_le_nonZeroDivisors_of_noZeroDivisors (adjoinGen_ne_zero hs)) (localAway hs)

end Away

attribute [local instance high] localAwayAlgebra localAwayToAlgebra

/-- **A cover is unramified away from `s`.** Let `φ : A → C` be finite and formally unramified and
`ψ : C → Ω` a point over `g : A → F[s, s⁻¹]`. For `N = K''(ψ(C))`, the integral closure of `F[s]`
in `N` is unramified at every prime not containing `s`. -/
theorem isUnramifiedAt_of_cover_of_not_mem {F A C Ω : Type*} [Field F] [CommRing A] [CommRing C]
    [Field Ω] [Algebra F Ω] {K'' : IntermediateField F Ω} {s : K''} (hs : Transcendental F s)
    [IsFractionRing (Algebra.adjoin F {s}) K''] (φ : A →+* C) (hfin : φ.Finite)
    (hfu : φ.FormallyUnramified) (ψ : C →+* Ω) (g : A →+* localAway hs)
    (hg : ∀ z, ((g z : K'') : Ω) = ψ (φ z)) {N : IntermediateField K'' Ω}
    (hN : IntermediateField.adjoin K'' (Set.range ψ) = N)
    (P : Ideal (integralClosure (Algebra.adjoin F {s}) N)) [P.IsPrime]
    (hsP : algebraMap (Algebra.adjoin F {s}) (integralClosure (Algebra.adjoin F {s}) N)
      (adjoinGen F s) ∉ P) :
    Algebra.IsUnramifiedAt (Algebra.adjoin F {s}) P := by
  subst hN
  let : Algebra A C := φ.toAlgebra
  have : Module.Finite A C := hfin
  have : Algebra.FormallyUnramified A C := hfu
  let : Algebra A (localAway hs) := g.toAlgebra
  let : Algebra A (IntermediateField.adjoin K'' (Set.range ψ)) :=
    ((algebraMap (localAway hs) (IntermediateField.adjoin K'' (Set.range ψ))).comp g).toAlgebra
  let : SMul A (localAway hs) := Algebra.toSMul
  let : SMul (localAway hs) (IntermediateField.adjoin K'' (Set.range ψ)) := Algebra.toSMul
  let : SMul (Algebra.adjoin F {s}) (localAway hs) := Algebra.toSMul
  let : SMul A (IntermediateField.adjoin K'' (Set.range ψ)) := Algebra.toSMul
  have : IsScalarTower A (localAway hs) (IntermediateField.adjoin K'' (Set.range ψ)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (localAway hs) K'' (IntermediateField.adjoin K'' (Set.range ψ)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Algebra.adjoin F {s}) (localAway hs)
      (IntermediateField.adjoin K'' (Set.range ψ)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := isLocalization_localAway hs
  have := isFractionRing_localAway hs
  have := isDedekindDomain_localAway hs
  let ψN : C →ₐ[A] IntermediateField.adjoin K'' (Set.range ψ) :=
    { toFun := fun c ↦ ⟨ψ c, IntermediateField.subset_adjoin K'' _ ⟨c, rfl⟩⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul ψ _ _)
      map_zero' := Subtype.ext (map_zero ψ)
      map_add' := fun _ _ ↦ Subtype.ext (map_add ψ _ _)
      commutes' := fun z ↦ Subtype.ext (hg z).symm }
  have hψ : IntermediateField.adjoin K'' (Set.range ψN) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hmap : (IntermediateField.adjoin K'' (Set.range ψN)).map
        (IntermediateField.adjoin K'' (Set.range ψ)).val =
          IntermediateField.adjoin K'' (Set.range ψ) := by
      rw [IntermediateField.adjoin_map]
      congr 1
      exact (Set.range_comp _ _).symm
    obtain ⟨y', hy', hyy'⟩ : (y : Ω) ∈ (IntermediateField.adjoin K'' (Set.range ψN)).map
        (IntermediateField.adjoin K'' (Set.range ψ)).val := by
      rw [hmap]
      exact y.2
    rwa [← Subtype.ext hyy']
  have hM : ∀ m ∈ Submonoid.powers (adjoinGen F s),
      algebraMap (Algebra.adjoin F {s}) (IntermediateField.adjoin K'' (Set.range ψ)) m ≠ 0 := by
    rintro m ⟨n, rfl⟩ h0
    have h0' : ((adjoinGen F s ^ n : Algebra.adjoin F {s}) : K'') = 0 :=
      (algebraMap K'' (IntermediateField.adjoin K'' (Set.range ψ))).injective
        (h0.trans (map_zero _).symm)
    exact pow_ne_zero n (adjoinGen_ne_zero hs) (Subtype.ext h0')
  have hdisj : Disjoint (Submonoid.powers (adjoinGen F s) : Set (Algebra.adjoin F {s}))
      (P.comap (algebraMap (Algebra.adjoin F {s}) (integralClosure (Algebra.adjoin F {s})
        (IntermediateField.adjoin K'' (Set.range ψ))))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hmem
    exact hsP ((Ideal.comap_isPrime _ P).mem_of_pow_mem n hmem)
  exact isUnramifiedAt_of_disjoint_of_point (K'' := K'') (Rf := localAway hs) _ hM ψN hψ P hdisj

end AlgebraicGeometry.TameMultiplicativeGroup

end
