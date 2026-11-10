module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramified primes of an integral closure from a localization of the base

Let `D` be a domain with a field `N` over it, `M ⊆ D` a multiplicative set of elements nonzero
in `N`, and `R_f = M⁻¹D`. Taking integral closures commutes with localization, so the integral
closure of `R_f` in `N` is the localization of the integral closure `B` of `D` in `N` at `M`. If it
is formally unramified over `R_f`, then `B` is unramified over `D` at every prime not meeting `M`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.isUnramifiedAt_of_isLocalization_integralClosure`:
  `B` is unramified over `D` at every prime not meeting `M`.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable {D N Rf : Type*} [CommRing D] [Field N] [Algebra D N] [CommRing Rf] [Algebra D Rf]
  [Algebra Rf N] [IsScalarTower D Rf N]

variable (D N Rf) in
/-- The integral closure of `D` in `N` is contained in the integral closure of `R_f` in `N`. -/
theorem integralClosure_toSubring_le :
    (integralClosure D N).toSubring ≤ (integralClosure Rf N).toSubring :=
  fun _ hx ↦ (hx : _root_.IsIntegral D _).tower_top

variable (D N Rf) in
/-- The inclusion of the integral closure of `D` into that of `R_f`, as an algebra. -/
abbrev integralClosureAlgebra : Algebra (integralClosure D N) (integralClosure Rf N) :=
  (Subring.inclusion (integralClosure_toSubring_le D N Rf)).toAlgebra

/-- **Unramified primes from a localization of the base.** If the integral closure of a
localization `R_f = M⁻¹D` in `N` is formally unramified over `R_f`, then the integral closure of
`D` in `N` is unramified over `D` at every prime whose contraction does not meet `M`. -/
theorem isUnramifiedAt_of_isLocalization_integralClosure (M : Submonoid D)
    (hM : ∀ m ∈ M, algebraMap D N m ≠ 0) [IsLocalization M Rf]
    [Algebra.FormallyUnramified Rf (integralClosure Rf N)]
    (P : Ideal (integralClosure D N)) [P.IsPrime]
    (hP : Disjoint (M : Set D) (P.comap (algebraMap D (integralClosure D N)))) :
    Algebra.IsUnramifiedAt D P := by
  let : Algebra (integralClosure D N) (integralClosure Rf N) := integralClosureAlgebra D N Rf
  have : IsScalarTower (integralClosure D N) (integralClosure Rf N) N :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower D (integralClosure D N) (integralClosure Rf N) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext (by
      change algebraMap (integralClosure Rf N) N (algebraMap D (integralClosure Rf N) x) =
        algebraMap D N x
      exact (IsScalarTower.algebraMap_apply D (integralClosure Rf N) N x).symm)
  have : IsLocalization (Algebra.algebraMapSubmonoid N M) N :=
    IsLocalization.of_le_isUnit fun _ ⟨m, hm, hx⟩ ↦ hx ▸ (hM m hm).isUnit
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure D N) M)
      (integralClosure Rf N) :=
    IsLocalization.integralClosure (R := D) (S := N) (Rf := Rf) (Sf := N) M
  have : Algebra.FormallyUnramified D Rf := Algebra.FormallyUnramified.of_isLocalization M
  have : Algebra.FormallyUnramified D (integralClosure Rf N) :=
    Algebra.FormallyUnramified.comp D Rf (integralClosure Rf N)
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid (integralClosure D N) M :
      Set (integralClosure D N)) (P : Set (integralClosure D N)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩
    exact Set.disjoint_left.mp hP hm
  have hQ : (P.map (algebraMap (integralClosure D N) (integralClosure Rf N))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid _ M) _ P ‹_› hdisj
  have hcomap : (P.map (algebraMap (integralClosure D N) (integralClosure Rf N))).comap
      (algebraMap (integralClosure D N) (integralClosure Rf N)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid _ M) _ ‹_› hdisj
  have hQur : Algebra.IsUnramifiedAt D
      (P.map (algebraMap (integralClosure D N) (integralClosure Rf N))) :=
    (Algebra.formallyUnramified_iff_forall.mp ‹_›) ⟨_, hQ⟩
  have : IsLocalization.AtPrime (Localization.AtPrime
      (P.map (algebraMap (integralClosure D N) (integralClosure Rf N))))
      ((P.map (algebraMap (integralClosure D N) (integralClosure Rf N))).comap
        (algebraMap (integralClosure D N) (integralClosure Rf N))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid _ M) _ _
  have hsub : ((P.map (algebraMap (integralClosure D N) (integralClosure Rf N))).comap
      (algebraMap (integralClosure D N) (integralClosure Rf N))).primeCompl = P.primeCompl := by
    ext x
    change x ∉ _ ↔ x ∉ _
    rw [hcomap]
  have h1 : IsLocalization P.primeCompl
      (Localization.AtPrime (P.map (algebraMap (integralClosure D N) (integralClosure Rf N)))) :=
    hsub ▸ this
  let e : Localization.AtPrime P ≃ₐ[integralClosure D N] Localization.AtPrime
      (P.map (algebraMap (integralClosure D N) (integralClosure Rf N))) :=
    IsLocalization.algEquiv P.primeCompl _ _
  exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars D).symm

end AlgebraicGeometry.TameMultiplicativeGroup

end
