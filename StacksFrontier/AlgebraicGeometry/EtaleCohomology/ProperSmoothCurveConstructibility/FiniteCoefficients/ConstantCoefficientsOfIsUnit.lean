module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.Scheme.IsUnitNatCastDvd
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibility of `Rf_* M̲` for a torsion exponent invertible on the base

The forms of `isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero_of_pos` (in
`Stacks.EtaleCohomology.FiniteCoefficients`) and
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_constant`
([Stacks, Tag 0GKW]) which ask for the constructibility of `R^k f_* (ℤ/ℓ)̲` only at the primes `ℓ`
dividing the exponent `n` of the coefficient module, and hence, for `n` invertible on `S`, need
[Stacks, Tag 0GKV] only at primes invertible on the base.

## Main results

* `isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero_of_pos_of_dvd`, in
  `Stacks.EtaleCohomology.FiniteCoefficients`.
* `isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit`, in
  `Stacks.EtaleCohomology`.

## References

* [Stacks Project, Tag 0GKW](https://stacks.math.columbia.edu/tag/0GKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology.FiniteCoefficients

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

variable {Λ} in
/-- **Dévissage on the torsion exponent.** If `R^k f_* (ℤ/ℓ)̲` is constructible for every prime
`ℓ ∣ m`, then `Rf_* M̲ ∈ D_c(S_étale, Λ)` for every finite `Λ`-module `M` killed by the integer
`m > 0`: for a prime `ℓ ∣ m` the short exact sequence `0 → M[ℓ] → M → M/M[ℓ] → 0` gives a
distinguished triangle, `M[ℓ]` is killed by `ℓ` and `M/M[ℓ]` by `m/ℓ`, and `D_c` is a
triangulated subcategory ([Stacks, Tag 03RZ]). For `m = 1` the module is zero. -/
@[sga "4 XIV 1.11" "more general"]
theorem isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero_of_pos_of_dvd (m : ℕ)
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ m → ∀ (k : ℕ),
      IsConstructibleEtaleModule (ZMod ℓ) (zmodDirectImage f k ℓ))
    (hm : 0 < m) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, m • x = 0) :
    IsConstructibleEtaleComplex Λ ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  induction m using Nat.strong_induction_on generalizing M with
  | _ m ih =>
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, u + 1} Λ f
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, u + 1} Λ f
  by_cases h1 : m = 1
  · subst h1
    have : Subsingleton M := ⟨fun x y ↦ by
      rw [show x = 0 by simpa using hM x, show y = 0 by simpa using hM y]⟩
    have hz := (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).map_isZero
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).map_isZero
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_isZero
          (ModuleCat.isZero_of_subsingleton M)))
    exact fun q ↦ (IsConstructibleEtaleModule Λ).prop_of_isZero
      ((DerivedCategory.homologyFunctor _ q).map_isZero hz)
  let ℓ := m.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hm'lt : m' < m := (lt_mul_left hm'0 hℓ.one_lt).trans_eq hm'.symm
  let K : Submodule Λ M := LinearMap.ker ((ℓ : ℕ) • LinearMap.id)
  let E := K.mkQ.shortComplexKer
  have hS : E.ShortExact := LinearMap.shortExact_shortComplexKer K.mkQ_surjective
  have : PreservesFiniteColimits
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (etaleSiteTerminalIsTerminal X)).leftAdjoint_preservesColimits.{0, 0}.preservesFiniteColimits
  have hS' := hS.map_of_exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have hT := (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).map_distinguished _
    hS'.singleTriangle_distinguished
  have : (IsConstructibleEtaleComplex Λ (X := S)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _)
  have : (IsConstructibleEtaleComplex Λ (X := S)).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _)
  refine (IsConstructibleEtaleComplex Λ).ext_of_isTriangulatedClosed₂ _ hT ?_ ?_
  · have : Module.Finite Λ (LinearMap.ker K.mkQ) :=
      Module.IsNoetherian.finite Λ (LinearMap.ker K.mkQ)
    refine isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero f ℓ
      (h ℓ (Nat.minFac_dvd m)) (ModuleCat.of Λ (LinearMap.ker K.mkQ)) fun x ↦ Subtype.ext ?_
    have := x.2
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · refine ih m' hm'lt (fun ℓ' _ hℓ' k ↦ h ℓ' (hℓ'.trans ⟨ℓ, by rw [hm', mul_comm]⟩) k) hm'0
      (ModuleCat.of Λ (M ⧸ K)) fun x ↦ ?_
    obtain ⟨y, rfl⟩ := K.mkQ_surjective x
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (ℓ : ℕ) • (m' • y) = 0
    rw [← mul_nsmul', ← hm', hM]

end Stacks.EtaleCohomology.FiniteCoefficients

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0GKW] for `n` invertible on `S`, granted [Stacks, Tag 0GKV] for primes
invertible on the base.** Let `f : X ⟶ S` be a proper smooth morphism of schemes with
geometrically connected fibres of dimension at most `1`, let `Λ` be a Noetherian ring and `M` a
finite `Λ`-module annihilated by an integer `n > 0` invertible on `S`. Then
`R^q f_* M̲ = H^q(Rf_* M̲)` is a constructible sheaf of `Λ`-modules on `S_étale`, for every `q`.

The ring `Λ` lives in `Type (u + 1)`, the coefficient universe of the sheaves on the small étale
site of `X : Scheme.{u}`, which is where [Stacks, Tag 0GKV] (`h0GKV`) is stated; see the module
documentation. The proof does not use the hypotheses on `f` beyond quasi-compactness and
quasi-separatedness except through `h0GKV`.

`h0GKV`: [Stacks, Tag 0GKV]
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit`),
needed only at the primes dividing `n`, which are invertible on `S`.

closing step: once `isConstructibleEtaleModule_homology_derivedDirectImage_zmod` holds with no
hypotheses, remove the binder `h0GKV` in place, supply it by that theorem, and register
`@[stacks 0GKW]` here. -/
theorem isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isUnit
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) → ∀ (q : ℤ),
        Stacks.EtaleCohomology.IsConstructibleEtaleModule (ZMod ℓ)
          ((DerivedCategory.homologyFunctor
              (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
            ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
              ((DerivedCategory.singleFunctor
                  (Stacks.EtaleCohomology.EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
                  (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f] :
    (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
    ∀ (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
      (M : ModuleCat.{max (u + 1) (u + 1)} Λ)
      [Module.Finite Λ M] (n : ℕ), 0 < n → (∀ m : M, n • m = 0) →
      IsUnit ((n : ℕ) : Γ(S, ⊤)) → ∀ q : ℤ,
      Stacks.EtaleCohomology.IsConstructibleEtaleModule Λ
        ((DerivedCategory.homologyFunctor
            (Stacks.EtaleCohomology.EtaleModules.{u, u + 1} Λ S) q).obj
          ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).obj
            ((DerivedCategory.singleFunctor
                (Stacks.EtaleCohomology.EtaleModules.{u, u + 1} Λ X) 0).obj
              ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{max (u + 1) (u + 1)} Λ)).obj M)))) := by
  intro hd Λ _ _ M _ n hn hM hnS q
  refine
    FiniteCoefficients.isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero_of_pos_of_dvd
    f n (fun ℓ _ hℓ k ↦ ?_) hn M hM q
  exact (IsConstructibleEtaleModule (ZMod ℓ)).prop_of_iso
    ((etaleModuleDerivedDirectImageSingleHomologyIso.{u, 0} (ZMod ℓ) f k).app _)
    (h0GKV f hd ℓ (isUnit_natCast_of_dvd hℓ hnS) k)

end Stacks.EtaleCohomology

end
