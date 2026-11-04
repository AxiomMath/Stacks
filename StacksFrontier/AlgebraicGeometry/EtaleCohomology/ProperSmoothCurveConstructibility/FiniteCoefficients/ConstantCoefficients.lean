module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.QuotientCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ExtendScalarsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.TorsionExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CohomologicalBound
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of constant sheaves with finite torsion coefficients

Let `f : X ⟶ S` be a proper smooth morphism of schemes with geometrically connected fibres of
dimension at most `1`, `Λ` a Noetherian ring and `M` a finite `Λ`-module killed by an integer
`n > 0`. Then every `R^q f_* M̲` is a constructible sheaf of `Λ`-modules: [Stacks, Tag 0GKW],
deduced from the case `Λ = M = ℤ/ℓ` of [Stacks, Tag 0GKV].

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `FiniteCoefficients.isConstructibleEtaleModule_constantDirectImage_quotient`:
  `R^q f_* (Λ/ℓΛ)̲` is constructible as soon as `R^q f_* (ℤ/ℓ)̲` is, for `f` quasi-compact and
  quasi-separated.
* `FiniteCoefficients.isConstructibleEtaleModule_constantDirectImage_of_nsmul_eq_zero`:
  the same for every finite `Λ`-module killed by `ℓ`.
* `isConstructibleEtaleModule_homology_derivedDirectImage_constant`:
  **[Stacks, Tag 0GKW]**, granted [Stacks, Tag 0GKV].

## Implementation notes

The proof follows the source with one change of route. The source reduces a module `M` killed by
a prime `ℓ` to finite free `Λ/ℓΛ`-modules through a resolution and the finite cohomological
dimension of `f_*` ([Stacks, Tag 095U]), and then compares `R^q f_* (Λ/ℓΛ)̲` with
`R^q f_* (ℤ/ℓ)̲ ⊗ Λ̲` by the projection formula ([Stacks, Tag 0F0G]). Here:

* `M ↦ R^q f_* M̲` is exact on modules killed by `ℓ`, because its underlying abelian sheaf only
  depends on the underlying abelian group (`constantDirectImageForgetIso`), and short exact
  sequences of `𝔽_ℓ`-vector spaces split; so a presentation `(Λ/ℓΛ)^a → (Λ/ℓΛ)^b → M → 0` already
  computes `R^q f_* M̲` as a cokernel (`prop_map_of_nsmul_eq_zero`), with no resolution and no
  bound on the cohomological dimension;
* the comparison `R^q f_* (ℤ/ℓ)̲ ⊗_ℤ Λ̲ ≅ R^q f_* (Λ/ℓΛ)̲`
  (`isIso_zmodExtendScalarsDesc_zmodDirectImageToQuotient`) is checked on underlying abelian
  sheaves, where both sides are direct sums of copies of `R^q f_* (ℤ/ℓ)̲` indexed by an
  `𝔽_ℓ`-basis of `Λ/ℓΛ`; this uses only that `R^q f_*` commutes with direct sums ([Stacks, Tag
  09Z1]), which is the input of the projection formula the argument needs.

Constructibility of `R^q f_* (ℤ/ℓ)̲ ⊗_ℤ Λ̲` is [Stacks, Tag 0GKB] for `ℤ → Λ`.

The coefficient ring `Λ` lives in `Type (u + 1)`, the coefficient universe of the sheaves on the
small étale site of `X : Scheme.{u}`: this is the universe in which [Stacks, Tag 0GKV] is stated
(`ZMod ℓ`-modules in `ModuleCat.{u + 1}`), and the comparison of the two takes place in one
category of abelian sheaves. It is the universe at which [Stacks, Tag 0GKX] consumes the result.

## References

* [Stacks Project, Tag 0GKW](https://stacks.math.columbia.edu/tag/0GKW)
* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
* [Stacks Project, Tag 0GKB](https://stacks.math.columbia.edu/tag/0GKB)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology.FiniteCoefficients

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (n : ℕ)
  (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`R^n f_* (Λ/ℓΛ)̲` is constructible as soon as `R^n f_* (ℤ/ℓ)̲` is**: it is
`R^n f_* (ℤ/ℓ)̲ ⊗_ℤ Λ̲` (`isIso_zmodExtendScalarsDesc_zmodDirectImageToQuotient`), which is
constructible by [Stacks, Tag 0GKB]. -/
theorem isConstructibleEtaleModule_constantDirectImage_quotient
    (h : IsConstructibleEtaleModule (ZMod ℓ) (zmodDirectImage f n ℓ)) :
    IsConstructibleEtaleModule Λ ((constantDirectImage f n Λ).obj (quotientModule Λ ℓ)) := by
  have := isIso_zmodExtendScalarsDesc_zmodDirectImageToQuotient f n Λ ℓ
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (asIso (zmodExtendScalarsDesc S.smallEtaleTopology Λ ℓ (zmodDirectImage f n ℓ)
      (zmodDirectImageToQuotient f n Λ ℓ)))
    (isConstructibleEtaleModule_zmodExtendScalars _ h)

/-- **`R^n f_* M̲` is constructible for every finite `Λ`-module `M` killed by `ℓ`**, as soon as
`R^n f_* (ℤ/ℓ)̲` is. The functor `M ↦ R^n f_* M̲` is exact on modules killed by `ℓ`
(`shortExact_map_of_nsmul_eq_zero`), so a presentation of `M` by finite free `Λ/ℓΛ`-modules
reduces to `Λ/ℓΛ` (`prop_map_of_nsmul_eq_zero`). -/
theorem isConstructibleEtaleModule_constantDirectImage_of_nsmul_eq_zero
    (h : IsConstructibleEtaleModule (ZMod ℓ) (zmodDirectImage f n ℓ))
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] (hM : ∀ m : M, ℓ • m = 0) :
    IsConstructibleEtaleModule Λ ((constantDirectImage f n Λ).obj M) :=
  prop_map_of_nsmul_eq_zero.{u + 1} (constantDirectImage.{u, u + 1} f n Λ)
    (IsConstructibleEtaleModule Λ) ℓ
    (fun hS hx ↦ shortExact_map_of_nsmul_eq_zero.{u + 1, u + 1}
      (constantDirectImage.{u, u + 1} f n Λ)
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S) (constantDirectImageAb f n)
      (constantDirectImageForgetIso f n Λ) ℓ hS hx)
    (isConstructibleEtaleModule_constantDirectImage_quotient f n Λ ℓ h) M hM

variable {Λ} in
/-- The derived form of `isConstructibleEtaleModule_constantDirectImage_of_nsmul_eq_zero`:
`Rf_* M̲ ∈ D_c(S_étale, Λ)` for every finite `Λ`-module `M` killed by `ℓ`, as soon as every
`R^n f_* (ℤ/ℓ)̲` is constructible. In negative degrees there is no cohomology. -/
theorem isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero
    (h : ∀ n : ℕ, IsConstructibleEtaleModule (ZMod ℓ) (zmodDirectImage f n ℓ))
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] (hM : ∀ m : M, ℓ • m = 0) :
    IsConstructibleEtaleComplex Λ ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  intro q
  rcases lt_or_ge q 0 with hq | hq
  · have : ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).obj
        ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))).IsGE 0 :=
      etaleModuleDerivedDirectImageUnbounded_obj_isGE.{u, u + 1} Λ f _ 0
    exact (IsConstructibleEtaleModule Λ).prop_of_isZero
      (DerivedCategory.isZero_of_isGE _ 0 q hq)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact (IsConstructibleEtaleModule Λ).prop_of_iso
      ((etaleModuleDerivedDirectImageSingleHomologyIso.{u, u + 1} Λ f k).app _).symm
      (isConstructibleEtaleModule_constantDirectImage_of_nsmul_eq_zero f k Λ ℓ (h k) M hM)

variable {Λ} in
/-- **Dévissage on the torsion exponent.** If every `R^k f_* (ℤ/ℓ)̲` is constructible for every
prime `ℓ`, then `Rf_* M̲ ∈ D_c(S_étale, Λ)` for every finite `Λ`-module `M` killed by an integer
`m > 0`: for a prime `ℓ ∣ m` the short exact sequence `0 → M[ℓ] → M → M/M[ℓ] → 0` gives a
distinguished triangle, `M[ℓ]` is killed by `ℓ` and `M/M[ℓ]` by `m/ℓ`, and `D_c` is a
triangulated subcategory ([Stacks, Tag 03RZ]). -/
@[sga "4 XIV 1.11" "partial"]
theorem isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero_of_pos
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ),
      IsConstructibleEtaleModule (ZMod ℓ) (zmodDirectImage f k ℓ))
    (m : ℕ) (hm : 0 < m) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, m • x = 0) :
    IsConstructibleEtaleComplex Λ ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, u + 1} Λ X) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  induction m using Nat.strong_induction_on generalizing M with
  | _ m ih =>
  by_cases h1 : m = 1
  · subst h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero f 2 (h 2) M
      fun x ↦ by rw [show x = 0 by simpa using hM x, smul_zero]
  let ℓ := m.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hm'; omega
  have hm'lt : m' < m := (lt_mul_left hm'0 hℓ.one_lt).trans_eq hm'.symm
  let K : Submodule Λ M := LinearMap.ker ((ℓ : ℕ) • LinearMap.id)
  let E := K.mkQ.shortComplexKer
  have hS : E.ShortExact := LinearMap.shortExact_shortComplexKer K.mkQ_surjective
  have : PreservesFiniteColimits
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (etaleSiteTerminalIsTerminal X)).leftAdjoint_preservesColimits.{0, 0}.preservesFiniteColimits
  have hS' := hS.map_of_exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, u + 1} Λ f
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, u + 1} Λ f
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
    refine isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero f ℓ (h ℓ)
      (ModuleCat.of Λ (LinearMap.ker K.mkQ)) fun x ↦ Subtype.ext ?_
    have := x.2
    rwa [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  · refine ih m' hm'lt hm'0 (ModuleCat.of Λ (M ⧸ K)) fun x ↦ ?_
    obtain ⟨y, rfl⟩ := K.mkQ_surjective x
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (ℓ : ℕ) • (m' • y) = 0
    rw [← mul_nsmul', ← hm', hM]

end Stacks.EtaleCohomology.FiniteCoefficients

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0GKW], granted [Stacks, Tag 0GKV].** Let `f : X ⟶ S` be a proper smooth
morphism of schemes with geometrically connected fibres of dimension at most `1`, let `Λ` be a
Noetherian ring and `M` a finite `Λ`-module annihilated by an integer `n > 0`. Then
`R^q f_* M̲ = H^q(Rf_* M̲)` is a constructible sheaf of `Λ`-modules on `S_étale`, for every `q`.

The ring `Λ` lives in `Type (u + 1)`, the coefficient universe of the sheaves on the small étale
site of `X : Scheme.{u}`, which is where [Stacks, Tag 0GKV] (`h0GKV`) is stated; see the module
documentation. The proof does not use the hypotheses on `f` beyond quasi-compactness and
quasi-separatedness except through `h0GKV`.

`h0GKV`: [Stacks, Tag 0GKV]
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedDirectImage_zmod`).

closing step: once `isConstructibleEtaleModule_homology_derivedDirectImage_zmod` holds with no
hypotheses, remove the binder `h0GKV` in place, supply it by that theorem, and register
`` here. -/
theorem isConstructibleEtaleModule_homology_derivedDirectImage_constant
    (h0GKV : ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f],
      (∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (q : ℤ),
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
      [Module.Finite Λ M] (n : ℕ), 0 < n → (∀ m : M, n • m = 0) → ∀ q : ℤ,
      Stacks.EtaleCohomology.IsConstructibleEtaleModule Λ
        ((DerivedCategory.homologyFunctor
            (Stacks.EtaleCohomology.EtaleModules.{u, u + 1} Λ S) q).obj
          ((Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ f).obj
            ((DerivedCategory.singleFunctor
                (Stacks.EtaleCohomology.EtaleModules.{u, u + 1} Λ X) 0).obj
              ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{max (u + 1) (u + 1)} Λ)).obj M)))) := by
  intro hd Λ _ _ M _ n hn hM q
  refine FiniteCoefficients.isConstructibleEtaleComplex_derivedDirectImage_of_nsmul_eq_zero_of_pos
    f (fun ℓ _ k ↦ ?_) n hn M hM q
  exact (IsConstructibleEtaleModule (ZMod ℓ)).prop_of_iso
    ((etaleModuleDerivedDirectImageSingleHomologyIso.{u, 0} (ZMod ℓ) f k).app _)
    (h0GKV f hd ℓ k)

end Stacks.EtaleCohomology

end
