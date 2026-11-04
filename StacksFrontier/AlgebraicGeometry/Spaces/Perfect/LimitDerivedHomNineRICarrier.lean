module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomPerfectCaseBaseDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomTorBridge09RI

/-!
# Stacks 09RI from its two clauses

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact and quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`.  Stacks 09RI asserts that

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism if either (1) `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or (2) `E₀`
is pseudo-coherent and `K₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension.

This file proves that disjunction for the canonical system of derived pullbacks, for an index
type `I : Type u` with `#I < B.cutoff.ord.cof`, given the colimit statement at the structure
sheaf over the affine objects étale over `X₀`.

## Main results

* `DescentSituation.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent`:
  the disjunction of Stacks 09RI, for the canonical system of derived pullbacks.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)
  (E₀ K₀ : derivedModules B S hS (D.stage D.base))

/-- **Stacks 09RI.**  In Situation 09RH with `#I < B.cutoff.ord.cof`, if either `E₀` is perfect
and every cohomology sheaf of `K₀` is quasi-coherent, or `E₀` is pseudo-coherent, every
cohomology sheaf of `K₀` is quasi-coherent and `K₀` has finite Tor dimension relative to `T`, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective, provided `hunit`: for every affine `V` étale over `X₀`, the analogous colimit
statement holds for the structure sheaf of `V` and the pullback of `K₀` to `V`.

The colimit is taken over the canonical system of derived pullbacks of Situation 09RH, whose
comparisons come from the factorisations `f_{ji} ≫ f_{i0} = f_{j0}` and `f_i ≫ f_{i0} = f_0`. -/
theorem isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (hunit : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (_hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 →
        PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
          (smallEtaleDerivedPullbackData B S hS)
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS V.1 V.2) 0).obj
            (SheafOfModules.unit _))
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀))
    (T : Stacks.SheafOfModules.DerivedTensorProduct
      (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
    (hcase :
      ((smallEtaleRingedSite B S hS (D.stage D.base).obj
            (D.stage D.base).property).IsPerfect E₀ ∧
          ∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
              n).obj K₀).IsQuasicoherentOnSite) ∨
        ((smallEtaleRingedSite B S hS (D.stage D.base).obj
            (D.stage D.base).property).IsPseudoCoherent E₀ ∧
          (∀ n : ℤ, ((DerivedCategory.homologyFunctor
            (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property)
              n).obj K₀).IsQuasicoherentOnSite) ∧
          Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T K₀)) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  hcase.elim
    (fun hperf => (isHomColimit_canonicalDerivedPullbackSystem_iff D E₀ K₀).2
      (isColim_of_structureSheafAffineBaseChange D E₀ K₀ hperf.1 hunit))
    (isHomColimit_canonicalDerivedPullbackSystem_of_isPseudoCoherent_of_hasFiniteTorDimension
      D E₀ K₀ hI T)

end DescentSituation

end AlgebraicGeometry.Space

end
