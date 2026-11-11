module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomPerfectQcohLeaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# Stacks 09RI with the derived tensor product of the small étale site

In Situation 09RH, let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`.  Stacks 09RI asserts that

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism if either (1) `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or (2) `E₀`
is pseudo-coherent and `K₀` lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension.  Finite Tor
dimension here is read along `⊗^L_{𝒪_{X₀}}`, the derived tensor product of Stacks 06YU on the
small étale ringed site of `X₀`, `AlgebraicGeometry.Space.smallEtaleDerivedTensorProduct`.

## Main results

* **Stacks 09RI**, both clauses, in `AlgebraicGeometry.Space.DescentSituation`:
  `isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_smallEtale`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Stacks 09RI.**  In Situation 09RH, let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`, put
`E_i = Lf_{i0}^*E₀`, `K_i = Lf_{i0}^*K₀` for `i ≥ 0` and `E = Lf_0^*E₀`, `K = Lf_0^*K₀`.  If
either `E₀` is perfect and `K₀` lies in `D_QCoh(𝒪_{X₀})`, or `E₀` is pseudo-coherent and `K₀`
lies in `D_QCoh(𝒪_{X₀})` and has finite Tor dimension, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(E_i, K_i) ⟶ Hom_{D(𝒪_X)}(E, K)`

is an isomorphism.

Finite Tor dimension is read along `⊗^L_{𝒪_{X₀}}`, the derived tensor product of Stacks 06YU on
the small étale ringed site of `X₀`, `AlgebraicGeometry.Space.smallEtaleDerivedTensorProduct`.
`#I < B.cutoff.ord.cof` is the size condition under which the limit of Situation 09RH is computed
inside the bounded site, the convention of Stacks 07SD; without it the statement is refuted by
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean`. -/
@[stacks 09RI "both clauses, at the tag's own hypotheses"]
theorem isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_smallEtale
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
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
          Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
            (smallEtaleDerivedTensorProduct B S hS (D.stage D.base)) K₀)) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  D.isHomColimit_canonicalDerivedPullbackSystem_of_isPerfect_or_isPseudoCoherent_of_mk_lt_cof_ord
    E₀ K₀ hI _ hcase

end DescentSituation

end AlgebraicGeometry.Space

end
