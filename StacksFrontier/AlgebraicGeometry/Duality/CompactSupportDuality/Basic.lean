module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.OpenDuality
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Duality for compactly supported cohomology

Let `k` be a field, `p : U ⟶ Spec k` separated of finite type and `ω_{U/k}^• = p^!𝒪_{Spec k}`.
[Stacks, Tag 0G5A] gives canonical isomorphisms of topological `k`-vector spaces

`Hom_k(H^i(U, K), k) = H^{-i}_c(U, R𝓗om(K, ω_{U/k}^•))`

functorial in `K ∈ D^b_{Coh}(𝒪_U)`.

## Main definitions

* `AlgebraicGeometry.compactSupportDualityLinearEquiv`: the `k`-linear isomorphism.
* `AlgebraicGeometry.compactSupportDualityEquiv`: **[Stacks, Tag 0G5A]**, the isomorphism of
  topological `k`-vector spaces.

## Main results

* `AlgebraicGeometry.compactSupportDualityEquiv_naturality`: **[Stacks, Tag 0G5A]**, its
  functoriality in `K`.

## Conventions

* `H^i(U, K)` is the hypercohomology `H^i(RΓ(U, K))` of the `k`-linear derived global sections
  `AlgebraicGeometry.derivedGlobalSectionsOver p`, as in [Stacks, Tag 0FVV] part (5).
* `p^!` is `Stacks.Duality.upperShriek` of [Stacks, Tag 0A9Y] at a compactification `c` of `U`,
  and `ω_{U/k}^•` is `AlgebraicGeometry.standardUpperShriekDualizingComplex p c`; `H^i_c` is
  `AlgebraicGeometry.compactSupportCohomology c`, Section 0G59's `lim_n H^i(X, K_n)`, with its
  limit topology. The statement holds for every compactification `c`; one exists by
  [Stacks, Tag 0F41].
* `R𝓗om(K, ω_{U/k}^•)` is `AlgebraicGeometry.openDualObj`, whose underlying object is
  `AlgebraicGeometry.RingedSite.derivedDualInto`.
* `Hom_k(V, k)` carries the topology of pointwise convergence, `Module.Dual.limitTopology`,
  which is the limit topology over the finite-dimensional subspaces of [Stacks, Section 0G59]
  (`Module.Dual.limitTopology_eq_iInf_finiteDimensional`).
* The derived categories `D(𝒪_U)` and `D(k)` are at `CategoryTheory.HasDerivedCategory.standard`,
  the model of `AlgebraicGeometry.BoundedCoherentDerived`,
  `AlgebraicGeometry.compactSupportCohomology` and `AlgebraicGeometry.openDualObj`; it is named in
  the statements by `letI`, inlined at elaboration.

## The proof

`D_U = R𝓗om(-, ω_U^•)` is an anti-equivalence of `D^b_{Coh}(𝒪_U)` ([Stacks, Tag 0A89]), so
`H^i(U, K) = Hom(𝒪_U, K[i]) = Hom((D_U K)[-i], ω_U^•)`, and `ω_U^• = ω_X^•|_U`; by
[Stacks, Tag 0G2H] this is `colim_n Hom_X(L_n, ω_X^•)` for the Deligne system `(L_n)` of
`(D_U K)[-i]`; by [Stacks, Tag 0FVV] part (5) each term is `Hom_X(𝒪_X, L_n)^∨`, finite
dimensional ([Stacks, Tag 0D0D]); dualizing gives `lim_n Hom_X(𝒪_X, L_n) = H^{-i}_c`.
This avoids the evaluation morphism of [Stacks, Tag 0G4I] and [Stacks, Tag 0G4U] used by the
source, which works with an extension of `K` to `X` instead of `D_U K`.

## References

* [Stacks Project, Tag 0G5A](https://stacks.math.columbia.edu/tag/0G5A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Duality

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of k))
  [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] (c : CompactificationOf (Over.mk p))

/-- **The `k`-linear duality isomorphism of [Stacks, Tag 0G5A]**
`Hom_k(H^i(U, K), k) ≃ H^{-i}_c(U, R𝓗om(K, ω_{U/k}^•))`, for the compactification `c` at which
`p^!` and `H^*_c` are computed. -/
def compactSupportDualityLinearEquiv (K : BoundedCoherentDerived U) (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    haveI := isNoetherian_of_locallyOfFiniteType p
    Module.Dual k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj)) ≃ₗ[k]
      compactSupportCohomology c
        (openDualObj (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) K) (-i) :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  haveI := isNoetherian_of_locallyOfFiniteType p
  compactSupportDualityOfPoints c _ (-i)
    (openDualityLinearEquiv p (standardUpperShriekDualizingComplex p c)
      (isDualizingComplex_standardUpperShriekDualizingComplex p c)
      ((restrictBoundedCoherentLift c.immersion).obj (compactificationDualizingObj c))
      (standardUpperShriekDualizingComplexIso p c).symm K i)

/-- **Stacks Project, Tag 0G5A.** Let `p : U ⟶ Spec k` be separated of finite type over a field
`k` and `ω_{U/k}^• = p^!𝒪_{Spec k}`. For `K ∈ D^b_{Coh}(𝒪_U)` and `i ∈ ℤ` there is a canonical
isomorphism of topological `k`-vector spaces

`Hom_k(H^i(U, K), k) ≃ H^{-i}_c(U, R𝓗om(K, ω_{U/k}^•))`,

for the topology of pointwise convergence on the dual (the limit topology over the finite
dimensional subspaces, `Module.Dual.limitTopology_eq_iInf_finiteDimensional`) and the limit
topology of [Stacks, Section 0G59] on compactly supported cohomology. It is functorial in `K`
(`AlgebraicGeometry.compactSupportDualityEquiv_naturality`). Here `p^!` and `H^*_c` are computed
at an arbitrary compactification `c` of `U` (one exists by [Stacks, Tag 0F41]). -/
@[stacks 0G5A "the isomorphism of topological k-vector spaces"]
def compactSupportDualityEquiv (K : BoundedCoherentDerived U) (i : ℤ) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    haveI := isNoetherian_of_locallyOfFiniteType p
    letI := Module.Dual.limitTopology k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj))
    Module.Dual k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj)) ≃L[k]
      compactSupportCohomology c
        (openDualObj (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) K) (-i) :=
  letI := HasDerivedCategory.standard U.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  haveI := isNoetherian_of_locallyOfFiniteType p
  letI := Module.Dual.limitTopology k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K.obj))
  (compactSupportDualityLinearEquiv p c K i).toContinuousLinearEquivOfIsHomeomorph
    (isHomeomorph_compactSupportDualityOfPoints c _ (-i) _)

/-- **Stacks Project, Tag 0G5A, functoriality.** The isomorphisms of
`AlgebraicGeometry.compactSupportDualityEquiv` are functorial in `K`: for `α : K ⟶ K'` and a
linear form `l` on `H^i(U, K')`, the image of `l ∘ H^i(α)` is the image of `l` under the map
`H^{-i}_c(U, D_U K') ⟶ H^{-i}_c(U, D_U K)` induced by `D_U α`. -/
@[stacks 0G5A "functoriality in K"]
theorem compactSupportDualityEquiv_naturality {K K' : BoundedCoherentDerived U} (α : K ⟶ K')
    (i : ℤ) (l :
      letI := HasDerivedCategory.standard U.Modules
      letI := HasDerivedCategory.standard (ModuleCat.{u} k)
      Module.Dual k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        ((derivedGlobalSectionsOver p).obj K'.obj))) :
    letI := HasDerivedCategory.standard U.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    haveI := isNoetherian_of_locallyOfFiniteType p
    compactSupportDualityEquiv p c K i
        (l ∘ₗ ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
          ((derivedGlobalSectionsOver p).map α.hom)).hom) =
      compactSupportCohomologyMap c
        (openDualMap (standardUpperShriekDualizingComplex p c)
          (isDualizingComplex_standardUpperShriekDualizingComplex p c) α) (-i)
        (compactSupportDualityEquiv p c K' i l) :=
  let := HasDerivedCategory.standard U.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} k)
  have := isNoetherian_of_locallyOfFiniteType p
  compactSupportDualityOfPoints_naturality c _ (-i) _ _ _
    (fun x => (openDualityLinearEquiv_naturality p _ _ _ _ α i x).symm) l

end AlgebraicGeometry

end
