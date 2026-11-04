module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation

/-!
# The top-degree identification for the twists on projective space

For a commutative ring `R`, for `n = m + 1 ≥ 1` and an integer `d ≤ -n - 1`, Serre's computation
identifies the top cohomology of a twisting sheaf on `𝐏^n_R` with a dual symmetric power. This
module records that identification in the form [Stacks, Tag 01XX] states it, namely

  `H^n(𝐏(E), 𝒪(d)) ≅ Hom_R(Sym^k(E) ⊗_R ⋀^{n+1}(E), R)`,  `E = R^{⊕ n + 1}`,  `k = -n - 1 - d`,

together with the two linear-algebra identifications it needs: the top exterior power of a free
module of rank `c` is the base ring, and `Sym^k(R^c) ⊗_R ⋀^c(R^c)` is the degree-`k` homogeneous
part of the polynomial ring on `c` variables.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.TopDegree.topExteriorPowerFreeEquiv`:
  `⋀^c(R^c) ≅ R`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.TopDegree.symTensorDetEquivHomogeneous`:
  `Sym^k(R^c) ⊗_R ⋀^c(R^c) ≅ (R[T₀, …, T_{c-1}])_k`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.TopDegree.topCohomologyTwistIsoSymTensorDet`:
  the `q = n` clause of [Stacks, Tag 01XX], over an affine base and for a free module, at the
  level of the cohomology module.

## The `q = n` clause

The `q = n` row of [Stacks, Tag 01XX] over an arbitrary base, for `ℰ` finite locally free of
constant rank, is
`Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageTopIso` in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Statement`; this module records the
identification at the absolute model, on the cohomology module.

## Implementation notes

Two deliberate choices keep this module from disturbing `BundleTwistVanishing`.

Nothing from `BundleTwistVanishing` is used, so it is not imported: adding imports to that
module would change the import closure of its pre-existing declarations, and hence the way
their statements elaborate.

The declarations sit in the sub-namespace `…ProjectiveBundleVanishing.TopDegree` rather than in
`…ProjectiveBundleVanishing` itself. The sub-namespace keeps them next to the vanishing clause
for reading while guaranteeing that no name here can collide with one declared there, under any
version of that module — a flat namespace shared between two modules is a collision surface,
and it produced one.
-/

open CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.TopDegree

@[expose] public noncomputable section

section TopDegree

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The only `c`-element subset of `Fin c` is the whole of it**, so the index type of the
monomial basis of the top exterior power of a free module of rank `c` is a subsingleton. -/
public theorem subsingleton_topPowersetCard (c : ℕ) :
    Subsingleton (Set.powersetCard (Fin c) c) :=
  ⟨fun s t => Subtype.ext <| by
    rw [Finset.eq_univ_of_card (s : Finset (Fin c)) (by simp),
      Finset.eq_univ_of_card (t : Finset (Fin c)) (by simp)]⟩

/-- **The top exterior power of a free module of rank `c` is the base ring**, `⋀^c(R^c) ≅ R`.
The basis of `⋀^c(M)` attached by `Module.Basis.exteriorPower` to a basis of `M` is indexed by
the `c`-element subsets of the index type, and for `M = R^c` there is exactly one. -/
public def topExteriorPowerFreeEquiv (R : Type u) [CommRing R] (c : ℕ) :
    ⋀[R]^c (Fin c → R) ≃ₗ[R] R :=
  letI := subsingleton_topPowersetCard c
  ((Pi.basisFun R (Fin c)).exteriorPower c).repr.trans
    (Finsupp.uniqueLinearEquiv R R (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin c) c))

/-- **`Sym^k(R^c) ⊗_R ⋀^c(R^c) ≅ (R[T₀, …, T_{c-1}])_k`.** The symmetric power of a module with
a basis is the degree-`k` homogeneous part of the polynomial ring on that basis, and the top
exterior power of a free module of rank `c` is the base ring, which the right unitor cancels. -/
public def symTensorDetEquivHomogeneous (R : Type u) [CommRing R] (k c : ℕ) :
    TensorProduct R (SymPow.symmetricPower k R (Fin c → R)) (⋀[R]^c (Fin c → R)) ≃ₗ[R]
      MvPolynomial.homogeneousSubmodule (Fin c) R k :=
  (TensorProduct.congr
      (SymPow.symmetricPowerEquivHomogeneousSubmodule (Pi.basisFun R (Fin c)) k)
      (topExteriorPowerFreeEquiv R c)).trans
    (TensorProduct.rid R _)

/-- **The top cohomology of the twists on projective space**: for a commutative ring `R`, for
`n = m + 1 ≥ 1`, an integer `d` and a natural number `k` with `k = -n - 1 - d`,

  `H^n(𝐏(E), 𝒪(d)) ≅ Hom_R(Sym^k(E) ⊗_R ⋀^{n+1}E, R)`,  `E = R^{⊕ n+1}`,

as `R`-modules. -/
@[stacks 01XX "the q = n identification for an affine base S = Spec R and a free module \
E = R^(n+1), n ≥ 1, on the cohomology module H^n(P(E), O(d))"]
public def topCohomologyTwistIsoSymTensorDet (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) (k : ℕ)
    (hk : (k : ℤ) = -((m + 1 : ℕ) : ℤ) - 1 - d) :
    Stacks.ProjectiveSpace.Cohomology.twistCohomology R (m + 1) d (m + 1) ≅
      ModuleCat.of R
        (TensorProduct R (SymPow.symmetricPower k R (Fin (m + 1 + 1) → R))
            (⋀[R]^(m + 1 + 1) (Fin (m + 1 + 1) → R)) →ₗ[R] R) := by
  have hd : d ≤ -((m + 1 : ℕ) : ℤ) - 1 := by push_cast at hk ⊢; omega
  have hk' : (-d - (((m + 1 : ℕ) : ℤ) + 1)).toNat = k := by push_cast at hk ⊢; omega
  refine (Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology R m d).degreeTopPolynomial hd
    ≪≫ ?_
  rw [hk']
  exact (LinearEquiv.arrowCongr (symTensorDetEquivHomogeneous R k (m + 1 + 1))
    (LinearEquiv.refl R R)).symm.toModuleIso

end TopDegree

end

end Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.TopDegree
